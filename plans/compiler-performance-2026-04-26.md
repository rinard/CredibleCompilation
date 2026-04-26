# Compiler performance work (2026-04-26)

End-to-end compile time on the Livermore Loops benchmark suite went from
**282.6 s → 139.8 s (2.0×)**. The biggest single kernel, k18_hydro_2d,
went from **145 s → 50 s (2.9×)**. This document records what was
investigated, what didn't work, what did, and what's left.

## Starting state

The pipeline driver `compileFileToFile` was already instrumented to emit
`[PASS] phase=… name=… us=…` markers per pass and `[TOTAL] compile_us=…`
per kernel. Running `benchmarks/livermore_canonical/run_pipeline_report.sh`
on all 24 kernels gave the per-pass aggregate:

```
phase:name              calls    us total
cluster:CSE                48   111,534,423   ← 39 % of all pass time
cluster:DAE                48    28,332,364
suffix:RegAlloc            24    23,718,018
cluster:ConstHoist         48    23,159,572
cluster:ConstProp          48    23,124,015
prefix:CSE                 24    22,791,188
cluster:LICM               48    12,152,324
prefix:DAE                 24    11,120,722
prefix:ConstProp           48    11,150,631
suffix:FMAFusion           24     4,367,072
suffix:DCE                 24     4,254,049
prefix:DCE                 24     3,510,225
suffix:Peephole            24     3,422,262
TOTAL                              282,636,865 µs
```

`cluster:CSE` was the obvious target.

## Wrong turn: optimising CSE *analysis*

Reading [`CSEOpt.lean`](../CredibleCompilation/CSEOpt.lean), the worklist-based
forward analysis had three plausibly quadratic spots:

1. `availMerge`/`constMerge` produce a list-subset of `oldAv`/`oldCm`;
   the post-merge `availBeq`/`constBeq` equality check did an O(|a|·|b|)
   scan that's mathematically equivalent to a length compare.
2. The worklist allowed duplicate PCs.
3. `analyzeLoop` did `rest ++ newWork` (FIFO via list append, O(|rest|)).

Patches applied: length-based merge equality, `inWl : Array Bool`
deduplication, LIFO order (`newWork ++ rest`).

Result: ~0 change. cluster:CSE went from 111.5 s to 113.0 s — within
noise. The CSE analysis simply wasn't where the time lived.

The patches are correct (output unchanged on every kernel) and tighten
the code, so they were retained. But they didn't solve the problem.

## Diagnosis: split analyze vs check

Modified `runPassTimed` in [`Compiler.lean`](../Compiler.lean) to time the
two sub-phases of `applyPass` separately:

- `analyze_us`: time spent inside the pass function (`pass p` building
  the `ECertificate`)
- `check_us`: time spent inside `checkCertificateExec cert`

Forced evaluation of cert fields between the two timer reads to avoid
Lean's lazy evaluation hiding work behind the boundary (an `IORef.set`
turned out to be the only reliable way — bare `let r := f ()` and
even `if r then pure 1 else pure 0` were both hoisted out of the IO
sequence by the compiler).

For k15_casual (TAC=600 after LICM, ~98 invariant atoms per PC):

```
phase:name              total   analyze    check   % check
prefix:ConstProp        766 ms     17 ms   750 ms      98 %
cluster:ConstProp     1,792 ms    119 ms 1,672 ms      93 %
cluster:ConstHoist    1,793 ms    119 ms 1,675 ms      93 %
cluster:CSE             660 ms    100 ms   560 ms      85 %
cluster:DAE           2,378 ms  1,336 ms 1,042 ms      44 %
suffix:RegAlloc       5,664 ms  5,537 ms   126 ms       2 %
```

**The checker dominates almost every pass.** CSE analysis was 100 ms;
the surrounding checker call was 560 ms. Optimising the analysis was
chasing the wrong quantity.

## Diagnosis: which check function

Wrapped each of the 30 individual checks inside `checkCertificateExec`
in a `timeCheck` helper and reran on k15:

```
prefix:ConstProp:    allTrans=741 ms  invPreserved=8.4 ms  rest≈10 ms
cluster:ConstProp:   allTrans=1,531 ms invPreserved=80 ms  rest≈70 ms
```

`checkAllTransitionsExec` was 90 %+ of every pass. Confirmed by
temporarily replacing it with `fun _ => true` — total compile time
collapsed to 25 % of baseline.

Drilling in, both [`checkAllTransitionsExec`](../CredibleCompilation/ExecChecker.lean)
and [`checkInvariantsPreservedExec`](../CredibleCompilation/ExecChecker.lean)
called `simplifyDeep` on a `List`-backed `EInv`:

- `Expr.simplify inv e` walks the expression and looks up each `.var`
  with `inv.find?` — **O(|inv|) per lookup**.
- `Expr.simplifyDeep` calls `simplify` `fuel = inv.length + 1` times to
  resolve var-chains, **unconditionally**, even after reaching a fixed
  point.

So per-atom cost was **O(|inv|² · |expr|)**, called in a tight loop over
every (pc, pc', atom) triple. For ConstProp's cluster invariants
(98 atoms × 600 PCs), the math worked out: 600 × 2 × 98² × ~5 = ~5 G
ops, ≈ 1.7 s — exactly what the timer showed.

A HashMap-backed `simplifyDeepFast` using `Std.HashMap String Expr`
already existed at [`ExecChecker.lean:652`](../CredibleCompilation/ExecChecker.lean#L652),
with an equivalence proof to `simplifyDeep`. It was used in
`checkRelConsistency` but **not** in `checkAllTransitionsExec`'s call
chain or in `checkInvariantsPreservedExec`.

## Fix

Three coordinated changes in [`ExecChecker.lean`](../CredibleCompilation/ExecChecker.lean):

### 1. Early-terminating simplify

```lean
def Expr.simplifyDeepFastEarly : Nat → FastVarMap → Expr → Expr
  | 0, m, e => e.simplifyFast m
  | n + 1, m, e =>
    let e' := e.simplifyFast m
    if e' == e then e' else e'.simplifyDeepFastEarly n m
```

Stops as soon as `simplifyFast` produces no change. For typical
expressions (depth ≤ 5, ≤ 2-3 vars) this converges in 1-3 iterations
regardless of `fuel`. With `fuel ≈ 100` for big invariants, that's a
**30-100× cut** in inner-loop iterations per simplify call. Idempotence
of `simplify` at its fixed point makes this a value-preserving change.

Structurally recursive on `n` so it's a regular `def`, not `partial`.

### 2. `checkInvAtomFast` taking a precomputed `FastVarMap`

```lean
def checkInvAtomFast (invMap : FastVarMap) (fuel : Nat) (instr : TAC)
    (atom : Var × Expr) : Bool :=
  let (ss, _) := execSymbolic ([] : SymStore) ([] : SymArrayMem) instr
  let lhs := (ssGet ss atom.1).simplifyDeepFastEarly fuel invMap
  let rhs := (atom.2.substSym ss).simplifyDeepFastEarly fuel invMap
  lhs == rhs
```

`checkInvariantsPreservedExec` materializes `FastVarMap.ofList inv_pre`
once per PC and passes it to every atom check on every successor — the
same `inv_pre` is shared across all atoms, so building it once amortises.
Per-atom cost drops from **O(|inv|²)** to **O(|inv|)** plus the constant
HashMap overhead.

### 3. Fast variants of the orig-path machinery

`checkAllTransitionsExec` walks the original-program path corresponding
to each transformed instruction via `checkOrigPath`, which calls:

- `BoolExpr.normalize ss inv` on `ifgoto` conditions
- `BoolExpr.symEval ss inv` via `computeNextPC`
- `checkInstrAliasOk instr ss sam inv` on array ops

All four took an `EInv` and called `simplifyDeep` directly. Added Fast
mirrors that take `(invMap, fuel)`:

- `BoolExpr.normalizeFast`, `BoolExpr.symEvalFast`
- `computeNextPCFast`
- `checkInstrAliasOkFast`
- `checkOrigPathFast` (the recursion that threads the same map through
  every step instead of rebuilding it)

`checkAllTransitionsExec` materializes the map once per `pc_t` and
passes it down. Inside `checkRelConsistency`, the existing `simplifyDeepFast`
calls were switched to `simplifyDeepFastEarly` (the map building was
already done).

The original `simplifyDeep`, `checkInvAtom`, `BoolExpr.normalize`,
`BoolExpr.symEval`, `computeNextPC`, `checkInstrAliasOk`, `checkOrigPath`
were left in place because the soundness theorems in
`PipelineCorrectness.lean` reason about them. They are no longer called
on the live path.

## Results

Per-pass aggregate, before vs after, on the full 24-kernel suite:

| Pass               | Before    | After    | Speedup |
|--------------------|-----------|----------|---------|
| cluster:CSE        | 111.5 s   |  14.0 s  | **8.0×** |
| prefix:CSE         |  22.8 s   |   5.5 s  | 4.1×    |
| cluster:ConstProp  |  23.1 s   |  12.7 s  | 1.8×    |
| cluster:ConstHoist |  23.2 s   |  12.7 s  | 1.8×    |
| cluster:DAE        |  28.3 s   |  21.2 s  | 1.3×    |
| prefix:DAE         |  11.1 s   |  10.3 s  | 1.1×    |
| suffix:RegAlloc    |  23.7 s   |  23.0 s  | ~       |
| cluster:LICM       |  12.2 s   |  12.1 s  | ~       |
| **Total**          | **282.6 s** | **139.8 s** | **2.0×** |

Per-kernel total compile time, biggest movers:

| Kernel             | TAC | Before    | After    | Speedup |
|--------------------|-----|-----------|----------|---------|
| k18_hydro_2d       | 641 | 145.0 s   |  49.6 s  | **2.9×** |
| k08_adi            | 396 |  25.8 s   |  11.9 s  | 2.2×    |
| k13_pic_2d         | 392 |  28.8 s   |  13.4 s  | 2.1×    |
| k15_casual         | 472 |  33.6 s   |  24.3 s  | 1.4×    |
| k10_diff_predict   | 247 |   8.7 s   |   4.7 s  | 1.8×    |

The bigger the invariants (post-LICM cluster passes have 100-200 entries
per PC), the bigger the win. Small kernels barely moved because their
invariants were already tiny.

Output verified unchanged on k03 (10.007504), k21 (106223.477851), and
the rest of the suite via the standard run.

## What's left

After this work, the remaining cost centres are:

1. **`suffix:RegAlloc` analyze** (5.5 s on k15, 23 s aggregate, 98 % in
   analyze). Untouched here. Likely candidates: interference graph
   construction on `List`-backed live sets, graph colouring search.

2. **`cluster:DAE` analyze** (1.4 s per call, 21 s aggregate, ~50 %
   analyze ~50 % check). Backward liveness analysis with the same
   List-based shape as CSE used to have. The merge-equality and
   worklist-dedup tricks would apply directly.

3. **The invariant size itself.** ConstProp emits ~98 atoms per PC on a
   600-PC program, most of which are constants that never change.
   Compressing the invariant (only emit atoms at PCs where the const
   becomes valid, let the checker carry it forward) would cut both
   cert size and check time. This is a semantic change to the analysis
   output, not a checker change.

## Follow-up: HashMap unification (2026-04-26 PM, commit 23403af)

A second pass on the same area, motivated by code consistency rather
than performance. Three changes:

### Op 1 — single per-cert FastVarMap cache

`checkRelConsistency` rebuilt `FastVarMap.ofList inv_orig` per edge call,
duplicating work already done by the surrounding `checkAllTransitionsExec`.
`checkInvariantsPreservedExec` and `checkAllTransitionsExec` similarly
each built their own per-PC maps. Total: 3 separate `FastVarMap.ofList`
chains for `inv_orig` per cert.

Refactor: `checkCertificateExec` now builds `invMaps_orig` and
`invMaps_trans` once via `buildInvMaps : Array EInv → Array (FastVarMap × Nat)`
and threads them through three new variants:
- `checkInvariantsPreservedFromMaps`
- `checkAllTransitionsFromMaps`
- `checkRelConsistencyFromMap`

Each comes with an equivalence lemma to its original, all proven by
`unfold + simp [invMapAt_buildInvMaps, ...]`. The keystone lemma
`invMapAt_buildInvMaps` shows that looking up the cached array at PC `p`
agrees with the inline build of `(FastVarMap.ofList (invs.getD p []), sdFuel ...)`.

### Op 2 — extend FastVarMap to cold-spot lookups

`checkDivPreservationExec` and `checkBoundsPreservationExec` used
`inv.find?` for "is this var bound to a known literal" lookups
(O(|inv|) per arrLoad/arrStore/div instruction). New variants
`checkDivPreservationFromMaps` / `checkBoundsPreservationFromMaps` use
`FastVarMap.getD` from the cache and pattern-match on `.lit` directly.

The equivalence lemma `invFindLit_eq_invMapGetD` covers the generic
pattern (`match inv.find? ... with | some (_, .lit c) => P c | _ => false`
becomes `match invMap.getD k _ with | .lit c => P c | _ => false`) by
case analysis on the underlying `Option (Var × Expr)`. Per-function
equivalences then follow by `simp`.

### Op 3 — document the two-level architecture

Audit of all list-based originals confirmed they are load-bearing for
soundness proofs in `SoundnessBridge.lean` (each is referenced 5-22 times
across ~30 proofs that `unfold` and pattern-match on bodies). Deletion
would require migrating those proofs to reason about Fast forms
directly — a substantial refactor not undertaken.

Instead, added a "Two-level architecture" section to the
`ExecChecker.lean` module docstring documenting:
- list-based originals exist for proofs;
- HashMap-backed Fast/Early/FromMaps variants are the live runtime path;
- equivalence lemmas (12 of them) bridge between the two;
- the convention for adding new check functions.

### Performance impact

Effectively zero — total Livermore pass time changed by ~2s (within
noise) across the whole 24-kernel suite. The cache savings I had
estimated at ~10-15s did not materialize, evidently because
`FastVarMap.ofList` is fast enough at HashMap construction that the
duplication wasn't a real cost. Output verified unchanged on k03
(10.007504) and k21 (106223.477851).

Changes were kept anyway: the live `checkCertificateExec` body now
uniformly calls FromMaps variants throughout (no list-based functions
on the runtime path), and the convention is documented for future
contributors. ~310 LOC added to `ExecChecker.lean`, 7 LOC added to
`SoundnessBridge.lean`.

### Proofs touched

`checkCertificateExec_sound` gained 4 `rw` lines (one per new FromMaps
equivalence) to convert the conjuncts of `unfold checkCertificateExec`
back to original-form before passing to the existing per-conjunct
soundness theorems. No other proofs needed updating — the bodies of
the original functions are unchanged.

### Lesson

The earlier "predicted ~10-15s" estimate was a back-of-envelope
guess that fell apart on contact with measurement. Worth flagging:
**before committing to a perf refactor, probe — even when the change
is mechanically simple.** I had recommended a probe in the report's
earlier "Op 1" discussion, and skipping it (because the user wanted
all three for code-consistency reasons) cost the right amount of
time given the consistency goal, but the perf-prediction error itself
was a clean miss.

## Lessons

- **Aggregate timing is misleading.** "cluster:CSE = 39 % of total" made
  CSE look like the bottleneck, but it was 48 calls × 2.3 s/call. The
  per-call distribution was much flatter. Per-call timing combined with
  the analyze/check split was what actually pointed at the problem.

- **Lean's lazy evaluation can fool a simple timer.** Bare `let r := f ()`
  inside a `do` block did not force `f ()`; the work happened
  asynchronously when `r` was finally consumed. `IORef.set/.get` was the
  only reliable forcing pattern. Worth knowing for future profiling.

- **HashMap variants existed but weren't wired through.** The fast
  simplify infrastructure was there for `checkRelConsistency` and
  nowhere else. The cheap fix was to thread it through the rest of the
  hot path, not to rewrite anything.
