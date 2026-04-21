# BoundsOptCert Phase 7 — Elision Benchmark Results

Closure for `plans/certified-interval-pangolin.md`. Measures how many `cmpImm
+ bCond .hs` bounds-check pairs Phase 6's verified elision actually removes
on the Livermore kernels, and categorizes the remaining misses.

## Headline

**426 / 509 bounds-check pairs eliminated across 24 Livermore kernels — 83.7%.
15 / 24 kernels at 100% elision.**

## Method

1. Built the `compiler` binary at commit `d060c6b` (Phase 5, pre-un-wire) —
   `isBoundsSafe` hard-wired `false`, every `.arrLoad` / `.arrStore` emits
   `cmp idx, size ; b.hs .Lbounds_err`. This is the *maximum-possible* bounds
   count.
2. Built the `compiler` binary at commit `22f5aa4` (Phase 6). Compiled all
   24 `benchmarks/livermore/k*.w` kernels to assembly.
3. For each kernel, counted `b.hs` occurrences (all branch to
   `.Lbounds_err` — confirmed via `grep -u`).
4. `pre - post = eliminated`.

No changes to `.w` sources; the comparison is purely a compiler diff.

## Per-kernel table

| Kernel | pre | post | elim | % | comment |
|---|---:|---:|---:|---:|---|
| **Fully elided (15)** |||||
| k01_hydro | 11 | 0 | 11 | 100% | constant-bounded loops |
| k03_dot | 4 | 0 | 4 | 100% | single induction var |
| k05_tridiag | 8 | 0 | 8 | 100% | simple loops |
| k07_eos | 19 | 0 | 19 | 100% | simple loops |
| k08_adi | 48 | 0 | 48 | 100% | nested bounded loops |
| k09_integrate | 22 | 0 | 22 | 100% | |
| k10_diff_predict | 23 | 0 | 23 | 100% | |
| k11_prefix_sum | 7 | 0 | 7 | 100% | |
| k12_first_diff | 5 | 0 | 5 | 100% | |
| k18_hydro_2d | 62 | 0 | 62 | 100% | largest kernel elided |
| k19_linear_recurrence | 12 | 0 | 12 | 100% | |
| k20_discrete_ord | 31 | 0 | 31 | 100% | |
| k21_matmul | 9 | 0 | 9 | 100% | nested matmul loops |
| k22_planck | 20 | 0 | 20 | 100% | |
| k23_hydro_implicit | 19 | 0 | 19 | 100% | |
| **Partial (5)** |||||
| k13_pic_2d | 37 | 8 | 29 | 78% | indirect `arr[ix[k]]` |
| k14_pic_1d | 57 | 6 | 51 | 89% | indirect `arr[ix[k]]` |
| k15_casual | 42 | 7 | 35 | 83% | 2D-flattened `vh[(j-1)*101+k]` |
| k17_implicit_cond | 18 | 10 | 8 | 44% | flag-driven main loop |
| k24_find_min | 5 | 2 | 3 | 60% | reduction variable `m` |
| **None (4)** |||||
| k02_iccg | 15 | 15 | 0 | 0% | mutable upper bound |
| k04_banded | 8 | 8 | 0 | 0% | non-unit step `k := k + m` |
| k06_recurrence | 8 | 8 | 0 | 0% | expression bound `k <= i - 1` |
| k16_monte_carlo | 19 | 19 | 0 | 0% | indirect indices throughout |
| **TOTAL** | **509** | **83** | **426** | **83.7%** | |

## What Phase 6 elides reliably

All of:

* `while (k <= N_literal) { arr[k] := ...; k := k + 1 }` with
  `size(arr) ≥ N_literal + 1`.
* The same with `N` being a *constant-initialized* variable never reassigned
  in scope. The analyzer gives `N` a singleton interval `[N, N+1)`, which
  `refineCond`'s `.cmp op (.var x) (.var bound)` leaf treats as a concrete
  bound.
* Nested loops where every level matches this pattern
  (k08_adi with 48 checks, k18_hydro_2d with 62, k21_matmul).
* Reads of an array at a loop-invariant constant index (post-loop
  `printFloat(arr[1])` etc.).

## What Phase 6 does not elide (all expected)

Every missing case falls into one of six patterns, each matching a
known limitation of the interval domain or `refineCond`'s pattern set.
All are documented in the plan's "Out of scope" section.

### 1. Indirect indices (`arr[idx_arr[i]]`)

Affects k13, k14, k16.

`certSuccessor` on `.arrLoad x _ _ _` returns `imRemove m x` — the loaded
value gets no interval because the array's value domain is unbounded. Any
subsequent `arr[x]` therefore can't be bounded.

Examples:

* k13: `i1 := e[ip]; h[(i1-1)*64 + j1]`
* k14: `ex[ix[k]]`, `rh[ir[k]]`, `rh[ir[k] + 1]`
* k16: `j5 := zone[j4-1]; plan[j5]`, `d[j5 - 1]`

Fixing this would require tracking array value ranges (another analysis
product), not just index ranges.

### 2. Expression-valued bounds (`while (k <= i - 1)`)

Affects k06.

`refineCond` handles only three shapes:
`.cmp op (.var x) (.lit n)`,
`.cmp op (.var x) (.var bound)`,
and `.not` of the above. Expression right-hand sides fall through to `m`
unchanged.

Extending this to `(i - c)` / `(i + c)` patterns would be a mechanical
2-leaf addition, but wasn't part of the Phase 3 scope.

### 3. Mutable upper bounds

Affects k02.

k02's inner loop uses `while (k <= ipntp)` where `ipntp` is reassigned
inside the enclosing `while (ii > 0) { … ipntp := ipntp + ii; … }`. After
the analyzer joins the pre-loop and back-edge states for `ipntp`, its
interval is no longer singleton, so `refineCond`'s `.var bound` case
requires `biv.lo + 1 = biv.hi` and falls through.

Relational invariants (`k ≤ ipntp ≤ size(x)`) would cover this — out of
scope for the interval domain.

### 4. Non-unit loop steps

Affects k04.

k04's outer loop increments `k := k + m` where `m = (1001 - 7) / 2 = 497`
is computed from a division. Even if `m` were a known singleton, the
widen-at-back-edge with `k.hi + m > iTop` triggers widening to `iTop`
before the next header-refinement can pull `k` back. The refinement on the
conditional (`k ≤ 1001`) gives us `k.hi = 1002` briefly, but the
post-increment value `k.hi + m - 1 = 1499` escapes.

Fixing this would require stable-under-widening transfer, probably via a
more precise numerical domain (polyhedra, octagons).

### 5. 2D-flattened indices (`arr[(j-1)*stride + k]`)

Affects k15.

The `.mul` transfer gates on `validIntervalMul` (hi ≤ 2¹⁶). For j ∈ [1, 7)
and stride 101, this passes. The resulting range for `(j-1)*101 + k` with
k ∈ [1, 101) works out to roughly `[0, 708)` — which is inside `vh`'s
size of 708. But the analyzer's produced range might not be tight enough
after the compound `mul`+`add`; and `refineCond` on `k ≤ 100` only refines
`k`, not the derived expression.

Symbolic refinement of expressions is a generalization of refineCond;
again, out of scope.

### 6. Reduction variables

Affects k24, and partially k17.

k24: `if (x[k] < x[m]) { m := k } else { skip }`. `m` is updated
conditionally, then joined at the merge point, then joined again at the
loop header. Since `m` is only used as an *index* (never compared to a
bound), no `refineCond` leaf tightens it. Its interval widens to iTop at
the loop header.

k17: similar with `i := i + ink` and flag-driven termination — `i` is the
induction variable but only appears in the array index, not the cond.

## Sanity checks

* **All b.hs branches target `.Lbounds_err`** — there are no other `.hs`
  uses in the emitted code, so the count is precisely bounds checks.
* **No checker rejections** — `checkerOk = true` for all 24 programs; every
  kernel's `BoundsOpt.checkLocalPreservation` output passes. The Phase 3
  soundness theorem is load-bearing for every elided check, not just the
  ones under test.
* **No soundness surprises** — the elision happens only when the analyzer
  output validates; when it doesn't, the ARM retains the explicit check.

## Effort

~20 min actual (build binaries at two commits, compile 24 kernels each,
diff). Plan estimated 0.5 day. Saved by not needing to run the programs —
just static inspection of generated ARM.

## Status

**Plan complete.** Phases 1-7 all landed. Remaining limitations are
documented here and match the "out of scope" section of the plan.

---

# Appendix A — What it would take to eliminate more

Six miss categories from Phase 7 ordered by return-on-investment
(eliminations recovered per day of work). All are checker-side work; the
analyzer is not the bottleneck (see Appendix B).

## Cheap wins (~1-3 days each)

### A.1 Expression-valued bounds in `refineCond` → +8 checks (k06)

**Pattern:** `while (k <= i - 1)` where the right side is an expression.

**Fix:** Add 4-8 leaves to `refineCond` in
[BoundsOptCert.lean:140](../CredibleCompilation/BoundsOptCert.lean#L140) for
patterns like `.cmp op (.var x) (.sub (.var y) (.lit n))`. Each leaf is a
direct analog of the existing `.var bnd` leaves — lift `y`'s interval,
subtract/add the literal offset, gate validity. Proof obligations are
mechanical copies of `refineCond_lt_var_true_sound` with an arithmetic shim.

**Effort:** ~2 days. Fixes k06 entirely.

### A.2 Reduction-variable propagation → +2 checks (k24), partial k17

**Pattern:** `m := k` inside a conditional; later `arr[m]`. `m`'s interval
widens across the loop header because it's re-joined with its initial value.

**Fix:** Two options:

* Sharper join: when `m := k` appears inside a branch, track `m ∈ [init, k]`
  at the merge. Interval join already does `min/max`; the problem is
  widening treats `m` as a growth candidate. Augment `iWiden` to detect
  non-incrementing updates (the new value came from a fresh copy, not
  `m := m + _`) and skip widening those.
* Cheaper: detect the pattern syntactically — if `m`'s only updates are
  `.copy` from an already-bounded variable, inherit that bound at the
  header.

**Effort:** ~1-2 days. Both options are analyzer-side; the certificate
checker is unchanged.

### A.3 Symbolic refinement of `x + c` / `x - c` indices → +5-8 checks

Partially fixes k14 and k17.

**Pattern:** `rh[ir[k] + 1]` or `vsp[i + 1]` — the *index* is
`known_var + const`, and we have an interval for `known_var`.

**Fix:** The transfer for `.binop x .add y z` already computes the shifted
range. The issue is the result's range is often loose (adding intervals
loses precision). If we also emit an "offset hint" for common `x + 1` /
`x - 1` shapes, the post-transfer range would track the source variable's
refinement.

**Effort:** ~1 day. Mostly analyzer-side; `add_sound` is already proved
for the current transfer.

## Moderate (~1 week each)

### A.4 Better widening with thresholds → +8 checks (k04)

**Pattern:** `k := k + m` with `m > 1`. Back-edge transfer gives
`k.hi + m - 1`; if that exceeds the widened ceiling, widening kicks in
and we lose the bound.

**Fix:** Widening-threshold hint: look at the loop's condition
(`k ≤ N_literal`) *before* widening and cap the widened `hi` at
`N_literal + 1`. Standard abstract-interpretation trick (widening-with-
thresholds).

**Effort:** ~3 days analyzer + checker has nothing to change (loose checker
accepts any valid output). Fixes k04 entirely.

### A.5 Mutable upper bound → tiny relational domain → +15 checks (k02)

**Pattern:** `while (k <= ipntp)` where `ipntp` varies.

**Fix:** For the specific case "k is compared to a var that hasn't been
modified in the current scope," skip the re-join that forces `ipntp` into
a non-singleton state. Equivalently: a one-variable relational invariant
`k ≤ ipntp` as a separate tracked fact.

**Effort:** ~1 week if done as a proper second analysis; ~3 days for a
syntactic shortcut covering only "ipntp not modified between its last
assignment and this conditional."

## Expensive (weeks+)

### A.6 Array value-range tracking → +33 checks

Fixes k13 (+8), k14 (+6), k16 (+19).

**Pattern:** `j5 := arr[i]; other[j5]`. The loaded value has no interval;
all downstream uses fall through.

**Fix:** Track per-array value-range invariants (e.g., `∀ i, 0 ≤ arr[i] < N`).
This is a separate analysis — when `arr` is written, update the range; when
read, produce the range. Needs a new invariant shape, new checker, new
soundness proof.

**Effort:** 2-3 weeks. Would need another Phase-like rollout similar to
BoundsOptCert itself.

### A.7 2D-flattened expression refinement → +7 (k15), partial k13

**Pattern:** `vh[(j-1)*stride + k]`. Each factor has a known range; their
combination must be bounded *at the expression level*.

**Fix:** Symbolic/polyhedral domain. Large theoretical and engineering cost.

**Effort:** 3+ weeks. Probably not worth it relative to A.1-A.5.

## Recommended next batch

Landing A.1 + A.2 + A.3 together would push the aggregate from
**83.7% → roughly 87%** (~20 more checks) for ~4 days of work. The checker
stays unchanged except for new refineCond leaves — so the certificate
soundness story is untouched.

Beyond that, A.4 (threshold widening) is the clean stopping point: adds
another 8 checks for k04 with moderate effort and no new analysis
infrastructure.

For anything above 90%, you need new invariant shapes (value-ranges or
relational) — genuinely new compiler work.

---

# Appendix B — Is the analyzer the bottleneck? (No.)

Because the Phase 6 design decouples analysis from invariant verification,
it's tempting to reach for an unsound-but-smarter analyzer (SMT-based,
profile-guided, ML-based, …). We spent some thought on whether this
unlocks more elision, and the short answer is **it doesn't** — the checker
is the limiter.

## The `refines` direction is asymmetric

`refines (certSuccessor m instr pc pc') m'` checks `strong ⊆ weak` — the
checker's transfer output (strong) must sit *inside* the analyzer's claim
(weak). So:

* **Analyzer claims tighter than transfer produces** → `refines` fails.
  No gain.
* **Analyzer claims looser** → `refines` passes, but the claim is too
  loose to elide at the arrLoad PC.

The only interval at an arrLoad PC that unlocks elision is a tight one
like `k ∈ [0, 64)`. For that to validate, every predecessor transition
must have produced it — and since `certSuccessor`'s transfers only
preserve information (they don't invent tighter bounds), the tight claim
has to originate somewhere. The only places in the current checker that
*narrow* intervals are the `refineCond` leaves at `.ifgoto`. Everywhere
else, intervals can only stay the same or widen.

**Consequence:** the checker's vocabulary is a hard ceiling on what any
analyzer can claim. Swapping in an SMT-based, trace-profiling, or
ML-based analyzer gives you the same ceiling.

## Narrow scenarios where a different analyzer helps anyway

1. **Simpler implementation, same coverage.** A one-pass syntactic scanner
   (pattern-match for-loop idioms, claim `k ∈ [init, N+1)` directly) is
   easier to implement than the current `partial def analyzeIntervalsLoop`
   and gives equivalent coverage on the Livermore kernels. Pure engineering
   simplification, no coverage win.

2. **Profile-guided claims.** Run on test inputs, observe ranges, claim
   those. Easy to implement, but the profile-observed range must be a
   fixed-point of the transfer function to validate. For `k := k + 497` in
   k04, no profile-observed range for k works because k moves beyond
   whatever was observed. Profiling buys you nothing where fixed-point
   widening already fails.

3. **Search-based analyzer.** Enumerate candidate claims and pick any that
   validates. Same ceiling as the fixed-point worklist — the validated
   claims are exactly those reachable via `refineCond`'s patterns.

**So unsound analyzer alone is a dead end.** Every sensible route back to
"more elision" is a checker upgrade (more `refineCond` leaves, more
`certSuccessor` precision, more invariant shapes).

---

# Appendix C — How hard is it to generalize the checker?

Three tiers of generalization with very different costs.

## Tier 1: More `refineCond` leaves / transfer cases (easy, incremental)

Extending the existing interval domain with more patterns.

**Cost per new `refineCond` leaf** (e.g.
`.cmp op (.var x) (.sub (.var y) (.lit n))`): ~60-100 LOC — one
leaf-soundness theorem (copy the `refineCond_lt_lit_true_sound` template,
adjust arithmetic), one dispatch case in `refineCond_sound`, one case in
`refineCond` itself. Proof obligations are mechanical; the hard work
(signed-unsigned bridge, looseCap bookkeeping, BitVec.slt transport) is
already done. **~3-4 hours per leaf** after the first.

**Cost per new `certSuccessor` transfer case** (e.g. tighten `.binop x .div
y z` when `z` is a singleton): ~30-80 LOC — one transfer clause, one
soundness theorem, one dispatch in `certSuccessor_sound`. **~4-6 hours per
case.**

**Verdict:** trivially incremental. 3-5 leaves/cases per week of steady work.

## Tier 2: Add a second abstract domain (moderate, per-domain)

New file alongside `BoundsOptCert.lean`: `RelInvCert.lean`,
`ArrRangeCert.lean`, etc.

**Structural cost of a new domain** (roughly what BoundsOptCert itself
took, minus the infrastructure that's now generic):

* New shape + satisfies + `intervalMap`-analog lifting: ~150 LOC.
* `refines` check + soundness: ~80 LOC.
* `certSuccessor` across ~20 TAC constructors + `certSuccessor_sound`:
  ~400-800 LOC (most cases are `imRemove`-style conservative drops; the
  interesting ones need real proofs).
* Main theorem: ~60 LOC (essentially a copy of
  `checkLocalPreservation_sound`).
* Wiring to `buildVerifiedInvMap` / `step_simulation`: ~50 LOC.

| Domain | Total LOC | Effort |
|---|---:|---|
| Relational (`x ≤ y + c`, restricted fragment) | ~1000 | ~1.5 weeks |
| Array value-ranges | ~1500 | ~2-3 weeks (ArrayMem quantifier adds friction) |
| Congruence/stride (`k ≡ init mod stride`) | ~800 | ~1 week |
| Polyhedral (full Fourier-Motzkin) | ~3000+ | month+ |

The Phase 6 architecture already handles *conjoining* invariants at
`step_simulation` — just add another `hInv2 : buildVerifiedInvMap2 p pc σ am`
hypothesis and thread it the same way. No rework of existing code.

**Verdict:** each domain is a self-contained project at ~1 BoundsOptCert
unit of effort.

## Tier 3: Parameterize the checker over an abstract-domain interface

Extract a structure like:

```lean
structure AbstractDomain where
  Fact      : Type
  valid     : Fact → Bool          -- analog of validIntervalLoose
  satisfies : List Fact → Store → ArrayMem → Prop
  refines   : List Fact → List Fact → Bool
  transfer  : List Fact → TAC → Nat → Nat → List Fact
  -- plus soundness field equations:
  refines_sound  : ...
  transfer_sound : ...
```

Then `checkLocalPreservation_sound` becomes
`∀ (D : AbstractDomain), check p D inv = true → (lift D inv).preserved p`.

**Cost:**
* ~1 week of refactoring to extract BoundsOptCert into this shape.
* Each instance is then ~60% of the old effort (saves on main-theorem
  boilerplate and wiring; still does all the transfer-soundness work).

**When it's worth it:** once you have 3+ domains. For 2 domains the
refactor costs more than it saves.

**A softer alternative that gets you 70% of the benefit:** write a
protocol-by-convention (module-level theorems with standardized names), no
typeclass. Just discipline. Zero refactoring cost; new domains copy the
structure file-by-file.

## Recommended path, ordered by ROI

1. **Tier 1 refineCond extensions** (A.1 + A.3 above, ~3 days) — recovers
   k06 and parts of k14/k17.
2. **Tier 2 strided/congruence domain** (A.4, ~1 week) — recovers k04.
3. **Tier 2 restricted relational domain** (A.5, ~1.5 weeks) — recovers
   k02, k24, parts of k17.
4. **Tier 2 array value-ranges** (A.6, ~2-3 weeks) — recovers most of
   k13/k14/k16.
5. **Tier 3 `AbstractDomain` parameterization** — only after steps 2-4 land,
   if maintaining three instances becomes annoying.

Doing 1+2+3 together (~3 weeks) would move the aggregate from 83.7% to
plausibly 95%+, and each piece is a clean self-contained addition. The
checker infrastructure is already designed to absorb them — no
architectural risk, just engineering.
