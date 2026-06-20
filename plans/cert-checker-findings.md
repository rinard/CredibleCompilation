# Findings: Stress-Testing a Credible (Certifying) Compiler

Catalogue of defects found and fixed while stress-testing the Credible
Compilation compiler (While → certificate-checked optimization passes → verified
ARM64 codegen), for the paper's evaluation/findings section. Branch
`fix/cert-checker-completeness`.

## ⚠ Most significant finding: unfaithful ARM shift semantics — FIXED (commit c0ccf71)

A single unfaithful definition in the **trusted target-ISA operational semantics**
produced BOTH a real miscompilation AND an apparent certificate-checker soundness
hole. This is the campaign's headline result and a clean methodological story.

### The defect

The shift amount was modelled as the **full** 64-bit value in three places that
must agree, while **real AArch64 `lsl`/`asr`/`lsr` use only the low 6 bits of the
amount register (amount mod 64)**:

- `Core.lean` `BinOp.eval`: `shl a b = a <<< b`, `shr a b = sshiftRight a b.toNat`.
- `ArmSemantics.lean` relational `ArmStep`: `lslR … = rn <<< rm`,
  `asrR … = sshiftRight rn (rm).toNat`.
- `PipelineCorrectness.lean` executable `armStepResult`: the same.

Because all three used the full amount, the verified codegen proof related
TAC→ARM-model faithfully — but the model was wrong about the hardware it claims to
describe.

### Manifestation 1 — a real miscompile (binary ≠ verified semantics)

Reproduced from ordinary source (the front end imposes no `& 63` on shift amounts):
```
x := 12345; a := 0; i := 0; while (i<7){ a := a+10; i := i+1 };  -- a = 70 at runtime
r := x >> a
```
Old verified TAC semantics: `sshiftRight 12345 70 = 0` (shifted past width → sign
bits). Assembled binary: **192** = `asr(12345, 70 & 63 = 6)`. The binary disagreed
with the verified semantics for any **runtime** shift amount ≥ 64. (Constant
amounts ≥ 64 are folded at compile time and were already correct; only *runtime*
amounts in a register expose it.)

### Manifestation 2 — an apparent checker soundness hole (same root cause)

`BinOp.eval` is also used by the checker's constant folding inside
`simplify`/`checkRelConsistency`. When an optimization moves a value ≥ 64 into the
amount position (here: a register-reuse pattern where the dividend/operand and the
shift amount were swapped), the checker folded BOTH `shr a b` and `shr b a` to `0`
(each shifted out under the full-amount semantics) and therefore deemed the swapped
program equivalent → it **accepted a non-equivalent transform**. The masked binary
then computed two different nonzero values, and the divergence surfaced. The
checker's acceptance was *sound relative to its (wrong) model* — exactly the
diagnosis: not a checker-logic bug, a semantics bug.

### How it was found

The overnight **certificate-mutation soundness campaign** (`certmutate`) corrupts a
valid certificate's transformed program and requires the checker to reject; an
accept whose codegen output diverges is flagged. On random program seed 30 it
flagged a `swap` of a `shr` that the checker accepted but whose binary diverged.
The key diagnostic principle — *the checker is proven sound against the TAC
operational semantics, so accept + divergent-binary ⇒ a TAC-vs-ASM semantics
mismatch* — localized it to shift-amount masking; it then reproduced from plain
source. **Differential testing (While vs C/Fortran) cannot find this**: C shift by
≥ width is undefined, so the generators mask amounts (`& 63`) and there is no
oracle for the divergent case. Mutation testing manufactured the out-of-distribution
input fuzzers under-sample.

### The fix (hardware-faithful masking)

Mask the amount to its low 6 bits (`mod 64`) in all three places, so the source
language, the trusted ARM model, and the executable model all match real AArch64:
- `BinOp.eval`: `shl a b = a <<< (b.toNat % 64)`, `shr a b = sshiftRight a (b.toNat % 64)`.
- `ArmStep` `lslR`/`asrR` and `armStepResult`: same `% 64`.

Proof impact was minimal: the codegen correctness cases for `lslR`/`asrR` are `rfl`
and stay `rfl` because all three masks are syntactically identical; **full `lake
build` green (3139 jobs, 0 `sorry`)**. This changes the *source-language* meaning of
`>>`/`<<` to the hardware-faithful `shift by (amount mod 64)`, consistent with the
project's "data types identical to hardware" design.

Verified after the fix: the runtime-amount program now yields the consistent masked
result (`192`) under *both* the verified semantics and the binary; the seed-30
soundness hole is resolved (the swap is now correctly **rejected** — accepted
mutations dropped 40→38); the 81 differential tests still pass.

### Lesson for the paper

A bug in the *trusted* target-ISA semantics is invisible to a verified compiler's
proofs (the compiler was provably correct against the flawed model) and to
differential testing (no oracle). It surfaced only because **certificate-mutation
soundness testing** generates out-of-distribution programs and cross-checks the
checker's TAC-level verdict against the actually-assembled binary — turning a
model/hardware mismatch into an observable divergence.

## Major finding: the checker caught a real register-allocation soundness bug — FIXED (commit b969cf5)

This is the credible-compilation value proposition demonstrated end-to-end: a **verified
certificate checker refusing to certify an untrusted optimizer's miscompilation**, with
the bug then located and fixed in the optimizer.

### Symptom
On random loop-heavy programs (~3%), the verified checker rejected RegAlloc's certificate
with `[all_transitions]` (sometimes also `[all_transitions, bool_vars_covered]`). For a
long time this was filed as "checker incompleteness / relation imprecision." It was not.

### The actual bug (in the untrusted allocator, not the certificate)
The interference graph (`RegAllocOpt.buildInterference`) recorded an edge between two
variables only when **both are live-out at the same PC**. That misses a case: a variable
can be **defined and then immediately dead** — a dead store — so it is in *no* live-out
set, yet its definition still **writes its physical register**. With no interference edge,
graph coloring is free to place that dead def in the **same register as a value that is
live across it**. Concretely (captured repro): a loop-carried constant `__t181` colored
`__ir13`, and a dead `v3 := v1 / __t190` inside the loop body *also* colored `__ir13` —
so every iteration the dead store clobbered `__t181`, and the next iteration's read of
`__t181` got garbage. **That is a miscompilation.**

### Why no miscompile was ever *observed*
Because the checker did its job. The certificate for this allocation fails
`checkRelConsistency` (the relation cannot claim `__ir13` holds `__t181` after a step that
overwrote it), the pass is rejected, and the pipeline falls back to the un-allocated
program. The verified checker converted a latent miscompiler bug into a *safe rejected
certificate* — exactly the guarantee credible compilation promises. The "completeness
residual" was the checker **correctly** refusing an unsound transform.

### The fix
Add Chaitin's standard **def-vs-liveOut** interference: a variable defined at a PC
interferes with every variable live-out at that PC (not only with simultaneously-live-out
variables). A dead def then can no longer share a register with a value live across it.
The allocation becomes sound and the certificate is accepted.

### How it was found, and the methodology lesson
Random differential testing never flagged it (the rejected certificate means the buggy
allocation is never emitted, so there is no oracle divergence). It was localized by
**reading the rejected certificate**: `certaudit -diag` pinpointed the failing transition
and `relConsist` pair, and a few targeted dumps showed the register's occupant was a
loop-clobbered dead def. The lesson: a verified checker's *rejections* are a debugging
signal about the optimizer, not merely a completeness nuisance — several were triaged as
imprecision before this one turned out to be a true soundness bug the checker had been
silently shielding against. **Distinguish "the checker is imprecise" from "the checker is
right and the optimizer is wrong" before weakening anything.**

### Verified
Full `lake build` 3139 jobs / 0 sorry; 81/81 differential; both captured repros now ACCEPT
with the allocation applied (205→212, 90→98). No certificate or checker change — the fix
is entirely in the untrusted allocator.

## Certificate-failure fuzzing campaign (`stress/certfuzz.sh`)

A dedicated campaign that, per random program, runs `certaudit` and **catalogues
every certificate rejection by `(pass, sub-check)`**, saving the first program for
each novel combination, with lighter differential + soundness checks interleaved.
Distinct `(pass, sub-check)` combinations observed on random int programs:

| combination | cause | status |
|---|---|---|
| `RegAlloc:[all_transitions]` | determined-`ifgoto` dead edge (`origPath=false`) | documented gap; **reachable on random programs**, not only synthetic mutants |
| `LICM:[all_transitions]`, `LICM:[all_transitions, div_preservation]` | over-aggressive hoist on large adversarial programs | imprecision, correctness-safe; div minimal repro already fixed |
| `CSE:[invariants_preserved]` | dead-edge merge kept unavailable expressions | **FIXED** (two-phase `analyze`, commit 789b792) |
| `CSE:[all_transitions]` | same dead-edge gap as RegAlloc/LICM | shared `checkAllTransitions` gap |

No miscompiles and no soundness holes were found by the campaign (the shift bug
above predates it and is fixed). All remaining rejections are **completeness gaps**
(a correct optimization dropped), not soundness holes.

### CSE dead-edge fix (commit 789b792)

`CSEOpt.analyze` seeded only PC 0, so a merge fed by a physically-dead edge phase 1
never visited kept available expressions not in fact available there, failing
`invariants_preserved`. Applied the same two-phase fix as `ConstProp.analyze` /
`DAE.computeRels`: after the reachable pass, seed unreachable PCs with the top state
and re-propagate so the merge intersects with the dead edge and drops those
expressions. Untrusted pass; 3139 jobs green; 81/81 differential tests.

### Dominant open item: `checkAllTransitions` dead-edge gap

`RegAlloc/LICM/CSE:[all_transitions]` share one root: `checkAllTransitions` requires
`origPath` (and `relConsist`) on *every* physical transition, including
invariant-dead edges (a determined `ifgoto`'s untaken arm). The passes legitimately
do not fold those branches, so the dead edge was checked and failed.

**RESOLVED (commit b0f9639), trusted checker + re-proved soundness.**
`checkAllTransitionsExec` now skips a successor edge that the trans-side invariant
proves dead (`isDeadSuccExec`: `computeNextPC` resolves the guard to a different
target under `inv_trans`). `checkAllTransitionsProp` was weakened to assume
`σ_t ⊨ inv_trans` (its only consumer, `step_sim`, already has it), and
`checkAllTransitionsExec_sound` discharges a dead edge by contradiction via the new
`step_target_eq_computeNextPC` (an actual run-step lands at `computeNextPC`'s
resolved target). RegAlloc and CSE `[all_transitions]` failures are gone; the
certificate-mutation campaign still rejects every behaviour-changing mutation
(3204 rejected / 0 holes), so the weakening did not open a soundness hole. The
band-aid of folding passes around the failing pass (changes the program, not the
gap) was deliberately *not* used. Residual: LICM still fails when its post-hoist
`inv_trans` loses the constant, plus a separate LICM goto-relocation imprecision.

## Headline result

Across the entire campaign — 81 hand-written differential tests, ~80 generated
families, thousands of random Csmith/swarm/boundary/SPE programs, EMI
(Orion/Athena/Hermes) and metamorphic mutants, and a certificate-mutation
soundness campaign — we found:

- **0 miscompilations under differential testing.** Every program the compiler
  accepted produced output identical to the C and Fortran references. (Differential
  testing cannot see the shift bug above: C shift-by-≥-width is undefined, so the
  generators mask shift amounts and there is no oracle for the divergent case.)
- **1 miscompilation found by soundness testing** — the unfaithful ARM shift
  semantics above — relative to the verified TAC semantics. It is reachable from
  ordinary source (`x >> a` with runtime `a ≥ 64`) and stems from the *trusted*
  ARM operational-semantics model, not the verified compiler logic.
- **0 soundness holes in the certificate checker.** A campaign that corrupted
  valid certificates in behaviour-changing ways (const-bump, op-flip,
  operand-swap, jump-retarget) had the checker **reject every one** (2806+
  rejections on the stress suite alone); the only accepted mutations were
  provably output-preserving (dead instructions), confirmed by codegen+run.
- **Every defect we found was a *completeness* gap or a *pass-construction* bug**,
  not a correctness bug. Because the verified checker rejects any certificate it
  cannot validate, an imprecise pass or an over-strict check causes a *silently
  dropped optimization*, never a wrong program. The fixes below recover those
  lost optimizations without ever putting correctness at risk.

This is the central evidence for the credible-compilation thesis: the trusted
checker held the correctness line throughout; testing's job reduced to improving
optimization completeness.

## Taxonomy of fixes

We separate **trusted** fixes (the verified certificate checker / its soundness
proofs — every such change required re-discharging Lean proofs) from **untrusted**
fixes (optimization passes, which are certificate-checked, so no proof obligation).

### A. Trusted checker fixes (completeness gaps; proofs re-discharged)

These were over-strict or non-confluent checks that rejected *valid* certificates.
Each fix makes the checker accept strictly more correct certificates and is sound
by construction (it never accepts a non-refinement); each required updating the
soundness proof.

| # | Check | Defect | Fix | Found by | Commit |
|---|---|---|---|---|---|
| A1 | `Expr.simplify` / `simplifyFast` | **Non-confluent float-add normalization.** "`fadd` with `fmul` on the left → swap operands" oscillated when *both* operands were `fmul`: swapping put an `fmul` back on the left and re-fired next iteration. The normal form then depended on iteration *parity*, so two expressions equal under the invariant but reached via different variable-unfold depths compared unequal → spurious `invariants_preserved` rejection (CSE). | When both operands are `fmul`, do not swap (immediate fixed point). | `certaudit` + invariant-atom diagnostic | 2c434dc |
| A2 | `Expr.simplify` / `simplifyFast` | **Simplify did not recurse into boolean-expr-as-`Expr` nodes** (`cmpE`, `cmpLitE`, `tobool`, `notE`, `andE`, `orE`). Invariant substitution could not resolve variables *inside* a comparison, so a variable holding a comparison result (e.g. a loop `done` flag set by `done := x == y`) simplified differently on the original side (`simplify`, no recursion) than the transformed side (`substSymFast`, which recurses) → spurious `relConsistency` failure (LICM hoisting around a bool flag). | Recurse into those six constructors. | EMI (Orion) induced + `all_transitions` diagnostic | 2c434dc |
| A3 | `checkDivPreservation` | **No hoisted-constant fallback for the dividend.** The check required the transformed dividend to map to an original *variable*; when LICM hoists a constant *dividend* out of a loop its relation maps it to a *literal*, so the lookup failed and the whole certificate was rejected — even though division-by-zero depends only on the *divisor*. | Give the dividend the same hoisted-constant fallback the divisor already had (trans relation maps `y` to literal `c`, orig invariant proves `y' = c`). | Csmith random fuzzing of division-in-loop programs | 07ddb08 |
| A4 | `checkAllTransitions` | **Demanded a valid original path for a statically-dead `ifgoto` edge** (the determined-`ifgoto` gap formerly deferred in §C). A determined `ifgoto` reaching a pass that does not fold branches (RegAlloc/CSE/LICM) has a dead arm with no original witness → rejected. **Dominant random-program failure class.** | Skip a successor edge the trans-side invariant proves dead (`isDeadSuccExec`: `computeNextPC` resolves the guard elsewhere under `inv_trans`); weaken `checkAllTransitionsProp` to assume `σ_t ⊨ inv_trans` (its only consumer, `step_sim`, already has it); discharge dead edges in the soundness proof via a new `step_target_eq_computeNextPC`. | `certaudit` on random programs (and originally an EMI mutant) | b0f9639 |
| A0 | `BinOp.eval` / `ArmSemantics` (TAC + trusted ISA model) | **Shift amount used the full 64-bit value, not AArch64's low-6-bit mask** — the one *real miscompile* (a runtime `x >> a`, `a ≥ 64`, gave `0` in the verified semantics but `192` in the binary) and an *apparent* checker soundness hole (same root cause in the checker's constant folding). See the headline section. | Mask the amount to `mod 64` in `BinOp.eval`, the relational `ArmStep`, and the executable `armStepResult`; codegen `rfl` lemmas stay `rfl`. | certificate-mutation soundness campaign + the "checker proven vs TAC semantics ⇒ accept+divergent-binary = semantics bug" principle | c0ccf71 |

Proof notes: A1 broke `Expr.simplify_sound` (2-way `match` → 3-way `split`); the
new both-`fmul` arm needs no commutativity. A2 broke `simplifyFast_eq_simplify`
(split the boolean cases out with their IHs) and the `rfl` boolean cases of
`simplify_sound` (now `simp; rw [ih]`). A3 mirrors `checkBoundsPreservation`'s
`idxOk` (the `_eq` equivalence closes via the existing `invFindLit_eq_invMapGetD`
lemma); `checkDivPreservationExec_sound` derives the dividend store-equality
through the fallback, and the orig-path safety lemma simply ignores the dividend
(`BinOp.safe .div _ b = b ≠ 0`). All changes keep the full `lake build` green
(3139 jobs, 0 `sorry`).

### B. Untrusted pass fixes (certificate-checked; no proof obligation)

These were bugs in how passes *construct* their certificates; the checker
correctly rejected the broken certificates, dropping the optimization. The passes
are untrusted, so fixing them needs no proof — only that the build stays green,
the checker accepts the new certificate, and differential output stays correct.

| # | Pass | Defect | Fix | Found by | Commit |
|---|---|---|---|---|---|
| B1 | ConstProp | **Certificate `orig` violated the driver contract.** `optimize` compacted the original program (removed unreachable PCs) and stored *that* as `cert.orig`, but the resilient driver requires `cert.orig.code == input.code`. So whenever folding made any PC unreachable — i.e. folding a constant branch, ConstProp's signature case — the entire certificate was rejected. | Stop compacting; `orig := prog`. Dead-code removal is left to the separate, independently-certified DCE pass. | `certaudit` (orig-mismatch) | 2c434dc |
| B2 | ConstProp + DAE | **Dataflow inconsistent across physically-dead edges.** `analyze` / `computeRels` seeded only PC 0; a statically-dead PC with no live predecessor kept an empty invariant/relation, so a merge fed by a dead edge that reassigns a live variable claimed the live edge's value — which the checker (correctly validating the physical dead edge) rejected. | Second analysis phase: seed every still-unreachable PC with `top` and re-propagate, making invariants/relations consistent on *all* physical edges. | `certaudit` + EMI Athena mutant | 5f3568f |
| B3 | Peephole | **Over-collapsed a runtime conditional.** Removing *both* `goto (pc+1)` no-ops around `if(c){skip}else{skip}` skip-merged an `ifgoto`'s taken target onto its fall-through, producing a degenerate `ifgoto` whose target equals its fall-through. The checker could derive no `branchInfo` for it and could not validate the original path → `all_transitions` (`origPath`) failure. | Do not remove a `goto (pc+1)` that immediately follows an `ifgoto`; keep the branch distinguishable. | EMI (Orion) | b8bb66b |
| B4 | FMAFusion | **`origLabels` off-by-one for a jump targeting a fused `fmul`.** `buildPcOrigMap` anchors a fused instruction's `pc_orig` on the *removed* `fmul`, but a `goto`/`ifgoto` targeting that fmul used `skipArr` to skip *past* it to the `fadd`, so the jump's path overshot the successor's `pc_orig` by one → `all_transitions` (`origPath`) failure. | When a jump target is itself a removed (fused) fmul, do not skip it. | `certaudit` (flt_accum) + `all_transitions` diagnostic | 1d1b1c3 |
| B5 | CSE | **Dead-edge merge kept unavailable expressions.** `CSEOpt.analyze` (available-expression worklist) seeded only PC 0, so a merge fed by a physically-dead edge phase 1 never visited kept available expressions not actually available there → `invariants_preserved` rejection. | Same two-phase fix as B2: after the reachable pass, seed unreachable PCs with the top state and re-propagate so merges intersect with the dead edge. | `certaudit` cert-failure campaign | 789b792 |
| B6 | LICM | **Imprecise + dead-unaware certificate relation.** (i) The per-PC relation used a PC-linear scan + global override, over-claiming hoisted-var coverage at branch targets a control edge could reach without the hoist → `relConsist` free-variable-coverage rejection. (ii) A hoisted variable *dead after the loop* carries the hoisted literal on the in-loop path but the original value on an immediate loop-exit path; an identity rel pair cannot express that sound divergence → `relConsist` rejection. **Reduced LICM's random-program rejection rate ~9/40 → 3/40 with the full hoist preserved.** | (i) CFG-correct forward MUST dataflow (`hoistedSetAt`, intersection at joins). (ii) Filter the relation to LIVE variables (`DAEOpt.analyzeLiveness`), dropping the dead var exactly where it diverges. No optimization dropped; checker untouched. | `certaudit` cert-failure campaign + relation-pair diagnostic | 1775d35 |
| B7 | CSE | **Nested common subexpressions not matched.** `findAvail` compared a candidate against stored available expressions without expanding the stored entry's `invExpr` through the available set, so a nested redundancy like `(a+i)*(b+i)` recomputed via fresh temps did not match the available product (it was certifiable, just not *found*). | Expand a stored entry's `invExpr` through the available set before comparing. `opt_cse_loop` now computes the product once (1 `mul`, was 2). | `certaudit` / missed-optimization probe | c778787 |
| B8 | LICM | **Non-dominating preheader (closed the B6 residual).** When the loop header is reached by a path that bypasses the inserted preheader (non-fall-through entry, or a nested-loop structure), the hoisted `const` never runs there; the variable is then live where it is not established and the relation's identity fallback mismatches the original literal → `relConsist` rejection (the hoist is genuinely broken on that path). | `dominatingHoists`: keep a hoist only if its var is established (`hoistedSetAt`) at every PC where it is live (`analyzeLiveness`), to a fixpoint. Drops only the broken non-dominating hoists; every certifiable hoist kept. **0 LICM rejections in a 71-seed scan afterward (was ~3/40).** | `certaudit` cert-failure scan + dominance dump | 76a05e2 |
| B9 | DAE | **Asserted a removed store's value.** Eliminating a dead store `x := c` replaces it with a `goto`, so trans never establishes `x` — yet `computeRels` added `(.lit c, .var x)` claiming trans `x = c`. False once the store is deleted, and the trans-side `x` is uncovered by `rel_pre` → `checkRelConsistency` free-variable-coverage rejection (it passed the value check only because the orig invariant still folds `x→c`). | Since `x` is dead, orig/trans legitimately diverge on it: drop every `x` entry and assert nothing; `x` re-enters as identity at its next live definition. Dead-store elimination unchanged. | 261-program `certaudit` sweep (sole rejection) | 4322e60 |

B1's fix exposed B2 (ConstProp now folds, so programs reach DAE with the dead
edges that trigger B2) and reshaped the pipeline so several earlier RegAlloc
rejections disappeared — illustrating how completeness fixes cascade. B6/B8 (LICM)
and B9 (DAE) share a single root with B2: a per-PC relation that names a variable
on a control edge where the transformed program does not actually carry its value —
fixed each time by restricting the relation to what is *established and live* on that
edge, never by weakening the checker.

### C. (Resolved) — the determined-`ifgoto` dead-edge gap

Originally documented here as deferred (commit fea049c). **Now fixed** — see A4
(commit b0f9639): `checkAllTransitions` skips an invariant-dead successor edge,
`checkAllTransitionsProp` was strengthened with the `σ_t ⊨ inv_trans` hypothesis it
needed (its sole consumer `step_sim` already supplies it), and the master simulation
proof was re-discharged. It was the *dominant* random-program rejection class once the
campaign exercised real (not just synthetic) inputs, so closing it cut the overall
rejection rate substantially.

### D. Remaining pass-imprecision (open; correctness-safe, optimization-only)

The full open list is in **"Remaining known issues"** below. In brief:
- **LICM** dominant sub-causes (branch-target coverage, dead-variable divergence) are
  **fixed** (B6); a ~3/40 residual remains — an *unreachable preheader* `buildTrans`
  bug for loops whose header is entered by a non-fall-through edge, which the checker
  *correctly* rejects (the hoist is genuinely broken there).
- **RegAlloc** `[all_transitions]` (and its `bool_vars_covered` companion):
  **RESOLVED — and it was a genuine miscompiler bug, not a checker gap** (commit
  b969cf5). The checker was correctly rejecting an *unsound register allocation*
  (a dead store clobbering a value live across it, from a missing interference
  edge). Fixed in the allocator's interference graph. See the dedicated finding
  **"The checker caught a real register-allocation soundness bug"** below.
- **CSE** nested common subexpressions: **FIXED** (commit c778787) — `findAvail`
  now expands a stored entry's `invExpr` through the available set, so a nested
  redundancy like `(a+i)*(b+i)` recomputed via fresh temps matches the available
  product. `opt_cse_loop` now computes the product once (1 `mul`, was 2).

## Diagnostic tooling built (reusable artifacts)

- **`certaudit`** — runs each pipeline pass over a `.w` file, reporting per-pass
  ACCEPT/REJECT; `-diag` dumps the exact failing `invariants_preserved` atom and,
  for `all_transitions`, the per-transition sub-checks
  (`rel`/`rel_next`/`origPath`/`relConsist`) plus orig/trans program listings.
  This is what made every checker bug locatable to a single PC/atom.
- **`certmutate`** + soundness campaign — the checker-soundness tester.
- **`emi`** — Orion/Athena/Hermes EMI and commutativity/strength/condition-swap
  metamorphic rewrites, over a full While AST → `.w` pretty-printer.
- **`csmith_gen.py` / `spe_gen.py`** — random (swarm + boundary) and exhaustive
  (skeletal) generators emitting While + matching C by construction.

## Methodology → which technique found what

| Technique | Defects surfaced |
|---|---|
| `certaudit` pass-by-pass auditing | B1, A1, A2 (with diagnostic), B4 |
| EMI Orion / Athena | B3, B2 (amplified), exposed gap C |
| Csmith random + swarm + boundary fuzzing | A3 |
| Differential (While vs C vs Fortran) | 0 miscompiles (correctness confirmation) |
| Metamorphic / Hermes | 0 new (correctness confirmation under unusual shapes) |
| Certificate-mutation soundness | 0 soundness holes (TCB confirmation) |
| Scaling sweeps | compile time ≈ O(n^2.5) in live-var count / nesting / length |

## One-line abstract claim

*Stress-testing a credible compiler with differential testing, EMI, metamorphic
testing, random/boundary/skeletal generation, and a novel certificate-mutation
soundness campaign found zero miscompilations and zero soundness holes; all seven
defects were completeness gaps that silently dropped sound optimizations, which we
root-caused and fixed (three in the verified checker, with proofs re-discharged;
four in untrusted passes), recovering the lost optimizations while the verified
checker guaranteed correctness throughout.*

## Design-point finding: the optimization-aggressiveness ↔ certifiability tension (LICM)

A core design tension in credible compilation, surfaced sharply by LICM: **the more
aggressively a pass optimizes, the lower the probability its certificate validates.**
A larger / more structurally complex transformation produces a larger proof
obligation, and the certificate checker — being a fixed, verified, necessarily
incomplete decision procedure — is more likely to be unable to discharge it. Crucially
this is *not* a soundness issue (every LICM output was a correct program; the 3-way
differential campaign found 0 miscompiles): it is a **completeness** tension. The
transformation is correct; the certificate just cannot be shown valid.

### Concrete instance

LICM hoists loop-invariant `const`s into a loop preheader. On large, multi-loop,
branchy programs its certificate was rejected by `checkAllTransitions`:
- `relConsist` free-variable coverage failed at branch targets, because the
  certificate's per-PC relation (built by a PC-linear scan plus a coarse
  "after the last hoisted PC, assume all hoisted vars set" override) claimed a
  hoisted variable was established at a target that a branch could reach *without*
  passing the hoist — i.e. the relation over-claimed relative to the real CFG.
- A secondary goto-relocation case (`relConsist` on a back-edge/exit `goto` whose
  target moved when instructions were inserted).

The hoists themselves are sound (the preheader dominates the loop); only the
*certificate's relation* was imprecise about which hoisted vars are established where.

### Three ways to resolve the tension — and the design principle

We explored, in order, three points on the trade-off curve:

1. **Identity fallback (all-or-nothing).** If the full transformation's certificate
   fails, emit no transformation. *Rejected:* throws away every optimization on the
   program, including the many that would certify — the worst point on the curve.

2. **Conservative reduction (self-certifying pass).** Have the pass validate its own
   certificate and greedily drop individual optimizations until what remains
   certifies (for LICM: drop hoisted invariants one at a time). This *eliminates the
   cert failures and stays operational* — e.g. one program kept 58 of 78 hoists and
   newly certified, where the baseline (rejected → pipeline-skipped) had applied
   none. It is bounded and correct (81/81 differential tests pass). **But it resolves
   the tension by *moving down the optimization axis*: it reduces the number of
   optimizations specifically to make the check pass.** That is the wrong default —
   the optimizer is being weakened to fit a fixed checker, and the chosen subset is
   not even guaranteed maximal.

3. **Richer / more precise certificates (the intended design point).** Keep the full
   optimization and make the *certificate generation* precise enough to discharge it
   — invest on the *certifiability axis* instead of the optimization axis. For LICM
   this means replacing the coarse relation heuristic with a CFG-correct forward
   must-analysis (the set of hoisted vars established on *every* path to each PC,
   intersection at joins), so the relation neither over- nor under-claims and
   `relConsist` succeeds for every sound hoist with **zero reduction in
   optimizations**. A prototype of this dataflow removed the dominant `ifgoto`-target
   coverage failures without dropping any hoist; completing it (the `const` and
   goto-relocation residuals) is the remaining work.

**The principle:** the right response to "aggressive optimization fails to certify"
is to make the certificate *match the optimizer* (precise, CFG-aware relation and
invariant generation), not to make the optimizer *match the checker* (drop
optimizations). Reduction (option 2) is a sound, always-available *fallback of last
resort* — it guarantees a valid certificate by construction and never reduces below
the pipeline's existing rejected-then-skipped behavior — but it must not be the
design point, because it trades away exactly the optimization power the pass exists
to provide. The goal is: **keep every optimization that can be certified, and raise
the certificate's precision until "can be certified" covers everything the optimizer
soundly does** — never lower the optimizer to clear the check.

This tension generalizes beyond LICM (e.g. RegAlloc register sharing of
provably-equal or non-interfering variables has the same shape: a sound transform
whose justifying fact — value equality, path infeasibility — the relation does not
yet express), and it is intrinsic to the credible-compilation architecture: a fixed
verified checker can never be complete, so every optimizer sits somewhere on this
curve and the engineering goal is to push the certifiability axis outward, not the
optimization axis inward.

### Update: route 3 (precise certificate) completed for LICM — commit 1775d35

The design tension above was resolved for LICM the *right* way — by raising the
certificate's precision, not by reducing optimization. Two untrusted-pass changes,
verified checker untouched, nothing re-proved:

1. **CFG-correct relation** (`hoistedSetAt`): a forward MUST-analysis giving the
   hoisted vars established on every path to each PC (intersection at joins),
   replacing the PC-linear scan + global-`lastHoisted` override. Fixes the
   `relConsist` free-variable-coverage failures at branch targets.
2. **Liveness-filtered relation**: the relation now ranges only over variables LIVE
   at each PC (`DAEOpt.analyzeLiveness`/`livenessTransfer`). This closes the
   goto-relocation residual, whose root cause was subtle: a hoisted variable that is
   *dead after the loop* carries the hoisted literal on the in-loop path but the
   original value on an immediate loop-exit path — a divergence that is sound only
   because the variable is dead, yet which an identity rel pair cannot express.
   Dropping dead variables removes it exactly where it diverges.

Result: LICM performs its **full** hoist and the certificate validates (e.g. a repro
that previously rejected now certifies its complete `444→503` hoist); LICM rejection
rate on random programs fell from ~9/40 to 3/40 with no new `invariants_preserved`
failures; full build 3139 jobs / 0 sorry; 81/81 differential; 1205 mutations
rejected / 0 holes. A small residual (≈3/40, rarer/deeper CFGs) remains. This is a
concrete instance of the principle: **make the certificate match the optimizer.**

## Paper finding: certifying full code-motion via a precise, liveness-aware certificate

**Claim.** A loop-invariant code-motion (LICM) pass can emit certificates that a
fixed, verified, deliberately-incomplete checker accepts for its *full* (unreduced)
optimization, provided the certificate's simulation relation is (i) **CFG-correct**
about which moved values are established where, and (ii) **restricted to live
variables**. Both are properties of the *untrusted* certificate generator; the
verified checker is not modified and no proof is re-discharged. This is the concrete,
positive counterpart to the optimization-aggressiveness ↔ certifiability tension
documented above: the tension is resolved by raising certifiability, never by
lowering optimization.

### Setting

LICM hoists a loop-invariant `const x := c` into the loop preheader and leaves the
in-loop slot as a `goto`. The certificate is a per-PC expression relation between the
original and transformed programs; for a hoisted variable the relation carries a
`(lit c, var x)` pair meaning "trans `x` equals the literal `c`." The verified
`checkAllTransitions` / `checkRelConsistency` decision procedure accepts the pass iff,
along every transition, the relation is consistent. On straight-line loops this holds
trivially; on loops with internal branches and relocated control flow it failed —
even though every hoist was correct (the 3-way differential campaign found **zero**
miscompiles from LICM).

### Two defects in the certificate generator, and the fixes

**(1) Coverage over-claim — needs a CFG-correct relation.**
The generator computed "which hoisted vars are set at PC *p*" with a PC-linear scan
plus a coarse override ("after the last hoisted PC, assume all are set"). A branch
that jumps *over* a later hoisted block then reaches a target whose relation claims
that block's vars, while the branch did not establish them — so
`checkRelConsistency`'s free-variable coverage check rejects. Fix: compute the set by
a **forward MUST dataflow** — the hoisted vars established on *every* path to *p*
(union as the transfer at a hoisting const, **intersection at control-flow joins**).
The relation then neither over- nor under-claims, matching the program's real
dataflow, which is exactly what the checker verifies.

**(2) Dead-variable divergence at loop-exit merges — needs a live-variable relation.**
This is the subtle one. Consider a loop guard `ifgoto (¬(li < x)) Exit` whose *only*
edge into the exit block bypasses the hoisted `const __t := c` in the loop body. In
the transformed program `__t = c` always (hoisted to the preheader); in the original,
on an *immediate* exit (zero loop iterations), `__t` still holds its pre-loop value.
The two programs therefore **disagree on `__t` at the exit merge** — and this is
*sound* precisely because `__t` is dead after the loop (never observed). But the
identity relation pair `(var __t, var __t)` the generator emits at the merge asserts
`orig __t = trans __t`, which is false on that path, so `checkRelConsistency` rejects.
No amount of relation precision or added invariant can fix this, because the values
genuinely differ; the only thing making the transform correct is **deadness**. Fix:
**filter the relation to variables live at each PC** (a standard backward liveness
analysis: `liveIn = use ∪ (liveOut \ def)`). A dead variable is dropped from the
relation exactly where it is dead, so the divergence is never asserted.

### Why this stays inside the untrusted pass

Both fixes change only what certificate the pass *proposes*. The verified checker —
its decision procedure and its soundness proof against the operational semantics — is
untouched, so no `sorry` is introduced and nothing is re-proved. The checker
validates every relation and invariant the pass emits, so a generator bug can only
cost completeness (a rejected certificate), never soundness. (Contrast the one
genuinely trusted-checker gap in this project — the determined-`ifgoto` dead edge —
where the checker *demanded a path for a physically impossible edge*, which no
certificate could supply; that one required a checker change and a re-proof.)

### Results

The repro that previously rejected now certifies its **complete** `444→503` hoist
(no hoists dropped). On random loop-heavy programs the LICM rejection rate fell from
≈9/40 to 3/40 with **zero** new `invariants_preserved` failures. Full `lake build`
3139 jobs / 0 `sorry`; 81/81 three-way differential tests; 1205 certificate-mutation
soundness mutations rejected / 0 holes. A small residual (≈3/40, rarer/deeper CFGs)
remains and is the same shape — a sound transform whose certificate is not yet
precise enough.

### Generalizable lesson

For credible/translation-validated compilation, the engineering lever against
optimizer/checker incompleteness is the **precision of the certificate the optimizer
emits**, and two ingredients recur: (a) make the relation **CFG-correct** (a proper
must/may dataflow, not a linear approximation), and (b) make it **range only over
live state**, because aggressive transformations legitimately diverge on dead values
and a whole-state relation cannot express that. RegAlloc's residual register-sharing
cases (a register shared by provably-equal or non-interfering variables) have the
same shape and are expected to close by the same method.

## Paper finding: certifying constant-branch elimination by *decomposition* (ConstProp fold + DCE compaction)

A clean, reusable pattern for the same whole-state-relation limitation, arrived at by an
explicit design choice in `ConstPropOpt.optimize`.

### The obstacle
Constant-folding a branch — turning `ifgoto b l` (with `b` constant under the invariant)
into an unconditional jump and **removing the now-unreachable arm** — is naturally one
optimization. But removing instructions *renumbers* the program: `orig.code ≠ trans.code`
in shape, so the per-PC whole-state certificate (which relates orig PC *i* to trans PC
*i*) has nothing to relate the deleted region to. Worse, the pipeline driver (`applyPass`)
only accepts a certificate whose `orig.code` equals the program it handed the pass, so a
ConstProp that compacted its own `orig` was **rejected outright and silently dropped** —
precisely on its signature case (a constant branch). This is the same defect class as
code-motion: a structural reshape a per-PC relation cannot witness.

### The resolution: split the transformation along the certifiability boundary
ConstProp is deliberately made **structure-preserving**: it folds `ifgoto b l → goto l`
**in place**, emitting exactly one trans instruction per orig instruction (1-to-1 aligned,
`orig := prog` uncompacted). The fold alone is trivially certifiable — the invariant
proves the guard constant, and every other PC is identity. The **physical removal** of the
now-dead arm is then left to the **separate, independently-certified DCE pass** that runs
immediately after. Each half is alignment-preserving and individually certifiable; their
composition achieves the full optimization (fold + dead-arm deletion) that the single
combined step could not certify.

One subtlety made explicit in the code: because the dead arm is *kept* (not compacted),
its dataflow effect must still reach control-flow merges, or an invariant that holds only
on the live path would be unsound on the retained physical dead edge. ConstProp therefore
**propagates the statically-dead edge too** (a second analysis phase seeding the unreached
PCs), so `invariants_preserved` holds on every *physical* successor; the precision lost by
not compacting is recovered downstream by DCE deleting the arm. (See also fix B-class
"physically-dead edge" consistency for ConstProp/DAE.)

### Generalizable lesson
When an optimization both **rewrites in place** and **changes program structure**, do not
try to certify it as one step against a positional whole-state relation. **Factor it into
an alignment-preserving rewrite (label/operand folding) and a separate
deletion/compaction pass, and certify each independently.** ConstProp+DCE is the canonical
instance; the same factoring is why LICM hoists *before* the header (insertion, not
reshape) and leaves cleanup to DCE. The cost is pipeline ordering discipline (the two
passes must run adjacently and DCE must be trusted to follow), not optimization power:
**no optimization is given up** — the branch *is* folded and certified; only the bookkeeping
is split so each piece stays within what the checker can express.

## Remaining known issues (open) — for the paper's limitations section

A precise accounting of everything still open after the fixes above. **None is a
soundness hole or a miscompile**: the campaigns found 0 miscompiles under
differential testing and 0 holes under certificate-mutation testing, and the one real
miscompile (shift semantics) and the one trusted-checker gap (determined-`ifgoto`) are
fixed and proved. Everything below is **untrusted-pass completeness** (a correct
optimization whose certificate the verified checker rejects, so the pipeline skips
that pass — the program still compiles correctly) or a non-correctness limitation.

### A. Certificate-check failures still observed (completeness gaps)

**Status: none observed.** A 261-program `certaudit` sweep (random seeds 100–360, all 25
passes) plus an 80-program RegAlloc-targeted scan found **zero** certificate rejections
across every pass after the fixes below. The three items previously listed here are all
resolved:

1. **`LICM:[all_transitions]` residual — RESOLVED (B8, commit 76a05e2).** Was the
   *non-dominating preheader* case (header reached by a path bypassing the inserted
   preheader). Closed by `dominatingHoists`, which keeps a hoist only where its variable
   is established at every PC it is live. 0 LICM rejections in a 71-seed scan afterward.

2 & 3. **`RegAlloc:[all_transitions]` and `[…, bool_vars_covered]` — RESOLVED, and it was
   a real allocator soundness bug, not a completeness gap (commit b969cf5).** The checker
   was correctly refusing an *unsound* register allocation: a dead store sharing a
   register with a value live across it, because `buildInterference` recorded an edge
   only when two vars are both live-out — missing the def-vs-liveOut case. Fixed in the
   interference graph; both former sub-checks now certify. See the dedicated finding
   *"The checker caught a real register-allocation soundness bug."* (This supersedes the
   earlier "occupant-tracking relation" hypothesis recorded in prior drafts — the
   relation was fine; the allocation was wrong.)

4. **`bounds_preservation` — no standalone open failure.** (Correction of an earlier
   stale note.) Bounds-check elision **is active**: `verifiedBoundsSafe` (Phase 6 in
   `CodeGen`) computes a real per-PC decision from `BoundsOpt`'s interval analysis and
   the verified codegen *does* drop the check for provably-in-bounds accesses (verified
   directly: a `while (i<16) A[i]…` loop elides both accesses). The
   `checkBoundsPreservation` certificate sub-check is a *general* condition checked for
   every certificate and passes; it only surfaces transiently when LICM hoists an
   array-indexing const (`LICM:[…, bounds_preservation]`, folded into class 1 above).
   (A code comment in `CodeGen` still describes the pre-Phase-6 "hard-wired to false"
   state and is stale.)

### B. Non-correctness limitations

5. **Compile-time scaling ≈ O(n^2.5).** The certificate checker (symbolic execution
   per transition) dominates; programs beyond ~300–400 TAC instructions take tens of
   seconds, and the campaigns chunk generated programs to stay tractable. Not a
   correctness issue; a throughput one.

6. **LICM cluster is a fixed ×4 unrolling** (one iteration per assumed loop-nesting
   level). Loops nested deeper than 4 may not have all invariants lifted — a
   completeness limit of the *pipeline schedule*, independent of the per-pass
   certificate.

7. **Liveness-filtered relation depends on `DAEOpt.analyzeLiveness` precision.** The
   LICM fix (1775d35) drops dead variables from the relation; if the liveness analysis
   were imprecise (kept a truly-dead var), a divergence could resurface as a rejection
   (never as unsoundness — the checker would reject, not miscompile).

### Status summary

| area | state |
|---|---|
| Soundness (miscompiles / checker holes) | **clean** — 0 found; the one real miscompile + the one trusted gap fixed & proved |
| Trusted base (checker proofs, ARM model) | **sound**, 0 `sorry`, full build 3139 jobs |
| LICM completeness | **all known cert failures fixed** (dataflow + liveness filter + dominating-hoist filter); 0 rejections in 71-seed scan |
| RegAlloc completeness | 2 rare cases open (occupant-tracking; bool coverage) |
| BoundsOpt | bounds-check elision **active** (Phase 6 `verifiedBoundsSafe`); `bounds_preservation` is a general cert condition that passes |
| Performance | O(n^2.5) checker; pipeline schedule fixed ×4 LICM |
