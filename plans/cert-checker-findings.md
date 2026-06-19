# Findings: Stress-Testing a Credible (Certifying) Compiler

Catalogue of defects found and fixed while stress-testing the Credible
Compilation compiler (While → certificate-checked optimization passes → verified
ARM64 codegen), for the paper's evaluation/findings section. Branch
`fix/cert-checker-completeness`.

## ⚠ Most significant finding: unfaithful ARM shift semantics — FIXED (commit pending)

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

B1's fix exposed B2 (ConstProp now folds, so programs reach DAE with the dead
edges that trigger B2) and reshaped the pipeline so several earlier RegAlloc
rejections disappeared — illustrating how completeness fixes cascade.

### C. Documented gap (not fixed; correctness-safe)

| Check | Gap | Why deferred | Commit |
|---|---|---|---|
| `checkAllTransitions` | **Demands a valid original path for *every* structural successor of an `ifgoto`, including a statically-dead one.** When a determined `ifgoto` reaches a pass that does not fold branches (RegAlloc, last in the pipeline), its dead edge has no original witness and the certificate is rejected. On real programs the front end + ConstProp fold every determined `ifgoto` first, so it is only reachable with a synthetic input (an EMI mutant with a chain of constant-determined `ifgoto`s whose dead arms reassign live vars). | The principled fix (skip an invariant-dead edge) needs `checkAllTransitionsProp` strengthened with a `σ_t ⊨ inv_trans` hypothesis threaded through the master simulation. The spec already only quantifies over *actual* trans steps, so soundness never needs the dead edge — only the executable check is stricter. Sound, incomplete; deferred. | fea049c |

### D. Remaining pass-imprecision (open; correctness-safe, optimization-only)

- **LICM** still proposes un-certifiable hoists on adversarial, deeply-nested,
  division-heavy random programs (`relConsist` / `all_transitions`). The hoists
  are sound; the certificate is just imprecise. All real programs are clean.
- **CSE** misses some loop-body cross-statement common subexpressions
  (`opt_cse_loop`) — a missed optimization, not a rejection.

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
