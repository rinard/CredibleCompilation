# Bugs Caught by Proofs, Certificate Checks, and Testing

Retrospective pulled from `CHANGELOG.md` and `git log` as of 2026-04-21.
Categorises each bug by which layer surfaced it and, for bugs the verified
pipeline *didn't* catch, notes the state of the relevant proofs at the time.

## 1. Bugs caught by correctness proof attempts

Bugs surfaced while trying to close a Lean proof — the proof refused to
go through until the underlying code was fixed.

- **Lib-call save/restore clobbered destination** ([CHANGELOG.md:739](../CHANGELOG.md#L739), 2026-04-17).
  `genCallerSaveAll` saved and restored *all* caller-saved regs including
  the destination. For `x := exp(y)` with `x` in a caller-saved freg, the
  restore would overwrite the computation result. Surfaced while closing
  the 8 `callerSave_composition` print-case sorrys; fixed by adding
  `callerSaveEntries` that filters out `DAEOpt.instrDef instr`.
- **`BoolExpr.normalize` unsound flip** ([CHANGELOG.md:874](../CHANGELOG.md#L874), 2026-04-14).
  Left-literal comparisons used an approximate flip (`.lt → .le`, `.le → .lt`)
  that blocked `normalize_eval`. Replaced with identity.
- **`checkSExpr` / `checkFExpr` type confusion** ([CHANGELOG.md:1200](../CHANGELOG.md#L1200), 2026-04-09).
  Checkers accepted float forms in int context. Proof attempts on
  `compileStmt_wt` exposed it; fixed by unifying into `checkExpr (ty : VarTy)`.
- **`BoolExpr.mapVarsRel` wrong catchall** ([CHANGELOG.md:875](../CHANGELOG.md#L875), 2026-04-14).
  Catchall used transformed variable names; replaced with `none` for
  non-var left operands.
- **Copy codegen missing non-freg→freg path** ([6ca5ac5](../), 2026-04-18).
  `verifiedGenInstr` copy case returned `none` when src was on the stack
  or in an ireg and dst was in a freg (e.g. spilled float copied back to a
  float register). Commit message: "closes the codegen gap identified
  during the totality proof."
- **Non-injective register layout (`__irN` / `__brN`)** ([7989ff6](../), 2026-04-18).
  Both names mapped to `xN`, violating layout injectivity required by the
  totality proof. Commit message: "pre-work for generateAsm totality."
- **`arraySize < 2⁶²` precondition gap** ([CHANGELOG.md:39](../CHANGELOG.md#L39), 2026-04-21).
  Phase 6 proof that `idxVal.toNat < arraySize` lifts to
  `idxVal < arraySizeBv` forced adding an upper bound on `arraySize` to
  `isBoundsSafe`; without it, `BitVec.ofNat 64 arraySize` can wrap.

## 2. Bugs caught by certificate check failures

The Bool-valued checker refused to validate optimizer output, exposing
bugs in the optimization passes themselves or in the checker's acceptance
criteria.

- **LICM hoisted-constant rejections** ([CHANGELOG.md:827-849](../CHANGELOG.md#L827), 2026-04-14).
  9/24 Livermore kernels failed. Three separate root causes:
  1. `BoolExpr.mapVarsRel` `.cmp` only handled `(.var, .var)` and
     `(.var, .lit)`; rejected `(.lit, .var)` pairs from hoisted constants.
  2. `checkDivPreservationExec` used `relFindOrigVar` for divisor mapping,
     requiring `(.var, .var)` — failed on hoisted literal divisors.
  3. `BoolExpr.normalize` returned left-literal forms unchanged, so
     `checkOrigPath` couldn't match mapped branch conditions.
- **LICM conflicting-constant hoist** ([548d350](../), 2026-04-14).
  Same temp assigned different constants at different points in a loop
  (e.g., `__t31 := 0` then `__t31 := 1`). LICM kept the first and
  generated a certificate that assumed the wrong value at the other site.
  Caught by checker failures on k16/k17.
- **CSE `fadd` + `fmul` normalization mismatch** ([10cc76d](../), 2026-04-15).
  CSE built `invExpr` as `fbin .fadd (fmul_subexpr) (other)`, but
  `Expr.simplify` normalizes `fadd`-with-`fmul`-on-left by swapping
  operands. `checkInvAtom` then compared un-normalized against normalized
  and failed `invariants_preserved`. Caught on k18_hydro_2d.
- **CSE chained var-lookup asymmetry** ([CHANGELOG.md:778-791](../CHANGELOG.md#L778), 2026-04-16).
  `checkInvAtom` compared a one-level-simplified lhs against a recursively
  simplified rhs. Checker rejected CSE on k02 inner loop because invariant
  entries referenced other entries that couldn't be resolved one-step.
  Fixed by introducing `simplifyDeep`.
- **Phase-3 checker cap too tight** ([CHANGELOG.md:171](../CHANGELOG.md#L171), 2026-04-21).
  Probe on 5 Livermore kernels showed widened loop-counter ranges up to
  ~5·10¹² on `k02_iccg`, above the `validInterval` cap of 2³¹. Checker
  would have rejected every real bounds-elision case; forced introducing
  `validIntervalLoose` (2⁶²).

## 3. Bugs caught by testing

Genuine miscompiles surfaced by running compiled programs and diffing
against reference output.

- **`mod` register aliasing** ([2aa7d9c](../), 2026-04-10).
  When `rd == rl || rd == rr`, `sdiv` clobbered the divisor before `msub`
  read it. Mod-using kernels produced wrong results; fixed by routing
  the quotient through scratch `x0`.
- **Missing `cset` in array bounds check** ([0cb9fe9](../), 2026-04-12).
  `cmpImm` / `cbz` emitted with no `cset` between them, so the branch
  condition wasn't materialized. Bounds checks silently misfired.
- **Invalid mixed `stp` in callee-save prologue** ([88d1c3e](../), 2026-04-14).
  Codegen emitted `stp x20, d12` (one ireg + one freg) instead of pairing
  separately; also blew past `stp`'s ±504 offset range. Caught when
  callee-save-using kernels faulted or corrupted state.
- **`d2` scratch clobber** ([ad1bc7b](../), 2026-04-12).
  Codegen used `d2` as scratch in `fcmp` / `fbinop`, but regalloc still
  considered it allocatable, so floats in `d2` got stomped. Fix excluded
  `d0-d2` from the allocatable set.
- **`k11` print index, `k07` timer** ([b533ca1](../), 2026-04-15).
  Reference-side, *not* compiler bugs: printed `x[1]` instead of
  `x[1001]`; elapsed time was `t0-t0` instead of `t1-t0`. The WL compiler
  was producing correct output; the C baseline was miscoded.

## 4. Why the testing-caught bugs slipped past the proofs

All four genuine miscompiles above predate the 2026-04-19 zero-sorry
milestone ([eeece53](../) "Close generateAsm_total: 0 sorrys remaining")
by 1–9 days. At the dates each bug was found, the relevant proof wasn't
yet in place.

| Bug (fix) | Date | Proof state at the time |
|---|---|---|
| `mod` register aliasing (2aa7d9c) | 2026-04-10 | `binop add/sub/mul` proved 2026-03-30; `binop div/mod` correctness case not yet closed. |
| `arrLoad` `cset` omission (0cb9fe9) | 2026-04-12 | `arrLoad` sorrys still open; bool `arrLoad` sorry not closed until 2026-04-17. |
| `d2` scratch conflict (ad1bc7b) | 2026-04-12 | `fcmp` / `fbinop` effective-register proofs not in place (finished 2026-04-16). No theorem yet reconciled RegAlloc's allocatable set with codegen's scratch assumption. Same commit also bypasses the optimization pipeline for k16/k17 — compiling via unverified paths by design. |
| Callee-save `stp` grouping (88d1c3e) | 2026-04-14 | Callee-save preference landed same day (dad7881); caller-save verified save/restore only the next day (1f7219d, 2026-04-15). Freshly-written codegen with no proof yet attached. |

Two bugs that look like testing finds in a skim of commit titles were
actually proof finds once the bodies are read:

- **Copy non-freg→freg** (6ca5ac5) — "closes the codegen gap identified
  during the totality proof."
- **`__irN` / `__brN` collision** (7989ff6) — "pre-work for generateAsm
  totality." The totality proof required layout injectivity; this
  violated it.

## Summary

- **Proof attempts surfaced** one clear miscompile (lib-call dst clobber),
  three analyzer unsoundnesses, two codegen gaps caught via the totality
  proof, and one precondition gap on `arraySize`. The proofs have
  consistently done work beyond bookkeeping — refusing to close until the
  code was actually correct.
- **Certificate checks surfaced** five optimizer / checker bugs (LICM × 2,
  CSE × 2, checker cap × 1). These were bugs in certificate-generation
  or in the checker's acceptance criteria, not in codegen.
- **Testing surfaced** four genuine miscompiles (`mod` aliasing, bounds
  `cset`, callee-save `stp`, `d2` scratch) plus two reference-side
  issues. Every one of these lived in code that was not yet under
  verification when found; the verified pipeline reached 0 sorrys
  1–9 days after the last of them.

The three layers have been covering complementary ground. Once the
pipeline closed on 2026-04-19, the copy / collision bugs caught that day
by the totality proof are the first clear instances of the verification
catching a bug *before* any test ran.
