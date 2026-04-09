# CredibleCompilation — Development Log

Chronological record of what was built and why, to reconstruct the sequence of decisions.

---

## 1. Initial semantics (`320b98f` — 2026-03-23)

Created `Semantics.lean`: a small imperative language in three-address code (TAC) form with scalar integer variables. Small-step structural operational semantics (Winskel-style). Includes `Store`, `BinOp` (add/sub/mul), `TAC` instructions (const/copy/binop/goto/ifgoto/halt), `Step` relation, `Steps` (reflexive-transitive closure), determinism, and basic metatheory.

## 2. Certificate checker + soundness (`8acac7f` — 2026-03-24)

Built the three-layer credible compilation framework:

- **PropChecker (CertChecker at the time):** Prop-based certificate definitions (`PCertificate`, `PCertificateValid`), simulation relation, soundness proofs for halt and diverge.
- **ExecChecker (DecidableChecker at the time):** Bool-based executable checker with symbolic execution, invariant preservation, label-based original path verification.
- **SoundnessBridge:** Proof that `checkCertificateExec = true` implies `PCertificateValid`, connecting the executable checker to the formal soundness theorem.
- **Examples:** Three verified examples (constant propagation, binop propagation, redundant assignment removal) plus a rejected bad example.

Certificates use `origLabels : List Label` to specify the sequence of original program PCs visited during each transition correspondence.

## 3. Strengthen soundness — reject mixed behaviors (`1481427` — 2026-03-24)

Changed the catch-all match arm from `True` to `False` in `credible_compilation_soundness` and `exec_checker_correct`. Now halting always maps to halting, and diverging always maps to diverging — mixed behavior pairs are explicitly rejected.

## 4. Rename Decidable → Executable (`31d7384` — 2026-03-24)

Renamed `DecidableChecker.lean` → `ExecChecker.lean` and all `D`-prefixed types (`DInv`, `DCertificate`, etc.) to `E`-prefixed (`EInv`, `ECertificate`, etc.) to avoid confusion with Lean's `Decidable` typeclass.

## 5. Rename Cert → Prop/Exec split, add P prefix (`0fcd1a5` — 2026-03-25)

Split `CertChecker` into `PropChecker` (Prop-based) and `PropExamples`. Added `P` prefix to Prop types (`PCertificate`, `PTransCorr`, etc.) to mirror the `E` prefix on executable types.

## 6. Generalize varmaps to expression-pair relations (`e5e0bf6` — 2026-03-25)

Replaced variable maps (`PVarMap`/`EVarMap`) with expression-pair relations (`PStoreRel`/`EExprRel`). Certificates can now express `e_orig.eval(σ_orig) = e_trans.eval(σ_trans)` for arbitrary expression pairs, not just variable lookups. This enables optimizations like CSE where a temporary variable maps to an expression in the original program.

## 7. Add CSE/IVE examples + totality theorem (`b21aa47` — 2026-03-25)

- Example 10: CSE with temporary variable mapped to expression.
- Example 11: Induction variable elimination (`k = 100 - rem`).
- Fixed `Expr.reassoc` pattern ordering (`.add` before `.sub`).
- Added `checkSuccessorsInBounds`: verify all successor PCs are in bounds.
- Proved `Step.progress`: in-bounds PC always admits a step.
- Proved `has_behavior`: bounds-closed programs always halt or diverge.
- Added `exec_checker_total`: complete end-to-end theorem combining behavior existence with semantic preservation.

## 8. BoolExpr for ifgoto (`69938af` — 2026-03-25)

Replaced `TAC.ifgoto : Var → Label → TAC` with `TAC.ifgoto : BoolExpr → Label → TAC`. `BoolExpr` supports `var`, `cmp`, `not`, `and`, `or` constructors. Symbolic branch resolution uses `BoolExpr.asVar` for `.var` cases with graceful fallback for complex expressions.

## 9. Optimization-focused example suite (`06547c8` — 2026-03-25)

Rewrote `ExecExamples` and `PropExamples` to cover six standard compiler optimizations: constant propagation, copy propagation, CSE, DCE, LICM, and IVE. Includes both executable checker and Prop-level proofs, plus negative examples demonstrating incorrect transformations.

## 10. Replace BoolExpr.var with cmpLit (`ba8205f` — 2026-03-25)

Removed the integer-is-nonzero test pattern (`BoolExpr.var x`) in favor of explicit comparison expressions (`BoolExpr.cmpLit op x n`). Added `BoolExpr.symEval` for symbolic branch resolution and `BoolExpr.mapVarsRel` for cross-program condition mapping. Rewrote all branch-related soundness proofs.

## 11. Add automatic optimizers (`9332be1` — 2026-03-25)

Added five automatic optimizers with example files:
- `ConstPropOpt` — constant propagation
- `CSEOpt` — common subexpression elimination
- `DCEOpt` — dead code elimination
- `LICMOpt` — loop-invariant code motion
- `PeepholeOpt` — peephole optimization

Refactored shared certificate-building code into `ExecChecker.lean`. Moved `Expr` type from `PropChecker` to `Semantics`. Cleaned up `Main.lean` to import from example modules.

## 12. Restructure PCertificate fields (`b0d3c2d` — 2026-03-25)

Moved `PTransMeasure` into `PCertificate` as a `measure` field (matching `ECertificate`). Moved `StepClosedInBounds` and `checkStepClosed` to `Semantics.lean`. Added `step_closed` to `PCertificateValid`. Eliminated the separate μ parameter threading.

## 13. Add Observation type (`6affaec` — 2026-03-26)

Added `Observation` inductive (`halt`/`stuck`/`nothing`) to `Semantics.lean`. Added `observe` function that inspects a configuration against a program and observable variables. This sets up the infrastructure for stuck-state (div-by-zero) reasoning.

## 14. Div-by-zero + close all sorry holes (`f433b56` — 2026-03-26)

Added `BinOp.div` with safety guard (denominator ≠ 0). Programs get stuck on division by zero, and the checker verifies this is preserved across transformations.

Key additions:
- `checkBinopSafe` in `checkOrigPath` — symbolic denominator verification along original paths.
- `checkDivPreservationExec` — ensures transformed `div` maps to original `div` with matching denominator.
- `checkStuckPreservationProp` + `stuck_pres` field in `PCertificateValid`.
- Three standalone ECertificate theorems: `exec_halt_preservation`, `exec_stuck_preservation`, `exec_diverge_preservation`.
- Closed the last `sorry` in `execPath_sound_gen` (binop safety proof from `checkBinopSafe`).

**Zero sorry holes remain.**

---

## File inventory

| File | Role |
|------|------|
| `Semantics.lean` | Language definition, operational semantics, `Observation`, `StepClosedInBounds` |
| `PropChecker.lean` | Prop-based certificate validity, simulation, soundness proofs |
| `PropExamples.lean` | Prop-level verified examples (6 optimizations + bad example) |
| `ExecChecker.lean` | Executable (Bool) checker, symbolic execution, shared cert utilities |
| `ExecExamples.lean` | Executable checker examples |
| `SoundnessBridge.lean` | `checkCertificateExec = true → PCertificateValid`, per-behavior ECert theorems |
| `ConstPropOpt.lean` | Constant propagation optimizer |
| `CSEOpt.lean` | Common subexpression elimination optimizer |
| `DCEOpt.lean` | Dead code elimination optimizer |
| `LICMOpt.lean` | Loop-invariant code motion optimizer |
| `PeepholeOpt.lean` | Peephole optimizer |
| `*OptExamples.lean` | Examples for each optimizer |
| `WhileLang.lean` | Source language AST, interpreter, compiler to TAC |
| `WhileExamples.lean` | End-to-end: source → TAC → optimize → check |
| `CompilerCorrectness.lean` | Compiler correctness: `compile_correct` (in progress, 3 sorrys) |
| `RefCompiler.lean` | Pure functional compiler with full correctness proof (0 sorrys) |

## 15. While source language (uncommitted — 2026-03-26)

Added a structured while-language as a source-level front-end:

- **AST**: `SExpr` (arithmetic), `SBool` (boolean), `Stmt` (skip, assign, seq, if-then-else, loop).
- **Interpreter**: `Stmt.interp` with fuel bound, for testing.
- **Compiler**: Monadic compiler (`CompM`) that flattens expressions into temporaries, emits `ifgoto`/`goto` with label patching for control flow. Produces a `Prog` (TAC array) ending with `halt`.
- **Examples**: 7 programs (sum, factorial, max, constant expr, absolute value, nested loops, division) all compiled to TAC and verified through the optimizer + certificate checker pipeline.
- The compiler is intentionally **unverified** — this is the credible compilation philosophy: the certificate checker (which IS verified) guarantees correctness of optimized output.

## 16. Compiler correctness framework (uncommitted — 2026-03-26)

Added `CompilerCorrectness.lean`: a framework for proving the while-to-TAC compiler correct.

- **Top-level theorem**: `compile_correct` — if `Stmt.interp fuel σ s = some σ'` (with division safety and tmp-freeness), then `haltsWithResult (compile s) 0 σ σ_tac` where `σ_tac` agrees with `σ'` on all non-temporary variables.
- **Fragment execution**: `FragExec` abstraction for reasoning about executing contiguous code blocks within a larger program.
- **Evaluation congruence**: `SExpr.eval_agree`, `SBool.eval_agree`, `eval_tmpAgree` — expressions that don't use `__t`-prefixed variables evaluate the same in stores that agree on non-tmps.
- **Code extension lemmas**: `compileStmt_code_ge` (code only grows), `compileStmt_code_preserved` (earlier entries unchanged) — proved for skip, assign lit/var, and seq cases.
- **Fully proved cases**: `skip` (trivial), `seq` (by composing IHs via `FragExec.trans'`).
- **13 sorrys remain**: primarily for `bin`/`ite`/`loop` cases (monad unfolding for complex expressions, patch reasoning for branches, fuel induction for loops).

## 17. Reference compiler with full correctness proof (uncommitted — 2026-03-26)

Added `RefCompiler.lean` (1026 lines): a pure functional compiler from the While language to TAC with a complete machine-checked correctness proof. Zero sorry holes.

**Compiler design:**
- Pure functions `refCompileExpr`, `refCompileBool`, `refCompileStmt` with explicit `(offset nextTmp : Nat)` parameters returning `(List TAC × ...)`.
- Pre-computed jump targets — no patching needed. Labels are computed from code lengths at compile time.
- `tmpName k` convention for temporaries; explicit counter threading avoids collisions.

**Correctness theorems (all fully proved):**
- `refCompileExpr_correct` — compiled expression code stores the correct value; preserves non-tmp variables and lower-indexed temporaries.
- `refCompileBool_correct` — compiled boolean code evaluates to the correct boolean; same preservation guarantees.
- `refCompileStmt_correct` — compiled statement code transforms the store correctly (by induction on AST + fuel for loops). Covers skip, assign, seq, ite, loop.
- `refCompile_correct` — top-level: if `s.interp fuel σ = some σ'` (with tmpFree + divSafe), then the compiled program halts with a store that agrees with `σ'` on all non-temporary variables.

**Supporting infrastructure:**
- `FragExec` composition lemmas (`trans'`, `single_*` for each TAC instruction).
- `CodeAt` predicate and splitting lemmas for reasoning about code embedded in a larger program.
- `refCompileExpr_nextTmp_ge`, `refCompileExpr_result_bound` — monotonicity and naming bounds.
- `Store.update_*` lemmas for reasoning about store updates vs temporary names.
- `SBool.divSafe` added to `CompilerCorrectness.lean` for boolean division safety.

This is the "verified compiler" counterpart to the credible compilation approach: instead of checking certificates post-hoc, the compiler itself carries a proof.

## 18. Stuck and divergence theorems for RefCompiler (uncommitted — 2026-03-26)

Added stuck-state and divergence preservation theorems to `RefCompiler.lean`, proving the compiler preserves all three observable behaviors.

**Stuck-state theorems (§13–§16):**
- `refCompileExpr_stuck`, `refCompileBool_stuck`: if an expression is not division-safe, compiled code gets stuck.
- `refCompileStmt_stuck` (line 1310): if `s.interp fuel σ = some σ'` but `¬s.divSafe fuel σ`, then the compiled code gets stuck.
- `refCompile_stuck` (line 1640): top-level stuck preservation.

**Divergence theorems (§17–§20):**
- `RefStepsN` (line 1659): step-indexed multi-step relation for counting execution steps.
- `Stmt.interp_fuel_succ`, `Stmt.interp_fuel_mono`, `Stmt.interp_none_of_le`: fuel monotonicity and its contrapositive.
- `Stmt.divSafe_fuel_succ`, `Stmt.divSafe_of_le`: division-safety anti-monotonicity.
- `loop_one_iter` (line 1855): one iteration of a divergent loop produces ≥2 steps back to loop head.
- `refCompileStmt_diverges` (line 1917): a divergent, div-safe statement produces unbounded steps (∀ N, ∃ n ≥ N, ...).
- `refCompile_diverge` (line 2252): top-level — if `∀ fuel, s.interp fuel σ = none` with division safety, the compiled program does not halt.

**Zero sorry holes remain.**

## 19. While language + RefCompiler committed (`5e1f3af` — 2026-03-26)

Committed entries 15–18 (While source language, compiler correctness framework, reference compiler, stuck/divergence theorems) in a single commit.

## 20. Typed Value system (`acc813d` — 2026-03-27)

Added a typed value system with `int` and `bool` types:

- `Value` inductive: `.int i` and `.bool b` constructors (replacing bare `Int`).
- `VarTy` inductive: `.int` and `.bool` for type contexts.
- `TAC.boolop`: new instruction that evaluates a `BoolExpr` and stores the boolean result.
- `TypedStore Γ σ`: every variable's value matches its declared type.
- Type preservation theorem: well-typed programs preserve `TypedStore` across steps.
- `Cfg.typeError`: new stuck configuration for type errors (e.g., adding a bool to an int).

## 21. Integrate typed Values across all modules (`19a86c1` — 2026-03-27)

Threaded the new `Value` type through all modules: `Semantics`, `PropChecker`, `ExecChecker`, `SoundnessBridge`, optimizers, and examples. Closed all sorry holes introduced by the type system migration.

## 22. Embed TyCtx in certificates + error semantics (`25f10fd` — 2026-03-27)

Embedded `TyCtx` directly in `PCertificate`/`ECertificate` (derived from original program). Renamed stuck semantics to error semantics (`Cfg.error`, `checkErrorPreservationProp`). Added `WellTypedProg` to `PCertificateValid` and `checkCertificateExec`.

## 23. Program refinement theorem + eliminate axioms (`a5fb5b1` — 2026-03-28)

Added `program_refinement` theorem: if the checker accepts, then `∀ σ₀, ∀ obs ∈ observations(trans), obs ∈ observations(orig)`. Eliminated all project-specific axioms — the entire development is axiom-free (modulo Lean's built-in axioms).

## 24. Prog as structure + Cfg.typeError (`4ff8f4f` — 2026-03-28)

Refactored `Prog` from a type alias (`Array TAC`) to a structure with `code`, `tyCtx`, and `observable` fields. Programs now carry their own type context and observable variable list. Added `Cfg.typeError` for type-mismatch errors at runtime.

## 25. Remove redundant certificate fields + type safety theorem (`4caf647` — 2026-03-28)

Removed standalone `tyCtx`/`observable` fields from certificates — they're now derived from the original program's `Prog` structure via abbreviations (`ECertificate.tyCtx`, `PCertificate.observable`). Added a `type_safety` theorem: well-typed programs never reach `Cfg.typeError`.

## 26. Check observable equality + per-program type checking (uncommitted — 2026-03-30)

Made both checkers verify that original and transformed programs have the same observable variables and are each well-typed under their own type context:

- **`PCertificateValid`**: `well_typed_trans` now requires `WellTypedProg cert.trans.tyCtx cert.trans` (was `cert.tyCtx`). Added `same_tyCtx : cert.orig.tyCtx = cert.trans.tyCtx` and `same_observable : cert.orig.observable = cert.trans.observable`.
- **`checkCertificateExec`**: uses `cert.orig.tyCtx` for orig and `cert.trans.tyCtx` for trans. Adds `cert.orig.observable == cert.trans.observable` check.
- **`soundness_bridge`** and all downstream end-to-end theorems take an extra hypothesis `htyctx : dc.orig.tyCtx = dc.trans.tyCtx` (function equality isn't decidable, so this can't be checked executably).
- **PropExamples**: `transProg` definitions carry explicit matching `tyCtx`/`observable` (no longer using `Prog.ofCode`).

## 27. Separate typeError from error in Observation (`11c792d` — 2026-03-30)

Split `Observation` and `Behavior` to distinguish runtime errors (div-by-zero) from type errors. This lets the credible compilation framework preserve error-kind distinctions through optimization.

## 28. While language parser + ARM64 codegen (`106b36a`–`9fdc5d6` — 2026-03-30)

Added a string parser for the While language and an ARM64 code generator producing `.s` assembly from TAC programs. Added a compiler executable for end-to-end While-to-ARM64 compilation.

## 29. ARM64 simulation framework + codegen verification (`69d0405`–`07c9718` — 2026-03-30–31)

Built formal ARM64 subset semantics (`ArmSemantics.lean`) and proved correctness of code generation for most TAC instructions: const, copy, binop (all ops including div with cbz guard), boolop, goto, iftrue, iffall, halt, error, binop_typeError. Proved `genBoolExpr_correct` for bvar, cmp, not cases. Added `backward_simulation` theorem. Remaining sorrys: cmpLit (needs loadImm64 large case) and genInstr boolop/ifgoto for and/or scratch slot issue.

## 30. Flatten and/or in TAC boolean expressions (`5569ddf`–`2bdc78c` — 2026-03-31)

Removed `BoolExpr.and`/`BoolExpr.or` constructors. The compiler now flattens `&&`/`||` into short-circuit control flow using `ifgoto` + integer 0/1 constants, producing a `cmpLit .ne tR 0` as the result. Proved `compileBool_wt` and `compileBool_allJumpsLe` for the flattened and/or cases (zero WhileLang sorrys). Proved `compileBool_eq_refCompileBool` for and/or.

## 31. Add true/false boolean literals (uncommitted — 2026-03-31)

Added `lit : Bool → BoolExpr` constructor to the TAC-level `BoolExpr` and `lit : Bool → SBool` constructor to the source-level `SBool`. Updated all pattern matches, evaluators, compilers, type checkers, code generators, optimizations, and proofs across the entire codebase (Semantics, WhileLang, RefCompiler, CompilerCorrectness, CodeGen, AsmSemantics, ConstPropOpt, ExecChecker, SoundnessBridge). No new sorrys introduced.

## 32. Register allocation pass (uncommitted — 2026-04-09)

Added graph-coloring register allocation (`RegAllocOpt.lean`) consumed by CodeGen at assembly emission time. The pass computes liveness (reusing `DAEOpt.analyzeLiveness`), builds separate interference graphs for int and float variables, and colors them with spill selection (longest live range heuristic).

**Register budget:** 15 int (x3-x7, x9-x18), 14 float (d2-d15). x0-x2 are int scratch, d0-d1 float scratch, x8 array address scratch.

**CodeGen changes:** Smart load/store helpers (`smartLoadVar`/`smartStoreVar`) check the coloring and emit `mov` (register) instead of `ldr`/`str` (stack). Register-allocated variables are initialized via `mov xN, #0` / `fmov dN, xzr`. At halt, register values are saved to stack slots before the printf sequence. Fixed mod codegen to use x0 instead of x3 (freeing x3 for allocation).

**Pipeline:** ConstProp → DCE → DAE → CSE → LICM → RegAlloc → Peephole. RegAlloc is an identity pass at the TAC level (certificate is trivially valid); the real optimization happens in CodeGen's assembly emission.

**Tests:** 3 new programs (71: int regalloc, 72: float regalloc, 73: spill test with 22 int variables in a loop). RegAlloc effectiveness test verifies the identity certificate and non-empty coloring. 98/98 tests pass, 3143 build jobs, no new sorrys.

## 33. TAC-level register allocation with weakened checker (uncommitted — 2026-04-09)

Replaced the identity RegAlloc certificate with real TAC-level variable renaming. Two-part change:

**Part 1 — Checker weakening (ExecChecker + SoundnessBridge):** Changed `checkRelConsistency` from iterating over all program variables to iterating only over `rel_post` pairs. The old approach required `∀ v, σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o am_o` which prevented renaming (a variable in orig but not trans fails the identity default). The new approach checks only what the certificate claims: each `(e_o, e_t)` pair in `rel_post` is preserved. `eRelToStoreRel` changed from universal quantification to `List.Forall` over `buildSubstMap` pairs. 3 new sorrys in SoundnessBridge (`forall_rel_identity`, `transRel_sound`, `checkDivPreservationExec_sound`).

**Part 2 — TAC renaming (RegAllocOpt + CodeGen):** `RegAllocOpt.optimize` now renames variables to register names (`__x{N}`/`__d{N}`) in the TAC program. Copy-back instructions (`copy origName regName`) are inserted before each halt to restore observable values to their original names (enables observable variables to use registers during execution). Expression relations track `(.var origName, .var regName)` pairs, computed via forward worklist on the orig program and mapped to trans PCs. CodeGen simplified: detects registers by name prefix (`__x` → int register, `__d` → float register) instead of coloring map lookup; `computeColoring` call removed from `generateAsm`.

**Certificate structure for copy-backs:** Copy-back PCs use zero-step orig paths (`origLabels = []`) with decreasing measures, mapping to the same orig PC as the halt they precede.

**Tests:** RegAlloc effectiveness test now verifies `cert.trans.code != cert.orig.code` (real TAC change). 98/98 tests pass.

---

## Key theorem locations

**ECertificate (SoundnessBridge.lean):**
- `exec_halt_preservation` (line 1630)
- `exec_stuck_preservation` (line 1641)
- `exec_diverge_preservation` (line 1652)
- `exec_checker_correct` (line 1557)
- `exec_checker_total` (line 1590)
- `soundness_bridge` (line 1426)

**RefCompiler (RefCompiler.lean):**
- `refCompileExpr_correct` (line 394)
- `refCompileBool_correct` (line 487)
- `refCompileStmt_correct` (line 639)
- `refCompile_correct` (line 1008)
- `refCompileStmt_stuck` (line 1310)
- `refCompile_stuck` (line 1640)
- `refCompileStmt_diverges` (line 1917)
- `refCompile_diverge` (line 2252)

**PCertificate (PropChecker.lean):**
- `soundness_halt` (line 319)
- `stuck_preservation` (line 935)
- `diverge_preservation` (line 981)
- `credible_compilation_soundness` (line 716)
- `credible_compilation_total` (line 737)
- `simulation_trace` (line 763)
- `has_behavior` (line 670)
