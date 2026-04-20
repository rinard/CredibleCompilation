# CredibleCompilation — Development Log

Chronological record of what was built and why, to reconstruct the sequence of decisions.

---

## Add `printInt` typed library call (2026-04-20)

**Goal:** Replace the unverified variadic `print` path with single-argument typed print variants that flow through standard ARM64 calling conventions and the existing verified codegen lib-call machinery (like `pow`, `exp`). First slice: `printInt` only, end-to-end.

**Architecture:** `printInt v` is a void library call — argument in `x0`, no return, havocs caller-saved. At the IR level (TAC), it's a no-op; at the ARM level, it's `vLoadVar v x0 ++ [bl _printInt]` wrapped with caller-save save/restore via the existing lib-call infrastructure (`isLibCallTAC`, `callerSaveEntries`).

**Changes:**
- **TAC.lean:** Added `printInt : Var → TAC` constructor, `Step.printInt` rule (no-op), `TAC.successors`/`vars`/`isScalar`/`Step.mem_successors`/`Step.store_congr` cases.
- **WhileLang.lean:** Added `printInt` to `IsSeqInstr` and the `compileToTAC` exhaustiveness pattern.
- **ArmDefs.lean / ArmSemantics.lean:** Added `ArmInstr.callPrintI` (no operands — argument in `x0` by ABI) and `ArmStep.callPrintI` (havoc caller-saved, increment PC).
- **TypeSystem.lean:** `WellTypedInstr.printInt : Γ v = .int → ...` — type constraint propagates to `verifiedGenInstr` so layout knows to use ireg/stack for the load. `checkWellTypedInstr`/sound/complete updated. Type-preservation cases added (no-op).
- **CodeGen.lean / ArmSemantics.lean § verifiedGenInstr:** New case emits `vLoadVar layout v .x0 ++ [.callPrintI]` (rejects float layouts as ill-typed). `isLibCallTAC` extended so the existing lib-call wrapping path (save → load → call → restore, with `callerSaveEntries layout varMap none` since printInt has no destination — `DAEOpt.instrDef = none` — already returns the full set) handles it for free.
- **ArmCorrectness.lean:** Real backward simulation proof for `printInt` in `verifiedGenInstr_correct` (~40 lines). Mirrors the existing `floatUnary` lib-call template, adapted for void semantics. Added `hNCSLPrintInt` hypothesis (vacuously discharged at the non-lib-call call site in `step_simulation`).
- **CodeGen.lean § totality:** `verifiedGenInstr_total` `printInt` case uses `WellTypedLayout.int_not_freg` to dispatch — mechanical. `instrLength_eq_length` and `verifiedGenInstr_length_pcMap_ind` extended.
- **Pattern-match exhaustiveness across 18 files:** PropChecker (5 sites), DAEOpt (`instrUse`/`isDead`), DCEOpt (`transformInstr` + `buildInstrCerts`), PeepholeOpt, RegAllocOpt (`renameInstr`), ExecChecker (`buildInstrCerts1to1` + `computeNextPC`), SoundnessBridge (8 sites including `transBranchInfo` and bound-failure dispatches), PipelineCorrectness (`Step_of_code_arrayDecls_eq`).

**Probe-driven design:** Before committing to the void-call generalization, ran three quick probes in `step_simulation`'s lib-call branch: (a) `DAEOpt.instrDef` already returns `Option Var` and gives `none` for prints — no rework. (b) `callerSaveEntries (exclude := none)` already returns the full set — exactly the void-print semantics. (c) Both `ExtStateRel.callerSave_composition` (for void calls) and `ExtStateRel.callerSave_composition_excluding` (for valued calls) already exist. All green — the infrastructure was already split along the void-vs-valued axis.

**Closed the void sub-case in step_simulation (2026-04-20).** Added the `printInt` arm in `step_simulation`'s lib-call branch that proves `hBaseExists` for the void library call. ~180 lines, mostly mechanical mirror of the `floatUnary` template but simpler (no destination layout split, no setFReg, no vStoreVarFP, σ' = σ everywhere).

Key trick: the load-step (vLoadVar) was constructed inline with a 3-way case split on `layout v` (`ireg .x0` / `ireg r ≠ .x0` / `stack off`) so that the resulting state `s1` has a concrete shape — needed to prove `s1.stack = s_saved.stack`, which the existing `vLoadVar_exec` doesn't return. Tried first to extend `vLoadVar_exec` itself with stack preservation, but that broke 39 call sites; the inline 3-way split was lower risk.

**Project at 0 sorrys again** after the printInt addition.

**Deferred:** WhileLang `Stmt.printInt` surface syntax + variadic-`print`-to-typed-print lowering in `compileToTAC`. Test programs continue using the old variadic `print` for now.

---

## Dedupe successor-bounds checks (2026-04-20)

**Goal:** Eliminate duplication flagged in the post-refactor audit. Three nearly-identical "all successors in bounds" checks existed: `TAC.checkStepClosed` (Prog-based, with soundness `StepClosedInBounds`), `checkSuccessorsInBounds` (ECertificate-based, mirrored checkStepClosed but on `cert.trans`), and `checkSuccessorsInBounds_prog` (Prog, goto/ifgoto only — strictly weaker, used by `checkBranchTargets_of_successorsInBounds`). On top of that, `successors` was duplicated as a bare `def` in ExecChecker.lean and as `TAC.successors` in TAC.lean.

**Changes:**
- Deleted the bare `successors` from ExecChecker.lean; all callers now use dot notation `instr.successors pc`, which resolves to `TAC.successors`. Updated: ConstPropOpt, CSEOpt, DCEOpt, DAEOpt, BoundsOpt, LICMOpt, RegAllocOpt, and ExecChecker's own use sites.
- Redefined `checkSuccessorsInBounds cert := TAC.checkStepClosed cert.trans`. Its soundness theorem collapses to a one-liner invoking `checkStepClosed_sound`.
- Renamed the PipelineCorrectness bridge from `checkSuccessorsInBounds_prog_of_exec` to `checkSuccessorsInBounds_prog_of_stepClosed` (the input is now on `Prog`, not `ECertificate`). Caller in `invariants_of_checkCertificateExec` adjusted — the chain `checkSuccessorsInBounds cert = true` → `checkStepClosed cert.trans = true` is now definitional.
- `SoundnessBridge.checkSuccessorsInBounds_sound` shrank from 42 lines of case-bashing to a single `checkStepClosed_sound h`.
- Kept `checkSuccessorsInBounds_prog` (the weaker goto/ifgoto-only check) — it's still needed as the argument to `checkBranchTargets_of_successorsInBounds`, which only cares about branch targets.

**Result:** ~40 lines removed across SoundnessBridge, ExecChecker, and PipelineCorrectness. Full build passes, 0 sorrys. No behavioral changes — all transformations are definitional or local.

---

## Totality over the optimization pipeline (2026-04-19)

**Goal:** Extend `generateAsm_total` to cover `applyPassesPure`, so we have a logical totality theorem for the full optimized codegen pipeline, not just the direct `compileToTAC` path.

**Key insight:** `checkCertificateExec` already verifies every codegen prerequisite on `cert.trans` — `checkWellTypedProg`, `checkCodegenPrereqs`, `checkSuccessorsInBounds`, `checkBoolExprSimpleOps`. And `applyPass_sound` gives `checkCertificateExec = true` whenever `applyPass` returns `.ok`. So invariants transfer across every successful pass; failed passes fall back to the input program, preserving the previous invariants.

**Changes:**
- **CodeGen.lean:** Extracted `compileToTAC_codegenPrereqs` as a standalone public theorem (the ~60-line block previously inlined in `generateAsm_total`). Simplified `generateAsm_total` to a one-liner. Removed `private` from `checkBranchTargets`, `checkSuccessorsInBounds_prog`, and `checkBranchTargets_of_successorsInBounds` so the pipeline module can reach them.
- **PipelineCorrectness.lean § 7:**
  - `checkSuccessorsInBounds_prog_of_exec`: bridge from the stricter exec-side check (verifies every successor of every instruction) to the codegen-facing prog-side check (goto/ifgoto targets only).
  - `invariants_of_checkCertificateExec`: right-to-left peel through 30 `Bool.and` conjuncts to extract the four needed invariants on `cert.trans`.
  - `applyPass_preserves_invariants`: invariants on `p'` after a successful pass, via `applyPass_sound`.
  - `applyPassesPure_preserves_invariants`: list induction; `.error` branch is identity.
  - `generateAsm_total_with_passes`: main theorem, reuses `compileToTAC_*` lemmas as the induction base, then invokes `verifiedGenerateAsm_total`.

**Result:** Logical totality over the full pipeline. 0 sorrys. ~110 lines in PipelineCorrectness, ~8-line refactor in CodeGen. Operational termination (partial defs in pass internals → fuel-bounded versions) remains a separate task.

---

## Type-based register naming convention (2026-04-18)

**Goal:** Prepare for removing `tyCtx` from `Prog` by making the typing context derivable from variable names alone.

**Stage 1 — Rename registers (c19eb61):**
- Register-allocated variables now encode TAC type in name prefix: `__ir{N}` (int), `__br{N}` (bool), `__fr{N}` (float) — was `__x{N}`/`__d{N}`
- Bool variables get separate `__br` prefix (previously shared `__x` with int)
- Updated `computeColoring` in RegAllocOpt, `varToArmReg`/`varToArmFReg`/`checkRegConvention` in CodeGen

**Stage 2 — Update tyCtx defaults (f5b5444):**
- Added `Program.defaultVarTy`: derives type from name prefix (`__f`→float, `__b`→bool, else int)
- `Program.tyCtx` now uses `defaultVarTy` instead of `isFTmp`-based check
- Updated `initStoreBase` to match the new convention
- Added bridge lemmas `defaultVarTy_of_isTmp`, `defaultVarTy_of_isFTmp`
- Fixed downstream `show` in CompilerCorrectness.lean

**Result:** The typing context correctly types all compiler-generated names by convention. No pass needs to modify `tyCtx`. Stage 3 (remove `Prog.tyCtx` field, eliminate `TyCtxSound`) is ready.

---

## Discharge print case sorrys, fix lib-call save/restore (2026-04-17)

**Goal:** Close the 8 `callerSave_composition` hypothesis sorrys in the print case of `step_simulation`, and fix a soundness bug in lib-call save/restore codegen.

**Print case (8 sorrys → 0):**
- Added `genCallerSaveAll_allCS_ireg`/`_freg` lemmas in ArmSemantics.lean (direct from filterMap definition)
- Added `checkCallerSaveSpec` runtime checker + `checkCallerSaveSpec_sound` soundness proof: boolean checks for hFresh, hNodup, hCoversIreg/Freg, hUniqIreg/Freg with O(n²) pairwise validation
- Added `callerSaveSpec` field to `GenAsmSpec`, proved in `verifiedGenerateAsm_spec` via the checker
- Print case now uses `spec.callerSaveSpec` destructuring + standalone allCS lemmas

**Lib-call codegen fix:**
- **Bug:** `genCallerSaveAll` saved/restored ALL caller-saved regs including the destination. For `x := exp(y)` where x is in a caller-saved freg, the restore would overwrite the computation result with the old saved value.
- **Fix:** Added `callerSaveEntries` helper that filters `genCallerSaveAll` to exclude `DAEOpt.instrDef instr` (the destination variable's register). Updated `bodyGenStep`, `instrLength`, `callSaveRestoreLen`, and `instrLength_eq_length` proof.

**Result:** 8 print sorrys eliminated. Lib-call codegen now correct (1 sorry remains for the lib-call proof, which needs a callerSave_composition variant handling σ → σ' with dst excluded).

---

## Effective registers for cmp/fcmp ifgoto codegen (2026-04-16)

**Goal:** Use allocated registers directly in cmp/fcmp branch-fused ifgoto code instead of always copying to scratch registers (x1/x2 for int, d1/d2 for float).

**Problem:** The old codegen always loaded cmp/fcmp operands into fixed scratch registers (.x1/.x2 or .d1/.d2), even when the variable was already in an allocated register. This generated unnecessary load instructions.

**Fix:**
- **ArmSemantics.lean**: `verifiedGenInstr` ifgoto cmp/fcmp sections now compute effective registers via `match layout v with | some (.ireg r) => r | _ => fallback`. For fcmp flit/var, the codegen emits the var load before the flit load so the proof-side PC plumbing stays uniform.
- **ArmCorrectness.lean**: Added 4 helper lemmas (`x1_ne_eff_x2`, `eff_ireg_val_preserved`, `d1_ne_eff_d2`, `eff_freg_val_preserved`) for reasoning about effective register preservation across loads. Rewrote all 12 proof cases (cmp × 3 + fcmp × 3) × (iftrue + iffall) using `vLoadVar_eff_exec`/`vLoadVarFP_eff_exec` with `Eq.subst` (▸) for PC plumbing and concrete value extraction for flag conditions.

**Key proof technique:** `simp [verifiedGenInstr]` expands `layout v` to `List.lookup v layout.entries`, creating a syntactic mismatch with proof-side `let` bindings. Solved by: (1) proving `hPC2'` via `rw [List.length_append, ← Nat.add_assoc]; exact hPC2`, (2) using `hPC2'.symm ▸ hCodeCmpBCond.head` for PC plumbing (definitional equality via ▸), (3) for iffall PC subgoal: `simp [List.length_append, Nat.add_assoc] at hPcN hPC2; rw [hPcN, hPC2]; rfl`.

**Result:** 0 new sorrys. All 24 benchmarks pass. No changes to existing binop/fbinop/arrLoad proofs.

---

## Checker: uniformly use simplifyDeep in all checker functions (2026-04-16)

**Goal:** Replace all uses of `Expr.simplify`/`Expr.simplifyFast` in checker functions and soundness proofs with `Expr.simplifyDeep`/`Expr.simplifyDeepFast`, so optimization passes don't need to pre-simplify certificate entries.

**Problem:** Only `checkInvAtom` used `simplifyDeep`. Other checker functions (`BoolExpr.normalize`, `BoolExpr.symEval`, `checkBinopSafe`, `isDivByZero`, `checkInstrAliasOk`, `checkRelConsistency`) still used single-pass `simplify`/`simplifyFast`, which couldn't resolve chained var-lookups through invariants.

**Fix:** Introduced `sdFuel` — an opaque fuel wrapper (`inv.length + 1`) that prevents Lean's type-checker from pattern-matching the Nat as `Nat.succ _`, which would unfold `simplifyDeep` one step and break `split`-based proof strategies. All checker functions and ~20 soundness proof call sites updated mechanically.

**Changes:**
- **ExecChecker.lean**: Added `sdFuel`. Updated `BoolExpr.normalize` (4 calls), `BoolExpr.symEval` (3), `checkBinopSafe` (1), `isDivByZero` (1), `checkInstrAliasOk` (2), `checkRelConsistency` (4 `.simplifyFast` → `.simplifyDeepFast`), `checkInvAtom` (uses `sdFuel` for consistency).
- **SoundnessBridge.lean**: Updated `symEval_sound`, `normalize_eval`, `checkInstrAliasOk_arrLoad_noalias`, `simplify_lit_val`/`simplify_blit_val`/`simplify_flit_val`, `checkRelConsistency_pairCheck`/`amCheck` (`simplifyFast_eq_simplify` → `simplifyDeepFast_eq_simplifyDeep`), `hpair_sound`, and array index/value proofs.

**Result:** 0 new sorrys. All existing tests pass. `Expr.simplify`, `simplify_sound`, `simplifyFast_eq_simplify` preserved as internal building blocks.

---

## CSE: simplifyDeep fixes chained var-lookup asymmetry (2026-04-16)

**Goal:** Fix the one-level `.var` lookup asymmetry in `checkInvAtom` that prevented CSE from working when invariant entries reference other entries (e.g., chained var lookups through the invariant).

**Problem:** `checkInvAtom` compared lhs (from `.var` lookup, one-level via `Expr.simplify`) vs rhs (recursively simplified). When invariant entries referenced other entries, the lhs wasn't fully resolved, causing mismatches. This prevented CSE in the second k02 inner loop.

**Fix:** Added `Expr.simplifyDeep` which iterates `Expr.simplify` to resolve chained `.var` lookups. Changed `checkInvAtom` to use `simplifyDeep` with fuel `inv.length + 1`. Simplified CSEOpt: `expandVarCert` is now identity (raw `.var` references), and `stateToInv` no longer pre-simplifies avail entries — the checker resolves chains itself.

**Changes:**
- **ExecChecker.lean**: Added `Expr.simplifyDeep` (iterates `simplify`). Changed `checkInvAtom` to use `simplifyDeep`.
- **SoundnessBridge.lean**: Added `simplifyDeep_sound` (7-line proof composing `simplify_sound`). Updated `checkInvAtom_sound`.
- **CSEOpt.lean**: `expandVarCert` → identity. `stateToInv` drops pre-simplification. Updated module docstring.

**Result:** 0 new sorrys. All 24 Livermore kernels compile and pass. Both k02 inner loops now eligible for CSE.

---

## CSE: cross-constant matching (2026-04-16)

**Goal:** Eliminate duplicate `k+1` computations in Livermore k02 inner loop, where each occurrence of the literal `1` gets a fresh temp from `compileExpr`.

**Problem:** CSE's `findAvail` matched on raw operand variable names. `binop _t34 add k _t33` and `binop _t37 add k _t36` look different even though `_t33` and `_t36` both hold constant `1`.

**Fix:** Added `ConstMap` tracking to the CSE analysis state. `findAvail` now uses `expandVarFull`/`expandExprConsts` to substitute known constants before comparing, so semantically equivalent expressions match regardless of which temp holds the constant. Certificate invariants include constant bindings, with avail entries pre-simplified through `Expr.simplify` for checker compatibility.

**Changes:**
- **CSEOpt.lean**: Added `ConstMap`, `constKill`, `constMerge`, `constBeq`. Split `expandVar` into `expandVarCert` (avail-only, for `invExpr`) and `expandVarFull` (avail+constants, for matching). Added `expandExprConsts` for recursive constant substitution. `transfer` now threads `ConstMap`. `stateToInv` pre-simplifies avail entries through constant invariants.
- **CSEOptExamples.lean**: Added § 8 test case (`const _t1 1; binop a add k _t1; const _t2 1; binop b add k _t2` → `copy b a`).

**Result:** First k02 inner loop eliminates duplicate `k+1` (verified correct, all 24 Livermore kernels pass). Second inner loop unaffected due to pre-existing `expandVarCert` instability during loop convergence (documented in module docstring).

---

## Close verifiedGenBoolExpr_correct sorry; scaffold iftrue/iffall (2026-04-16)

**Goal:** Eliminate the `verifiedGenBoolExpr_correct` sorry (line 877) and the `iftrue`/`iffall` sorrys in `verifiedGenInstr_correct`.

**Result:** `verifiedGenBoolExpr_correct` fully proved (0 sorry). `iftrue`/`iffall` remain sorry — the fused `bCond` codegen paths (`.not (.cmp ...)` and `.not (.fcmp ...)`) require per-operand-combination proofs inside `verifiedGenInstr_correct`'s more complex hypothesis context. The fallback `cbnz` path structure is validated.

**Changes:**
- **ArmCorrectness.lean**:
  - `verifiedGenBoolExpr_correct`: Full proof for all `BoolExpr` cases — `bexpr` (contradiction), `lit` (single mov), `bvar` (vLoadVar + andImm), `not` (recursive + eorImm), `cmp` (4 operand subcases: var+var, var+lit, lit+var, lit+lit), `fcmp` (4 operand subcases: var+var, var+flit, flit+var, flit+flit).
  - Uses `BoolExpr.hasSimpleOps_cmp`/`hasSimpleOps_fcmp` for operand case splits.
  - `Cond.negate_correct` (already in ArmDefs.lean) enables fused branch proofs.

**Sorry count:** 6 remaining (2 print, 2 iftrue/iffall, 2 arrLoad/arrStore).

---

## Handle LICM-hoisted constants in checker: left-literal comparisons, invariant-based div safety (2026-04-14)

**Goal:** Fix LICM certificate checker rejecting `(lit c, .var x)` relation pairs from hoisted constants. 9/24 Livermore kernels failed; after this change 16/24 pass (remaining 8 are `bounds_preservation` / `all_transitions` issues unrelated to this fix).

**Root causes:**
1. `BoolExpr.mapVarsRel` `.cmp` case only handled `(.var, .var)` and `(.var, .lit)`, rejecting `(.lit, .var)` — caused `all_transitions` failures on branches comparing hoisted constants.
2. `checkDivPreservationExec` used `relFindOrigVar` for divisor mapping, which requires `(.var, .var)` pairs — failed on hoisted literal divisors like `__t23 → lit 2`.
3. `BoolExpr.normalize` left-literal case returned the expression unchanged — prevented `checkOrigPath` from matching mapped branch conditions against original conditions.

**Changes:**
- **ExecChecker.lean**:
  - `BoolExpr.mapVarsRel`: Added `(.lit n, .var y')` arm in `.cmp` case. Flips comparison: `.eq`/`.ne` → symmetric `.cmpLit`; `.lt`/`.le` → `.not (.cmpLit flipped ...)` since we lack `.gt`/`.ge`.
  - `BoolExpr.mapVarsRel`: `.not` case now eliminates double negation (`¬¬p → p`) to prevent `.not (.not (.cmpLit ...))` from the flip + outer negation.
  - `BoolExpr.normalize`: Left-literal case now flips comparison (same logic as `mapVarsRel`) instead of returning unchanged. `.not` case adds double negation elimination.
  - `checkDivPreservationExec`: For div/mod, accepts original divisor known nonzero from `inv_orig` as alternative to `relFindOrigVar` operand mapping.
  - `checkAllTransitionsExec`: Augments relation with invariant-derived `(.lit n, .var v)` entries for `mapVarsRel` branch condition resolution.
- **SoundnessBridge.lean**:
  - `BoolExpr.eval_mapVarsRel`: Restructured `.cmp` proof to handle `(.lit, .var)` case with op-based case split. Proved flip correctness via `BEq.comm`/`bne_comm` for eq/ne, `decide_not`+`not_not` for lt/le. `.not` case handles double negation with `Bool.not_not`.
  - `BoolExpr.normalize_eval`: Matched new `normalize` structure — left-literal case proved with same flip lemmas; `.not` case uses `Bool.not_not` for double negation.
  - `checkDivPreservationExec_sound`: Left disjunct (invariant nonzero divisor) proves contradiction: `σ_o z' = c ≠ 0` from invariant vs `b = 0` from `hunsafe`.
  - `transRel_sound` (`hDivSafe`): Left disjunct derives `op.safe a b` directly from invariant entry `σ_o z_o = c ≠ 0`.

**No new sorrys.** Pre-existing: 2 in ArmCorrectness.lean (arrLoad/arrStore).

---

## Refactor SoundnessBridge for relFindOrigExpr, close noCallerSavedLayout sorry (2026-04-14)

**Goal:** Fix SoundnessBridge.lean build errors caused by ExecChecker changes (removal of `checkRelInvLink`, rewrite of `BoolExpr.mapVarsRel` to use `relFindOrigExpr`, normalize-based branch matching in `checkOrigPath`). Close the `noCallerSavedLayout` sorry in CodeGen.lean.

**Context:** ExecChecker was changed to:
1. Remove `checkRelInvLink` condition (no longer needed since `relFindOrigVar` no longer has the LICM fallback for `(lit c, .var x)` pairs).
2. Rewrite `BoolExpr.mapVarsRel` to use `relFindOrigExpr` instead of `relFindOrigVar`, folding literals into branch conditions as `.cmpLit`.
3. Use `BoolExpr.normalize` for semantic matching of branch conditions in `checkOrigPath` (instead of syntactic `b == origCond`).

**Changes:**
- **SoundnessBridge.lean**:
  - Added `relFindOrigExpr_mem`: if `relFindOrigExpr rel x = some e`, then `(e, .var x) ∈ rel`.
  - Rewrote `BoolExpr.eval_mapVarsRel` to match the new `relFindOrigExpr`-based `mapVarsRel`. Removed `hinvrel` parameter. Proved `.bvar`/`.cmpLit`/`.not` cases and the `.cmp (.var, .var)`, `.cmp (.var, .lit)` cases. Catchall cases (non-var left-side operands) marked sorry pending re-introduction of a checker condition.
  - Removed `hinvrel` parameter from `branchInfo_of_step_with_rel` and `eRelToStoreRel_of_relFindOrigVar`.
  - Removed `hrelinvlink` parameter from `transRel_sound`, `checkAllTransitionsExec_sound`, and `checkDivPreservationExec_sound`. Deleted `checkRelInvLink_pair` theorem and `hrelinvlink_dtc`/`hinvrel` derivations.
  - Fixed `soundness_bridge` decomposition: 19 conjuncts (was 20 with `checkRelInvLink`).
  - Updated `execPath_sound` branch-info proof for normalize-based matching (`b.normalize ss inv == origCond.normalize ss inv`). Added sorry pending `BoolExpr.normalize_eval` lemma.
- **CodeGen.lean**:
  - Closed `noCallerSavedLayout` sorry in `verifiedGenerateAsm_spec`. Proof: the `if hasLibCall && !checkNoCallerSavedLayout` guard ensures that when a non-native `floatUnary` exists (proving `hasLibCall = true`), `checkNoCallerSavedLayout` must be true. Used `Array.any_eq_true` to witness the instruction, `checkNoCallerSavedLayout_spec` to derive the Prop.

**Additional ExecChecker fixes:**
- Fixed `BoolExpr.normalize`: replaced approximate flip (`(.lt → .le, .le → .lt)`) for left-literal case with identity (leave unchanged). The approximate flip was unsound and prevented proving `normalize_eval`.
- Fixed `BoolExpr.mapVarsRel`: replaced catchall case (using transform variable names) with `none` for non-var left operands. The `(.var, .var)` and `(.var, .lit)` arms cover all practical LICM cases.
- Fixed `.fcmp` case: now requires both operands to be `.var`, returning `none` otherwise.

**Sorry status:**
- CodeGen.lean: 0 sorrys (was 1).
- SoundnessBridge.lean: 5 sorrys. 1 for `normalize_eval` body (case analysis on `Expr.simplify` results — proof outline exists with `simplify_lit_val`/`simplify_blit_val` helpers, needs interactive tactic session). 4 for `eval_mapVarsRel` catchall `none`-elimination (Lean can't reduce nested match on abstract `Expr` in `| _ =>` wildcard; needs `cases ey <;>` enumeration within interactive session).
- ArmCorrectness.lean: 2 pre-existing (arrLoad/arrStore simulation).

---

## Close verifiedGenerateAsm_spec sorry, refactor WellTypedLayout completeness (2026-04-12)

**Goal:** Prove `verifiedGenerateAsm_spec`: a successful `verifiedGenerateAsm p = .ok r` satisfies `GenAsmSpec p r` (well-typedness, layout consistency, bodyPerPC size/content, pcMap prefix-sum, layout completeness for instruction variables).

**Problem:** `WellTypedLayout` had a third conjunct `∀ v, layout v ≠ none` (completeness for ALL strings), which is unprovable for finite-entry layouts (`VarLayout` backed by `List.lookup`). This was added in a prior session to eliminate `none`-layout cases but made `verifiedGenerateAsm_spec` unprovable as stated.

**Changes:**
- **ArmSemantics.lean**: Removed `∀ v, layout v ≠ none` from `WellTypedLayout` (now two conjuncts: non-float not in freg, float not in ireg). Removed `WellTypedLayout.complete`. Updated `float_not_ireg` to use `h.2`.
- **ArmCorrectness.lean**: Added `hMapped : ∀ v, v ∈ be.vars → layout v ≠ none` parameter to `verifiedGenBoolExpr_correct`. Added `hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none` to `verifiedGenInstr_correct` and `ext_backward_simulation`. Replaced ~22 `hWTL.complete x` calls with `hMapped x (by simp [heq, TAC.vars])` or equivalent membership proofs. For boolop/ifgoto cases, derived bool-expr-level completeness from instruction-level completeness.
- **TAC.lean**: Added public `TAC.vars` (equivalent to private `instrVars` in CodeGen).
- **CodeGen.lean**: Added `layoutComplete` field to `GenAsmSpec`. Updated `step_simulation` to pass `spec.layoutComplete pc hPC` to `ext_backward_simulation`. Proved `verifiedGenerateAsm_spec` via:
  - `checkWellTypedLayout_wellTyped`: soundness of layout type-consistency check
  - `checkWellTypedLayout_instrMapped`: soundness of layout completeness check for instrVars
  - `body_foldl_spec`: foldl invariant (size = code.size, each entry from verifiedGenInstr)
  - `instrLength_eq_length`: pcMap-independence of instruction list length (case split on all TAC constructors)
  - `instrVars_eq_vars`: definitional equality of private `instrVars` and public `TAC.vars`

**Sorry status:** 0 sorrys in CodeGen.lean. 2 pre-existing sorrys remain in ArmCorrectness.lean (arrLoad/arrStore simulation, lines 3036/3038).

---

## Whole-program refinement theorem for verifiedGenerateAsm (2026-04-12)

**Goal:** Lift the per-instruction `ext_backward_simulation` to a multi-step simulation over `verifiedGenerateAsm`.

### New theorems (CodeGen.lean § 5a)

- **`whole_program_refinement`** — If `verifiedGenerateAsm p = .ok r`, then any TAC execution `p ⊩ Cfg.run pc σ am ⟶* cfg'` starting from an ARM state satisfying `ExtSimRel` is simulated by `ArmSteps` on the flat body program preserving `ExtSimRel`. Proof by induction on `Steps`, composing `step_simulation` at each step with `step_run_or_terminal` for case classification and `type_preservation` for `TypedStore` maintenance.
- **`initial_extSimRel`** — Establishes `ExtSimRel` at the initial zero-initialized configuration.
- **`step_simulation`** — Per-step wrapper around `ext_backward_simulation`, discharging `CodeAt` from `codeAt_of_bodyFlat` and wiring `GenAsmSpec` invariants.
- **`step_run_or_terminal`** — Classifies a step's successor as either `.run` (with `TypedStore` preserved) or terminal (no further steps).
- **`GenAsmSpec`** — Structure capturing invariants extracted from a successful `verifiedGenerateAsm` call (well-typedness, layout, body size, per-PC instruction generation, pcMap prefix-sum property).
- **`buildPcMap_zero`**, **`buildPcMap_succ`**, **`buildPcMap_sum`** — Prefix-sum properties of `buildPcMap`.
- **`codeAt_of_bodyFlat`** — Each per-PC instruction block is `CodeAt` in the concatenated flat body at the pcMap offset.

### Proven lemmas

- `Step.pc_lt_of_step` — extract `pc < p.size` from any Step
- `step_run_or_terminal` — classify step result as running (with TypedStore) or terminal
- `buildPcMap_zero` — prefix sum starts at 0
- `buildPcMap_succ` — prefix sum recurrence: `pcMap (pc+1) = pcMap pc + lengths[pc]`
- `prefixSumList_length/head/succ` — recursive prefix-sum characterization
- `foldl_push_getD_zero` — foldl-with-push preserves index 0
- `foldl_push_toList` — foldl-with-push = prefixSumList (generalized bridge)
- `buildPcMap_offsets_eq` — connects Array.foldl to prefixSumList

### Newly proven (2026-04-12, continued)

- `flatMap_segment_getElem` — list induction: element j of segment k in a flattened list-of-lists is at position (sum of first k segment lengths) + j
- `buildPcMap_eq_take_length` — pcMap = total length of first pc segments, by induction on pc using buildPcMap_succ
- `codeAt_of_bodyFlat` — composes the above two with Array↔List bridge
- `step_simulation` hPcNext — weakened `hPcNext` in `ext_backward_simulation` / `verifiedGenInstr_correct` / `genInstr_correct` from `∀ pc'` to `pc + 1` only, making goto/iftrue cases vacuous; 47 mechanical call-site updates in ArmCorrectness.lean

### Remaining sorrys (1 new, 2 pre-existing propagated)

- `verifiedGenerateAsm_spec` — extraction from `verifiedGenerateAsm` internals (hardest remaining sorry)
- Pre-existing: 2 arrLoad/arrStore sorrys in `verifiedGenInstr_correct` propagate through

---

## Add layout completeness to WellTypedLayout, eliminate 6 none-layout sorrys (2026-04-11)

**Goal:** A well-formed layout maps every variable to a location. Add completeness conjunct to `WellTypedLayout` and use it to discharge impossible `| none =>` cases.

### Changes

- **ArmSemantics.lean**: Extended `WellTypedLayout` with third conjunct `∀ v, layout v ≠ none`. Updated `float_not_ireg` to use `h.2.1`. Added `WellTypedLayout.complete` helper.
- **ArmCorrectness.lean**: Added `hMapped : layout v ≠ none` parameter to `vLoadVar_exec`, `vLoadVar_eff_exec`, `vLoadVarFP_exec`, `vLoadVarFP_eff_exec`. Replaced `sorry` in their `| none =>` cases with `exact absurd hv hMapped`. Replaced `sorry` in intToFloat/floatToInt `| none =>` cases with `exact absurd hLX/hLY (hWTL.complete x/y)`. Updated all call sites (14 total) to supply `hWTL.complete v`.

### Result

6 sorrys eliminated. 3 remain: arrLoad, arrStore, floatExp freg.

---

## Prove cmp/cmpLit/fcmp cases in verifiedGenBoolExpr_correct (2026-04-11)

**Goal:** Complete the boolean expression correctness proofs for the verified codegen path (ExtStateRel/VarLayout).

### Changes

- **ArmSemantics.lean**: Added `WellTypedLayout` predicate (non-float vars not in fregs, float vars not in iregs) with convenience lemmas `int_not_freg`, `bool_not_freg`, `float_not_ireg`.
- **ArmCorrectness.lean**: Added `hWTL : WellTypedLayout Γ layout` hypothesis to `verifiedGenBoolExpr_correct`, `verifiedGenInstr_correct`, and `ext_backward_simulation`. Proved `cmp` case (vLoadVar×2 + cmpRR + cset using `Flags.condHolds_correct`). Proved `cmpLit` case (vLoadVar + loadImm64 + cmpRR + cset with register preservation through loadImm64). Proved `fcmp` case (vLoadVarFP×2 + fcmpRR + cset using `Flags.condHolds_float_correct`). Fixed `bvar` hNotFreg sorry using `WellTypedLayout.bool_not_freg`.

### Result

4 sorrys eliminated (bvar hNotFreg, cmp, cmpLit, fcmp). No new sorrys introduced.

---

## Refactor eRelToStoreRel to membership-based quantification (2026-04-11)

**Goal:** Change `eRelToStoreRel` from `∀ v, σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o am_o` to `∀ e_o v, (e_o, .var v) ∈ rel → σ_t v = e_o.eval σ_o am_o`. The old definition falsely claims `σ_t v = σ_o v` for unmapped variables, breaking RegAlloc (which renames `a → __x0`).

### Changes

- **Core.lean**: Added `Expr.freeVars` (collect variable names from an expression).
- **ExecChecker.lean**: Added `relFindOrigVar` (explicit membership-based variable lookup). Changed `checkRelAtStartExec` to accept identity pairs. Changed `BoolExpr.mapVarsRel` to require explicit pairs via `relFindOrigVar`. Changed `checkDivPreservationExec`/`checkBoundsPreservationExec` to use `relFindOrigVar`. Replaced `defaultCheck` in `checkRelConsistency` with `fvCheck` + `amFvCheck` for free-variable coverage. Changed `buildInstrCerts1to1` to accept `allVars` and populate identity pairs. Updated `buildHaltCerts` to inherit `rel` from instrCerts.
- **SoundnessBridge.lean**: Changed `eRelToStoreRel` definition. Added `substSym_sound_fv`, `eRelToStoreRel_identity_pair`, `eRelToStoreRel_ssGet`, `eRelToStoreRel_of_relFindOrigVar`, `relFindOrigVar_mem`. Rewrote `checkStartCorrespondenceExec_sound`, `checkHaltObservableExec_sound`, `BoolExpr.eval_mapVarsRel`, `branchInfo_of_step_with_rel`, `transRel_sound` (post-state relation, div-safety, bounds, arrStore sections), `checkDivPreservationExec_sound`.
- **All optimizer files**: Added identity pairs via `collectAllVars` to ConstPropOpt, CSEOpt, LICMOpt, ConstHoistOpt, DCEOpt, PeepholeOpt. Updated DAEOpt to start with identity pairs and preserve them through live writes. Fixed RegAllocOpt's `mapRelsToTrans` to add identity pairs after copy-back instructions.
- **Tests/OptEffectiveness.lean**: Re-enabled `checkCertificateExec` for RegAlloc test.

### Result

0 sorrys, 0 errors (excluding LivermoreLoops). RegAlloc certificate now validates successfully.

---

## Remove gotoFree from program_refinement (2026-04-11)

**Goal:** Extend `Stmt.interp` and `refCompileStmt` so that the `gotoFree` hypothesis can be removed from `program_refinement` and all program-level refinement theorems.

### Approach

The root blocker was `progCompile_body_codeAt`, which needed `gotoFree` to bridge `compileStmt` (with labels) and `refCompileStmt` (without labels). Three coordinated changes eliminate this:

1. **WhileLang.lean** — `Stmt.interp` now returns `some (σ, am)` for `.goto` (no-op) and `some (σ, am)` for `.ifgoto b _` when `b.isSafe` (no-op). Previously both returned `none`. This makes goto/ifgoto "terminating" in the interpreter, which prevents the divergence contradiction from triggering vacuously.

2. **RefCompiler/Defs.lean** — `refCompileStmt` takes `(labels : List (String × Nat) := [])`. With labels, goto/ifgoto emit correct jump targets (matching `compileStmt`). Default `[]` preserves all existing callers.

3. **RefCompiler/Refinement.lean** — `compileStmt_eq_refCompileStmt` extended to any labels. `progCompile_body_codeAt` passes `collectLabels` to both sides, eliminating the `gotoFree` dependency.

### gotoFree removed from

- `progCompile_halt`, `progCompile_no_halt_unsafe`, `progCompile_reaches_error`
- `progCompile_no_halt_diverge`, `progCompile_no_halt_diverge_unsafe`
- `refCompileStmt_diverges`, `refCompile_diverge`
- **`program_refinement`** (the main goal)

### New sorry

`refCompileStmt_correct` has 2 sorry cases (goto, ifgoto) because `FragExec` assumes the PC ends at `offset + code.length`, but goto jumps elsewhere. Fixing this requires a non-local control flow model in `FragExec`. The sorry is localized — for programs without gotos, the sorry is never reached.

### Files changed

WhileLang.lean, CompilerCorrectness.lean, RefCompiler/Defs.lean, RefCompiler/Correctness.lean, RefCompiler/ErrorHandling.lean, RefCompiler/Metatheory.lean, RefCompiler/Refinement.lean

---

## Extract bounds check elision into BoundsOpt module (2026-04-10)

**Goal:** Factor the interval analysis for bounds check elision out of CodeGen into a standalone `BoundsOpt.lean` module. CodeGen independently verifies the invariant claims before eliding bounds checks, so a buggy analysis can never produce unsafe code.

### Design rationale

Explored adding `arrLoadSafe`/`arrStoreSafe` TAC constructors with "no bounds error" semantics, but this design has fundamental issues:
1. Every subsequent optimization pass must preserve the bounds invariant — no guarantee that index variable mappings maintain the in-bounds property across simulation chains.
2. If an `arrLoadSafe` instruction reaches CodeGen without valid verification, CodeGen silently generates out-of-bounds memory accesses. The formal correctness proofs hold vacuously (precondition unmet) but real hardware reads garbage.

Instead: no new TAC constructors. `BoundsOpt.lean` contains the interval analysis as a standalone module. CodeGen imports it, runs the analysis, and checks the results at each `arrLoad`/`arrStore` before deciding to elide bounds checks. If invariants are absent or insufficient, CodeGen always emits bounds checks.

### Changes

- **BoundsOpt.lean** (new): interval domain (`IRange`, `IMap`), transfer function, condition refinement, worklist solver with widening, `analyzeIntervals` entry point. All definitions are public (not `private`) for reuse.
- **CodeGen.lean**: removed embedded interval analysis (~130 lines). Now imports `BoundsOpt` and calls `BoundsOpt.analyzeIntervals`. `genInstr` uses `BoundsOpt.imLookup`/`BoundsOpt.IRange.inBounds` to check invariants at each array access.
- **CredibleCompilation.lean**: added `import CredibleCompilation.BoundsOpt`.

No TAC, proof, or optimizer changes. Benchmark results unchanged.

---

## Three performance optimizations (2026-04-10)

**Goal:** Close the gap vs clang -O2 on Livermore Loops benchmarks.

### 1. Copy coalescing in CodeGen
When all operands of an instruction are register-allocated (`__xN`/`__dN`), emit direct register-to-register ARM64 instructions instead of routing through scratch registers d0/d1/d2 or x0/x1/x2. Applied to fbinop, binop, intToFloat, floatToInt, floatExp, and cmp/fcmp comparisons. E.g. `fmul d3, d5, d6` instead of `fmov d1,d5; fmov d2,d6; fmul d0,d1,d2; fmov d3,d0`.

### 2. Constant hoisting (ConstHoistOpt pass)
New `ConstHoistOpt` pass that detects `const x v` instructions where ConstProp analysis shows `x` already holds `v`, and replaces with `goto (pc+1)`. Peephole compacts these. Runs after LICM in pipeline. Uses only ConstProp invariants — completely independent of CSE analysis, avoiding checker simplification conflicts.

### 3. Bounds check elision via interval analysis
Forward dataflow interval analysis in CodeGen tracking `[lo, hi)` per integer variable at each PC. Worklist algorithm with widening at back edges. Refines intervals at `ifgoto` branch points (handles cmp/cmpLit with lt/le and negations). When arrLoad/arrStore index is provably in `[0, arrSize)`, the `cmp`/`b.hs` bounds check is omitted. CodeGen-level only, no certificate impact.

**Files changed:** CodeGen.lean (~250 lines), ConstHoistOpt.lean (new, ~70 lines), LICMOpt.lean (reverted to CSE-only).

---

## Add exp() float intrinsic + K22 Planck radiation benchmark (2026-04-10)

**Goal:** Add `exp(x)` (e^x) as a unary float→float intrinsic, following the intToFloat/floatToInt pattern. Enable Livermore K22 (Planck radiation) benchmark.

### Changes across ~22 files

**Core definitions:**
- `Core.lean`: opaque `floatExpBv : BitVec 64 → BitVec 64`, `Expr.floatExp` constructor, eval/hasArrRead/eval_noArrRead cases
- `TAC.lean`: `TAC.floatExp : Var → Var → TAC`, `Step.floatExp`/`Step.floatExp_typeError`, isScalar/successors/deterministic/store_congr/mem_successors
- `TypeSystem.lean`: `WellTypedInstr.floatExp` (Γ x = .float → Γ y = .float), checker, progress, preservation, no_typeError, type_safety

**Source language + parser:**
- `WhileLang.lean`: `SExpr.floatExp`, compile/typecheck/eval/toString/isSafe + all proof cases (compileExpr_wt, compileStmt_wt, IsSeqInstr, compileExpr_allSeq, compileStmt_allJumpsLe)
- `Parser.lean`: `"exp"` keyword, `exp(...)` parsing in parseAtom, isFloatExpr/resolveSExpr cases

**Optimizer infrastructure:**
- `ExecChecker.lean`: simplify, substSym, execSymbolic, successors, instrVars, isNonZeroLit, buildInstrCerts1to1, computeNextPC
- All 7 optimization passes: ConstPropOpt, CSEOpt, LICMOpt (no change needed), DAEOpt, DCEOpt, PeepholeOpt, RegAllocOpt

**Code generation:**
- `CodeGen.lean`: `bl _exp` with d0 in/out, save/restore x29,x30 around call; collectVars

**Proofs (sorry where needed):**
- PropChecker, SoundnessBridge, CompilerCorrectness, RefCompiler/{Defs,Correctness,ErrorHandling,Metatheory,Refinement}, ArmSemantics, ArmCorrectness

**Benchmark:**
- `benchmarks/livermore/k22_planck.w` and `k22_planck.c`: Planck radiation kernel x/(e^x - 1), 1024 elements × 10000 reps. WhileLang achieves 1.0x vs C -O2.

---

## Div-safety chain: prove 3 of 4 sorrys, substantial progress on transRel_sound (2026-04-10)

**Goal:** Prove the 4 div-safety sorrys in SoundnessBridge.lean. These form a dependency chain around division-by-zero safety in the soundness bridge between executable Bool checkers and Prop-level specifications.

### Changes

**ExecChecker.lean:**
- Strengthened `checkOrigPathBoundsOk` to also reject div/mod binops at intermediate orig path labels (prevents div-by-zero in multi-step original paths)

**SoundnessBridge.lean:**
- **Proved `checkDivPreservationExec_sound`**: error preservation for div-by-zero and array-bounds errors. Case-splits the error step (Step.error, arrLoad_boundsError, arrStore_boundsError), extracts checker info per pc_t, transfers values through the store relation (eRelToStoreRel), and constructs matching error steps in the original program.
- **Eliminated `checkBinopSafe_sound` sorry**: replaced the impossible runtime-variable case with a `hDivSafe` parameter on `execPath_sound_gen`. The parameter provides div-safety for the first instruction; `hRestNoDivMod` covers intermediate labels (no div/mod allowed).
- **Proved `execPath_sound_gen` sorry**: uses `hDivSafe` for the first binop instruction, derives `hDivSafe₁` for recursive call via `hRestNoDivMod` (intermediate instructions can't be div/mod).
- **Substantial progress on `transRel_sound`**: proved the `hDivSafe` derivation (from `checkDivPreservationExec` + transformed step safety + store relation transfer), proved `hOrigBounds` (from `hOrigFirstOk` + bounds preservation), and scaffolded the main proof calling `execPath_sound`. Remaining: post-state relation via `checkRelConsistency`, array memory equality, and edge case (orig has div/mod but transformed instruction is not a binop).
- Updated `checkOrigPathBoundsOk_extract` to extract both scalar and no-div/mod conditions
- Updated `checkAllTransitionsExec_sound` to thread `hdivpres` through to `transRel_sound`

### Sorry count: 10 declarations with sorry (was 10), but SoundnessBridge reduced from 4 decls to 1 decl
- SoundnessBridge: 3 sorry lines in `transRel_sound` (was 4 sorrys in 4 declarations)
- ExecChecker: 1, ArmSemantics: 2 decls, ArmCorrectness: 4 decls (unchanged)

---

## Prove fassign/farrWrite cases, float ErrorHandling, delete intTyped (2026-04-10)

**Goal:** Prove remaining float-related sorry cases in Correctness.lean and ErrorHandling.lean, delete deprecated `intTyped` infrastructure. 29→25 sorrys (−4 net, but also fixed a pre-existing sorry in ErrorHandling barrWrite).

### Changes

**RefCompiler/Defs.lean:**
- Added `FragExec.single_arrStore_float` lemma for float array stores

**RefCompiler/Correctness.lean:**
- Proved `fassign` case in `refCompileStmt_correct` — 6 sub-cases matching specialized compilation: `flit` (const), `var` (copy), `fbin` (fbinop), `intToFloat`, `farrRead` (arrLoad float + copy), and wildcard fallback (4 expression forms)
- Proved `farrWrite` case — mirrors `arrWrite` but with float val type and `single_arrStore_float`

**RefCompiler/ErrorHandling.lean:**
- Proved `refCompileExpr_stuck` float cases: `flit` (impossible), `fbin` (mirrors bin), `intToFloat`/`floatToInt` (delegate to sub-expr), `farrRead` (mirrors arrRead with .float)
- Proved `refCompileBool_stuck` fcmp case (mirrors cmp)
- Proved `refCompileStmt_stuck` and `refCompileStmt_unsafe` fassign cases — specialized sub-cases for fbin/intToFloat/farrRead, wildcard delegation for remaining forms
- Proved `refCompileStmt_stuck` and `refCompileStmt_unsafe` farrWrite cases — mirrors arrWrite with float val
- Proved assign float sub-cases in both `_stuck` and `_unsafe` (flit impossible, rest delegate to `refCompileExpr_stuck`)
- Fixed pre-existing sorry in barrWrite `hvidx_bool` (was discarding `hfprev_bool`)

**CompilerCorrectness.lean:**
- Deleted deprecated `SBool.intTyped`, `Stmt.intTyped` definitions
- Deleted `checkSExpr_intVars`, `checkSBool_intTyped`, `checkStmt_intTyped`, `Program.typeCheck_intTyped` (3 sorry-using declarations removed)

**RefCompiler/Metatheory.lean:**
- Deleted `Stmt.intTyped_fuel_succ` and `Stmt.intTyped_of_le` (2 sorry-using declarations removed)

### Sorry count: 25 (was 29)
- Metatheory: 5 (pre-existing)
- Refinement: 3 (pre-existing)
- ArmCorrectness: 7, ArmSemantics: 4, SoundnessBridge: 5, ExecChecker: 1

---

## Livermore Loops benchmark suite (2026-04-10)

**Goal:** Add realistic numerical-kernel tests from the Lawrence Livermore National Laboratory loop benchmark (McMahon, 1986) to stress-test all optimization passes on array-heavy, float-heavy, multi-loop programs, and measure compiled-code performance vs clang.

### Changes

**Tests/LivermoreLoops.lean (new):**
- 8 kernels translated to TAC: K1 (hydro fragment), K3 (dot product), K5 (tri-diagonal elimination), K7 (equation of state), K11 (prefix sum), K12 (first difference), K21 (matrix multiply), K24 (find minimum)
- Each kernel tested individually through selected optimization passes (ConstProp, CSE, LICM, DAE, Peephole, RegAlloc) with certificate verification
- Full `optimizePipeline` regression test runs all 8 kernels end-to-end
- Exercises: indirect array indexing, flattened 2-D arrays, nested loops (3-deep for matmul), float reductions, conditional updates, loop-carried dependencies

**benchmarks/livermore/ (new):**
- 18 WhileLang source programs (.w) and 18 equivalent C programs (.c)
- Kernels: K1 hydro, K2 ICCG, K3 dot product, K4 banded linear, K5 tri-diagonal, K6 general recurrence, K7 EOS, K8 ADI/stencil, K9 integrate predictors, K10 difference predictors, K11 prefix sum, K12 first difference, K14 1-D PIC, K17 implicit conditional, K18 2-D explicit hydro, K20 discrete ordinates, K21 matrix multiply, K24 find minimum
- Skipped: K13 (2-D PIC, too complex), K15/K16 (need RNG), K19 (variant of K6), K22 (needs exp()), K23 (variant of K18)
- `run.sh` benchmark runner: compiles both, measures wall-clock time, prints comparison table
- C programs include internal `clock_gettime` timing (kernel-only, excludes init)

**CodeGen.lean:**
- Fixed `.space` directive to use actual declared array size instead of hardcoded 8192 bytes

### Benchmark results (Apple M-series, 1024-element arrays, 10K reps)

| Kernel            | C -O2 (s) | WhileLang (s) | Ratio |
|-------------------|-----------|--------------|-------|
| K1 hydro          | 0.33      | 0.28         | 0.9x  |
| K2 ICCG           | 0.28      | 0.36         | 1.3x  |
| K3 dot product    | 0.26      | 0.28         | 1.1x  |
| K4 banded linear  | 0.26      | 0.29         | 1.1x  |
| K5 tri-diag       | 0.31      | 0.35         | 1.1x  |
| K6 recurrence     | 0.26      | 0.25         | 1.0x  |
| K7 EOS            | 0.26      | 0.30         | 1.1x  |
| K8 ADI stencil    | 0.26      | 0.30         | 1.1x  |
| K9 integrate      | 0.26      | 0.29         | 1.1x  |
| K10 diff predict  | 0.28      | 0.29         | 1.0x  |
| K11 prefix sum    | 0.26      | 0.36         | 1.4x  |
| K12 first diff    | 0.26      | 0.28         | 1.1x  |
| K14 1-D PIC       | 0.26      | 0.26         | 1.0x  |
| K17 implicit cond | 0.27      | 0.28         | 1.1x  |
| K18 2-D hydro     | 0.26      | 0.69         | 2.6x  |
| K20 discrete ord  | 0.67      | 0.34         | 0.5x  |
| K21 matmul        | 0.28      | 0.32         | 1.2x  |
| K24 find min      | 0.29      | 0.27         | 0.9x  |

---

## Unified checkExpr type-checker and sorry elimination (2026-04-09)

**Goal:** Fix `checkSExpr`/`checkFExpr` bug (accepted float forms in int context), write correct `checkExpr_typedVars` bridge, eliminate sorrys. 34→26 sorrys (−8 net).

### Changes

**WhileLang.lean:**
- Replaced `checkSExpr`/`checkFExpr` with unified `checkExpr (ty : VarTy) : SExpr → Bool` + `abbrev` wrappers
- Unified `compileExpr_wt`/`compileExpr_float_wt` into `compileExpr_typed_wt` with ty parameter (eliminates 6 sorrys for float cases + floatToInt)
- Fixed `compileStmt_wt` — `assign (floatToInt e)` now proven, all float-in-int-context cases closed by contradiction

**CompilerCorrectness.lean:**
- Generalized `checkSExpr_declared` → `checkExpr_declared` (works with any `ty`)
- **New: `checkExpr_typedVars`** — single induction gives `e.typedVars σ am` + `wrapEval` correctness from `checkExpr ty e + TypedStore`. This is the correct replacement for the 4 bridge sorrys.
- Proved `checkSBool_declared` for `fcmp` case (was sorry)
- Proved `checkStmt_declared` for `fassign`/`farrWrite` (2 sorrys → 0)
- Proved `Stmt.interp_preserves_typedStore` for `fassign`/`farrWrite` (2 sorrys → 0)
- Proved `Stmt.interp_some_implies_safe` for `fassign`/`farrWrite` (2 sorrys → 0)
- Proved `Stmt.interp_tmpAgree` for `fassign`/`farrWrite` (2 sorrys → 0)
- Closed `checkSExpr_intVars` float contradiction cases (4/5 done, `floatToInt` still sorry — predicate is wrong)

### Remaining blockers
- 4 bridge sorrys (`typedVars_of_intVars` etc.) are **fundamentally unprovable** as stated — they assume uniform value types but `floatToInt`/`intToFloat` have mixed types. Callers should migrate to `checkExpr_typedVars`.
- `intTyped`/`intVars` predicate is wrong for float statements — needs replacement with `typedVars`-based predicate. Blocks `checkStmt_intTyped` for `fassign`/`farrWrite`/`fcmp`.
- `refCompileExpr_correct_int` wrapper sorrys blocked by above.

---

## Generalize refCompileExpr_correct for float expressions (2026-04-09)

**Goal:** Eliminate the 5 sorrys in `refCompileExpr_correct` for float expression cases (flit, fbin, intToFloat, floatToInt, farrRead). These were blocked because the theorem conclusion hard-coded `.int` wrapping but float TAC stores `.float`.

### Changes

**WhileLang.lean:**
- Fixed `SExpr.eval` `.var` case: `.toInt` → `.toBits` (transparent for int vars via `toBits_int` simp lemma, correct for float vars)
- Added `SExpr.wrapEval`: type-aware evaluation returning `Value` (`.int` for int-producing, `.float` for float-producing, `σ x` for `.var`)
- Added `SExpr.typedVars`: context-sensitive typing predicate with embedded `wrapEval` bridge for sub-expressions

**RefCompiler/Defs.lean:**
- Added `FragExec.single_fbinop`, `single_intToFloat`, `single_floatToInt`, `single_arrLoad_float`
- Added `SExpr.safe_fbin_left`, `safe_fbin_right`

**RefCompiler/Correctness.lean:**
- **Generalized `refCompileExpr_correct`** — all 9 expression cases now fully proven (0 sorry):
  - New signature: `hftf` (isFTmp), `htypedv` (typedVars), 2-arg `hagree`, `wrapEval` conclusion, ftmpName preservation
  - New cases: flit, fbin, intToFloat, floatToInt, farrRead — each proved using new FragExec helpers
- Added `refCompileExpr_result_ftmp_bound` (mirrors `result_bound` for `isFTmp`/`ftmpName`)
- Added `refCompileExpr_correct_int` backward-compatible wrapper (old signature, uses bridge lemmas)
- Updated `refCompileBool_correct` signature to accept `hftf`

**CompilerCorrectness.lean:**
- Added `noTmpDecls_not_ftmp`, `Stmt.ftmpFree`, `Program.typeCheck_ftmpFree`
- Added bridge lemmas (temporary sorry): `typedVars_of_intVars`, `typedVars_of_floatVars`, `wrapEval_eq_int`, `wrapEval_eq_float`

### Sorry status
- **Eliminated:** 5 sorrys in `refCompileExpr_correct` (the main target)
- **Added (temporary):** 6 sorrys in bridge lemmas and backward-compat wrapper
- **Next:** Fix `checkSExpr`/`checkFExpr` mutual recursion to properly reject float-producing forms in int context, enabling clean bridge proofs. Then update `Stmt.intTyped` to use `typedVars`.

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

## 25. Float temporary infrastructure and WhileLang float proofs (2026-04-09)

**Phase 0 — Float temporary infrastructure:**
- Added `ftmpName (k : Nat) : Var := s!"__ft{k}"` and `String.isFTmp` predicate
- Updated `compileExpr`/`compileStmt` to use `ftmpName` for float-producing expressions (`flit`, `fbin`, `intToFloat`, `farrRead`)
- Extended `tyCtx` to map `__ft`-prefixed vars to `.float` (others still default to `.int`)
- Extended `noTmpDecls` to also check `!x.isFTmp`
- Added `initStoreBase` (float temps default to float zero) for correct TypedStore
- Proved `tyCtx_ftmp_wt`, `ftmpName_isFTmp_wt`, `tmpName_not_isFTmp`, `lookup_none_of_isFTmp_wt`
- Mirrored all changes in RefCompiler/Defs.lean with `ftmpName_injective`, `ftmpName_ne`, collision lemmas

**Phase 1 — WhileLang.lean float proofs (65 sorrys remain, down from ~71):**
- Added `compileExpr_float_wt`: parallel to `compileExpr_wt` but uses `checkFExpr` and proves result type `.float`
- Filled `compileBool_wt .fcmp` using `compileExpr_float_wt`
- Filled `compileStmt_wt .fassign` (all sub-cases except degenerate `floatToInt`) and `.farrWrite`
- Filled `compileStmt_allJumpsLe` for `.fassign`, `.farrWrite`, and `.assign` float fallback cases
- Remaining WhileLang sorrys: 5 dead (superseded by `compileExpr_float_wt`), 3 degenerate (type checker permits `floatToInt` in float context / float exprs in int context)

## 26. Sorry elimination — Phases 2, 5, 6 (2026-04-09)

Eliminated 19 sorrys across three RefCompiler files. Down from ~65 to ~35 sorrys.

**Phase 6 — RefCompiler/Refinement.lean (5 sorrys → 0):**
- `compileExpr_eq_refCompileExpr` float cases: `rfl` for `flit`, `simp` with IHs for `fbin`/`intToFloat`/`floatToInt`/`farrRead`
- `compileBool_eq_refCompileBool` `fcmp`: `simp` with `compileExpr_eq_refCompileExpr`
- `compileStmt_eq_refCompileStmt` `fassign`: case-split on expr, `rfl`/`simp` for each sub-case
- `compileStmt_eq_refCompileStmt` `farrWrite`: `simp` with `compileExpr_eq_refCompileExpr`

**Phase 5 — RefCompiler/Metatheory.lean (10 sorrys → 0):**
- `SExpr.isSafe_of_safe` float cases: mirrors int pattern (`simp [SExpr.safe/isSafe]` + IHs)
- `SBool.isSafe_of_safe` `fcmp`: `simp` with `SExpr.isSafe_of_safe`
- Added `interp_ne_none_of_safe_fassign` and `interp_ne_none_of_safe_farrWrite` helper lemmas
- `Stmt.interp_fuel_succ`, `safe_fuel_succ`, `intTyped_fuel_succ` for `fassign`/`farrWrite`: `simp_all [Stmt.interp/safe/intTyped]` (no fuel dependence)
- `refCompileStmt_diverges` for `fassign`/`farrWrite`: `exfalso` via new helper lemmas (leaf stmts can't diverge)

**Phase 2 — RefCompiler/Correctness.lean (9 sorrys → 5):**
- `refCompileExpr_nextTmp_ge` float cases: mirror int pattern with `omega`
- `refCompileBool_nextTmp_ge` `fcmp`: mirror `cmp` pattern
- `refCompileExpr_result_bound` float cases: `ftmpName` results use `left` + `ftmpName_not_isTmp`; `floatToInt` uses `right` (produces `tmpName`)
- `refCompileBool_vars_bound` `fcmp`: mirrors `cmp` exactly
- **5 remaining**: `refCompileExpr_correct`, `refCompileBool_correct`, `refCompileStmt_correct` float cases require generalizing theorem from `.int` to `.float` result wrapping — blocked on `refCompileExpr_float_correct` infrastructure
