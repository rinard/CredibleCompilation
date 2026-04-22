# Full Backward Correctness Theorems for the Verified ARM Pipeline

## Framing

Current state: forward simulation is done at TAC→ARM, but only one-directional ("if TAC halts, ARM reaches some s' with matching observables"). The new theorems invert direction and also partition the ARM state space: every ARM run lands in one of four bins (haltFinal, divS, boundsS, diverges), and each bin maps to a unique source behavior.

Three orthogonal axes of work:
- **A. Infrastructure**: `haltFinal = bodyFlat.size` (✅ Phase 2a done; Phase 2b pending for the stepping proof), refined `unsafe_div`/`unsafe_bounds` (✅ Phase 1 done), `ArmDiverges` (Phase 5), tightened `ExtSimRel` for `.halt` (Phase 2b optional / Phase 4).
- **B. Forward sharpening**: tighten existing forward theorems to name specific PCs and distinguish div/bounds.
- **C. Backward inversion**: prove the five backward theorems via ARM determinism + "no other behavior is possible" exhaustion.

## Existing theorems that must be preserved

- **`generateAsm_total`** at [PipelineCorrectness.lean:580](CredibleCompilation/PipelineCorrectness.lean#L580): well-typed source ⇒ codegen produces ARM (0 sorrys, closed at commit eeece53).
- **`generateAsm_total_with_passes`** at [PipelineCorrectness.lean:562](CredibleCompilation/PipelineCorrectness.lean#L562): same with cert-validated passes.
- Phase 2 restructures `bodyFlat` to include `haltSaveBlock`; the totality proof needs a small update to cover this addition (straightforward — the halt-save block is a finite deterministic construction). Phases 3–7 don't touch codegen structure, so totality is preserved automatically.

This compile-time totality (distinct from Phase 6's runtime totality-of-ARM-behavior) is the property that `verifiedGenerateAsm` returns `.ok` on any well-typed input, rather than potentially erroring.

## Pre-plan refactors already landed

- **`genHaltSave` restructured** ([CodeGen.lean:614](CredibleCompilation/CodeGen.lean#L614)): `filterMap` replaced by `flatMap` over a per-observable helper `genHaltSaveOne`. All four observable-location cases (ireg, freg, stack, no-layout) are explicit. Semantically identical to the previous version; cleaner proof surface for Phase 2. No spec changes yet.

## Probe findings (pre-implementation investigation)

- **Cfg.error volume**: 25 direct mentions across 5 files (PropChecker 13, PipelineCorrectness 6, SoundnessBridge 3, TAC 2, TypeSystem 1). Smaller than the initial "200+ lines" estimate — Phase 3 downsized.
- **ArmStep totality**: all ~40 rules have only `prog[s.pc]? = some instr` as precondition; no state-dependent hypotheses (even `sdivR` fires on zero divisor because `BitVec.sdiv` is total). Phase 6's per-constructor totality lemma is near-trivial.
- **`haltSaveInstrs` structure**: confirmed flat `str`/`fstr` sequence, no branches, no pseudo-ops.
- **`step_simulation` signature** ([CodeGen.lean:3464](CredibleCompilation/CodeGen.lean#L3464)): `∃ s', ArmSteps s s' ∧ ExtSimRel cfg' s'` — the exact shape needed for `Classical.choose` + `Nat.rec` divergence construction.
- **`genHaltSave` silently drops observables** (motivator for Phase 2 spec addition): observables without a varMap entry, or without a layout entry, produce no save instruction. Needs a `haltSaveComplete` spec clause in `GenAsmSpec` to rule these cases out.

## Phases

### Phase 1 — Split source safety into unsafe_div / unsafe_bounds — ✅ DONE (commit `d82557a`, 2026-04-21)

**Landed in**: [CompilerCorrectness.lean](CredibleCompilation/CompilerCorrectness.lean) § 4a′ only. `WhileLang.lean` and `RefCompiler/ErrorHandling.lean` untouched — predicates are dormant until Phase 3 wires them through `Cfg.error`.

**Shipped**:
- Predicates: `SExpr.unsafeDiv`, `SExpr.unsafeBounds`, `SBool.unsafeDiv`, `SBool.unsafeBounds`, `Stmt.unsafeDiv`, `Stmt.unsafeBounds`, plus list-lifts `SExpr.listUnsafeDiv`/`listUnsafeBounds` for `Stmt.print`.
- Lemmas (3 per level × 4 levels — SExpr, SBool, SExpr-list, Stmt): `safe_iff_not_unsafe`, `not_safe_iff_unsafeDiv_or_unsafeBounds`, `unsafeDiv_unsafeBounds_disjoint`.
- Eval-order discipline matched: short-circuit `and`/`or` guards on `a.safe ∧ a.eval = true/false ∧ b.unsafe...`, `seq`/`loop` thread state via `s₁.interp`, `print` uses left-fold list helper.

**Notes for downstream phases**:
- `CompilerCorrectness.lean` now imports `Mathlib.Tactic.Tauto` and `Mathlib.Tactic.Push` (was Mathlib-free). `tauto` does the heavy lifting on the 3-disjunct `.bin .div`/`.mod` cases.
- New `section UnsafeSplit` opens `Classical` for `by_cases` on Prop-valued safety predicates. Phase 3 callers can either stay inside this section or re-derive what they need outside.

**Status**: 0 sorrys; full `lake build` green. ~370 LOC of meaningful code (574 lines of diff with comments).

### Phase 2a — Infrastructure: haltSaveBlock in bodyFlat, haltFinal as real PC — ✅ DONE (commit `b59713b`, 2026-04-21)

**Landed in**: 2 files — `CodeGen.lean` and `ArmSemantics.lean`. Net diff: +538 / −215. No downstream files required changes (additive spec clauses, renamed field picked up cleanly from the pretty-printer only).

**Shipped**:
- `VerifiedAsmResult.haltSaveInstrs` renamed to `haltSaveBlock`.
- `VerifiedAsmResult.bodyFlat := (bodyPerPC.toList.flatMap id ++ haltSaveBlock.toList).toArray` (halt-save block lives inside the verified region).
- New field `haltFinal : Nat`. Relationship: `haltFinal = haltS + haltSaveBlock.size = bodyFlat.size`.
- Killed the `p.code.size * 1000` sentinel. New values: `haltS := pcMap p.code.size` (= start of halt-save block), `divS := haltFinal + 1`, `boundsS := haltFinal + 2` (off-the-end of bodyFlat, stuck).
- `instrLength` refactored to not take `haltS`/`divS`/`boundsS` args (labels don't affect instruction count). This breaks the circular definition of `haltS := pcMap p.code.size`.
- New **`verifiedGenInstr_length_params_ind`** lemma (ArmSemantics.lean): `verifiedGenInstr` output length depends on neither `pcMap` nor the haltS/divS/boundsS label values. This generalizes the existing `_pcMap_ind` and enables the dummy-labels trick in `instrLength`.
- New **`CodeAt.liftToSuffix`** (ArmSemantics.lean): `CodeAt pre.toArray startPC instrs → CodeAt (pre ++ suf).toArray startPC instrs`. General utility for any future bodyFlat-extension work.
- New **`codeAt_of_bodyFlat'`** wrapper in CodeGen.lean: per-PC block embeds in the new bodyFlat (flat ++ haltSaveBlock suffix). Used by the 3 `step_simulation` / `tacToArm_correctness` call sites.

**GenAsmSpec additions** (all discharged, 0 sorrys):
- `haltS_eq : r.haltS = (r.bodyPerPC.toList.flatMap id).length` — proved via `buildPcMap_eq_take_length` + `bodyGenStep_length`.
- `haltFinal_eq : r.haltFinal = r.haltS + r.haltSaveBlock.size` — rfl by construction.
- `divS_eq : r.divS = r.haltFinal + 1`, `boundsS_eq : r.boundsS = r.haltFinal + 2` — rfl.
- `haltSaveBlock_eq : r.haltSaveBlock.toList = genHaltSave p.observable r.layout r.varMap`.
- `haltSaveComplete : ∀ v ∈ p.observable, (ireg ir ∧ varMap off) ∨ (freg fr ∧ varMap off) ∨ (stack off)` — rules out `genHaltSaveOne` silent-drop cases.

**New helper lemmas** (parallel to existing `buildVarLayout_complete`):
- `observable_subset_collectVars : ∀ v ∈ p.observable, v ∈ collectVars p`.
- `buildVarMap_lookup_of_mem : ∀ v ∈ collectVars p, lookupVar (buildVarMap (collectVars p)) v ≠ none`.

**Notes for Phase 2b and downstream phases**:
- `haltS`/`divS`/`boundsS`/`haltFinal` are **fields on VerifiedAsmResult, not defs**. Chosen to minimize downstream disruption; their values are constrained by the new `GenAsmSpec` clauses.
- `verifiedGenerateAsm_spec` was **moved later in the file** (from line 1387 to just before `step_simulation`) so it can use `buildPcMap_eq_take_length`, `codeAt_of_bodyFlat'`, and the observable/varMap helpers (all of which live after the original spec location).
- `ExtSimRel` halt case is **still** `ExtStateRel ∧ arm.arrayMem = am` (no PC constraint). Tightening to include `arm.pc = haltFinal` is Phase 2b scope.
- `step_simulation`'s halt case **still produces** `s'.pc = haltS` (= start of halt-save block, not haltFinal). Phase 2b adds the stepping through.
- The `haltSaveComplete` clause doesn't yet rule out stack-offset collisions; Phase 2b needs either a new `varMap` invariant in `GenAsmSpec` or has to derive it from existing spec components.

**Effort**: ~1 session (less than the 3–4 day estimate for full Phase 2). Surprises: (i) writing the `params_ind` lemma took some tactic fiddling for the `.binop .div/.mod`, `.arrLoad/.arrStore unsafe` cases where labels appear inside specific instructions; solved via `cases h; simp [List.length_*]`. (ii) Moving `verifiedGenerateAsm_spec` below the needed helpers was necessary; forward-reference doesn't work without `mutual`.

### Phase 2b — Halt-case step-through to haltFinal — ✅ DONE (commit `2051691`, 2026-04-21)

**Landed in**: 1 file — `CodeGen.lean`. Net diff: +391 / −32. No downstream files required changes.

**Shipped**:
- **`armSteps_haltSaveBlock`** lemma: given `ExtStateRel layout σ s` and `CodeAt prog s.pc (genHaltSave observable layout varMap)` plus the two new spec invariants, produces `s'` with `ArmSteps prog s s'`, `s'.pc = s.pc + (genHaltSave ...).length`, `s'.arrayMem = s.arrayMem`, `ExtStateRel layout σ s'`. Proved by induction on `observable`, case-splitting each `genHaltSaveOne` into its 4 branches (ireg+varMap, freg+varMap, stack, none) and using `ExtStateRel.setStack_fresh` for the writing branches.
- **Halt intercept in `step_simulation`**: added `by_cases hHalt : p[pc] = .halt` in the normal-case branch, handling halt manually (one `ArmStep.branch` to `r.haltS`, then `armSteps_haltSaveBlock`) rather than delegating to `ext_backward_simulation`.
- Two new `GenAsmSpec` clauses (both discharged):
  - `varMapInjOnOffsets : ∀ v w off, lookupVar r.varMap v = some off → lookupVar r.varMap w = some off → v = w`. Discharged via new helpers `mem_keys_of_lookupVar_some` / `mem_of_lookupVar_some` + existing `lookupVar_buildVarMap_injOn`.
  - `layoutStackComesFromVarMap : ∀ v off, r.layout v = some (.stack off) → lookupVar r.varMap v = some off`. Discharged by unfolding `buildVarLayout`'s filterMap.

**ExtSimRel halt-case tightening**: **NOT done** (deferred to Phase 4). Phase 2b's halt arm now *reaches* `haltFinal` in the ARM trace, but `ExtSimRel (.halt σ am) arm` still reads `ExtStateRel ∧ arm.arrayMem = am` (no PC constraint). Phase 4's forward-theorem sharpening is where `arm.pc = haltFinal` surfaces through the interface.

**Downstream churn**: zero. `step_simulation`'s signature unchanged; the halt case takes more ARM steps than before but the existing `ExtSimRel` contract is preserved by `armSteps_haltSaveBlock` (halt case depends only on `ExtStateRel σ s'` and `s'.arrayMem = am`).

**Notes for downstream phases**:
- `armSteps_haltSaveBlock` is reusable — Phase 6 (ARM totality) will need it to handle the halt-save branch of its per-PC successor argument.
- The two new spec clauses are available to any future proof needing halt-save freshness or varMap/layout coherence.
- Phase 4 must now produce the `arm.pc = r.haltFinal` conjunct in `while_to_arm_correctness`; the ARM trace actually reaches that PC, it just isn't currently asserted in `ExtSimRel`.

**Surprises / snags**:
- `Array.getElem?_toArray` doesn't exist; used `List.getElem?_toArray` instead for the `CodeAt` construction on the `bodyFlat` halt-save suffix.
- The freshness argument splits cleanly into 4 cases per observable but the initial attempt with a unified `hFresh_of` helper was clumsier than just inlining per case.

**Status**: 0 sorrys; full `lake build` green. ~250 LOC of meaningful code.

### Phase 3 — Split Cfg.error into Cfg.errorDiv / Cfg.errorBounds — ✅ DONE (commit `5f5a496`, 2026-04-21)

**Landed in**: 13 files — TAC, TypeSystem, PropChecker, SoundnessBridge, RefCompiler/{Correctness, ErrorHandling, Refinement}, PipelineCorrectness, ArmSemantics, ArmCorrectness, CodeGen, ExecChecker. Net diff: +796 / −524.

**Shipped**:
- `Cfg.error σ am` → `Cfg.errorDiv σ am` + `Cfg.errorBounds σ am` (two constructors).
- `Step.error` renamed to `Step.binop_divByZero`, produces `.errorDiv`. `arrLoad_boundsError` / `arrStore_boundsError` produce `.errorBounds`.
- New `Step.no_step_from_errorDiv` / `no_step_from_errorBounds` terminal lemmas.
- New cause-agnostic `Cfg.isError : Cfg → Prop` predicate + `Step.no_step_from_isError` lemma — used by downstream callers (e.g. `error_run_no_halt`, `whileToTAC_reaches_error`) that only need "some runtime error" without caring which kind.
- `checkErrorPreservationProp` restructured as a conjunction (errorDiv branch ∧ errorBounds branch), each cause-preserving.
- `Behavior.errors σ'` clause in `program_behavior` and `program_behavior_init` is now a disjunction `errorDiv ∨ errorBounds` — preserves the cause-agnostic user-facing view while routing cause through the pipeline.
- `compileExpr_stuck` / `compileBool_stuck` / `compileStmt_stuck` / `compileStmt_unsafe` / `compileExprs_unsafe` conclusions now have extra `∃ c_err, ... ∧ c_err.isError ∧ ...` fields — ~40 destructure/construct sites mechanically updated.
- `SoundnessBridge.checkDivPreservationExec_sound` restructured as `refine ⟨?divBranch, ?boundsBranch⟩`, each dispatching on the matching Step constructor.

**Notes for downstream phases**:
- **ExtSimRel error cases are still `True`** — `.errorDiv _ _ => True | .errorBounds _ _ => True`. Pattern-matches distinctly but doesn't constrain `arm.pc` yet. Phase 4 tightens these to `arm.pc = divS` / `arm.pc = boundsS` as part of the forward-theorem sharpening. The existing `verifiedGenInstr_correct` error arms still return `⟨s, .refl, trivial⟩`; Phase 4 will trace through the `cbz … divS` / `cmpImm…; bCond .hs … boundsS` code and actually step to the sentinel.
- **Churn beyond probe**: probe estimated 25 direct `Cfg.error` mentions; actual patch touched ~60 sites because the disjunction form had to propagate through every `∃` / `match` that surfaced an error config (`program_behavior_init`, `whileToTAC_reaches_error`, `applyPass_preserves_error_am`, `applyPassesPure_preserves_error_am`, `while_to_arm_error_preservation`, every `steps_to_*_decompose`, etc.).
- **`while_to_arm_error_preservation` signature changed**: now takes an ambient `c_err : Cfg` with `c_err = Cfg.errorDiv _ _ ∨ c_err = Cfg.errorBounds _ _` plus a reach to `c_err`. Phase 4 will split this into `while_to_arm_div_preservation` / `while_to_arm_bounds_preservation` with specific PC conclusions.
- **`unsafe_binop_errors`** in `RefCompiler/Correctness.lean` now produces `.errorDiv` directly — Phase 4 can rely on this.

**Status**: 0 sorrys; full `lake build` green.

### Phase 4 — Tighten forward theorems (name haltFinal; distinguish div vs bounds) — ✅ DONE (commit `915c019`, 2026-04-21)

**Landed**:
- `ExtSimRel` parameterized on `divS`/`boundsS`; errorDiv/errorBounds arms pin `arm.pc` to the respective sentinel.
- `ArmCorrectness`'s three error arms (`binop_divByZero`, `arrLoad_boundsError`, `arrStore_boundsError`) step through the emitted `cbz` / `cmpImm + bCond .hs` to reach `divS`/`boundsS`.
- `step_simulation` gains a halt-PC side output: `cfg' = .halt` ⇒ `s'.pc = r.haltFinal`. Threaded through `tacToArm_refinement`, `tacToArm_correctness`, `while_to_arm_correctness`.
- `while_to_arm_error_preservation` replaced by the cause-specific pair `while_to_arm_div_preservation` / `while_to_arm_bounds_preservation` (errorDiv ⇒ `s'.pc = r.divS`; errorBounds ⇒ `s'.pc = r.boundsS`). Both conclude `∃ fuel, unsafeDiv ∨ unsafeBounds` on the source side; per-cause matching deferred to Phase 7 (pending `compileStmt_unsafe` refactor).
- `whileToTAC_refinement`'s `.errors` arm upgraded to produce the unsafe disjunction directly via the Phase 1 iff.

**Surprise / side-effect**: `boundsSafe = true` elision became incompatible with the new `ExtSimRel.errorBounds = (arm.pc = boundsS)` constraint (`verifiedGenInstr` with `boundsSafe = true` omits the bounds-check instructions, so the error arm has no branch to `boundsS`). Temporarily disabled elision (`isBoundsSafe` hard-wired to `false`; `hBoundsSafeFalse` threaded through `verifiedGenInstr_correct` / `ext_backward_simulation`). Re-enabled via the separate **BoundsOptCert** plan (plans/certified-interval-pangolin.md), which landed in 7 phases through commit `fb42764`.

**Status**: 0 sorrys; full `lake build` green.

### Phase 5 — ARM divergence predicate + forward divergence simulation

**Files**: new section in `CredibleCompilation/ArmSemantics.lean` (or new `ArmDivergence.lean`), `CredibleCompilation/PipelineCorrectness.lean`.

**Phase 5a — Infrastructure (✅ DONE, 2026-04-21)**:
- `ArmStepsN prog s s' n` — counted multi-step ARM closure parallel to `StepsN`.
- Six utility lemmas: `ArmStepsN_extend`, `ArmStepsN_split_last`, `ArmStepsN_trans`, `ArmStepsN_prefix`, `ArmSteps_to_ArmStepsN`, plus the by-construction `ArmStepsN_refl` case in the definition.
- `ArmDiverges` defined **in reachability form**:
  ```lean
  def ArmDiverges (prog : ArmProg) (s₀ : ArmState) : Prop :=
    ∀ n, ∃ s, ArmStepsN prog s₀ s n
  ```

  The originally-planned exists-function form (`∃ f : Nat → ArmState, f 0 = s₀ ∧ ∀ n, ArmStep prog (f n) (f (n+1))`) is strictly stronger in general nondeterministic systems (König's lemma needs finite branching). In ARM specifically, PC is deterministic — havoc at libcall/printcall only affects caller-saved register values, not PC — so the canonical PC sequence is unique and any `ArmStepsN init s n` witness has the canonical PC at step `n`. **Both forms discharge the Phase 7 backward arguments equivalently**: "source halts → ARM's canonical PC reaches `haltFinal` at step `M`, which is stuck → `ArmStepsN_split_last` on any alleged length-`(M+1)` reach forces a predecessor at `haltFinal` with no successor — contradiction." The reachability form is cheaper to prove forward and equally usable backward.

**Phase 5b — Forward divergence theorem (PARTIAL)**:

The remaining Phase 5 deliverable is proving
```lean
theorem while_to_arm_divergence_preservation :
    ... → ArmDiverges r.bodyFlat initState
```
which under the reachability definition expands to `∀ n, ∃ s, ArmStepsN r.bodyFlat init s n`.

**Shipped so far** (commit TBD, 2026-04-21):
- `verifiedGenBoolExpr_length_pos` — side lemma: under `be.hasSimpleOps = true`, `(verifiedGenBoolExpr layout be).length ≥ 1`. The `.bexpr` arm is dispatched via `simp [BoolExpr.hasSimpleOps]` at the hypothesis (any `.bexpr` makes `hasSimpleOps` false). All other arms discharge by `simp only [verifiedGenBoolExpr, List.length_append, List.length_cons, List.length_nil]` + `omega`.

**Remaining**:
- `verifiedGenInstr_output_pos`: case analysis on all 19 TAC constructors under full `GenAsmSpec` typing/layout invariants. The `.copy dst src` arm is the hardest (freg-src subcase needs `WellTypedLayout` + `VarLayoutInjective` to rule out vStoreVarFP's `r' == r` elision; non-freg-src subcase needs `RegConventionSafe.not_x0` + layout completeness to rule out vLoadVar returning `[]` at scratch `.x0`). ~115 LOC when fully written out.
- `bodyPerPCLengthPos` field on `GenAsmSpec`: dispatches to `verifiedGenInstr_output_pos` (normal case), `spec.callSiteSaveRestore` (lib-call: baseInstrs is `verifiedGenInstr` of `.floatUnary`/`.fbinop .fpow`/`.printInt/B/F/S`, all non-empty), or `spec.printSaveRestore` (print case trivially has `[.printCall _]`). ~30 LOC.
- Divergence theorem itself: The key hurdle (discovered during initial implementation) is that **step-count positivity needs structural tracking, not just static length**. Given `bodyPerPCLengthPos`, proving `step_simulation` produces `ArmStepsN` with `k ≥ 1` requires either (a) refactoring `step_simulation` to track step count at each internal case, or (b) post-hoc extraction combined with case-by-case arguments that rule out `ArmSteps.refl`. Case (b) fails cleanly for `.goto pc` self-loops where `s = s'` is state-level, even though the ARM trace executes `.b pcMap(pc)` (one step). So (a) appears necessary — approximately ~200 LOC refactor of `step_simulation` or a parallel `step_simulation_countN`. Deferred to follow-up session.

The expected proof shape: chain `tacToArm_correctness` through prefixes of the infinite TAC trace to obtain `∀ N, ∃ s k, ArmStepsN init s k ∧ ExtSimRel (f N) s`, then argue `k` grows unboundedly with `N`. Not on the critical path for Phase 7 if the backward theorems can locally build the needed "source diverges → ARM reaches arbitrary length" argument from `tacToArm_correctness` + pc-determinism — a design decision for Phase 7.

**New theorem**: `while_to_arm_divergence_preservation` strengthened to also conclude `ArmDiverges r.bodyFlat initState`.

**Hard proof**: TAC divergence → ARM divergence. Given `IsInfiniteExec p f`, build `g : Nat → ArmState` with `ArmStep` between consecutive.
- Each TAC step `Step p (f n) (f (n+1))` gives ARM `s'` with `ArmSteps s s'` via `step_simulation`.
- Concatenate into one ARM trace. One TAC step ↦ k ARM steps where k = `instrLength(pc_n)` ≥ 1 (deterministic per TAC instruction; havoc affects register values, not step counts).
- Use `Classical.choose` + `Nat.rec` to build infinite sequence. Standard König-style — same pattern as `has_behavior` at [PropChecker.lean:581](CredibleCompilation/PropChecker.lean#L581).
- Non-determinism from `bl _printf` havoc: ArmStep isn't deterministic, so the built trace is one specific path, not canonical. Fine for existence.

**Pre-Phase-5 derisk probes (2026-04-21)**:
- **Probe A (step counts)**: Confirmed every live TAC instruction emits ≥1 ARM instruction, *after* the self-copy fix (commit `5870a78`, 2026-04-21) landed. Without that fix, `.copy x x` with freg-resident x produced 0 instructions via `vStoreVarFP`'s `r == tmp` elision, breaking the König argument.
- **Probe B (IsInfiniteExec shape)**: Clean — `(∃ σ₀ am₀, f 0 = .run 0 σ₀ am₀) ∧ ∀ n, p ⊩ f n ⟶ f (n+1)` at [PropChecker.lean:110](CredibleCompilation/PropChecker.lean#L110). Direct analog for `ArmDiverges`.
- **Probe C (König template)**: `has_behavior` already executes the exact planned pattern (classify-by-n → `Classical.choose` → reconstruct via `StepsN_split_last` + determinism). Copy-adapt, don't reinvent.
- **Probe D (ArmStepsN)**: Missing. Phase 5 opens with defining `ArmStepsN` + porting ~6 utilities (`_det`, `_extend`, `_split_last`, `_compose`, `Steps_to_StepsN`) from the TAC versions. ~0.5 day of mechanical work.
- **Probe E (havoc variability)**: Not a risk. Libcall/printcall havoc register values but the ARM instruction count per TAC step is a deterministic function (`instrLength layout arrayDecls safe instr varMap`). Index bijection is `ARM_index(TAC_step_n) = pcMap(pc_n)`.

**Risk**: **LOW** (downgraded from HIGH after derisk probes + self-copy fix). All three flagged concerns (variable-k bijection, havoc-driven existentials, König scaffolding) resolved favorably. **Effort**: 2–3 days (was 3–5). Breakdown: ~0.5 day for ArmStepsN utilities, ~0.5 day for step_simulation → ArmStepsN converter, ~1 day for divergence theorem via has_behavior template. **Checkpoint**: 0 sorrys.

### Phase 6 — ARM behavior totality / exhaustion

**Files**: new section in `CredibleCompilation/PipelineCorrectness.lean`.

**New theorem**:
```lean
theorem arm_behavior_exhaustive :
    (∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.haltFinal) ∨
    (∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.divS) ∨
    (∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.boundsS) ∨
    ArmDiverges r.bodyFlat init
```

**Proof strategy**: analogous to `has_behavior` in PropChecker.lean:574. For each n, either ARM reached a sentinel by step n, or still running. If always still running, construct divergence witness via same König pattern as Phase 5.

**Key lemma**: ARM is stuck-free on any reachable state with pc < bodyFlat.size. Strengthens `GenAsmSpec`: "for every pc < bodyFlat.size, ArmStep has a successor AND the successor's pc ∈ {< bodyFlat.size, haltFinal, divS, boundsS}". Defended by existing branch-target checker but needs hoisting to ARM level.

**Risk**: Medium (downgraded from HIGH after probe). Probe confirmed every ArmStep rule's only precondition is `prog[s.pc]? = some instr` — no state-dependent hypotheses. The per-constructor case analysis is nearly trivial: each constructor trivially produces a successor. Real work is composing that into a reachability-preserving invariant. **Effort**: 2–3 days (was 4–6; downsized after probe).

### Phase 7 — The five backward theorems

**Files**: `CredibleCompilation/PipelineCorrectness.lean`.

**Statements** (abbreviated):
1. `arm_halts_implies_while_halts`: ArmSteps init s ∧ s.pc = haltFinal ⇒ source halts with matching observables + arrayMem.
2. `arm_div_implies_while_unsafe_div`: s.pc = divS ⇒ ∃ fuel, unsafeDiv.
3. `arm_bounds_implies_while_unsafe_bounds`: s.pc = boundsS ⇒ ∃ fuel, unsafeBounds.
4. `arm_diverges_implies_while_diverges`: ArmDiverges ⇒ ∀ fuel, interp = none.
5. (Already in Phase 6) `arm_behavior_exhaustive`.

**Proof schema**: Phase 6 (some ARM behavior exists) + Phase 4/5 (forward in other three directions) + sentinel distinctness. Suppose ARM lands in bin X. Source can only be in {halts, unsafeDiv, unsafeBounds, diverges}. Forward sim sends each to a specific ARM bin. If source were in bin ≠ X, ARM would land in a different sentinel — contradiction. So source is in matching bin.

Critical sub-step: ARM sentinels distinct and terminal. Since haltFinal = bodyFlat.size, divS = +1, boundsS = +2, they're pairwise distinct and none has outgoing ArmStep.

**Risk**: Medium. Each theorem ~30 lines given tight forward side. Intellectual work is in 5/6. **Effort**: 2–3 days. **Checkpoint**: final 0 sorrys.

## Critical path

```
Phase 1 ──┐                           ┌─→ Phase 4 ─┐
          ├─→ Phase 3 ─────────────── │            │
Phase 2a ─┤                           │            ├─→ Phase 7
          └─→ Phase 2b ───────────────┤            │
                                      └─→ Phase 6 ─┤
                                                   │
            Phase 5 ────────────────────────────────┘
```

- Phases 1 and 2a independent; both done.
- Phase 3 needs Phase 1 (unsafe predicates); done.
- Phase 4 needs Phase 3 (Cfg.error split) **AND Phase 2b** (haltFinal must be an actually-reachable ARM PC before `while_to_arm_correctness` can conclude `s'.pc = r.haltFinal`).
- Phase 5 needs Phase 3 (tightened ExtSimRel).
- Phase 6 needs Phase 2b (ARM totality argument uses `haltFinal = bodyFlat.size` as the clean-halt sentinel, and `divS`/`boundsS` as the off-the-end stuck sentinels — all now in place as real PCs).
- Phase 7 needs 4, 5, 6.

## Risks and unknowns

1. **Phase 5 coinductive divergence (highest)**: TAC→ARM divergence construction via Classical.choose. Fiddly arithmetic around variable ARM step lengths per TAC step + nondeterministic printf havoc.
2. **Phase 6 ARM totality**: requires new explicit "ARM bodyFlat is stuck-free inside bounds" invariant. Currently implicit. May need dedicated lemma `ArmStep_total_of_codeAt : ∀ s, CodeAt bodyFlat s.pc [i] → ∃ s', ArmStep bodyFlat s s'` by case analysis on ArmInstr. **Now includes the halt-save block** (str/fstr instructions, trivially stuck-free).
3. **Phase 3 Cfg.error split**: widespread mechanical churn; risk of missing a case in ErrorHandling. — retired (Phase 3 done).
4. **Pseudo-instructions**: haltSaveBlock is flat str/fstr sequence, no branches — confirmed by Phase 2a.
5. **Libcall havoc in divergence construction**: ARM nondeterministic at libcall sites; built sequence is one path. Existence suffices.
6. **Phase 2b ExtStateRel preservation**: the halt-save block writes to `stack[lookupVar varMap v]` for each ireg/freg observable. Preservation requires both `varMap` offset-injectivity and the invariant that any stack-layout variable's offset comes from `varMap`. Both hold by `buildVarLayout`/`buildVarMap` construction, but require new `GenAsmSpec` clauses to expose.

## Checkpoints (0 sorrys expected)

- ✅ After Phase 1 (new predicates, dormant) — 2026-04-21
- ✅ After Phase 2a (bodyFlat layout rework infrastructure) — 2026-04-21
- ✅ After Phase 2b (halt-case steps through save block) — 2026-04-21
- ✅ After Phase 3 (Cfg.error split) — 2026-04-21
- ✅ After Phase 4 (forward theorems distinguish causes; name haltFinal) — 2026-04-21 (commit `915c019`)
- ✅ Pre-Phase-5 prerequisite: self-copy nop emission — 2026-04-21 (commit `5870a78`)
- ✅ After Phase 5a (ArmStepsN + ArmDiverges in reachability form) — 2026-04-21
- After Phase 5b (forward divergence theorem) — deferred indefinitely; not on Phase 6/7 critical path
- Phase 6/7 infrastructure partial (Path B, 2026-04-22): `sentinel_stuck`, feeder lemmas (`pcMap_le_haltS`, `checkBranchTargets_to_labels_in_bounds`), `applyPassesPure_preserves_stepClosedInBounds`, `pipelined_has_behavior`, `pipelined_no_typeError`, sentinel distinctness, P2 probe (`arm_step_pc_det` via `armNextPC` projection), P3 probe (`type_safety` fit confirmed), P1 probe attempted (needs restructuring). 9 sorrys remain.
- Phase 6/7 derisk probe session 2 (2026-04-22): PD1/PD2 validated opaque havoc + projection trick; PE1/PE2/PE3 validated call-site refactor and .ifgoto pattern; PF1'/PF2' validated Fix B' (self-loop ArmDiverges); PF3 confirmed step_count_pc_uniqueness requires the pivot. **Final plan: pivot + Fix B' per [`plans/phase6-7-NEXT-SESSION.md`](phase6-7-NEXT-SESSION.md).**
- After Phase 7 pivot + Fix B' — next session target, ~980 LOC, 9 → 3 sorrys
- After Phase 6 exhaustion — separate session, ~700 LOC, 3 → 0 sorrys

## Effort estimate (post-probe, post-Phase-4)

| Phase | Days | Status |
|---|---|---|
| 1 | 1–2 | ✅ Done |
| 2a | ~1 | ✅ Done (less than est. due to clean refactor) |
| 2b | ~1 | ✅ Done (under est.; ExtSimRel tightening deferred to Phase 4) |
| 3 | 1–2 | ✅ Done |
| 4 | 3 | ✅ Done (+ BoundsOpt elision re-enabled via separate BoundsOptCert plan) |
| 5 | 2–3 | Risk downgraded HIGH→LOW after derisk probes + self-copy fix |
| 6 | 2–3 | Unchanged |
| 7 | 2–3 | Unchanged |

**Remaining**: 6–9 days (~1.5–2 weeks solo). 80% band: 7–8 days. Risk buffer for Phase 5 shrunk from 2–3 days to <1 day after probes.

Phase 2a came in under estimate (1 session instead of 3–4 days) because: (i) `haltS`/`divS`/`boundsS` as fields (not defs) kept downstream disruption to zero; (ii) `CodeAt.liftToSuffix` made the bodyFlat extension mechanical; (iii) the `verifiedGenInstr_length_params_ind` lemma, though fiddly, was inherited from the existing `_pcMap_ind` structure.

Phase 2b came in at the low end of estimate (1 session, under the 1–2 day band) because: (i) the Phase 2a infrastructure (`CodeAt.liftToSuffix`, `codeAt_of_bodyFlat'`, the five spec clauses anchoring `haltS`/`haltFinal`/`divS`/`boundsS`/`haltSaveBlock_eq`/`haltSaveComplete`) was pre-positioned precisely for the induction in `armSteps_haltSaveBlock`; (ii) deferring the `ExtSimRel` halt tightening to Phase 4 avoided a ~10-site churn across downstream `ExtSimRel (.halt _)` consumers.

## Critical files

- [PipelineCorrectness.lean](CredibleCompilation/PipelineCorrectness.lean)
- [CodeGen.lean](CredibleCompilation/CodeGen.lean)
- [ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean)
- [ArmCorrectness.lean](CredibleCompilation/ArmCorrectness.lean)
- [RefCompiler/ErrorHandling.lean](CredibleCompilation/RefCompiler/ErrorHandling.lean)
- [CompilerCorrectness.lean](CredibleCompilation/CompilerCorrectness.lean)
- [TAC.lean](CredibleCompilation/TAC.lean)

## Out of scope

- typeError case (ruled out by `whileToTAC_refinement` for well-typed programs)
- Verified label resolution (`.Lhalt` → PC via assembler stays unverified)
- Verified div-by-zero / bounds error handler code (stays unverified in wrapper)
- Verified epilogue (callee-save restore, sp restore, ret — still unverified)
- Proc/function calls (separate future work)
