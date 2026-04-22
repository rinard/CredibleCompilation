# CredibleCompilation — Development Log

Chronological record of what was built and why, to reconstruct the sequence of decisions.

---

## Phase 6/7 session 3: Phase A + Phase B partial, Phase 7d closed (2026-04-23)

**Goal**: execute the pivot + Fix B' plan written at the end of session 2
(plans/phase6-7-NEXT-SESSION.md).  Target: 9 → 3 sorrys.

**Achieved: 9 → 7 sorrys.**  Phase A (pivot) fully landed.  Phase B
partial — Phase 7d closed, but Steps 7–8 (Fix B' composition) deferred
to session 4 where they're actually consumed.

### Phase A — deterministic havoc pivot (commit `d41636e`, ~302 LOC)

- `ArmDefs.lean:208-210`: added opaque `havocRegsFn` / `havocFRegsFn`
  oracles.  Rationale: pre-pivot `ArmStep` took post-libcall register
  contents as existential arguments, making the step relation
  nondeterministic and obstructing state-uniqueness proofs.  The pivot
  makes post-call contents a fixed-but-unknown function of the pre-
  call state.
- `ArmSemantics.lean`: 7 `ArmStep` libcall constructors refactored
  (printCall, callPrintI/B/F/S, callBinF, floatUnaryLibCall) — dropped
  `newRegs`/`newFregs` args; successors now use `havocRegsFn s` /
  `havocFRegsFn s` inline.  6 call sites in `ArmStep_total_of_codeAt`
  updated.
- `ArmCorrectness.lean`: 6 forward-sim call sites updated.  Minimal-
  diff: kept `let newRegs := havocRegsFn s1` / `let newFregs :=
  havocFRegsFn s1` bindings so downstream proofs (havoc preservation
  of ExtStateRel, arrayMem irrelevance) work unchanged.
- `CodeGen.lean`: 7 verifiedGenerateAsm_spec call sites updated.
- `PipelineCorrectness.lean`:
  - Fixed `ArmStep.pc_eq_armNextPC` binder counts for the 7 refactored
    constructors.
  - Added `armStepResult : ArmState → ArmInstr → ArmState` (~85 LOC
    match over all ~53 ArmInstr variants).
  - Added `ArmStep.eq_armStepResult` (full-state projection, ~65 LOC
    `cases` enumeration — scales cleanly from PD2's 5-case probe).
  - Added `arm_step_det` (6 LOC — direct projection + `Option.some.inj`).
  - Added `step_count_state_uniqueness` (15 LOC — direct induction on
    n using `arm_step_det`).  Pre-pivot, this lemma's inductive step
    failed (two intermediate states could have same PC but different
    regs under nondet).  Post-pivot it collapses to 15 LOC.
  - Filled `step_count_pc_uniqueness` sorry as a 2-line `.pc`
    projection corollary.

Order chosen:
1. Add opaque oracles (build still green, 9 sorrys).
2. Refactor `ArmStep` rules (build breaks, 19 call sites become errors).
3. Fix the 19 call sites + pc_eq_armNextPC binders (build green again,
   9 sorrys).
4. Add `armStepResult` / `eq_armStepResult` / `arm_step_det`.
5. Move the block to before `step_count_state_uniqueness` (needed for
   visibility — section ordering).
6. Prove `step_count_state_uniqueness` + close `step_count_pc_
   uniqueness` sorry.

### Phase B partial — Phase 7d closed (commit `8524574`, ~184 LOC)

**`has_behavior_init` wrapper** in [RefCompiler/Refinement.lean](CredibleCompilation/RefCompiler/Refinement.lean)
(~50 LOC): mirrors `has_behavior`'s proof structure but packages
witnesses into `program_behavior_init` (fixing am to `ArrayMem.init`)
instead of `program_behavior` (leaving am existential).  Added in
Refinement.lean rather than PropChecker.lean (which the original plan
suggested) because `program_behavior_init` lives in Refinement.lean
and PropChecker doesn't import it.

**Fix B' primitives** ported from probe files to
[PipelineCorrectness.lean](CredibleCompilation/PipelineCorrectness.lean):
- `arm_self_loop_diverges` (from PF1')
- `arm_diverges_of_prefix_reaches_self_loop` (from PF1')
- `tac_goto_self_loop_implies_arm_self_loop` (from PF2')

**Phase 7d** (`arm_diverges_implies_while_diverges`, ~50 LOC):
- Case on `has_behavior_init` output.
- halts/errors-div/errors-bounds: forward sim gives `ArmSteps init
  s_sent` with `s_sent.pc = sentinel`.  ArmDiverges at length `n + 1`
  (where n = length of forward trace) produces a state reached in
  n+1 steps.  `ArmStepsN_split_last` decomposes: exists s_mid reached
  in n steps + one outgoing ArmStep.  `step_count_state_uniqueness`
  gives s_mid = s_sent, so the outgoing step fires at the sentinel
  PC — but `sentinel_stuck` says no step leaves a sentinel PC.
  Contradiction.
- typeErrors: excluded via `pipelined_no_typeError`.
- diverges: apply `while_to_arm_divergence_preservation` directly.

Key observation that guided session 3's deviation from the plan:
**Phase 7d does not require the Fix B' composition** (Steps 7, 8 of
the plan).  The plan ordered Steps 7, 8 in Phase B because they're
"Fix B' machinery" and Phase B was labeled "Fix B' + Phase 7d", but
7d's proof above uses only state_uniqueness + sentinel_stuck +
while_to_arm_divergence_preservation (for the .diverges source bin,
which has an explicit IsInfiniteExec witness — no need to reconstruct
one from scratch).

Steps 7, 8 are only consumed by Phase C (7a/b/c) where source-
diverges at a non-matching bin must be contradicted by showing ARM
would also diverge (→ sentinel stuck).  Deferred to session 4.

### Plan deviation: Step 7's structural issue

The original plan said "Prove `tac_iftrue_self_loop_implies_arm_self_
loop` — similar to PF2' but navigates `.ifgoto`'s 3-arm be match.  ~60
LOC."

Attempted in session 3 but revealed a **structural issue**:
`.ifgoto be pc` (with `be.eval σ = true`) compiles to a multi-
instruction ARM sequence (evaluate `be` into regs/flags, then a
conditional branch).  The emitted sequence has at least 2 ARM
instructions (usually 4+ for compare-based conditions).  So:

- **`ArmStep r.bodyFlat s s`** (single-step self-loop, the PF2' form)
  is NOT provable for the `.ifgoto` case.  Intermediate ARM states
  after the evaluate-`be` loads/cmp have modified regs/flags; only the
  final branch returns PC to `pcMap pc = s.pc`.

The fix (for session 4): generalize
`arm_diverges_of_prefix_reaches_self_loop` to accept an `ArmSteps s
s'` cycle where `s'.pc = s.pc` but `s' ≠ s`.  Then the forward sim
of a `.ifgoto` TAC self-loop produces this `ArmSteps` cycle directly,
without a dedicated single-step lemma.

This reframing also simplifies Step 8
(`source_diverges_gives_ArmDiverges_init`): it no longer needs to
case-split on whether a given TAC step is a self-loop — every TAC
step produces an `ArmSteps prog s s'` of length ≥ 1 via forward sim,
and the cumulative sequence forms `ArmDiverges` directly.

Documented in plans/phase6-7-NEXT-SESSION.md § Next Session Work Plan
(session 4).

### Current sorry count: 7

Remaining in PipelineCorrectness.lean:

| Sorry | Scope for next session |
|---|---|
| `bodyFlat_branch_target_bounded` (Phase 6) | Out of scope — separate ~600 LOC |
| `arm_behavior_exhaustive` (Phase 6) | Out of scope — ~100 LOC König |
| `halt_state_observables_deterministic` (Phase 7a helper) | Session 4 — ~15 LOC corollary |
| `arm_halts_implies_while_halts` (Phase 7a) | Session 4 — ~80 LOC |
| `arm_div_implies_while_unsafe_div` (Phase 7b) | Session 4 — ~60 LOC |
| `arm_bounds_implies_while_unsafe_bounds` (Phase 7c) | Session 4 — ~60 LOC |
| `verifiedGenInstr_ifgoto_branch_bounded` (P1 probe placeholder) | Out of scope — subsumed by Phase 6 sweep |

Session 4 target: **7 → 3 sorrys** (Phase 7 complete).

### Branch status

- `phase6-prep` on commit `8524574`.
- 11 commits ahead of `main`.
- Pushed to `origin/phase6-prep` (first push in session, set upstream).
- Also merged in during session: unrelated benchmark tuning
  (commit `632b130` — Livermore iteration counts + opt/C2 compare
  harden).

---

## Phase 6/7 probe session 2: Fix B' + pivot validated (2026-04-22)

**Goal**: derisk the pivot plan further before committing to the full
~750 LOC refactor.  Ran 6 additional probes beyond the initial PD1/PD2/PD3
(landed in the prior session).

**New probes** (files in `CCTests/Tests/PivotProbe*.lean`; not imported
in `CCTests.lean`, build individually):

- **PE1** (1-TAC-step ArmStepsN-length, partial): validated the
  cases-on-ArmSteps pattern for halt/error sub-cases (.refl contradicted
  by PC mismatch; .step gives K ≥ 1).  Confirmed BLOCKED for the
  "source diverges" sub-case, since no forward-sim witness has a
  definite sentinel PC there.

- **PE2** (call-site grep): enumerated 19 `ArmStep.X` libcall sites
  across `ArmSemantics.lean` (6), `ArmCorrectness.lean` (6), and
  `CodeGen.lean` (7).  All mechanical-with-ripple (~15 LOC per site);
  no deep rewrites needed.  Revised Step 2 estimate: 150 → 210 LOC.

- **PE3** (.ifgoto v2 inline): rewrote the broken P1 probe without
  helper `have` blocks; used `split at hmem` inline.  Compiled first
  try.  Validates the 14-case sweep pattern and gives a blueprint
  that unblocks the .ifgoto 3-nest case that had stalled previously.

- **PF1'** (arm_self_loop_diverges): trivially proved
  `ArmStep s s → ArmDiverges s` (~10 LOC) and a bonus
  `arm_diverges_of_prefix_reaches_self_loop` (~15 LOC) that lifts via
  ArmSteps prefix.  KEY INSIGHT: works under the CURRENT
  nondeterministic ArmStep model — Fix B' doesn't require the pivot.

- **PF2'** (TAC self-loop → ARM self-loop): `.goto pc` self-loop +
  `GenAsmSpec` + `ExtSimRel.run` ⇒ `ArmStep r.bodyFlat s s` (~55 LOC).
  Proof navigates spec.instrGen, unfolds verifiedGenInstr, uses the
  newly-un-privatized `codeAt_of_bodyFlat'` to lift from bodyPerPC to
  bodyFlat.

- **PF3** (step_count_pc_uniqueness micro-probe, ❌ blocked): direct
  induction stalls at the inductive step because `arm_step_pc_det`
  requires SAME starting state; two traces from init produce
  intermediate states with same PC but potentially different regs
  (havoc divergence).  Confirms step_count_pc_uniqueness for bodyFlat
  under nondeterminism requires ~300+ LOC (per-PC spec structure
  analysis OR uninit-reads abstract interpretation), NOT the ~150 LOC
  initially estimated.

**Final decision**: pivot + Fix B'.  Total budget ~750 LOC for Phase 7.

**Un-privatized** in `CodeGen.lean` (no semantic change):
- `buildPcMap_eq_take_length`
- `codeAt_of_bodyFlat`
- `codeAt_of_bodyFlat'`
- `isLibCallTAC`

**New plan docs**:
- [`plans/phase6-7-NEXT-SESSION.md`](plans/phase6-7-NEXT-SESSION.md) —
  final authoritative plan + handoff for next session.
  **Read this first.**
- [`plans/phase6-7-pivot-probe-findings.md`](plans/phase6-7-pivot-probe-findings.md) —
  PD1/PD2/PD3 detailed findings (from prior session).
- [`plans/phase6-7-deterministic-pivot-plan.md`](plans/phase6-7-deterministic-pivot-plan.md) —
  older pivot-only plan, superseded header added.

**Status**: 9 sorrys unchanged (none closed this session; all probe-only
work).  Full `lake build` green.  Branch `phase6-prep` has 8 commits
ahead of `main`.

**Commits**:
- `63e88d3` — Path B infrastructure (prior session, sentinel_stuck,
  feeder lemmas, pipelined helpers)
- `eb899b9` — Session report (process narrative)
- `ec91423` — Original pivot plan (now superseded)
- `75a47f8` — PD1/PD2/PD3 probes + findings
- `0732a55` — PE1/PE2/PE3 probes
- `166f873` — PF1'/PF2' probes + un-privatizations
- `4094678` — PF3 micro-probe confirming step_count_pc_uniqueness
  is pivot-dependent

Next session picks up with Phase A (pivot) per NEXT-SESSION.md.

---

## Phase 6 Path B: infrastructure + 2 validated probes (2026-04-22)

**Goal:** Land Phase 6/7 infrastructure that reliably compiles (feeder lemmas, pipelined helpers, sentinel lemmas) + validate two derisk probes for the remaining heavy work (14-case `bodyFlat_branch_target_bounded` sweep and `step_count_pc_uniqueness`).

**Shipped** (all in [PipelineCorrectness.lean](CredibleCompilation/PipelineCorrectness.lean)):

- **`sentinel_stuck`** (§ 8 Phase6Skeleton): sentinel PC implies `bodyFlat[pc]? = none`, invokes `ArmStep_stuck_of_none`. Uses the `bodyFlat.size = haltFinal` rewrite via `spec.haltFinal_eq` + `spec.haltS_eq`.
- **`pcMap_le_haltS`** (§ 8): every live TAC PC `l ≤ p.size` has `r.pcMap l ≤ r.haltS`. Uses the newly un-privatized `buildPcMap_eq_take_length` (CodeGen.lean:3532).
- **`checkBranchTargets_to_labels_in_bounds`** (§ 8): bridge from `checkBranchTargets p.code = none` to `∀ pc < p.size, ∀ l, p[pc] = .goto l ∨ ∃ be, p[pc] = .ifgoto be l → l < p.size`.
- **`haltFinal_ne_divS`, `haltFinal_ne_boundsS`, `divS_ne_boundsS`** (§ 8): sentinel distinctness, trivial by `omega` over spec equalities.
- **`stepClosed_of_checkCertificateExec`** (§ 9): extracts `checkStepClosed cert.trans = true` from `checkCertificateExec cert = true` (condition 6).
- **`applyPass_preserves_stepClosedInBounds`, `applyPassesPure_preserves_stepClosedInBounds`** (§ 9): Prop-form `StepClosedInBounds` preservation through certificate-checked passes. Parallel to the existing 4-invariant preservation.
- **`pipelined_has_behavior`** (§ 9): `has_behavior` at the pipelined TAC level. Thin wrapper over `applyPassesPure_preserves_stepClosedInBounds` + existing `has_behavior`.
- **`pipelined_no_typeError`** (§ 9): pipelined TAC never reaches `Cfg.typeError`. Uses existing `type_safety` in TypeSystem.lean (confirmed shape via P3 probe).

**Probe P2 — validated** (§ 10b Phase6Probes2):
- **`armNextPC`** helper + **`ArmStep.pc_eq_armNextPC`** projection theorem: every `ArmStep prog s s'` has `s'.pc = armNextPC s i` where `i` is the instruction at `s.pc`. Enumerates all ~50 `ArmStep` constructors, maps each to a pure function of `(s, instr)`. Havoc rules (printCall, callBinF, etc.) advance `pc` by 1 regardless of havoc outcomes (via `ArmState.havocCallerSaved_pc` simp lemma).
- **`arm_step_pc_det`**: PC determinism for two `ArmStep`s from the same state. Uses the projection — sidesteps the 50×50 `cases`-explosion that timed out.

**Probe P1 — partial, deferred**:
- Helpers `formalLoadImm64_no_branches`, `vLoadVarFP_no_branches`, `verifiedGenBoolExpr_no_branches` landed and reusable.
- `verifiedGenInstr_ifgoto_branch_bounded` attempted; proof structure sound but Lean's elaborator trips on nested-match type signatures inside `have loadA_nb / loadB_nb`. Fix requires inlining the load analysis (no helpers) or flattening the helper type. Deferred to the 14-case sweep session. Commented-out attempt preserved in the file for reference.

**Probe P3 — validated**: `type_safety` in [TypeSystem.lean:560](CredibleCompilation/TypeSystem.lean#L560) matches the shape `pipelined_no_typeError` needs exactly; no adapter lemma required.

**Status**: full `lake build` green; 9 sorrys remain (down from 11 baseline, net −2 after adding P1 placeholder). 3137 jobs. Touched files: [PipelineCorrectness.lean](CredibleCompilation/PipelineCorrectness.lean) (+≈600 LOC landed, +≈260 LOC P1 attempt commented), [CodeGen.lean](CredibleCompilation/CodeGen.lean) (buildPcMap_eq_take_length un-privatized).

**Risks realized & deferred**:
- **`step_count_pc_uniqueness`**: design doc estimated ~80 LOC; analysis shows it's spec-dependent — in generic ARM, havoc followed by cbz/cbnz/bCond on a havoc'd register can produce different next PCs in different traces. Proving the "no branch reads havoc'd reg" invariant for `r.bodyFlat` requires traversing `bodyPerPC` via spec, ~200+ LOC. Deferred.
- **`.ifgoto` branch-target-bounded**: proof pattern works but helper type-signature elaboration is fiddly. Fix is ~30 min of inline rewrite.

**Remaining for next session**: the 14-case `verifiedGenInstr_branch_target_bounded` sweep (~400 LOC; `.binop` and `.goto` already done as probes, `.ifgoto` attempted), `bodyFlat_branch_target_bounded` lift (~55 LOC), `step_count_pc_uniqueness` (spec-dependent, ~200 LOC), `arm_behavior_exhaustive` (~100 LOC), Phase 7a/b/c/d (~240 LOC + ~100 LOC observable-determinism helper).

---

## Phase 5b: bodyPerPC_length_pos theorem (2026-04-22)

**Goal:** Piece 1 of 4 remaining Phase 5b deliverables — prove every live TAC PC's ARM block has ≥ 1 instruction. Consumed by the upcoming `step_simulation` refactor to extract a positive ARM step count per TAC step.

**Shipped**:

- **`verifiedGenInstr_output_pos`** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean) § 8d′): unified dispatcher over all 19 TAC constructors. `.print` is vacuous (returns `none`, contradicted by hGen); the other 18 delegate to the per-constructor `verifiedGenInstr_<ctor>_output_pos` lemmas. Also removed `private` from those lemmas + `formalLoadImm64_length_pos` so downstream modules can use them.
- **`bodyPerPC_length_pos`** ([CodeGen.lean](CredibleCompilation/CodeGen.lean) before `verifiedGenerateAsm_spec`): `GenAsmSpec tyCtx p r → ∀ pc (hpc : pc < p.size), 1 ≤ (r.bodyPerPC[pc]).length`. Three-case split:
  - **print** (`spec.printSaveRestore`): output = saves ++ `[.printCall _]` ++ restores → trailing `.printCall` gives ≥ 1.
  - **lib-call** (`spec.callSiteSaveRestore`): output = saves ++ baseInstrs ++ restores, baseInstrs from `verifiedGenInstr` → apply `verifiedGenInstr_output_pos`.
  - **normal** (`spec.instrGen`): output directly from `verifiedGenInstr` → apply `verifiedGenInstr_output_pos`.

**Design choice**: `bodyPerPC_length_pos` is a standalone theorem, not a `GenAsmSpec` structure field. Since it's derivable from the existing spec fields (plus the output_pos suite), making it a theorem avoids re-proving it inside `verifiedGenerateAsm_spec` and is easier to evolve.

**Status**: 0 sorrys; full `lake build` green (3137 jobs). Files touched: 2 Lean files, +132 LOC (78 in ArmSemantics, 39 in CodeGen, net new; minus 18 `private` keywords removed).

**Remaining for Phase 5b** (deferred to a later session with a fresh context):
- `step_simulation` refactor to return `ArmStepsN _ _ _ (k+1)` (~150 LOC, 60% confidence — the main Phase 5b risk).
- `tacToArm_refinement` threading the step count through induction (~30 LOC).
- `while_to_arm_divergence_preservation` divergence theorem (~30 LOC).

---

## Phase 5b: all remaining verifiedGenInstr_<ctor>_output_pos lemmas (2026-04-22, same session)

**Goal:** Complete the per-constructor output_pos lemmas needed to discharge `bodyPerPCLengthPos` (Phase 5b spec field) — covering every TAC constructor produced by `verifiedGenInstr`'s verified path. Extends the `split at hGen` pattern from `.binop`/`.boolop`/`.ifgoto`.

**Shipped** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean) § 8d′):

- **`formalLoadImm64_length_pos`**: helper — `formalLoadImm64 rd n` emits ≥ 1 instruction (either `[.mov]` or a `movz`-led 1–4 sequence).
- **`verifiedGenInstr_const_output_pos`**: three Value sub-cases (`.int`/`.bool`/`.float`). The int arm uses `formalLoadImm64_length_pos`; bool/float use the `.mov`/`.fmovToFP` witness tokens.
- **`verifiedGenInstr_goto_output_pos`** / **`_halt_output_pos`**: trivial `subst hGen; simp`, output is `[.b _]`.
- **`verifiedGenInstr_arrLoad_output_pos`** / **`_arrStore_output_pos`**: the `[.arrLd]` / `[.arrSt]` / `[.farrLd]` / `[.farrSt]` middle token provides ≥ 1 uniformly across `ty` sub-cases.
- **`verifiedGenInstr_fbinop_output_pos`**: 3-way layout match (ireg-exclusion); `[fpInstr]` in the default arm. Dropped the `cases fop` step — the match returns a single `ArmInstr` and `:: vStoreVarFP` makes it a cons, so `List.length_cons` + `omega` closes without enumerating the binop.
- **`verifiedGenInstr_intToFloat_output_pos`** / **`_floatToInt_output_pos`** / **`_floatUnary_output_pos`**: 2-way layout matches.
- **`verifiedGenInstr_fternop_output_pos`**: 4-way layout match.
- **`verifiedGenInstr_printInt_output_pos`** / **`_printBool_output_pos`** / **`_printFloat_output_pos`**: 1-way layout match with `[.callPrintI]` / `[.callPrintB]` / `[.callPrintF]` trailing token.
- **`verifiedGenInstr_printString_output_pos`**: layout-independent; emits exactly `[.callPrintS lit]`.

**Refined pattern** (applied to all of the above):

```
  simp [verifiedGenInstr, hRCb, hIIb] at hGen
  split at hGen <;> first
    | (subst hGen
       simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    | (rcases hGen with ⟨_, rfl⟩
       simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    | simp at hGen
```

**Key lesson (corrects the `.boolop`/`.ifgoto` entry above)**: the `first` alternative ordering matters. `simp at hGen` must be LAST, not first — in the success arm, simp rewrites `some X = some Y` to `X = Y` *without closing*, causing `first` to greedily pick it and leave the goal open. Putting `subst hGen` / `rcases hGen with ⟨_, rfl⟩` first ensures they're tried before simp, and simp is the fallback for failure arms (`none = some _` → `False` → closes). When hGen's shape after simp is a conjunction (e.g., `.arrStore`'s `if`-guarded body), `rcases hGen with ⟨_, rfl⟩` strips the ignored Bool condition and substitutes the equation. `.const` was an earlier casualty of this ordering — its `first` initially had simp first, causing "simp made no progress" in the success arm.

**Status**: 0 sorrys; full `lake build` green (3137 jobs). Files touched: 1 Lean file, +474 LOC. All 18 verifiedGenInstr non-`.print` constructors now have output_pos lemmas. The `.print` constructor returns `none` (handled by unverified codegen), so no lemma needed.

**Remaining for Phase 5b**: `bodyPerPCLengthPos` GenAsmSpec field + discharge (~30 LOC), `step_simulation` ArmStepsN refactor (~150 LOC, main risk), `tacToArm_refinement` threading + divergence theorem (~60 LOC). Total ~240 LOC.

---

## Phase 5b: collapsed output_pos lemmas (.binop, .boolop, .ifgoto) via `split at hGen` (2026-04-22)

**Goal:** Investigate whether a Lean 4 tactic macro could collapse the 27-way `cases layout lv / layout rv / layout dst + freg-contradiction` pattern in `verifiedGenInstr_binop_output_pos` (312 LOC hand-unrolled). Target: ≤ 80 LOC.

**Finding**: no custom macro needed — `split at hGen` already does it. Applied to `match layout lv, layout rv, layout dst with`, it enumerates the four *coverage arms* (three freg-failure → `none`, one default) in one tactic call, rather than the 4³ = 64 layout combinations the old `cases hL : layout x with | none | some ...` peeling produced. `first | simp at hGen | (split at hGen <;> ...)` dispatches.

**Shipped** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean) § 8d′):

- **`verifiedGenInstr_binop_output_pos`**: collapsed from 312 LOC → 36 LOC (15 proof body). Supersedes the hand-unrolled form from 7d77343.
- **`verifiedGenInstr_boolop_output_pos`**: 36 LOC. `cases be.hasSimpleOps` for the outer guard, then inner `split at hGen` on the `notFreg` guard; `verifiedGenBoolExpr_length_pos` + `omega` for the success arm.
- **`verifiedGenInstr_ifgoto_output_pos`**: 43 LOC. Three match arms (fused `.not (.cmp ...)`, fused `.not (.fcmp ...)`, fallback) all close uniformly under `split at hGen <;> (obtain rfl := ...; simp only; omega)` — the trailing `[cmp; bCond]` / `[cbnz]` suffix provides the ≥ 1 witness.

**Key enabling conditions** (a.k.a. the P2 pitfall reaffirmed):
1. Pre-extract `hRCb : layout.regConventionSafe = true` and `hIIb : layout.isInjective = true` from hGen. Without these, `simp [verifiedGenInstr]` produces a conjunction `(cond ∧ cond) ∧ ...` rather than a clean match equation.
2. Use full `simp [verifiedGenInstr, hRCb, hIIb] at hGen` (not `simp only`) so the `!true || !true = false` reduction fires.

**Why not `.copy`**: its 143-LOC proof needs per-case positivity helpers (`vLoadVar_length_pos_of_not_freg`, `vStoreVarFP` freg-r'≠r injectivity) that `split at hGen` can't synthesize. Left unchanged.

**Status**: 0 sorrys; full `lake build` green. Full build: 3137 jobs ok. Files touched: 1 Lean file (-276 / +95 net LOC — 312-LOC theorem replaced, 79 LOC of new theorems added). Plus design note update.

---

## Phase 5b side-lemma: verifiedGenBoolExpr_length_pos (2026-04-21)

**Goal:** First slice of Phase 5b (plans/backward-jumping-octopus.md). Establishes the static positivity of verified boolean-expression codegen — one of three infrastructure lemmas feeding the eventual `bodyPerPCLengthPos` spec field (every live TAC PC emits ≥ 1 ARM instruction) required by the Phase 5b forward-divergence theorem.

**Shipped** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean) § 8d′):

- **`verifiedGenBoolExpr_length_pos`**: under `be.hasSimpleOps = true`, `(verifiedGenBoolExpr layout be).length ≥ 1`. Five structural cases (`.lit`, `.bvar`, `.cmp`, `.not`, `.fcmp`) discharge by `simp only [verifiedGenBoolExpr, List.length_append, List.length_cons, List.length_nil]` + `omega`. The `.bexpr` arm is dispatched by unfolding `BoolExpr.hasSimpleOps` at the hypothesis — it reduces any `.bexpr` to `false`, contradicting the `= true` hypothesis.

**Why only this slice, not the full Phase 5b**: initial implementation attempted the full three-lemma infrastructure plus divergence theorem in a single pass. `verifiedGenInstr_output_pos` (the 19-constructor version) requires delicate hypothesis plumbing (`RegConventionSafe`, `VarLayoutInjective`, `WellTypedLayout`, `WellTypedInstr`, layout-completeness) with `.copy` freg/non-freg subcase splits that don't reduce cleanly under `split at hGen` + `simp`. More importantly, the plan's proposed divergence-theorem proof strategy ("chain `tacToArm_refinement` through n TAC steps, convert `ArmSteps → ArmStepsN`, show `k ≥ n` from `bodyPerPCLengthPos + pcMapLengths`") has a subtle gap: `bodyPerPCLengthPos` is a *static* length claim, but showing `ArmSteps s s'` (from `step_simulation`) has `k ≥ 1` step post-hoc requires ruling out `ArmSteps.refl`, which PC-based arguments cover in all cases *except* `.goto pc` self-loops (where `s = s'` is legitimately state-level). Fixing this needs either a `step_simulation` refactor to produce `ArmStepsN` with explicit step count, or manual per-case reconstruction — either way, substantially more than 160 LOC. Scoped this commit to the one piece that stands alone and is uncontroversial.

**Remaining for Phase 5b** (see plan notes):
- `verifiedGenInstr_output_pos` — 19-constructor case analysis under full spec invariants. ~115 LOC.
- `bodyPerPCLengthPos` spec field on `GenAsmSpec` + discharge. ~30 LOC.
- Divergence theorem itself — requires `step_simulation`-level step-count tracking. ~200 LOC refactor.

**Status**: 0 sorrys; full `lake build` green. Files touched: 1. Net: +27 / -0.

---

## Phase 5a: ArmStepsN infrastructure + ArmDiverges predicate (2026-04-21)

**Goal:** Phase 5a of plans/backward-jumping-octopus.md — define the counted multi-step ARM closure and the ARM divergence predicate that Phase 7's backward theorems will consume. Leaves Phase 5b (the forward theorem `while_to_arm_divergence_preservation`) for a follow-up.

**Shipped** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean)):

- **`ArmStepsN prog s s' n`** — counted multi-step closure of `ArmStep`, parallel to `StepsN` on the TAC side. `| 0 => s = s'`, `| n+1 => ∃ s'', ArmStep prog s s'' ∧ ArmStepsN prog s'' s' n`.
- **Six utility lemmas**: `ArmStepsN_extend`, `ArmStepsN_split_last`, `ArmStepsN_trans`, `ArmStepsN_prefix`, `ArmSteps_to_ArmStepsN` (plus the `refl` case in the definition). Each is a mechanical induction mirroring the existing `StepsN_*` ported from PropChecker.lean. No `_det` — ARM is not deterministic (havoc at libcall/printcall sites), and the backward arguments don't need it.
- **`ArmDiverges (prog) (s₀)`** — defined in **reachability form**: `∀ n, ∃ s, ArmStepsN prog s₀ s n`.

**Scope decision: reachability form over exists-function form.** The plan originally targeted `∃ f : Nat → ArmState, f 0 = s₀ ∧ ∀ n, ArmStep prog (f n) (f (n+1))`, strictly stronger in general nondeterministic systems (König's lemma needs finite branching). But in ARM, PC is deterministic — `ArmStep`'s non-determinism at libcall/printcall affects only caller-saved register values, not PC — so the canonical PC sequence is unique and any length-`n` `ArmStepsN` witness has the canonical PC at step `n`. Both forms discharge Phase 7 equivalently: if source halts, ARM's canonical PC reaches `haltFinal` (stuck) at step `M`, and `ArmStepsN_split_last` on any alleged length-`(M+1)` reach forces a predecessor at `haltFinal` with no successor — contradiction. The reachability form is cheaper to prove forward (saves ~200 LOC of `verifiedGenInstr_output_pos` + DC-style construction) and equally usable backward.

**Status**: 0 sorrys; full `lake build` green. Files touched: 1. Net: +64 / −0.

**What's left of Phase 5**:
- **Phase 5b (pending)**: `while_to_arm_divergence_preservation` producing `ArmDiverges r.bodyFlat init` from `IsInfiniteExec p f`. The proof requires chaining `tacToArm_correctness` through TAC-trace prefixes and showing cumulative ARM step count grows unboundedly — which needs `bodyPerPC[pc].length ≥ 1` for every live `pc`. This `verifiedGenInstr_output_pos` lemma requires case analysis on all ~19 TAC constructors under the full `GenAsmSpec` typing/layout invariants. Not on the critical path if Phase 7 can build the equivalent argument locally from `tacToArm_correctness` + PC-determinism — design decision deferred to Phase 7.

---

## Self-copy nop emission (Phase 5 prerequisite) (2026-04-21)

**Goal:** Guarantee that every live TAC step produces ≥1 ARM step. Needed for Phase 5's divergence argument (plans/backward-jumping-octopus.md): if some live TAC step could produce 0 ARM instructions, an infinite TAC trace wouldn't yield an infinite ARM trace.

**Problem:** The `r == tmp` optimization inside `vStoreVarFP` elides the fmov when the destination freg equals the source freg. Under `layout.isInjective`, this only fires for `.copy x x` where `layout x = some (.freg _)`. Without PeepholeOpt, such self-copies survive into codegen and produce `verifiedGenInstr ... = some []` — a 0-instruction output for a live TAC step.

**Fix:** [ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean) — `verifiedGenInstr .copy dst src` now checks `dst == src` at the top. On self-copy it emits `[.movR .x0 .x0]` (a scratch-register write, semantically a no-op since `.x0` is excluded from the layout by `regConventionSafe`). Non-self-copy falls through to the existing ireg/freg/stack case split unchanged.

**Proof plumbing:**
- [ArmCorrectness.lean](CredibleCompilation/ArmCorrectness.lean): `verifiedGenInstr_correct`'s `.copy` arm wraps the existing logic in `by_cases hxy : x = y`. Self-copy branch: one `ArmStep.movR .x0 .x0`; `ExtStateRel` preserved because `.x0` is scratch (discharged per VarLoc case). The three existing subcases (FP, non-freg→freg, non-freg→non-freg) get `if_neg hxy` added to their `simp` so the new leading `if dst == src` reduces to the else branch.
- [CodeGen.lean](CredibleCompilation/CodeGen.lean): `generateAsm_total`'s `.copy` case wraps in `by_cases hxy`; self-copy branch provides `[.movR .x0 .x0]` as witness; non-self-copy branch unchanged modulo a `hxy_false`-driven `simp only` to reduce the new if.

**Notes:**
- PeepholeOpt already removes self-copies ([PeepholeOpt.lean:34](CredibleCompilation/PeepholeOpt.lean#L34)), so in a standard pipeline the emitted nop is never actually generated. Zero practical overhead.
- Phase 5 can now prove `instrLength ≥ 1` for every live TAC instruction unconditionally (no hypothesis burden on downstream).
- Probes confirmed the other `.refl` arms in step_simulation are either terminal configs (halt, typeError — unreachable in infinite traces) or intermediate sub-lemmas (vLoadVar no-ops inside save/restore machinery that composes with non-refl steps). The self-copy case was the only genuine blocker.

**Status:** 0 sorrys; full `lake build` green. Files touched: 3. Net: +58 / −16.

---

## BoundsOptCert Phase 6: un-wire isBoundsSafe (2026-04-21)

**Goal:** Phase 6 of plans/certified-interval-pangolin.md — un-wire `isBoundsSafe`'s hard `false` so the verified codegen produces real elision decisions driven by the Phase 3 checker. Discharges the Phase-5 oracle from the validated `buildVerifiedInvMap` invariant threaded step-by-step through `tacToArm_refinement`. Re-enables the `boundsSafe = true` path end-to-end.

**Shipped** ([BoundsOptCert.lean](CredibleCompilation/BoundsOptCert.lean), [CodeGen.lean](CredibleCompilation/CodeGen.lean)):

- **Loose checker** ([BoundsOptCert.lean:62](CredibleCompilation/BoundsOptCert.lean#L62), [:195](CredibleCompilation/BoundsOptCert.lean#L195), [:253](CredibleCompilation/BoundsOptCert.lean#L253)):
  - `IMap.satisfies` gated on `validIntervalLoose`: entries whose range fails loose validity are skipped (vacuously satisfied since `IntervalInv.satisfies r bv` requires `0 ≤ r.lo` and fails otherwise). Rules out `irTop`-shaped claims for float vars automatically.
  - `refinesSingle` now returns `true` when the weak entry fails `validIntervalLoose` (skip-invalid-weak), else gates on `validIntervalLoose` of the strong side.
  - `certSuccessor` add/sub arms gate on `validIntervalLoose` (2⁶²) instead of `validInterval` (2³¹). Loop counters widened to iTop = 10¹² fit loose; mul stays at `validIntervalMul` (2¹⁶) since the product needs a tighter per-operand bound.
- **Loose transfer-soundness lemmas** ([:467](CredibleCompilation/BoundsOptCert.lean#L467), [:551](CredibleCompilation/BoundsOptCert.lean#L551), [:564](CredibleCompilation/BoundsOptCert.lean#L564), [:627](CredibleCompilation/BoundsOptCert.lean#L627)):
  - `BitVec64.toNat_add_small` / `_sub_small` generalized from 2³¹ ceiling to 2⁶² (sum stays < 2⁶³ < 2⁶⁴, no wrap).
  - `add_sound`, `sub_sound`, `constInt_sound`, `copy_sound`, `mul_sound`, `refineCond*_sound` (8 leaves + wrapper), `certSuccessor_sound`, `refines_sound`, `imRemove_sound`, `identity_sound`: all target gate changed from `validInterval r = true` to `validIntervalLoose r = true`. `IMap.satisfies` hypotheses updated to pass the loose validity through (extra argument at each `hM v r hMem` call site).
  - `imLookup_mem_of_valid_loose` added alongside the tight `imLookup_mem_of_valid`; `irTop.lo = -10¹² < 0` rules out the fall-through for loose just like for tight.
  - `validIntervalLoose` definitions moved to § 1 so they precede `IMap.satisfies` in § 2 (the concretization predicate now references loose gating).
- **`isBoundsSafe` un-wired** ([CodeGen.lean:486](CredibleCompilation/CodeGen.lean#L486)):
  - Signature gains a `checkerOk : Bool` prefix arg. Returns `true` only when (a) `checkerOk`, (b) `instr` is `.arrLoad`/`.arrStore`, (c) `intervals[pc]` has a `validIntervalLoose` entry for `idx` whose `hi ≤ arraySize arr`, AND (d) `arraySize arr < 2⁶²` (required so `arraySizeBv = BitVec.ofNat 64 arraySize` doesn't wrap and `bv < arraySizeBv` agrees with the Nat comparison).
  - `verifiedBoundsSafe p pc` composes: runs `checkLocalPreservation + checkInvAtStart` to compute `checkerOk` once, then delegates. `verifiedBoundsSafe_rfl` (the old `= false` shortcut) is gone.
  - `bodyGenStep`, `bodyGenStep_push`, `bodyGenStep_none`, `bodyGenStep_length`, `bodyGenStep_preserves_some` all take `checkerOk : Bool` as a new parameter. `verifiedGenerateAsm` computes it once and threads to both the length-pass and the body-pass so they agree on the `safe` value.
- **Invariant threading through `tacToArm_refinement`** ([CodeGen.lean:5904](CredibleCompilation/CodeGen.lean#L5904)):
  - `step_simulation` takes `hInv : buildVerifiedInvMap p pc σ am` as a new hypothesis; used to build the real oracle at the `arrLoad`/`arrStore` arms.
  - `tacToArm_refinement` takes `hInv` at the entry pc and preserves it step-by-step via `spec.invPreserved` at each TAC transition (matches the `TypedStore` threading pattern).
  - `tacToArm_correctness` discharges the initial `hInv` via `spec.invAtStart` at pc=0.
- **Oracle-discharge helper** ([CodeGen.lean:4029](CredibleCompilation/CodeGen.lean#L4029)):
  - New `verifiedBoundsSafe_sound` theorem: `verifiedBoundsSafe p pc = true + buildVerifiedInvMap p pc σ am → (arrLoad-bound ∧ arrStore-bound at pc)`. Unpacks the safe flag into `checkerOk` + per-pc interval claim; unpacks the invariant (under checker-accepting) into `IMap.satisfies`; combines to extract `idxVal.toNat < arraySize`, then transports to `idxVal < arraySizeBv` via the `arraySize < 2⁶² < 2⁶⁴` bound.
- **`step_simulation` oracle construction** ([CodeGen.lean:5797](CredibleCompilation/CodeGen.lean#L5797)):
  - The trivial `intro hBS; exact absurd hBS (by decide)` from Phase 5 is gone. Replaced with `fun hBS => verifiedBoundsSafe_sound hPC hBS hInv` — a real derivation from the threaded invariant.
  - `let safe : Bool := verifiedBoundsSafe p pc` (was `false` in Phase 5); matches the per-instr form that `instrGen` now provides.

**Structural surprises:**

- **Widening and the `refines` direction.** The analyzer widens loop-header ranges to `iTop = 10¹²`; downstream transfers (e.g. `i+1` at the back edge) can produce `hi = iTop + 1 = 10¹² + 1`, strictly wider than the analyzer's widened claim. Under the tight `refines` (`strong ⊆ weak`), this would fail. Under `validIntervalLoose` + skip-invalid-weak, both the `10¹²` and `10¹²+1` values pass loose; the refinement check itself uses `strong.hi ≤ weak.hi` but in Probe D's empirical test on simpleLoopProg / firstDiffProg, this doesn't actually fail because the analyzer's widening produces coherent fixed points where strong ⊆ weak holds at the relevant PCs. No additional clamping needed inside `certSuccessor`.
- **`arraySize` bound required.** `BitVec.ofNat 64 arraySize` wraps when `arraySize ≥ 2⁶⁴`, so `idxVal.toNat < arraySize` doesn't lift to `idxVal < arraySizeBv` without an upper bound on `arraySize`. Strengthened `isBoundsSafe` to additionally require `arraySize arr < 2⁶²` per-pc; this matches the `validIntervalLoose` cap on `hi` and keeps the proof clean. Empirical arrays fit well within this.
- **`let`-binding in hypothesis elimination.** `let safe := verifiedBoundsSafe p pc` followed by `cases hBS : safe` doesn't destructure cleanly because `safe` is a `let`-bound name; the `Bool.and_eq_true` simp still works on the original form, so I avoided `cases` on `safe` and used direct `simp only [verifiedBoundsSafe, isBoundsSafe, Bool.and_eq_true]` to unpack.
- **`Array.getD` vs `getElem?.getD` in call-site proofs.** `bodyGenStep` uses `code.getD pc .halt = Array.getD` but the spec's instrGen form uses `p.code.getD pc .halt`. These are defeq but surface forms differ; a local `have hbs : verifiedBoundsSafe p pc = isBoundsSafe ... := by simp only [verifiedBoundsSafe]; congr 1; simp [Array.getD, hpcCode]` bridges them without a heartbeat timeout (the naive "show … = some _" with the full unfolded form timed out at 200k heartbeats).

**Empirical verification (probe, not Phase 7 benchmark):**

```
#eval verifiedBoundsSafe simpleLoopProg 3   -- true
```

where `simpleLoopProg` is a `for i = 0..64 { t := arr[i]; i := i + 1 }` loop with `arr : int[64]` — the pc=3 arrLoad is elided. Phase 7 will extend to livermore kernels and count elided pairs.

**Effort vs plan (1.5 day estimate):** ~3 hours actual. Faster because the plan's "refinesSingleLoose + skip-invalid-weak" design was precise enough to just translate into edits, and Phase 5's invariant-preservation plumbing (in `GenAsmSpec.invPreserved` / `invAtStart`) was already in place. The invariant-threading through `tacToArm_refinement` was the novel load-bearing bit — about 15 LOC once the helper `verifiedBoundsSafe_sound` extracted the messy destructuring into its own 70-LOC proof.

**Status:** 0 sorrys; full `lake build` green; probe confirms elision fires on a simple loop. Files touched: 3 (`BoundsOptCert.lean`, `CodeGen.lean`, `CHANGELOG.md`). `ArmCorrectness.lean` not touched — Phase 5's oracle shape was already sufficient.

**Next:** Phase 7 (~0.5 day) — benchmark elision on livermore kernels; count eliminated `cmpImm + bCond .hs` pairs.

---

## BoundsOptCert Phase 5: oracle hypothesis in verifiedGenInstr_correct (2026-04-21)

**Goal:** Phase 5 of plans/certified-interval-pangolin.md — re-enable `boundsSafe = true` elision in `verifiedGenInstr_correct`. Replace the blunt `hBoundsSafeFalse : boundsSafe = false` hypothesis with a refined oracle that, under `boundsSafe = true`, produces the bounds-safety fact on the arrLoad/arrStore index — enough to discharge the `_boundsError` arms' step to the ARM bounds label.

**Shipped** ([ArmCorrectness.lean](CredibleCompilation/ArmCorrectness.lean), [CodeGen.lean](CredibleCompilation/CodeGen.lean)):

- **`verifiedGenInstr_correct` signature change** ([ArmCorrectness.lean:1748](CredibleCompilation/ArmCorrectness.lean#L1748)):
  - `(hBoundsSafeFalse : boundsSafe = false)` → `hBoundsSafeOracle`, a `boundsSafe = true → (⟨arrLoad-bound, arrStore-bound⟩ conjunction)` keyed on the instruction shape found via `p[pc]?`. Using `p[pc]?` (rather than `instr`) lets the hypothesis sit before `instr : TAC` in the parameter list — the `instr` binder isn't in scope yet.
- **Bounds-error arm discharges** ([ArmCorrectness.lean:1919](CredibleCompilation/ArmCorrectness.lean#L1919), [ArmCorrectness.lean:1967](CredibleCompilation/ArmCorrectness.lean#L1967)):
  - `arrLoad_boundsError` `boundsSafe = true` branch: pull the `arrLoad` side of the oracle, apply with `hPcArr := heq ▸ hInstr` (the per-arm `p[pc]? = some (.arrLoad ...)` witness) and `hidx`, rewrite `arrayDecls = p.arrayDecls`, contradict `hbounds`.
  - Symmetric for `arrStore_boundsError`.
  - Both arms previously closed via `absurd hBS (by rw [hBoundsSafeFalse]; decide)` — ~30 lines of vestigial "pragmatic punt" comments (from the Phase 4 stand-down) removed along with the blunt discharge.
- **`ext_backward_simulation` signature change** ([ArmCorrectness.lean:5406](CredibleCompilation/ArmCorrectness.lean#L5406)):
  - Same replacement as `verifiedGenInstr_correct`. Hypothesis moved into the `{implicit} pc σ am cfg' s` group so `p[pc]?` and `σ` resolve. Threads through to `verifiedGenInstr_correct`.
- **`step_simulation` call-site discharge** ([CodeGen.lean:5764](CredibleCompilation/CodeGen.lean#L5764)):
  - Phase 5 discharge is **trivial**: `safe` is still `false` (Phase 6's `isBoundsSafe` un-wiring hasn't landed), so the oracle's `safe = true` branch is vacuous — closed with `intro hBS; exact absurd hBS (by decide)`. The `spec.invPreserved` / `inv_preserved_steps` chain the plan outlines is dead code until Phase 6 makes `safe = true` actually reachable; wiring it now would run ahead of what the architecture needs.

**Design deviation from the plan:**

- **Trivial step_simulation discharge instead of `invMap + inv_preserved_steps + reachability`.** The plan's Phase 5 description envisioned the full invariant-to-bounds-safety derivation happening here. But the current codebase threads `verifiedBoundsSafe p pc = false` everywhere (via hard-wired `isBoundsSafe`), so the oracle's `boundsSafe = true` branch is unreachable at every call site. The architectural move — replacing `hBoundsSafeFalse` with the richer oracle — is complete; the load-bearing discharge is deferred to Phase 6, when `isBoundsSafe` un-wires and `boundsSafe = true` starts to fire. This matches the plan's risk #1 note ("weaken the oracle ... at the pipeline theorem level") — we're just deferring the substantive part of the weakening to where it's actually needed.
- **Reachability threading not materialized.** The plan's risk #1 flagged potential need to thread `Steps p (.run 0 σ₀ am₀) (.run pc σ am)` through `step_simulation` for `inv_preserved_steps`. Not done — under the current trivial discharge, the invariant isn't consumed. Phase 6 will decide between threading reachability or carrying `buildVerifiedInvMap p pc σ am` step-by-step (preserved via `spec.invPreserved`) depending on which is lighter.

**Structural surprises:**

- **Oracle parameter placement.** Dropping the oracle after `(instr : TAC)` would let it reference `instr` directly (cleaner `instr = .arrLoad ...` than `p[pc]? = some (.arrLoad ...)`). But rearranging the parameter order would touch every call site. Using `p[pc]?` keeps the parameter order stable; the per-arm witness `hPcArr := heq ▸ hInstr` derives `p[pc]? = some (.arrLoad ...)` in ~1 line.
- **`hAD ▸ hBound` fails** when the equality doesn't literally match the result type — Lean's `▸` is surface-level. Replaced with explicit `rw [hAD] at hBound` for the `arrayDecls → p.arrayDecls` rewrite, which succeeds regardless of where the equality appears in `hBound`'s type.
- **Pre-existing `hBoundsSafeFalse` comments in `arrLoad_boundsError`** — the ~27-line "pragmatic punt" block narrating why the `boundsSafe = true` case can't be closed in isolation — was written before the oracle pattern existed. Removed in favor of a 5-line comment describing the oracle resolution.

**Effort vs plan (1 day estimate):** ~1 hour actual. Faster than expected because the plan-risk #1 (reachability threading) was sidestepped by the Phase 4 `buildVerifiedInvMap` wiring already being in place, plus the realization that Phase 5's discharge at step_simulation can be trivial pending Phase 6. The only real work was the oracle shape (getting `p[pc]?` vs `instr` right) and threading through the three signatures.

**Status:** 0 sorrys; full `lake build` green. Files touched: 2 (`ArmCorrectness.lean`, `CodeGen.lean`) plus `CHANGELOG.md`. No changes to the pipeline top-level theorems (`tacToArm_refinement` / `tacToArm_correctness`) — the oracle is fully discharged inside `step_simulation`.

**Next:** Phase 6 (~0.5 day) — un-wire `isBoundsSafe`'s hard `false` to produce real per-PC elision decisions from the validated `BoundsOpt` certificate. The trivial `step_simulation` discharge above will need to be replaced with the real invariant-to-bounds-safety derivation at that point.

---

## BoundsOptCert Phase 4: GenAsmSpec wiring (2026-04-21)

**Goal:** Land Phase 4 of plans/certified-interval-pangolin.md — thread the Phase 3 checker output into `GenAsmSpec` so Phase 5 can consume `invPreserved` + `invAtStart` at the `arrLoad/arrStore_boundsError` arms. Pure plumbing; the validated invariant is not yet load-bearing, so `hBoundsSafeFalse` in `ext_backward_simulation` stays intact.

**Shipped** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):

- **Helper functions** (new section after `isBoundsSafe` at [CodeGen.lean:476](CredibleCompilation/CodeGen.lean#L476)):
  - `verifiedBoundsSafe p pc : Bool` — the per-PC bounds-check elision flag the spec refers to by name. Defined as `isBoundsSafe p.arrayDecls (BoundsOpt.analyzeIntervals p) pc (p.code.getD pc .halt)`; currently `false` via the hard-wired `isBoundsSafe`. Companion `verifiedBoundsSafe_rfl` closes the rewrite back to `false` for downstream consumers.
  - `checkInvAtStart inv : Bool` — entry-PC triviality check: accepts `inv[0]? = some (some [])` (the initial claim `analyzeIntervals` emits before any join/widen) or `inv[0]? = none` (empty program). Soundness `checkInvAtStart_sound` closes `intervalMap inv 0 σ am` for any `σ, am` under either branch.
  - `buildVerifiedInvMap p : PInvariantMap` — the validated invariant map. If `checkLocalPreservation p inv && checkInvAtStart inv`, lifts via `BoundsOpt.intervalMap`; otherwise falls back to `fun _ _ _ => True`. Companion `buildVerifiedInvMap_preserved` and `buildVerifiedInvMap_atStart` discharge `.preserved p` and `∀ σ am, _ 0 σ am` on both branches (via `checkLocalPreservation_sound` / `checkInvAtStart_sound` on the accepted path, trivially on the fallback).
- **`GenAsmSpec` extensions** ([CodeGen.lean:859](CredibleCompilation/CodeGen.lean#L859)):
  - `instrGen` sharpened — `false` → `verifiedBoundsSafe p pc`. Shape now matches the per-pc form the Phase 6 un-wiring will produce.
  - `callSiteSaveRestore` sharpened — `isBoundsSafe p.arrayDecls (BoundsOpt.analyzeIntervals p) pc p[pc]` → `verifiedBoundsSafe p pc`. Unifies the safe-flag expression with `instrGen`; `verifiedBoundsSafe p pc` unfolds (by `rfl`) to the exact form `bodyGenStep` emits.
  - **`invPreserved : (buildVerifiedInvMap p).preserved p`** — new field. Load-bearing for Phase 5 (fed to `inv_preserved_steps` at the arrLoad/arrStore arms).
  - **`invAtStart : ∀ σ am, buildVerifiedInvMap p 0 σ am`** — new field. Initial-state hypothesis for the `inv_preserved_steps` base case.
  - Both discharged in `verifiedGenerateAsm_spec` at [CodeGen.lean:3620](CredibleCompilation/CodeGen.lean#L3620) by directly applying the corresponding `buildVerifiedInvMap_*` theorems.
- **Discharge updates**:
  - `instrGen` case: the old `have hbs : isBoundsSafe ... = false := rfl; rw [hbs] at hGenInstr` pattern is reversed — now rewrite `verifiedBoundsSafe p pc` into the unfolded form inside the goal before `exact`.
  - `callSiteSaveRestore` case: no tactic changes needed — `verifiedBoundsSafe p pc` unfolds by `rfl` to the existing `isBoundsSafe ...` form that `hGenInstr` already has, so the existing `⟨armInstrs, hGenInstr, hEq⟩` transports via defeq.

**Design deviations from the plan:**

- **`invMap` is not a `GenAsmSpec` field.** `GenAsmSpec` is `Prop`-valued, so data-typed fields (`PInvariantMap`, `Nat → Bool`) aren't allowed. Instead, consumers reference `buildVerifiedInvMap p` and `verifiedBoundsSafe p` by name and obtain the two preservation proofs (`invPreserved`, `invAtStart`) from the spec. Semantically identical to the plan's design; surface shape differs.
- **`boundsSafe` is `verifiedBoundsSafe p : Nat → Bool`**, a top-level function rather than a spec field. Same reason (Prop-valued structure). Downstream Phase 5/6 can keep using `spec.instrGen` output; the safe-flag name is now stable.
- **`boundsSafe pc` logic stays trivial (`false`) until Phase 6.** The plan envisioned populating `boundsSafe pc` via `inv[pc]?` + arr-index-var check in Phase 4. Deferred: that check is Phase 6's job once `isBoundsSafe` un-wires; Phase 4 just wires the field shape and leaves the contents trivial, as the plan's fallback branch already allows.

**Structural surprises:**

- **`Prop`-valued `GenAsmSpec`.** Adding `invMap : PInvariantMap` as a field failed with `failed to generate projection ... field must be a proof`. Routed around by pulling the map into a top-level `buildVerifiedInvMap` function; the spec exposes only the two preservation proofs.
- **`unfold buildVerifiedInvMap; split` didn't fire** because the unfolded body has the shape `(have inv := ...; if _ then _ else _).preserved p` — the `.preserved` projection wraps the `if`, and `split` only fires on a visible `if/match` at the outer type. Restructured `buildVerifiedInvMap` with the `fun pc σ am =>` on the outside and the `if` directly in the body so `simp only [buildVerifiedInvMap]` exposes the conditional for `split`.
- **`by_cases` on a `Bool`-valued condition** (the `&&` of two checker booleans) produces a `decide (… = true) = true` hypothesis via Lean's `Decidable` elaboration, which doesn't rewrite back into the original `if` term. Avoided by using the `fun ... => if then else` form + tactic `split`, which doesn't go through `decide`.
- **`List.not_mem_nil ?m` computes to `False`** in this Lean/Mathlib version — applying it to `hmem : (v, r) ∈ []` fails the type mismatch `False vs ¬ (v, r) ∈ []`. Replaced with plain `cases hmem`, which closes the goal via the empty `List.Mem` pattern match.

**Effort vs plan (0.5 day estimate):** ~1.5 hours actual. Time went into:
- the `Prop`-valued-structure redesign (discovering the constraint, then routing around it), and
- the `unfold; split` plumbing (three different `split`/`rw`/`show` attempts before settling on `simp only [buildVerifiedInvMap]; split`).

The `verifiedGenerateAsm_spec` discharge itself was ~5 minutes — the refine just took two extra arguments (`buildVerifiedInvMap_preserved p, buildVerifiedInvMap_atStart p`), and the `instrGen` case needed one `rw` direction flipped.

**Status:** 0 sorrys; full `lake build` green. Files touched: 2 (`CodeGen.lean`, `CHANGELOG.md`). No changes to `ArmCorrectness.lean` or `hBoundsSafeFalse` — those are Phase 5/6.

**Next:** Phase 5 (~1 day) — replace `hBoundsSafeFalse` in `ext_backward_simulation` with `hBoundsSafeOracle`; discharge via `spec.invPreserved` + `inv_preserved_steps` + the reachability trace at the arrLoad/arrStore bounds-error arms.

---

## BoundsOptCert Phase 3 completion: full-fidelity checker soundness (2026-04-21)

**Goal:** Close out Phase 3 of plans/certified-interval-pangolin.md by lifting the two scope cuts (`certSuccessor`'s `.ifgoto` returning `m`, `.mul` dropping destination unconditionally). The checker now refines through comparison guards and accepts bounded multiplication.

**Shipped** ([BoundsOptCert.lean](CredibleCompilation/BoundsOptCert.lean)):

- **7 new refineCond leaves** — `refineCond_{lt,le}_{lit,var}_{true,false}_sound` (with `refineCond_lt_lit_true_sound` from the prep commit as the 8th). `.var bnd` variants use the `biv.lo + 1 = biv.hi` singleton condition to force `σ bnd`'s `toNat` equal to `biv.lo.toNat`, then apply the appropriate signed-unsigned bridge.
- **`refineCond_sound`** — structural induction on `BoolExpr`. `.not inner` flips `isTrue` (via `congrArg Bool.not` + direction manipulation) and recurses on `inner`; `.cmp` dispatches by `cases op / e1 / e2` with the 8 leaves at the supported shapes (all others fall through to `m`). Handled the `.cmp` catchall via nested `cases` rather than a single catchall `_, _, _` match — Lean's reducer won't unfold `refineCond` on abstract constructors, so concrete destructuring is required.
- **`BitVec64.toNat_mul_small`** — `(a * b).toNat = a.toNat * b.toNat` when both `< 2¹⁶`. `Nat.mul_le_mul` + `decide` on the constant upper bound gives the no-wrap proof.
- **`mul_sound`** + **`validIntervalMul`** — `.binop x .mul y z` soundness gated on both operand intervals having `hi ≤ mulCap = 2¹⁶`. Output range `⟨iy.lo * iz.lo, (iy.hi - 1) * (iz.hi - 1) + 1⟩`. Uses `Int.toNat_mul` for the nonneg-product transport and `Nat.mul_le_mul` for the range bound.
- **`certSuccessor` rewired** — now takes `pc` alongside `succPC` (needed to distinguish iftrue-branch from iffall-branch when they coincide). `.ifgoto be l` calls `refineCond m be true` iff `succPC = l ∧ succPC ≠ pc + 1` (unambiguous true-branch), `refineCond m be false` iff the symmetric condition, otherwise `m` (the ambiguous `l = pc + 1` case where both `Step.iftrue` and `Step.iffall` target `pc + 1`). `.mul` uses the new `mul_sound` under `validIntervalMul` gating.
- **`certSuccessor_sound`** `iftrue`/`iffall`/`.mul` arms updated to dispatch via `refineCond_sound` / `mul_sound`. `checkLocalPreservation` and `checkLocalPreservation_sound` updated to pass `pc` to `certSuccessor`.

**Structural surprises:**

- **`.var bnd` singleton step**: straightforward — combine `validIntervalLoose biv` (gives `biv.lo ≥ 0`) + `biv.lo + 1 = biv.hi` to force `bv'.toNat = biv.lo.toNat` via `omega` (from `biv.lo.toNat ≤ bv'.toNat < biv.hi.toNat = biv.lo.toNat + 1`).
- **`l = pc + 1` ambiguity on `.ifgoto`**: When the true-branch target equals the fallthrough, `Step.iftrue` and `Step.iffall` both target `pc + 1`. Without `pc` in `certSuccessor`'s signature, we couldn't tell which refinement to apply. Added `pc` as an explicit parameter and return `m` (no refinement) in the ambiguous case.
- **`cases op / e1 / e2` with catchall**: tactic-level `match op, e1, e2 with | ... | _, _, _ => simp [refineCond]` doesn't work — Lean's reducer won't unfold `refineCond` on abstract constructors even when the match's wildcard case is "everything not matched by earlier patterns." Instead, use nested `cases` with `with | foo => ... | _ => ...`, which destructures constructors concretely so `simp only [refineCond]` can reduce.
- **`cases hIT : isTrue` ordering**: Bool's constructor declaration order is `false, true`, so the first goal after `cases isTrue` has `isTrue = false`, not `= true`. Led to several application-type-mismatch errors on an earlier draft where I assumed the opposite order. Fix: name cases explicitly (`case false => ... case true => ...`).
- **`if isTrue then A else B` where `isTrue : Bool`**: Lean's elaboration turns this into `if isTrue = true then A else B` (Prop-valued `if` via `Decidable`). After destructuring `isTrue`, need `simp only [Bool.false_eq_true, if_false]` or `simp only [if_true]` to reduce the `if true = true then ...` / `if false = true then ...` form.

**Effort vs plan (3–4h estimate):** ~2.5 hours actual. Leaves were mechanical clones of the prototype; `mul_sound` mirrored `add_sound`. Time went into the `cases op / e1 / e2` exploration (Lean's matcher didn't cooperate with a single-level catchall) and the `l = pc + 1` corner-case design for the `.ifgoto` arm.

**Status:** 0 sorrys; full `lake build` green. Files touched: 1 (`BoundsOptCert.lean`); CHANGELOG.

---

## BoundsOptCert Phase 3 prep: refineCond soundness groundwork (2026-04-21)

**Goal:** De-risk the full-fidelity Phase 3 follow-up (refineCond + mul) by landing the helper lemmas and validating the leaf-proof shape end-to-end. Nothing in this commit is consumed by `checkLocalPreservation_sound` — it all sits downstream, ready for the next session to plug in.

**Empirical input (probe on 5 livermore kernels):** BoundsOpt's widened loop-counter ranges have `hi` up to ~5·10¹² (max seen on k02_iccg). This sits above the Phase 3 `validInterval` cap of `2³¹`, so any gate in `refineCond` keyed on `validInterval iv` would reject the most important case (loop counters with widened `hi`). Fix: a second, looser cap.

**Shipped** ([BoundsOptCert.lean](CredibleCompilation/BoundsOptCert.lean)):
- `looseCap = 2⁶²` and `validIntervalLoose` — wider validity check for intermediate intervals. Accepts all empirical BoundsOpt outputs, stays safely under `2⁶³` so signed-unsigned bridges still apply. Companion `validInterval_imp_loose` lets the tight cap flow into the loose context.
- `BitVec64.toInt_eq_toNat_of_lt_pow63` — factors the `split <;> omega` idiom previously inlined in `constInt_satisfies`. Reused 8× in the refineCond leaves.
- `BitVec64.slt_toNat_lt / not_slt_toNat_ge` and `sle_toNat_le / not_sle_toNat_lt` — signed-to-unsigned bridges over `BitVec.slt_iff_toInt_lt` / `sle_iff_toInt_le` (both in core Lean, confirmed by probe). Each ~8 lines; handles the four `CmpOp × {true, false}` combinations.
- **Prototype leaf `refineCond_lt_lit_true_sound`** — full proof for the true branch of `refineCond m (.cmp .lt (.var x) (.lit n)) true`. Landed in ~55 lines; the other 7 leaves (`.cmp .lt (.var x) (.var bnd)` × 2, `.cmp .le (.var x) (.lit n)` × 2, `.cmp .le (.var x) (.var bnd)` × 2) follow the same outline. The `.var bnd` variants add `biv.lo + 1 = biv.hi` singleton reasoning on top of the same machinery.

**Design note — what the prototype validated:**
- `rcases ⟨rfl, rfl⟩` on `mem_imSet.mp` eliminates the theorem's `x` parameter (substituting `x := v`), not `v`. Proof body refers to `v` throughout post-rcases. Hypotheses mentioning `x` in the signature get rewritten to reference `v`. Pattern is load-bearing and worth capturing for the other seven leaves.
- The signed-unsigned bridge needs `bv.toNat < 2⁶³`. `validIntervalLoose iv` gives `iv.hi ≤ 2⁶²`, so `bv.toNat < iv.hi.toNat ≤ 2⁶²` closes it. `n.toNat < 2⁶³` is derived from `n.toInt ≥ 0` (via the new-range validity chain) combined with `BitVec.toInt_eq_toNat_cond` — the latter pair implies `n.toNat < 2⁶³` by unsigned/signed dichotomy.
- `(min a b).toNat` for mixed signed/unsigned is easier handled by `rw [Int.min_def]; split` than by pre-computing a `min_toNat` equality. Split into the two branches and invoke the matching premise (`bv < iv.hi.toNat` in one, `bv < n.toNat = n.toInt.toNat` in the other).

**What's NOT shipped (follow-up):**
- The other 7 cmp leaves. Each ~25–30 lines, mechanical copies of the prototype plus a biv-singleton step for `.var bnd` patterns.
- `refineCond_sound` itself (induction on BoolExpr that dispatches to the 8 leaves + a trivial `_` case via `refineCond = m`).
- `mul_sound` and `BitVec64.toNat_mul_small`.
- Flipping `certSuccessor`'s `.ifgoto` arm to call `refineCond` (currently it returns `m`), and its `.mul` arm to re-enable the `[0, 2¹⁶)` claim.

**Effort rollup** (revised with this probe): full-fidelity Phase 3 = this prep + 7 leaves (~2h) + `refineCond_sound` induction (~30min) + mul (~30min) + `certSuccessor` rewire (~15min). **~3–4 hours** on top of what's landed. Medium risk, de-risked by the working prototype.

**Status:** 0 sorrys; full `lake build` green. Files touched: 1 (`BoundsOptCert.lean`); CHANGELOG. No wiring changes to CodeGen / ArmCorrectness.

---

## BoundsOptCert Phase 3: Checker soundness (2026-04-21)

**Goal:** Close the checker–concretization loop. Phase 3 of plans/certified-interval-pangolin.md. After this phase, `intervalMap inv` is a provably-`preserved` `PInvariantMap` whenever `checkLocalPreservation` accepts — ready for Phase 4's wiring into `GenAsmSpec`.

**Main theorem** ([BoundsOptCert.lean](CredibleCompilation/BoundsOptCert.lean)):
```
theorem checkLocalPreservation_sound (p : Prog) (inv : Array (Option IMap))
    (hChk : checkLocalPreservation p inv = true) :
    (intervalMap inv).preserved p
```

**Decomposition into three stages:**

1. **Bridge lemmas** — `Int.toNat_mono_of_nonneg`, `BitVec64.toNat_add_small` / `toNat_sub_small` (both ~3-line omega proofs), plus a `BitVec.toInt_eq_toNat_cond`-based bridge for `toInt`/`toNat` agreement under `intervalCap = 2³¹`. Structural lemmas on `imRemove` / `imSet` / `imLookup` (membership extraction via `List.mem_filter` and `List.find?_some`) pinned down where each IMap operation is needed.
2. **`refines_sound`** — the decisive step. If `m_strong` pointwise refines `m_weak` (via the `refinesSingle` check) and every valid-interval entry of `m_strong` concretizes soundly under `σ`, then so does `m_weak`. Range inclusion transports from `m_strong` to `m_weak` via `Int.toNat_mono` on the nonneg sides.
3. **`certSuccessor_sound`** — per-`Step`-constructor case analysis (the `@binop`/`@const` patterns needed to name the implicit `BinOp`/`Value` arguments in Lean 4). Three soundness templates do the bulk of the work:
   - `imRemove_sound` for every transfer that only touches `x` (handles 11 Step constructors: `boolop`, `arrLoad`, `fbinop`, `intToFloat`, `floatToInt`, `floatUnary`, `fternop`, `const .bool/.float`, `binop div/mod/bit/shift/mul`).
   - `identity_sound` for transfers that don't touch the store (handles `goto`, `iftrue`, `iffall`, `arrStore`, all five `print*` constructors).
   - Dedicated soundness lemmas for the three int-producing-with-claim cases: `constInt_sound` (`.const x (.int n)`), `copy_sound` (`.copy x y`), `add_sound` (`.binop x .add y z`), `sub_sound` (`.binop x .sub y z`).

**Main theorem structure:** case-splits on `inv[pc]?` vs `inv[pc']?`. The `inv.size = p.size` precondition (checked by Phase 2) forces `inv[pc]? = none ↔ pc ≥ p.size`, so the Step hypothesis's `p[pc]? = some instr` contradicts the `none` case via `Prog.getElem?_eq_some_iff`. The `some none` case makes `intervalMap` `False`, so preservation is vacuous. The `some (some m)` case specializes the per-pc checker obligation to the specific `pc'` successor, then invokes `refines_sound ∘ certSuccessor_sound`.

**Scope cuts shipped (for follow-up):**
- `.ifgoto be l` uses `certSuccessor m instr pc' = m` (no refinement). `refineCond` is defined in the file as a total `def` ready for a future phase; its soundness lemma (per-pattern, with signed-unsigned bridges from `BitVec.slt`/`sle`) is not proved here. Direct impact: `while (i < size) { arr[i] ... }` won't yet elide bounds checks on `arr[i]` — the refinement that says "in the false branch, `i < size`" isn't yet threaded. Unblocks Phases 4–6 wiring without additional effort there.
- `.binop x .mul y z` also drops the destination. The `mulCap = 2¹⁶` gated claim in Phase 2's `certSuccessor` is preserved but unused; a future phase can add `mul_sound` and re-enable it by flipping the `.mul` arm in `certSuccessor`.
- `.binop x .add y z` and `.sub` require **both** operand intervals be `validInterval`. Phase 2's `certSuccessor` was tightened to gate on this (it drops the destination otherwise), mirroring the soundness proof's preconditions.

**Bridge-lemma detail that caught us:** `validInterval r = true` doesn't force `validInterval (imLookup m v)` when `r` is derived from a min/max with `imLookup` — refinement patterns can narrow without re-validating the fallback. Addressed by `imLookup_mem_of_lo_nn`, which needs only `0 ≤ (imLookup m v).lo` to rule out the `irTop` fallback (since `irTop.lo = iBot < 0`). Weaker premise than `validInterval`, enough for `refineCond`'s eventual soundness proof.

**Status:** 0 sorrys; full `lake build` green. Files touched: 1 (`BoundsOptCert.lean`); CHANGELOG. Phase 3 delivers the complete certificate-checker-soundness theorem for the cases covered by `certSuccessor`; ifgoto-refinement and mul-elision are queued for a follow-up without blocking Phases 4–6.

---

## BoundsOptCert Phase 2: Local preservation checker (2026-04-21)

**Goal:** Decidable `Bool`-valued checker that validates BoundsOpt's untrusted `Array (Option IMap)` output on a per-PC local-preservation basis. Phase 2 of plans/certified-interval-pangolin.md. No proof obligations in this phase — soundness ships in Phase 3.

**Shipped** ([BoundsOptCert.lean](CredibleCompilation/BoundsOptCert.lean)):
- `imRemove : IMap → Var → IMap` — filter a var out. Many transfer cases drop a destination without making a claim.
- `refineCond : IMap → BoolExpr → Bool → IMap` — total, structurally-recursive re-implementation of BoundsOpt's `partial def refineCondition`. Needed because Phase 3 case-splits on it; a `partial def` can't be unfolded in proofs. Covers the same syntactic patterns: `.not` flips `isTrue` and recurses on the strictly-smaller `inner`; `.cmp .lt/.le (.var _) (.lit _ | .var _)` refine symmetrically; every other boolean shape falls through unchanged.
- `certSuccessor : IMap → TAC → Nat → IMap` — certified transfer function mirroring `transferInterval` for the cases where we can prove soundness, and dropping the destination (via `imRemove`) for cases where we can't (`boolop`, `arrLoad`, float-producing ops, `binop` div/mod/bitwise, out-of-range `mul`). The `.mul` case gates on both inputs fitting `[0, 2¹⁶)` (`mulCap = 65536`); otherwise drops. `.ifgoto be l` dispatches on whether `succPC = l` and feeds the flipped `isTrue` flag into `refineCond`.
- `refinesSingle / refines` — pointwise refinement check. `m_weak` is refined by `m_strong` iff every `(v, r') ∈ m_weak` has a corresponding `(v, r) ∈ m_strong` with `validInterval` on both and `r ⊆ r'`. Absent entries fail — the checker won't accept a successor claim that isn't backed by the transfer's output.
- `checkLocalPreservation : Prog → Array (Option IMap) → Bool` — the decidable entry point. Requires `inv.size = p.size` (so `none` always means OOB, used in Phase 3 to rule out the `pc ≥ p.size` Step case by contradiction). For each `pc < p.size` with `inv[pc]? = some (some m)`, for each successor `pc' ∈ instr.successors pc`, checks that `refines (certSuccessor m instr pc') m'` when `inv[pc']? = some (some m')`; successors with no claim or out-of-bounds impose no obligation. PCs with no claim at source are skipped.

**Design notes:**
- `certSuccessor` diverges from BoundsOpt's `successorIMap` intentionally. BoundsOpt optimizes for claim strength (feeds through `irTop`-shaped intervals that would pass `satisfies` vacuously); we optimize for proof shape, dropping the destination wherever a sound claim isn't cheap to state. This means BoundsOpt might produce stronger post-states than `certSuccessor`; that just means the `refines` check will sometimes reject valid BoundsOpt output, not the other way around. Safe direction.
- The `.mul` cap is set to `2¹⁶`. Could be generalized to `a.hi * b.hi < 2⁶³` with more work; per the plan's risk analysis this is probably fine for benchmark coverage.

**Status:** 0 sorrys; full `lake build` green. Files touched: 1 (`BoundsOptCert.lean`).

---

## BoundsOptCert Phase 1: Interval-invariant wrapper (2026-04-21)

**Goal:** First chunk of the certificate-based BoundsOpt re-enable plan (plans/certified-interval-pangolin.md). BoundsOpt stays untrusted; this phase sets up the concretization that lifts its output into `PInvariantMap` shape so `inv_preserved_steps` can consume it downstream. No wiring into codegen yet — Phases 4–6 do that.

**Shipped** ([BoundsOptCert.lean](CredibleCompilation/BoundsOptCert.lean) — new file):
- `IntervalInv.satisfies : IRange → BitVec 64 → Prop` — `0 ≤ r.lo ∧ r.lo.toNat ≤ bv.toNat ∧ bv.toNat < r.hi.toNat`. The `r.lo ≥ 0` clause makes `irTop`-shaped ranges vacuously false, so they fall out without special casing.
- `IMap.satisfies : IMap → Store → Prop` — pointwise: every explicit `(v, r)` entry in the map demands `σ v = .int bv` with `bv ∈ r`. Array memory is ignored (this domain tracks ints only).
- `intervalMap : Array (Option IMap) → PInvariantMap` — lifts BoundsOpt's `Array (Option IMap)` into `PropChecker`'s `PInvariantMap` shape. PCs with `none`, `some none`, or out-of-bounds give the trivial invariant `True` — they impose no obligation, so Phase 2's checker only needs to handle `some (some m)` predecessors.
- `validInterval : IRange → Bool` — structural `0 ≤ lo ≤ hi ≤ 2³¹`. The `2³¹` cap is the overflow-safe bound: `a + b < 2³² < 2⁶³` for any `a, b < 2³¹`, so bitvec addition can't wrap. Every Phase 3 transfer-soundness lemma will gate on `validInterval`.

**Status:** 0 sorrys; full `lake build` green. Files touched: 1 (new `BoundsOptCert.lean`).

---

## Phase 4: Tighten forward theorems — name haltFinal; distinguish div vs bounds (2026-04-21)

**Goal:** Surface the concrete ARM sentinels (`haltFinal`, `divS`, `boundsS`) through the forward simulation interface so Phase 7's backward theorems have bin-by-bin statements to destructure. Part of plans/backward-jumping-octopus.md.

**`ExtSimRel` tightening** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean)):
- `ExtSimRel` parameterized on two new `Nat`s: `divS` and `boundsS`. The `.errorDiv`/`.errorBounds` cases changed from `True` to `arm.pc = divS` / `arm.pc = boundsS`. The `.halt` case kept agnostic (still `ExtStateRel ∧ arm.arrayMem = am`); the clean-halt PC surfaces as a side output of `step_simulation` instead (see below), because `verifiedGenInstr`'s halt emission only reaches `haltS` — the `armSteps_haltSaveBlock` continuation to `haltFinal` is driven by `step_simulation`'s halt intercept, not by `verifiedGenInstr_correct`.

**ARM error arms step to sentinels** ([ArmCorrectness.lean](CredibleCompilation/ArmCorrectness.lean)):
- `verifiedGenInstr_correct`'s `binop_divByZero` arm now walks through `vLoadVar lv ++ vLoadVar rv ++ [.cbz rv_reg divLabel]`: the loads preserve `ExtStateRel`; at `.cbz rv_reg divLabel`, the divisor is `0` (derived from `¬ op.safe a b` + BinOp.safe specialization for `.div`/`.mod`) so `ArmStep.cbz_taken` fires and `arm.pc` ends at `divLabel`. Both `div` and `mod` share the same prefix, so they're handled uniformly.
- `verifiedGenInstr_correct`'s `arrLoad_boundsError` / `arrStore_boundsError` arms step through `vLoadVar idx ++ [.cmpImm idx_reg size, .bCond .hs boundsLabel]`: `ArmStep.cmpRI` sets the flags, and because `¬ (idx < size)` we have `condHolds .hs = true`, so `ArmStep.bCond_taken` branches to `boundsLabel`.
- All three `*_typeError` arms stay at `⟨s, .refl, trivial⟩` since the new `ExtSimRel` keeps `.typeError` as `True` (they're vacuous for well-typed programs).

**BoundsOpt elision disabled** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)): `isBoundsSafe` is temporarily wired to unconditional `false`. Reason: when `boundsSafe = true`, `verifiedGenInstr` drops the `cmpImm`/`bCond` bounds check, so the `arrLoad_boundsError` arm has no branch to step to `boundsLabel`. Re-enabling the elision requires proving soundness of `BoundsOpt.analyzeIntervals` (so that `boundsSafe = true` implies the step can never produce `arrLoad_boundsError`/`arrStore_boundsError`). To discharge the now-vacuous `boundsSafe = true` branches of `verifiedGenInstr_correct`, a new `hBoundsSafeFalse : boundsSafe = false` hypothesis is threaded through `verifiedGenInstr_correct` and `ext_backward_simulation`. The `GenAsmSpec.instrGen` clause was tightened from `∃ safe, ...` to `verifiedGenInstr ... false = some ...` (since that's what the actual codegen produces now).

**Halt PC as side-output** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- `step_simulation`'s output now includes a fourth conjunct `(∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)`. Lib-call and print cases discharge it vacuously (they produce `.run` cfg's); the normal non-halt path discharges via `cases hStep` (only `Step.halt` could produce `.halt`, which contradicts the `hHalt : p[pc] ≠ .halt` guard); the halt intercept path discharges by chaining `haltFinal_eq` + `haltSaveBlock_eq` with the PC accumulated by `armSteps_haltSaveBlock`.
- `tacToArm_refinement` and `tacToArm_correctness` threaded through unchanged — each carries the halt-PC conjunct alongside the `ExtSimRel`.

**Forward theorem sharpening** ([PipelineCorrectness.lean](CredibleCompilation/PipelineCorrectness.lean)):
- `while_to_arm_correctness` conclusion now includes `s'.pc = r.haltFinal`.
- `while_to_arm_error_preservation` replaced by two cause-specific theorems:
  - `while_to_arm_div_preservation`: input is `TAC ⟶* Cfg.errorDiv σ_err am_err`; conclusion is `s'.pc = r.divS` plus the source-side unsafe witness.
  - `while_to_arm_bounds_preservation`: input/output analogous for `errorBounds`/`boundsS`.
- Both theorems conclude `∃ fuel, unsafeDiv ∨ unsafeBounds` on the source side (not cause-matched per-theorem). Full cause-matching (`errorDiv` input ↔ `unsafeDiv` output) requires threading the cause through `compileStmt_unsafe`'s structural induction; that's deferred to Phase 7's backward direction. The split here is sufficient for Phase 5/6/7 to consume the ARM-side PC binning.

**`whileToTAC_refinement` error arm upgraded** ([RefCompiler/Refinement.lean](CredibleCompilation/RefCompiler/Refinement.lean)):
- `.errors` conclusion now `∃ fuel, prog.body.unsafeDiv fuel ... ∨ prog.body.unsafeBounds fuel ...`. Converted the existing `by_contra hall; push_neg at hall` to rebind `hall` as `∀ fuel, safe fuel` via `Stmt.safe_iff_not_unsafe.mpr`, leaving the rest of the proof (unbounded-execution vs terminal-step contradiction) untouched.

**Status:** 0 sorrys; full `lake build` green. Files touched: 5 (ArmSemantics, ArmCorrectness, CodeGen, PipelineCorrectness, RefCompiler/Refinement).

**Scope not done in this phase (deferred):**
- Threading cause through `compileStmt_unsafe` and helpers (`compileExpr_stuck`, `compileBool_stuck`, `compileExprs_unsafe`). Would upgrade `while_to_arm_div_preservation` / `while_to_arm_bounds_preservation` to produce the specific cause (`unsafeDiv` for divS; `unsafeBounds` for boundsS) instead of the disjunction. Mechanical but wide structural-induction work; best co-scoped with Phase 7's backward direction where cause-matching is necessary anyway.
- BoundsOpt soundness — required to re-enable the `boundsSafe = true` elision. Independent of the Phase 4–7 critical path.

**Notes for downstream phases:**
- Phase 5 (ARM divergence) can now assume the tightened `ExtSimRel` — in particular, error cfg's pin ARM's PC to the sentinels.
- Phase 6 (ARM totality exhaustion) needs `haltFinal`/`divS`/`boundsS` as distinct PCs, all now anchored by GenAsmSpec clauses.
- Phase 7's backward direction can destructure on `s'.pc ∈ {haltFinal, divS, boundsS}` and dispatch each case to the matching forward theorem via sentinel distinctness.

---

## Phase 2b: Halt-case step-through to haltFinal (2026-04-21)

**Goal:** Complete the Phase 2a infrastructure by extending `step_simulation`'s halt case to step through the halt-save block instead of stopping at `haltS`. After this phase, a TAC `.halt` is simulated by ARM steps ending at `haltFinal = bodyFlat.size` — the clean-halt sentinel. Part of plans/backward-jumping-octopus.md.

**Core lemma** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- New `armSteps_haltSaveBlock`: from any `ExtStateRel`-compatible state with `CodeAt prog s.pc (genHaltSave observable layout varMap)`, ARM reaches `s'` with `s'.pc = s.pc + (genHaltSave ...).length`, `s'.arrayMem` preserved, and `ExtStateRel` preserved. Proved by induction on `observable`, case-splitting on each `genHaltSaveOne`: writes to `stack[off]` use `ExtStateRel.setStack_fresh` with the freshness argument derived from the two new `GenAsmSpec` invariants.

**GenAsmSpec additions** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)): two new spec clauses, both discharged:
- `varMapInjOnOffsets : ∀ v w off, lookupVar r.varMap v = some off → lookupVar r.varMap w = some off → v = w`. Follows from `buildVarMap_offsets_nodup` + the new helpers `mem_keys_of_lookupVar_some` / `mem_of_lookupVar_some` + the existing `lookupVar_buildVarMap_injOn`.
- `layoutStackComesFromVarMap : ∀ v off, r.layout v = some (.stack off) → lookupVar r.varMap v = some off`. Discharged by unfolding `buildVarLayout`'s filterMap and observing that the stack branch's offset is exactly `lookupVar varMap v`.

**Freshness argument** (made explicit for future reference):
If the save block writes `stack[off]` because `layout v = .ireg _/.freg _` and `lookupVar varMap v = some off`, then for any `w` with `layout w = some (.stack off)`:
- `layoutStackComesFromVarMap` gives `lookupVar varMap w = some off`.
- `varMapInjOnOffsets` then forces `v = w`.
- But `layout v = .ireg _/.freg _` and `layout w = .stack off` — contradiction (layout is a function).
Hence `ExtStateRel.setStack_fresh` applies and each individual save preserves `ExtStateRel`.

**`step_simulation` halt intercept** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- Added `by_cases hHalt : p[pc] = .halt` in the normal-case branch (before delegating to `ext_backward_simulation`).
- Halt branch manually steps: first `.b r.haltS` (extracted from `verifiedGenInstr .halt = [.b r.haltS]` via `ArmStep.branch`), then applies `armSteps_haltSaveBlock` to reach `s'.pc = r.haltS + (genHaltSave ...).length = r.haltFinal` (using `haltS_eq` and `haltSaveBlock_eq` to build the relevant `CodeAt` on `bodyFlat`'s halt-save suffix).
- Non-halt branch unchanged (still delegates to `ext_backward_simulation`).

**Helper lemmas** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- `mem_keys_of_lookupVar_some {l : List (Var × Nat)}`: `lookupVar l v = some off → v ∈ l.map Prod.fst`.
- `mem_of_lookupVar_some {vars : List Var}`: `lookupVar (buildVarMap vars) v = some off → v ∈ vars` (combines the above with `buildVarMap_map_fst`).

**`ExtSimRel` halt-case tightening**: NOT done in this phase — deferred to Phase 4. Rationale: tightening to `arm.pc = haltFinal` would require every downstream consumer of `ExtSimRel (.halt ...)` (all of `verifiedGenInstr_correct`'s halt arm, `tacToArm_refinement`, every call site producing `⟨_, .refl, trivial⟩` for halt) to carry/produce the PC constraint. That work belongs with Phase 4's wider forward-theorem sharpening; Phase 2b here limits its scope to "ARM actually reaches `haltFinal`" — Phase 4 will then expose that PC in the interface.

**Downstream churn**: None. `step_simulation`'s signature is unchanged — the halt case just steps *further* than before, and the resulting `ExtSimRel` still holds (halt case depends only on `ExtStateRel σ s'` and `s'.arrayMem = am`, both preserved by `armSteps_haltSaveBlock`).

**Status:** 0 sorrys; full `lake build` green. Files touched: 1 (CodeGen.lean). ~250 LOC added.

**Notes for Phase 4 and beyond:**
- `armSteps_haltSaveBlock` is a reusable building block: Phase 6 (ARM totality) needs it for the halt-save branch of its per-PC successor argument.
- The two new GenAsmSpec clauses `varMapInjOnOffsets` / `layoutStackComesFromVarMap` are available to downstream proofs that need to reason about halt-save freshness or varMap/layout coherence.
- The halt step-through produces ARM state at `haltFinal` but this is not yet exposed in `ExtSimRel`. Phase 4's `while_to_arm_correctness` sharpening (`s'.pc = r.haltFinal` conjunct) is where that constraint surfaces.

---

## Phase 2a: Halt-save block lives inside bodyFlat; haltFinal becomes a real PC (2026-04-21)

**Goal:** Restructure the ARM output layout so the halt-save instructions (which spill observable register-allocated values back to their output stack slots) live inside the verified `bodyFlat` region instead of being an unverified tail. Downstream theorems in Phase 4/6/7 need `haltFinal` to name a concrete PC reachable from a `.halt` TAC. Part of plans/backward-jumping-octopus.md.

**Core layout change** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- `VerifiedAsmResult.haltSaveInstrs` renamed to `haltSaveBlock` and semantically relocated: it is now concatenated into `bodyFlat` immediately after the per-PC regions, rather than being a separate unverified tail.
- `VerifiedAsmResult.bodyFlat` redefined: `(bodyPerPC.toList.flatMap id ++ haltSaveBlock.toList).toArray`.
- New field `haltFinal : Nat` = `bodyFlat.size`. New relationship: `haltS ≤ haltFinal` with `haltFinal - haltS = haltSaveBlock.size`.
- Killed the `p.code.size * 1000` sentinel magic. Redefined:
  - `haltS := pcMap p.code.size` (= sum of per-PC instruction lengths = start of halt-save block inside bodyFlat).
  - `haltFinal := haltS + haltSaveBlock.size`.
  - `divS := haltFinal + 1`, `boundsS := haltFinal + 2` (off-the-end of bodyFlat, hence stuck in ARM).

**Label-independence of `instrLength`** ([ArmSemantics.lean](CredibleCompilation/ArmSemantics.lean), [CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- New `verifiedGenInstr_length_params_ind`: the length of `verifiedGenInstr` output depends on neither `pcMap` nor the `haltS`/`divS`/`boundsS` label values (they appear as immediates inside single `.b`/`.cbz`/`.bCond` instructions but do not affect instruction count).
- `instrLength` refactored to not take `haltS`/`divS`/`boundsS` args; it internally calls `verifiedGenInstr layout (fun _ => 0) instr 0 0 0 ...`. The `_params_ind` lemma bridges to any real label set used downstream.
- This lets Pass 1 compute lengths (and hence `pcMap`, `bodyInstrSize`) purely from layout/instruction structure, breaking the circular definition of `haltS := pcMap p.code.size`.

**GenAsmSpec additions** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)): six new spec clauses, all discharged:
- `haltS_eq : r.haltS = (r.bodyPerPC.toList.flatMap id).length` (via `buildPcMap_eq_take_length` and `bodyGenStep_length`).
- `haltFinal_eq : r.haltFinal = r.haltS + r.haltSaveBlock.size` (by construction).
- `divS_eq : r.divS = r.haltFinal + 1`, `boundsS_eq : r.boundsS = r.haltFinal + 2` (rfl).
- `haltSaveBlock_eq : r.haltSaveBlock.toList = genHaltSave p.observable r.layout r.varMap`.
- `haltSaveComplete : ∀ v ∈ p.observable, (∃ ir off, layout = .ireg ir ∧ lookupVar varMap = off) ∨ (∃ fr off, layout = .freg fr ∧ lookupVar varMap = off) ∨ (∃ off, layout = .stack off)` — rules out `genHaltSaveOne`'s silent-drop cases. Discharged via `observable_subset_collectVars` + `buildVarLayout_complete` + `buildVarMap_lookup_of_mem`.

**New helper lemmas** ([CodeGen.lean](CredibleCompilation/CodeGen.lean)):
- `observable_subset_collectVars : ∀ v ∈ p.observable, v ∈ collectVars p`. Follows because `collectVars` ends with a foldl over `p.observable` that adds each observable (parallel to `buildVarLayout_complete`).
- `buildVarMap_lookup_of_mem : ∀ v ∈ collectVars p, lookupVar (buildVarMap (collectVars p)) v ≠ none`. Alias around the existing `lookupVar_of_mem_collectVars`.
- `CodeAt.liftToSuffix : CodeAt pre.toArray startPC instrs → CodeAt (pre ++ suf).toArray startPC instrs`. Lets per-PC `CodeAt` conclusions drawn from the old flat array survive the new bodyFlat's halt-save suffix.
- `codeAt_of_bodyFlat' r ...` wrapper: per-PC block still embeds in `r.bodyFlat`, now that `r.bodyFlat` has the halt-save suffix.

**`verifiedGenerateAsm` rewiring** ([CodeGen.lean:749+](CredibleCompilation/CodeGen.lean)):
1. Pass 1 computes `lengths` using `instrLength` (label-free).
2. `pcMap := buildPcMap lengths.toArray`; `bodyInstrSize := pcMap p.code.size`.
3. `haltSaveBlock := genHaltSave p.observable layout varMap`.
4. `haltS := bodyInstrSize`; `haltFinal := bodyInstrSize + haltSaveBlock.length`; `divS := haltFinal + 1`, `boundsS := haltFinal + 2`.
5. Pass 2 calls `bodyGenStep ... haltS divS boundsS` — real labels propagate into branch immediates.
6. Record construction fills in the new fields.

**Downstream call sites updated:**
- Pretty-printer ([CodeGen.lean:5500](CredibleCompilation/CodeGen.lean)) renamed `r.haltSaveInstrs` → `r.haltSaveBlock`.
- `step_simulation`/`tacToArm_correctness` callers of `codeAt_of_bodyFlat` switched to `codeAt_of_bodyFlat'` (the suffix-lifted wrapper).
- All existing `GenAsmSpec` consumers (ArmCorrectness, PipelineCorrectness, SoundnessBridge) unchanged — the new spec clauses are purely additive.

**Pending for Phase 2b:**
- `armSteps_haltSaveBlock` lemma (stepping through the save block from `haltS` to `haltFinal` preserves `ExtStateRel` and `arrayMem`, and writes observable values to their output stack slots).
- Halt case of `step_simulation` updated to step through `haltSaveBlock` to `haltFinal` (currently still reaches `haltS` and stops).
- ExtSimRel halt-case tightening (optional — `arm.pc = haltFinal`).

**Notes for downstream phases:**
- `ExtSimRel` halt case remains `ExtStateRel ∧ arm.arrayMem = am` (unchanged). Phase 2b can tighten to include `arm.pc = haltFinal`.
- `r.haltS`, `r.divS`, `r.boundsS` are still fields (not defs) for minimal downstream disruption; their values are constrained by the new `GenAsmSpec` clauses.
- The `* 1000` magic is gone. `haltS = pcMap p.code.size` is now a stable, meaningful PC anchored to bodyFlat layout.

**Status:** 0 sorrys; full `lake build` green. Files touched: 2 (CodeGen.lean, ArmSemantics.lean). Downstream theorem consumers unchanged.

---

## Phase 3: split Cfg.error into Cfg.errorDiv / Cfg.errorBounds (2026-04-21)

**Goal:** TAC-level counterpart to Phase 1's source-level `unsafeDiv`/`unsafeBounds` split. Distinguishes div-by-zero errors from bounds errors in the TAC `Cfg` and `Step` types so Phase 4's forward theorems can name the specific PC (`divS` vs `boundsS`) and Phase 7's backward theorems can conclude a specific unsafe kind. Part of plans/backward-jumping-octopus.md.

**Core TAC changes** ([TAC.lean](CredibleCompilation/TAC.lean)):
- `Cfg.error σ am` → `Cfg.errorDiv σ am` and `Cfg.errorBounds σ am` (two constructors replacing one).
- `Step.error` renamed to `Step.binop_divByZero`, now produces `.errorDiv`.
- `Step.arrLoad_boundsError` / `Step.arrStore_boundsError` now produce `.errorBounds`.
- New terminal-config lemmas `Step.no_step_from_errorDiv`, `Step.no_step_from_errorBounds`.
- New cause-agnostic predicate `Cfg.isError : Cfg → Prop` plus lemma `Step.no_step_from_isError` for call sites that need "some runtime error" without caring which kind.

**Threaded through 11 files**:
- `TypeSystem.lean`: `Step.progress` / `Step.progress_untyped` / `type_safety` renamed `error` match arms to `binop_divByZero` and split bounds terminators.
- `PropChecker.lean`: `checkErrorPreservationProp` is now a conjunction (errorDiv branch ∧ errorBounds branch), each cause-preserving. `Behavior.errors` clause in `program_behavior` is now a disjunction of errorDiv / errorBounds reach. New `steps_to_errorDiv_decompose` / `steps_to_errorBounds_decompose` and `errorDiv_preservation` / `errorBounds_preservation`, with cause-agnostic wrapper `error_preservation`. `observeProp` handles both kinds.
- `SoundnessBridge.lean`: `checkDivPreservationExec_sound` restructured as `refine ⟨?divBranch, ?boundsBranch⟩` — div branch dispatches via `binop_divByZero`, bounds branch via `arrLoad_boundsError`/`arrStore_boundsError`. `exec_error_preservation` now uses the disjunction form.
- `RefCompiler/Correctness.lean`: `error_run_no_halt` generalized to take a `c_err : Cfg` with `c_err.isError` witness; `unsafe_binop_errors` now produces `.errorDiv`.
- `RefCompiler/ErrorHandling.lean`: `compileExpr_stuck`, `compileBool_stuck`, `compileStmt_stuck`, `compileStmt_unsafe`, `compileExprs_unsafe` conclusions updated to `∃ ... c_err, ... Step ... c_err ∧ c_err.isError ∧ ...`. ~40 call sites mechanically updated to destructure/construct the extra `c_err` and `hisErr` fields.
- `RefCompiler/Refinement.lean`: `program_behavior_init` errors clause switched to disjunction; `whileToTAC_reaches_error` returns `∃ c_err, c_err.isError ∧ reach`; `RefStepsN.no_step_error` generalized to `isError`; backward refinement's errors/typeErrors/diverges cases now destructure the disjunction/isError witness.
- `PipelineCorrectness.lean`: `Step_of_code_arrayDecls_eq` renamed `error` arm; `applyPass_preserves_error_am`, `applyPassesPure_preserves_error_am`, `while_to_arm_error_preservation` all use the disjunction form (cause preserved across passes and compilation).
- `ArmSemantics.lean`: `ExtSimRel` pattern-matches `.errorDiv` and `.errorBounds` distinctly (both currently `True`; Phase 4 tightens to `arm.pc = divS` / `arm.pc = boundsS`).
- `ArmCorrectness.lean`: `verifiedGenInstr_correct`'s error arm renamed `error` → `binop_divByZero`.
- `CodeGen.lean` + `ExecChecker.lean`: `step_run_or_terminal` and `observeExec` handle both new constructors.

**Philosophy — why disjunction at `Behavior.errors` level?** We preserve cause end-to-end: if the optimized TAC hits `.errorDiv`, the unoptimized TAC and source are also div-unsafe; likewise for bounds. But at the coarse `Behavior.errors σ'` level (source-visible), the user only sees "an error occurred" — hence the disjunction, which all downstream consumers (`credible_compilation_soundness`, `whileToTAC_refinement`, etc.) project out as needed.

**Status:** 0 sorrys; full `lake build` green. Files touched: 11. Direct `Cfg.error` / `Step.error` sites patched: far more than the probe's 25 (the disjunction had to propagate through every `∃` / `match` that surfaced an error config). Plan estimate 1–2 days held; actual ~1 session.

---

## Phase 1: split source safety into unsafeDiv / unsafeBounds (2026-04-21)

**Goal:** Dormant infrastructure for the backward-correctness theorem suite (plans/backward-jumping-octopus.md). Lets Phase 3+ ask *why* an unsafe source program fails — division vs. bounds — and maps each to a distinct ARM sentinel PC.

**Added** (in [CompilerCorrectness.lean:734+](CredibleCompilation/CompilerCorrectness.lean) new § 4a′):
- Predicates `SExpr.unsafeDiv`, `SExpr.unsafeBounds`, `SBool.unsafeDiv`, `SBool.unsafeBounds`, `Stmt.unsafeDiv`, `Stmt.unsafeBounds` — structural duals of the existing `.safe` predicates. First-error-wins semantics for short-circuit `and`/`or` and sequential `seq` / variadic `print`: whichever sub-expression evaluates first determines the error class.
- List-lifts `SExpr.listUnsafeDiv`, `SExpr.listUnsafeBounds` for `Stmt.print`'s argument list.
- Bridge theorems at each syntactic level (`SExpr`, `SBool`, `SExpr` list, `Stmt`):
  - `safe_iff_not_unsafe` — `safe ↔ ¬unsafeDiv ∧ ¬unsafeBounds`
  - `not_safe_iff_unsafeDiv_or_unsafeBounds` — `¬safe ↔ unsafeDiv ∨ unsafeBounds` (classical corollary)
  - `unsafeDiv_unsafeBounds_disjoint` — `¬(unsafeDiv ∧ unsafeBounds)`

**New imports:** `Mathlib.Tactic.Tauto`, `Mathlib.Tactic.Push` (for `tauto` and `push_neg`). Classical logic opened in a `section UnsafeSplit`.

**Why it's dormant:** no existing theorem references these predicates yet. Phase 3 switches `Cfg.error` to `Cfg.errorDiv` / `Cfg.errorBounds` and threads the cause through the forward proofs; at that point these predicates become live.

**Status:** 0 sorrys; full `lake build` green.

---

## Drop auto-dump of observable variables on halt (2026-04-20)

**Goal:** Separate I/O from semantic preservation so .w outputs match .c/.f directly.

**Before:** The `.Lhalt:` epilogue emitted a printf for every declared variable (treating `Prog.observable` as both a semantic-preservation contract AND an I/O dump). WL programs printed user-explicit prints first, then dumped all variables. `run_fast.sh` had to special-case this with a "compare first numeric token" rule and a "WL prints the result first, then dumps" comment.

**After:** Output happens **only via explicit `print*` statements**. The `.Lhalt:` epilogue now just spills observable values to stack via `genHaltSave` (the semantic-preservation contract — values are mechanically inspectable from outside the process via debugger) and exits.

**Conceptually:** `Prog.observable` keeps its semantic role (the refinement theorem says `σ_src v = σ_compiled v` at halt for `v ∈ observable`) but loses its I/O role.

**Changes:**
- [CodeGen.lean:5400+](CredibleCompilation/CodeGen.lean) — removed the printf-emitting loop in the halt epilogue (~40 lines deleted)
- Removed dead labels `.Lfmt:`, `.Lfmt_float:`, `.Lname_<v>:` from the rodata section (only used by the deleted dump; variadic-print uses per-PC `.Lfmt_print_<pc>` labels which stay)
- Updated `run_fast.sh` correctness-check comment

**Behavior verified:** k03_dot.w smoke test confirms `// Spill observable values to stack` is present, the old `// Print observable variables` is gone, and the user's `printfloat(q); printstring("\n")` still emits `_printFloat`/`_printString` calls.

**WL and Fortran/C outputs now match directly** (modulo float formatting differences from `%f` vs Fortran's default field width).

---

## Add parser support for typed-print surface syntax (2026-04-20)

**Goal:** Surface the four typed `Stmt` constructors in the WhileLang concrete syntax so `.w` files can use them directly.

**New surface syntax:**
```
printint(<expr>)         -- prints int-typed expression
printbool(<bexpr>)       -- prints bool expression  
printfloat(<expr>)       -- prints float-typed expression
printstring "literal"    -- prints string literal
```

**Variadic `print "fmt", args` syntax kept** working as before — its parsing is unchanged. Both surfaces coexist; the variadic form still compiles via the unverified TAC.print path while the typed forms flow through the verified pipeline.

**Changes:**
- Tokenizer: added `printint`, `printbool`, `printfloat`, `printstring` to the keywords list
- Parser: added 4 cases in `parseStmtAtom`, each parsing the appropriate operand (`parseExpr` for int/float, `parseBOr` for bool, string literal for string)

**Smoke-tested:** All four typed-print syntaxes parse correctly and a benchmark-style `.w` program with `printfloat(q); printstring "\n"` parses, type-checks, and codegens end-to-end.

**Livermore benchmarks: still use variadic print** — they're not edited yet. Migrating them is the next step.

---

## Close `Stmt.printBool` sorry; loosen TAC.printBool to accept int (2026-04-20)

**Goal:** Close the 1 sorry from the previous commit by eliminating the bool-temp-class issue at its root.

**Root cause:** The previous design materialized `Stmt.printBool b`'s result into a `__bt`-prefixed bool temp via `boolop`. The `hagree` invariant in `RefCompiler/Correctness` only recognizes `__t`/`__ft` prefixes as compiler temps — `__bt` looked like a "user variable" requiring source-vs-TAC store agreement, which the compiler-introduced bool temp couldn't satisfy.

**Fix:** Two coordinated changes:

1. **Loosen `WellTypedInstr.printBool`** from `Γ v = .bool` to `Γ v = .bool ∨ Γ v = .int`. Justification: `_printBool` runtime function reads `x0` as a 64-bit int and prints "true"/"false" based on 0/non-0. Bools and ints both live in iregs/stack at the codegen level, both go through `vLoadVar`. No soundness loss — purely type-discipline relaxation matching the runtime's actual behavior.

2. **Rewrite `compileStmt` for `Stmt.printBool b`** to use the `barrWrite`-style ifgoto+const sequence to materialize the bool result into an int temp (`tmpName`), then call `printBool` with the int:
   ```
   compileBool b ++
   [ifgoto be trueL, const tmp 0, goto endL, const tmp 1] ++
   [printBool tmp]
   ```
   No bool temp introduced. `tmpName k` is a `__t`-prefixed int temp that `hagree`'s existing `isTmp` check correctly excludes.

**Knock-on changes:**
- `verifiedGenInstr_correct`'s printBool case: now case-splits on the `.bool ∨ .int` disjunction (both arms work — bool/int both land in ireg/stack)
- `WhileLang` lemmas about printBool: `compileStmt_wt`, `compileStmt_length`, `compileStmt_allJumpsLe`, `compileStmt_code_simpleOps` updated for the new 5-instruction structure (compileBool + 4 conv + printBool)
- `compileStmt_noRegVar` updated for new conv-instr layout
- `compileStmt_correct`'s printBool case: full proof modeled on `barrWrite`'s correctness proof. Case-splits on `b.eval σ am`, walks the ifgoto-falls-through-then-const-0-then-goto path or the ifgoto-jumps-then-const-1 path, composes with `compileBool_correct`. ~70 lines.
- TypeSystem checker updated for disjunction: `decide (Γ v = .bool) || decide (Γ v = .int)`

**Btmp infrastructure (`btmpName`, `String.isBTmp`, `tyCtx_btmp_wt`, etc.) is no longer reachable** but left in place since it builds clean and could be useful for a future clean refactor (Phase 1 of the temp-class unification design discussed earlier). It can be removed in a follow-up cleanup commit.

**All four typed Stmt constructors** (`printInt`, `printBool`, `printFloat`, `printString`) now flow through the entire verified compiler pipeline (Stmt → TAC → ARM) at **0 sorrys**.

---

## Add typed `Stmt` constructors (Option A, partial — 1 sorry) (2026-04-20)

**Goal:** Lift the four typed prints from TAC into WhileLang at the surface (`Stmt`) level so they flow through the entire verified compilation pipeline (source `Stmt` → TAC → ARM), not just the TAC layer.

**Constructors added:**
- `Stmt.printInt : SExpr → Stmt`
- `Stmt.printBool : SBool → Stmt`
- `Stmt.printFloat : SExpr → Stmt`
- `Stmt.printString : String → Stmt`

**Type rules:** `Stmt.printInt e` requires `e` is int-typed; `Stmt.printFloat e` requires float-typed; `Stmt.printBool b` requires SBool; `Stmt.printString` is unconstrained.

**compileStmt lowering:**
- `printInt e` → compile `e` to int temp, emit `TAC.printInt temp`
- `printFloat e` → compile `e` to float temp, emit `TAC.printFloat temp`
- `printBool b` → compile `b` to BoolExpr, materialize to bool temp via `boolop`, emit `TAC.printBool btmp`
- `printString lit` → emit `TAC.printString lit` (no operand)

**New infrastructure:**
- `btmpName k = s!"__bt{k}"` for bool temps; `String.isBTmp` predicate; `noTmpDecls` extended to reject btmp prefixes; `tyCtx_btmp_wt` shows `tyCtx (btmpName k) = .bool` (via existing `__b → .bool` defaultVarTy mapping)
- `FragExec.single_printInt/Bool/Float/String` helpers in RefCompiler
- New ARM-level helpers `btmpName_noArmReg`, `btmpName_noArmFReg`, `btmpName_not_violates`, `btmpName_noRegVar` for the regalloc safety side

**Pattern-match exhaustiveness updates** across 11 files: WhileLang (bigStep, isSafe, stmtCodeLen, checkStmt, noReservedVars, compileStmt, plus 4 supporting lemmas), Parser (resolveStmt), CompilerCorrectness (interp_tmpAgree, Stmt.safe, safe_of_terminating, typedVars, typeCheck_typedVars, type_preservation), RefCompiler (Defs.intSafe + 4 single-step FragExec helpers, Correctness.compileStmt_correct, ErrorHandling 2 sites, Metatheory 2 sites, Refinement.compileStmt_shape_labels), CodeGen (compileStmt_noRegVar), PipelineCorrectness (1 destructure adjustment for the new noTmpDecls 3-conjunct shape).

**Status:** Build clean; **1 sorry** in `RefCompiler/Correctness.compileStmt_correct` for the `printBool` case.

**The sorry's design issue:** the `boolop` step writes to `btmp = btmpName k`. The `hagree` invariant requires source-vs-TAC store agreement on non-temp variables (`isTmp = false → isFTmp = false → ...`). `btmp.isTmp = false` (since `__bt` doesn't match the `__t`-prefix check), so the invariant requires `σ_tac btmp = σ btmp` — but `σ_tac` was just updated. Three resolutions identified:
- Add `isBTmp = false` as a 3rd `hagree` conjunct (touches ~30 sites in CompilerCorrectness/RefCompiler)
- Loosen `WellTypedInstr.printBool` to accept `.bool ∨ .int` and use `tmpName` for the bool temp (~5 sites in TAC layer)
- Drop `Stmt.printBool` entirely and surface bool printing only via the parser-level desugaring path (commit 2)

**printInt, printFloat, and printString flow through end-to-end at 0 sorrys** — they don't have the bool-temp issue because their temps already use the `__t` (int) or `__ft` (float) prefix that `hagree` recognizes, or use no temp at all (printString).

**Deferred (commit 2):** Parser desugaring — variadic `print "fmt", args` parses into a sequence of typed Stmt prints + literal segments, eliminating the variadic `Stmt.print` from any post-parse AST.

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

---

## Add `printString` typed library call (2026-04-20)

**Goal:** Second typed-print variant. Unlike printInt (which loads a Var into x0), printString is fully self-contained — the literal is embedded in rodata and the call sets x0 to its address.

**Probe-driven design:** Initially worried that printString would need pc threaded through `verifiedGenInstr` to generate unique format-string labels (mirroring the existing variadic `print`'s `.Lfmt_print_{pc}`). On reflection, that was anchoring on the wrong template — the label only needs to be **a deterministic function of the string content**, not pc-keyed. Switched to `stringPoolLabel : String → String` which encodes UTF-8 bytes as lowercase hex (`.Lstr_<hex>`). Pure function: identical strings dedupe automatically, distinct strings never collide.

**Pipeline:**
- TAC.printString : String → TAC (no-op step semantics)
- ArmInstr.callPrintS : String → ArmInstr
- ArmStep.callPrintS havocs caller-saved (no return value, no operand observation)
- verifiedGenInstr returns `[.callPrintS lit]` — a single instruction, no load (simpler than printInt)
- ppInstr emits `adrp x0, <label>@PAGE; add x0, x0, <label>@PAGEOFF; bl _printString`
- String-pool emission at end of generateAsm walks `p.code`, dedupes printString literals, emits one `.asciz` per distinct string under the deterministic label
- isLibCallTAC printString = true → flows through existing lib-call save/restore

**Proofs:**
- verifiedGenInstr_correct: ~25 lines (no load step, just havoc)
- step_simulation lib-call branch: new printString arm parallels printInt's structure but skips the load — just callPrintS step + 7 hBaseExists obligations. ~100 lines, simpler than printInt because no vLoadVar to thread through.
- 18 files updated for pattern-match exhaustiveness

**WellTypedInstr.printString is unconstrained** — no operand to type-check.

**Project remains at 0 sorrys.**

---

## Add `printFloat` typed library call (2026-04-20)

**Goal:** Third typed-print variant. The freg-mirror of printInt — argument passed in `d0` instead of `x0`, follows the standard ARM64 calling convention for double-precision arguments.

**Pipeline:**
- TAC.printFloat : Var → TAC (no-op step semantics)
- ArmInstr.callPrintF + ArmStep.callPrintF (havoc caller-saved)
- WellTypedInstr.printFloat requires `Γ v = .float`
- verifiedGenInstr returns `vLoadVarFP layout v .d0 ++ [.callPrintF]` (rejects ireg layouts as ill-typed)
- ppInstr emits `bl _printFloat`
- isLibCallTAC = true → existing lib-call save/restore wrapping

**Easier than printInt in two ways:**
1. `vLoadVarFP_exec` (and `vLoadVarFP_eff_exec`) already returns `s'.stack = s.stack` as a conjunct — no need for the inline 3-way layout case-split that printInt's step_simulation arm required to derive stack preservation.
2. `WellTypedLayout.float_not_ireg` already exists — drops in directly to `verifiedGenInstr_total` for the totality proof.

**Proofs:**
- verifiedGenInstr_correct: ~40 lines (mirrors printInt template)
- step_simulation lib-call branch: ~110 lines (cleaner than printInt's ~190 because hStack1 comes for free from vLoadVarFP_exec)
- 18 files updated for pattern-match exhaustiveness

**Three of four typed-print variants now end-to-end verified.** printInt on x0/ireg path; printFloat on d0/freg path; printString on rodata-pointer-x0 path. printBool still pending — would mirror printInt almost verbatim. The original variadic `print` constructor is still alive in TAC for backwards compat with unverified codegen.

---

## Add `printBool` typed library call (2026-04-20)

**Goal:** Fourth and final typed-print variant. Structurally identical to printInt at the proof level — bool values are passed in `x0` like integers, the only difference is the runtime function name (`bl _printBool` vs `bl _printInt`).

**Pipeline:**
- TAC.printBool : Var → TAC (no-op step semantics)
- ArmInstr.callPrintB + ArmStep.callPrintB (havoc caller-saved)
- WellTypedInstr.printBool requires `Γ v = .bool`
- verifiedGenInstr returns `vLoadVar layout v .x0 ++ [.callPrintB]` (rejects freg layouts)
- ppInstr emits `bl _printBool`
- isLibCallTAC = true → existing lib-call wrapping

**Proofs are mechanical copies of printInt with substitutions:** `printInt → printBool`, `callPrintI → callPrintB`, `int_not_freg → bool_not_freg`. The verifiedGenInstr_correct case (~40 lines), the lib-call branch arm in step_simulation (~190 lines including the inline 3-way layout case-split for `s1.stack` preservation), and totality proof all transfer with no architectural changes.

**All four typed-print variants now end-to-end verified.** The complete set:

| Variant | Reg class | Operand | proof template |
|---------|-----------|---------|----------------|
| printInt | x0 (ireg) | Var | original |
| printBool | x0 (ireg) | Var | clone of printInt |
| printFloat | d0 (freg) | Var | mirror via vLoadVarFP |
| printString | x0 (rodata ptr) | String literal | self-contained, no load |

The original variadic `print` constructor is still alive in TAC for backwards compat with the unverified codegen path; future work could remove it once all callers are migrated to the typed variants.

**Project remains at 0 sorrys.**

**Project remains at 0 sorrys.**

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
