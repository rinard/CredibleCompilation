# Phase 6/7 Next Session — Final Plan and Handoff

**Read this first.**  Supersedes all earlier Phase 6/7 planning documents
in this directory.  Last updated: 2026-04-22 after two full probe
sessions.

## TL;DR

Close Phase 7 by doing **pivot (deterministic havoc) + Fix B' (direct
ArmDiverges from self-loops)**.  Total budget ~750 LOC.  All major
risks validated by probes.  Work order in § Next Session Work Plan.

## Final decision

After extensive exploration, the cheapest robust path is:

1. **Deterministic havoc pivot** — refactor `ArmStep`'s 5 libcall
   constructors to use opaque havoc functions instead of existential
   arguments.  Cost: ~370 LOC (refactor + call-site updates +
   `arm_step_det`).  Gives `step_count_state_uniqueness` at ~15 LOC.
2. **Fix B'** — handle TAC self-loops by direct ArmDiverges derivation
   (no handler, no ExtSimRel revision).  Cost: ~250 LOC.  Complementary
   to the pivot; stacks cleanly.
3. **Phase 7a/b/c/d** — ~200 LOC given the above.  `halt_state_
   observables_deterministic` collapses to ~15 LOC under state
   uniqueness.

**Phase 6 exhaustion** (`bodyFlat_branch_target_bounded` + 14-case
sweep + `arm_behavior_exhaustive` König) is separate, optional,
~700 LOC.  Not required to close Phase 7.

## Why not alternatives

| Rejected | Why |
|---|---|
| **Fix B' alone (no pivot)** | `step_count_pc_uniqueness` under nondeterministic `ArmStep` requires ~300+ LOC of per-PC spec-structure analysis.  Micro-probe PF3 confirmed naive induction fails at the inductive step (two intermediate states have same PC but potentially different regs due to havoc).  Comparable or worse total cost vs pivot, with reactive-stacking hindsight penalty risk. |
| **Pivot alone (no Fix B')** | Step 6's `source_diverges_arm_pc_in_bodyFlat` requires partial Phase 5b (step-count positivity) — ~150 LOC of its own, even under the pivot.  Fix B' eliminates this with a direct ArmDiverges argument for ~100 LOC less. |
| **Full Phase 5b** | ~660–1940 LOC per phase5b-design.md.  Overkill for just Phase 7's needs. |
| **Handler approach (Fix B with ARM-level diverge trampoline)** | Changes ExtSimRel.run invariant.  Ripples through all forward-sim proofs: ~300+ LOC.  Fix B' is strictly better. |

## What's landed (branch `phase6-prep`)

### Infrastructure (commit `63e88d3`)

In [`CredibleCompilation/PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean):

- `sentinel_stuck`: sentinel PC ⇒ no ArmStep.
- `pcMap_le_haltS`: live TAC PCs map to ARM PCs ≤ haltS.
- `checkBranchTargets_to_labels_in_bounds`: spec bridge.
- `haltFinal_ne_divS`, `haltFinal_ne_boundsS`, `divS_ne_boundsS`:
  sentinel distinctness.
- `stepClosed_of_checkCertificateExec`: extract condition 6.
- `applyPass_preserves_stepClosedInBounds` /
  `applyPassesPure_preserves_stepClosedInBounds`.
- `pipelined_has_behavior` (wrapper over `has_behavior`).
- `pipelined_no_typeError` (wrapper over `type_safety`).

### Probes — all confirmed working

All probes at `CCTests/Tests/PivotProbe{PD,PE,PF}*.lean`:

| Probe | Status | What it validates |
|---|---|---|
| PD1 — opaque interaction | ✅ | `opaque` functions work with rfl/simp/exact/rw |
| PD2 — mini arm_step_det | ✅ | Projection trick scales to full state (5 constructors) |
| PD3 — forward-sim composability | ⚠️ sig only | Step 6 would be ~150 LOC without Fix B' |
| PE1 — 1-TAC-step positivity | ⚠️ partial | Works for halt/error sub-cases; blocked for diverges |
| PE2 — call-site grep | ✅ | 19 sites, ~210 LOC mechanical update |
| PE3 — .ifgoto inline | ✅ | 14-case sweep pattern validated |
| **PF1' — self-loop ArmDiverges** | ✅ | `ArmStep s s → ArmDiverges s` (~10 LOC). Works under nondet. |
| **PF2' — TAC→ARM self-loop** | ✅ | spec + TAC self-loop → ArmStep s s (~55 LOC) |
| PF3 — step_count_pc_uniqueness | ❌ blocks | Naive induction stalls; confirms pivot is necessary |

Probe files (reusable blueprints — **clone for the real proofs**):
- [`CCTests/Tests/PivotProbePD2.lean`](../CCTests/Tests/PivotProbePD2.lean) — mini `ArmStepDet` + `arm_step_det` via projection.  Blueprint for pivot Step 3.
- [`CCTests/Tests/PivotProbePF1.lean`](../CCTests/Tests/PivotProbePF1.lean) — `arm_self_loop_diverges` + `arm_diverges_of_prefix_reaches_self_loop`.  Copy-ready for Fix B'.
- [`CCTests/Tests/PivotProbePF2.lean`](../CCTests/Tests/PivotProbePF2.lean) — `tac_goto_self_loop_implies_arm_self_loop`.  Blueprint for Fix B' self-loop analysis.
- [`CCTests/Tests/PivotProbePE3.lean`](../CCTests/Tests/PivotProbePE3.lean) — `.ifgoto` inline-style branch-bound proof.  Blueprint for the 14-case sweep (if Phase 6 tackled).

### Un-privatized infrastructure

For probe and pivot support, these `CodeGen.lean` declarations were
un-privatized (no semantic change):
- `buildPcMap_eq_take_length`
- `codeAt_of_bodyFlat`
- `codeAt_of_bodyFlat'`
- `isLibCallTAC`

### Current sorry count

9 sorrys in PipelineCorrectness.lean:
- `bodyFlat_branch_target_bounded` (Phase 6)
- `step_count_pc_uniqueness` (will be filled by pivot Step 4)
- `arm_behavior_exhaustive` (Phase 6)
- `halt_state_observables_deterministic` (Phase 7a helper)
- Phase 7a/b/c/d theorem bodies
- `verifiedGenInstr_ifgoto_branch_bounded` (P1 probe placeholder;
  PE3 validated the fix pattern)

## Commits on `phase6-prep`

```
4094678 Phase 6/7 micro-probe PF3: step_count_pc_uniqueness under nondet
166f873 Phase 6/7 pivot probes PF1', PF2': Fix B' validated
0732a55 Phase 6/7 pivot probes PE1, PE2, PE3: findings before starting pivot
75a47f8 Phase 6/7 pivot probes: PD1, PD2 passed; PD3 flags LOC blowup
ec91423 Phase 6/7 deterministic pivot implementation plan (SUPERSEDED by this doc)
eb899b9 Phase 6/7 session report: deterministic havoc pivot
63e88d3 Phase 6/7 Path B: infrastructure + P2/P3 probes validated
85cecb5 Bring main design doc into repo plans/
```

## Next Session Work Plan

### Phase A — pivot (Steps 1–5 of old plan, ~450 LOC total)

Goal: deterministic `ArmStep` + `step_count_state_uniqueness` + Phase 7d.

1. **Add opaque havoc functions** in
   [`CredibleCompilation/ArmDefs.lean`](../CredibleCompilation/ArmDefs.lean):

   ```lean
   opaque havocRegsFn : ArmState → ArmReg → BitVec 64
   opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64
   ```
   ~15 LOC including docstring.

2. **Refactor 5 `ArmStep` libcall constructors** in
   [`CredibleCompilation/ArmSemantics.lean`](../CredibleCompilation/ArmSemantics.lean):
   drop `(newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64)`
   arguments; use `havocRegsFn s`, `havocFRegsFn s` inline.
   Constructors: `printCall`, `callPrintI`, `callPrintB`, `callPrintF`,
   `callPrintS`, `callBinF`, `floatUnaryLibCall`.
   ~20 LOC.

3. **Update 19 call sites** (PE2 classified, see below):
   - `ArmSemantics.lean` (6 sites in `ArmStep_total_of_codeAt`): trivial,
     drop `(fun _ => 0) (fun _ => 0)` witnesses.
   - `ArmCorrectness.lean` (6 sites in forward sim): each has pattern
     `let newRegs := fun _ => 0; let newFregs := fun _ => 0; let s2 := ...
     .callPrintX newRegs newFregs hCodeCall`.  Update `s2` definition
     to use `havocRegsFn`/`havocFRegsFn`; drop args.  Standard proofs
     (e.g., `havocCallerSaved_preserved`) are generic — no proof rework.
   - `CodeGen.lean` (7 sites in `verifiedGenerateAsm_spec`): same
     pattern.  ~15 LOC per site.
   - `PipelineCorrectness.lean` § 10b: update `ArmStep.pc_eq_armNextPC`
     binder counts (remove `_ _` for havoc args in the 5 libcall
     cases).  ~20 LOC.

   **Total Step 3**: ~210 LOC mechanical.

   After Step 3, run `lake build` — should be green with same sorry
   count as before (9).

4. **Prove `arm_step_det`** via the projection trick validated in PD2:

   ```lean
   private def armStepResult (s : ArmState) (i : ArmInstr) : ArmState := ...
   private theorem ArmStep.eq_armStepResult (h : ArmStep prog s s') :
       ∃ i, prog[s.pc]? = some i ∧ s' = armStepResult s i := ...
   theorem arm_step_det {prog s s₁ s₂}
       (h1 : ArmStep prog s s₁) (h2 : ArmStep prog s s₂) : s₁ = s₂ := ...
   ```

   Clone `PivotProbePD2.lean`'s structure for 5 constructors.  Scaling
   to ~50 constructors is mechanical pattern-matching.  ~100 LOC.

5. **Prove `step_count_state_uniqueness`** in PipelineCorrectness.lean:
   direct induction via `arm_step_det`.  ~15 LOC (exact template in
   `PivotProbePD2.lean`).  Also fill the existing
   `step_count_pc_uniqueness` sorry as a 3-line corollary.

**Checkpoint after Phase A**: 9 → 8 sorrys (`step_count_pc_uniqueness`
filled).  Commit as "Phase A: deterministic havoc + state_uniqueness
landed."

### Phase B — Fix B' + Phase 7d (~310 LOC)

Goal: handle source-divergence bin for all Phase 7 theorems.

6. **Port probes to PipelineCorrectness.lean**: copy
   `arm_self_loop_diverges`, `arm_diverges_of_prefix_reaches_self_loop`,
   `tac_goto_self_loop_implies_arm_self_loop` from the probe files.
   ~80 LOC (already proven — transfer takes minimal effort).

7. **Prove `tac_iftrue_self_loop_implies_arm_self_loop`**
   (`.ifgoto be pc` with `be.eval = true`).  Similar to PF2' but
   navigates `.ifgoto`'s 3-arm be match.  ~60 LOC.  Reference the
   `.binop .div` / `.goto` probes in § 10 of PipelineCorrectness.lean
   and PE3 for the pattern.

8. **Prove `source_diverges_gives_ArmDiverges_init`** — the
   composition theorem.  Induction on TAC prefix length with case
   split: if any TAC step is a self-loop, apply
   `arm_diverges_of_prefix_reaches_self_loop`; else, use the fact that
   non-self-loop TAC steps produce non-refl ArmSteps (via ExtSimRel
   forcing state change).  ~120 LOC.

9. **Add `has_behavior_init` wrapper** in PropChecker.lean to
   strengthen `has_behavior`'s conclusion to `program_behavior_init`
   (fixing `am₀ = ArrayMem.init`).  Update `pipelined_has_behavior` to
   use it.  ~15 LOC.

10. **Phase 7d** — `arm_diverges_implies_while_diverges`:
    Case on `pipelined_has_behavior_init`:
    - halts/errors: forward sim → contradiction via
      `step_count_state_uniqueness` + `sentinel_stuck`.
    - typeErrors: `pipelined_no_typeError`.
    - diverges: existing `while_to_arm_divergence_preservation`.
    ~35 LOC.

**Checkpoint after Phase B**: 8 → 7 sorrys.  Commit.

### Phase C — Phase 7a/b/c (~220 LOC)

11. **Phase 7b** (`arm_div_implies_while_unsafe_div`): case on source
    behavior.  Halts/errors-bounds/typeErrors: contradict via state
    uniqueness + sentinel distinctness (`divS ≠ haltFinal`,
    `divS ≠ boundsS`).  Errors-div: direct via
    `while_to_arm_div_preservation`.  Diverges: contradict via Fix B'
    (`source_diverges_gives_ArmDiverges_init` gives `ArmDiverges`; then
    contradict with `sentinel_stuck` on `s.pc = divS`).  ~60 LOC.

12. **Phase 7c** — symmetric to 7b with `boundsS`.  ~60 LOC.

13. **Phase 7a** (`arm_halts_implies_while_halts`): case on source.
    Halts bin: forward sim gives `s_fwd` with `ExtStateRel σ_src s_fwd`
    and `s_fwd.pc = haltFinal`.  `step_count_state_uniqueness` gives
    `s = s_fwd`, so observables at `s` match `σ_src`.  Under the pivot,
    `halt_state_observables_deterministic` helper is subsumed by state
    uniqueness — close inline without a separate helper.  ~80 LOC.

14. **Close `halt_state_observables_deterministic` sorry**: becomes
    direct corollary of `step_count_state_uniqueness` applied at
    lengths k₁ = k₂ = min(k_fwd, k_hyp) or similar.  ~15 LOC (collapses
    from the design doc's 100 LOC estimate).

**Checkpoint after Phase C**: 7 → 3 sorrys (Phase 7a/b/c/d done +
halt observables).  Commit as "Phase 7 complete."

### Remaining after Next Session

Still open for full 0-sorry:
- `bodyFlat_branch_target_bounded` (Phase 6, 14-case sweep) — ~600 LOC
- `arm_behavior_exhaustive` (Phase 6 König) — ~100 LOC
- `verifiedGenInstr_ifgoto_branch_bounded` probe — subsumed by sweep

These are **Phase 6 exhaustion only** — not required for Phase 7
closure.  Do in a separate session if desired.

## Total budget summary

| Phase | LOC | Sorry change | Confidence |
|---|---|---|---|
| A — pivot + state_uniqueness | ~450 | 9 → 8 | 90% (probes validated) |
| B — Fix B' + 7d | ~310 | 8 → 7 | 80% |
| C — 7a/b/c + halt obs | ~220 | 7 → 3 | 80% |
| **Phase 7 total** | **~980** | **9 → 3** | **~75%** |
| D — Phase 6 exhaustion (optional) | ~700 | 3 → 0 | 65% |

Net: 6 sorrys closed for full Phase 7 in ~980 LOC.  9 sorrys closed in
~1680 LOC for full Phase 6/7.

## Risk tracker

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Step 3 call-site rewrite has hidden non-mechanical sites | 20% | +50 LOC | PE2 enumerated all 19; spot-checked each pattern. |
| Step 4 `armStepResult` ~50-constructor enumeration hits compile-time | 15% | +1hr | Tier by structure: seq (~40), two-branch (~6), havoc (~5).  Clone PD2 pattern exactly. |
| Step 8 `source_diverges_gives_ArmDiverges_init` composition harder than estimated | 30% | +80 LOC | Well-defined induction; probe PF1' validates core primitives. |
| Step 13 Phase 7a's observable match needs more than state uniqueness | 25% | +30 LOC | State uniqueness is strictly stronger than PC uniqueness; observable-match inline via ExtStateRel. |
| `has_behavior_init` wrapper turns out >30 LOC | 20% | +20 LOC | Internal of `has_behavior` already gives `ArrayMem.init`; wrapper is just signature tightening. |

## Session prep checklist

Before starting:
- [ ] Read this document end-to-end.
- [ ] Skim [`CCTests/Tests/PivotProbePD2.lean`](../CCTests/Tests/PivotProbePD2.lean) (the `arm_step_det` blueprint).
- [ ] Skim [`CCTests/Tests/PivotProbePF1.lean`](../CCTests/Tests/PivotProbePF1.lean) and [`CCTests/Tests/PivotProbePF2.lean`](../CCTests/Tests/PivotProbePF2.lean) (Fix B' blueprints).
- [ ] Confirm `lake build` on commit `4094678` is green (baseline sanity).
- [ ] Have an enumeration of the 19 call sites handy (PE2 output in
      `phase6-7-pivot-probe-findings.md`).

## Key files and their purposes

| File | Purpose |
|---|---|
| [`CredibleCompilation/PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean) | Phase 6/7 theorems + infrastructure. Main workspace. |
| [`CredibleCompilation/ArmDefs.lean`](../CredibleCompilation/ArmDefs.lean) | Where opaque `havocRegsFn`/`havocFRegsFn` live. |
| [`CredibleCompilation/ArmSemantics.lean`](../CredibleCompilation/ArmSemantics.lean) | `ArmStep` inductive.  5 libcall constructors to refactor. |
| [`CredibleCompilation/ArmCorrectness.lean`](../CredibleCompilation/ArmCorrectness.lean) | Forward sim.  6 call sites need updating. |
| [`CredibleCompilation/CodeGen.lean`](../CredibleCompilation/CodeGen.lean) | Codegen + spec.  7 call sites need updating. |
| [`CredibleCompilation/PropChecker.lean`](../CredibleCompilation/PropChecker.lean) | `has_behavior`.  Add `has_behavior_init` wrapper. |
| [`CCTests/Tests/PivotProbe*.lean`](../CCTests/Tests/) | Probe files.  Blueprints to clone. |
| [`plans/phase6-7-NEXT-SESSION.md`](phase6-7-NEXT-SESSION.md) | This document. |
| [`plans/phase6-7-deterministic-pivot-plan.md`](phase6-7-deterministic-pivot-plan.md) | Original pivot plan.  SUPERSEDED — see header note. |
| [`plans/phase6-7-pivot-probe-findings.md`](phase6-7-pivot-probe-findings.md) | PD1/PD2/PD3 probe findings. |
| [`plans/phase6-7-session-report-2026-04-22.md`](phase6-7-session-report-2026-04-22.md) | Session 1 process report. |
| [`plans/backward-jumping-octopus.md`](backward-jumping-octopus.md) | Master plan doc.  Phase 6/7 checkpoints. |
| [`plans/backward-jumping-octopus-phase6-design.md`](backward-jumping-octopus-phase6-design.md) | Original Phase 6 design. |
| [`plans/backward-jumping-octopus-phase5b-design.md`](backward-jumping-octopus-phase5b-design.md) | Phase 5b design (not on critical path). |

## One-liner summary for fast handoff

**Pivot + Fix B', order: refactor ArmStep → arm_step_det → state_uniqueness → 7d → 7b → 7c → 7a.  Budget ~980 LOC.  All blueprints in `CCTests/Tests/PivotProbe*.lean`.  9 sorrys → 3 sorrys.  No changes needed to TAC, passes, ExtSimRel, or top-level theorems.**
