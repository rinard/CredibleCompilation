# Phase 6/7 Pivot — Probe Findings Addendum

Addendum to `plans/phase6-7-deterministic-pivot-plan.md` recording
results of the three derisk probes run before starting the pivot.
Probes are at
`CCTests/Tests/PivotProbePD{1,2,3}.lean` on branch `phase6-prep`.

## Probe outcomes

| Probe | Status | Time | Verdict |
|---|---|---|---|
| PD1 — Opaque function interaction | ✅ PASSED | ~15 min | Zero issues.  Opaque works with rfl/simp/exact/rw/existentials/constructors.  No fallback needed. |
| PD2 — Minimal `arm_step_det` for 5 constructors | ✅ PASSED | ~30 min, first try | Projection approach scales to full ArmState equality.  Compiled clean.  Scaling to 50 constructors is mechanical. |
| PD3 — Forward-sim composability | ⚠️ SIGNATURE ONLY | ~45 min | Step 6 LOC estimate revised from ~80 to ~150.  Proof requires either partial Phase 5b refactor or inline step-count-tracking composition. |

## Confidence updates

### Steps 1–5 (ArmStep refactor + `arm_step_det` + `step_count_state_uniqueness` + 7d)

**Confidence up** from 85% to 95% for each step.  PD1 removes the
"opaque misbehaves" risk entirely.  PD2 validates the projection
approach — scaling to 50 constructors is a pure copy-paste exercise
(~100 LOC).  No surprises expected.

Total Steps 1–5 LOC unchanged at ~350 LOC.

### Step 6 (source_diverges_arm_pc_in_bodyFlat)

**Confidence down** from 65% to 55%.  PD3 revealed that the proof
requires lower-bounding the ArmStepsN length from tacToArm_refinement,
which `ArmSteps_to_ArmStepsN` loses.  Two routes:

- (a) Invest in the Phase 5b `step_simulation` refactor to return
  ArmStepsN with explicit length.  ~150 LOC.
- (b) Roll our own step-count tracking inline.  ~100 LOC.

Plus ~50 LOC for the outer induction over TAC prefix lengths.

**Revised Step 6 estimate**: ~150 LOC (was 80).  Additional 50 LOC if
we pursue the stricter "for all k ≤ K, intermediate PC is in bodyFlat"
variant vs the weaker "for this K only" variant.

### Steps 7–8 (Phase 7b/c/a)

**Unchanged**.  ~260 LOC total.  Depends on Step 6 completing.

## Revised total pivot budget

From the original plan's ~690 LOC:

| Step | Original LOC | Revised LOC | Delta |
|---|---|---|---|
| 1. ArmStep refactor | 30 | 30 | 0 |
| 2. Call-site updates | 150 | 150 | 0 |
| 3. arm_step_det | 100 | 100 | 0 |
| 4. step_count_state_uniqueness | 20 | 20 | 0 |
| 5. Phase 7d | 50 | 50 | 0 |
| 6. source_diverges helper | 80 | **150** | +70 |
| 7. Phase 7b/c | 180 | 180 | 0 |
| 8. Phase 7a | 80 | 80 | 0 |
| **Total** | **~690** | **~760** | **+70** |

## Recommendations based on probes

### 1. Steps 1–5 are safe to execute as planned

All risks derisked.  The refactor ripple (Step 2 call-site count) is
still unknown in absolute numbers but not in nature — just mechanical.
Run a grep to enumerate sites before starting.

### 2. Add an early checkpoint for Step 6

Before writing the full `source_diverges_arm_pc_in_bodyFlat`, run a
micro-probe inside the pivot session:

**Micro-probe**: prove "forward sim of 1 TAC step gives ArmStepsN init
s 1 or greater" for a single TAC step (not composed).  If this takes
more than an hour, the full Step 6 will take 4+ hours.

If the micro-probe stalls, pivot to partial delivery: land Step 5
(Phase 7d) and defer 7a/b/c.

### 3. Consider weaker claim variant

The target helper's claim can be weakened to:

```lean
-- Weak form: just this K, not all k ≤ K
theorem source_diverges_arm_pc_in_bodyFlat_weak
    ... (k : Nat) {s : ArmState}
    (hArm : ArmStepsN r.bodyFlat init s k) :
    s.pc < r.haltFinal
```

vs the stronger:

```lean
-- Strong form: for all intermediate k' ≤ k
theorem source_diverges_arm_pc_in_bodyFlat_strong
    ... (k : Nat) :
    ∀ k' ≤ k, ∀ s, ArmStepsN r.bodyFlat init s k' → s.pc < r.haltFinal
```

The weak form is sufficient for Phase 7a/b/c's needs (each theorem
applies the helper once at a specific K).  Strong form costs ~50 LOC
more without buying anything for 7a/b/c.

**Recommendation**: write the weak form.  If a future theorem needs
the strong form, upgrade then.

### 4. Escape hatch: partial delivery at Step 5

If Step 6 is consumed by the positivity problem, commit Steps 1–5
(deterministic model + arm_step_det + step_count_state_uniqueness +
7d) as a self-contained delivery.  Phase 7 would be "1 of 4 theorems
closed plus full determinism available to future work."

This is a meaningful checkpoint even without 7a/b/c.

## Artifact locations

- `CCTests/Tests/PivotProbePD1.lean` — opaque interaction tests.
- `CCTests/Tests/PivotProbePD2.lean` — mini `ArmStepDet` + `arm_step_det`
  + `step_count_state_uniqueness_mini`.  **Valuable blueprint**; when
  writing the full versions, clone the proof structure from here.
- `CCTests/Tests/PivotProbePD3.lean` — signature check + detailed
  analysis comments.

These are one-shot probes, not added to `CCTests.lean` imports.  Build
individually via `lake build CCTests.Tests.PivotProbePDN`.  Remove
before merging Phase 6/7 to main, or keep as historical artifacts.

## Session plan (revised)

Given the probe results, next session order of operations:

1. **Review probe files** (~10 min) — refresh the mini `ArmStepDet`
   pattern from PD2 before Step 3.
2. **Run Step 2 call-site grep** — count exact sites before starting.
3. **Execute Steps 1–5** with high confidence.  Budget ~5 hours.
4. **Step 6 micro-probe** at the start of Step 6 — prove 1-TAC-step
   length-positive extraction.  Budget 1 hour; if stalled, commit
   Steps 1–5 and stop.
5. **Execute Step 6 (weak form)** if micro-probe passes.  Budget ~3 hours.
6. **Execute Steps 7–8** if time remains.  Budget ~4 hours.
7. **Commit + CHANGELOG + plan update.**

Total: ~12–14 hours.  Feasible in 2 focused sessions, optimistic for
1.

## Bottom line

- ✅ Pivot is viable.  Pillars (opaque + projection approach) both
  validated.
- ⚠️ Step 6 is harder than the original plan's 80 LOC estimate.
  Budget 150 LOC, prepare for partial delivery fallback.
- 🎯 Target: Steps 1–5 + Phase 7d in one session (5–6 hours);
  Steps 6–8 in a follow-up session if Step 6 cooperates.
