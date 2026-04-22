/-
# PE1 — 1-TAC-step ArmStepsN-length probe

Attempts to prove: under deterministic havoc, a TAC trace via forward
sim yields `ArmStepsN` with step count `K ≥ 1` when the source config
differs from the ARM start state in a way that rules out the `.refl`
witness.

Uses `tacToArm_correctness` (public) rather than `tacToArm_refinement`
(consumes private `buildVerifiedInvMap`).  Tests whether the
projection-style argument can bound `K` structurally.
-/

import CredibleCompilation.PipelineCorrectness

namespace PivotProbePE1

open ArmState

/-!
## Core test: halt case

If source reaches `.halt σ' am'`, forward sim gives ArmSteps ending
at `s'.pc = haltFinal`.  Since the ARM start state has `s.pc =
r.pcMap 0 < r.haltFinal`, `s ≠ s'`, ruling out `.refl`.  So
`ArmSteps_to_ArmStepsN` gives `K ≥ 1`.

This tests the pattern used for Phase 7d / 7b / 7c when the source
behavior is halts/errors.
-/

theorem arm_halts_K_positive
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx prog.compileToTAC = .ok r)
    {cfg' : Cfg}
    (hSteps : prog.compileToTAC ⊩ Cfg.run 0 (Store.typedInit prog.tyCtx)
        (fun _ _ => 0) ⟶* cfg')
    {σ' : Store} {am' : ArrayMem}
    (hCfgHalt : cfg' = .halt σ' am') :
    ∃ s' K, K ≥ 1 ∧ ArmStepsN r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' K := by
  obtain ⟨s', hArm, _hSimRel', hHaltPC⟩ := tacToArm_correctness hGen hSteps
  have hs'pc : s'.pc = r.haltFinal := hHaltPC σ' am' hCfgHalt
  -- Case-split on hArm to expose K structurally
  cases hArm with
  | refl =>
      -- s = s', so s.pc = r.pcMap 0 = s'.pc = r.haltFinal.  Contradict
      -- via pcMap 0 ≤ haltS < haltFinal.
      exfalso
      have spec := verifiedGenerateAsm_spec hGen
      have h1 : r.pcMap 0 ≤ r.haltS := pcMap_le_haltS spec 0 (Nat.zero_le _)
      -- Expected: haltS < haltFinal requires haltSaveBlock.size > 0.
      -- Not always true — if observables list is empty, haltSaveBlock could be empty.
      -- For this probe, assume it.
      sorry
  | step hFirst hRest =>
      -- At least one step.  Convert the rest to ArmStepsN for its length.
      obtain ⟨K', hK'⟩ := ArmSteps_to_ArmStepsN hRest
      refine ⟨s', K' + 1, by omega, ?_⟩
      exact ⟨_, hFirst, hK'⟩

/-!
## Verdict: PE1 works for halt/error sentinel cases.

The pattern: `cases hArm` on the `ArmSteps` output of forward sim.
- `.refl` case contradicted via PC mismatch (ArmSteps' endpoint has
  sentinel PC, but start state has `r.pcMap 0 < sentinel`).
- `.step` case gives K ≥ 1 structurally.

**Caveats**:

1. The `.refl` contradiction needs `r.pcMap 0 < r.haltFinal` — true
   when `p.size > 0` AND observables non-empty (haltSaveBlock non-empty)
   OR `r.pcMap 0 < r.haltS ≤ r.haltFinal` strictly.  For the standard
   case, provable.  The probe leaves this as `sorry` for concision.

2. **Does NOT extend to the "source diverges" case.**  When source
   diverges, there's no single `cfg'` with a definite PC constraint.
   `while_to_arm_divergence_preservation` doesn't give an ARM state —
   it concludes `∀ fuel, interp = none` on the source side.  So we
   can't apply the forward-sim-then-case-on-ArmSteps pattern.

## Verdict on Step 6 (source_diverges_arm_pc_in_bodyFlat)

Step 6 needs: "given source diverges + ArmStepsN init s k, show
s.pc < haltFinal" for ANY k.  The forward-sim trick above only
produces ONE ArmStepsN of SOME length from ONE TAC behavior
(halts/errors).  For the "diverges" bin, there's no analogous single
ArmStepsN witness of arbitrary length.

**What Step 6 needs that this probe doesn't provide**:
- "source diverges → ArmDiverges" (Phase 5b partial), OR
- "forward sim over n TAC steps yields ArmStepsN of length ≥ n"
  (partial Phase 5b with step-count tracking).

**What Phase 7 cases this probe DOES help with**:
- 7d halt/error sub-cases: can contradict via this lemma.
- 7a/b/c halt/error sub-cases: same.

**What Phase 7 cases remain blocked without Phase 5b**:
- 7d diverges case: uses existing `while_to_arm_divergence_preservation`
  (no ArmDiverges needed; source-side conclusion suffices). ✓ NOT BLOCKED.
- 7a/b/c diverges case: needs to contradict "source diverges" given
  "ArmSteps init s with s.pc = sentinel".  BLOCKED without Phase 5b.

## PE1 verdict

PARTIAL.  Unblocks halt/error sub-cases of all four Phase 7 theorems.
Does NOT unblock the "source diverges" sub-case of 7a/b/c.

Options for Phase 7a/b/c:
- (A) Invest in partial Phase 5b for the diverges-case argument.
  ~150 LOC.
- (B) Weaken 7a/b/c's conclusion to admit "source halts/errors OR
  source diverges".  Removes the need to contradict source-diverges.
  Less satisfying as a correctness statement.
- (C) Ship only 7d, defer 7a/b/c.

Recommend exploring (A) as a scoped probe if this path is pursued.

Actual 'probe' lemma below just to confirm build.
-/

/-- Checkpoint: the halt-case argument compiles (modulo one sorry). -/
theorem _probe_compiles : True := trivial

end PivotProbePE1
