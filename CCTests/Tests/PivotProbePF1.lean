/-
# PF1' — ArmDiverges from self-loop step

Probes the core Fix B' primitive: `ArmStep prog s s → ArmDiverges prog s`.

If this lands trivially (as expected), Fix B' has its main building
block for handling source divergence via self-loops without needing
step-count positivity or an explicit diverge handler.
-/

import CredibleCompilation.ArmSemantics

namespace PivotProbePF1

/-- **PF1' — ArmDiverges from self-loop step.**  A single ArmStep that
    returns to the same state witnesses divergence: every length `n`
    has a state (namely `s` itself) reachable in `n` steps. -/
theorem arm_self_loop_diverges {prog : ArmProg} {s : ArmState}
    (h : ArmStep prog s s) : ArmDiverges prog s := by
  intro n
  induction n with
  | zero => exact ⟨s, rfl⟩
  | succ k ih =>
      obtain ⟨s'', hk⟩ := ih
      -- hk : ArmStepsN prog s s'' k.  Build (k+1) by prepending the self-step:
      -- ArmStepsN prog s s'' (k+1) = ∃ m, ArmStep prog s m ∧ ArmStepsN prog m s'' k.
      -- Pick m = s via h, then use hk.
      exact ⟨s'', s, h, hk⟩

/-- Convenience: ArmDiverges from a self-loop state, lifted to an
    earlier state via ArmSteps prefix. -/
theorem arm_diverges_of_prefix_reaches_self_loop
    {prog : ArmProg} {init s : ArmState}
    (hReach : ArmSteps prog init s)
    (hSelf : ArmStep prog s s) : ArmDiverges prog init := by
  intro n
  -- From hReach: ArmSteps init s.  Convert to ArmStepsN with some length k.
  obtain ⟨k, hK⟩ := ArmSteps_to_ArmStepsN hReach
  -- From arm_self_loop_diverges: for any m, ArmStepsN prog s _ m.
  have hDiv : ArmDiverges prog s := arm_self_loop_diverges hSelf
  -- For target n: if n ≤ k, truncate hK's prefix.  If n > k, extend hK by n - k.
  by_cases hnk : n ≤ k
  · -- n ≤ k: prefix of hK gives ArmStepsN init _ n
    have : ∃ m, k = n + m := ⟨k - n, by omega⟩
    obtain ⟨m, hm⟩ := this
    rw [hm] at hK
    exact ArmStepsN_prefix hK
  · -- n > k: compose hK (length k) with hDiv (length n - k)
    obtain ⟨s', hDiv'⟩ := hDiv (n - k)
    have heq : k + (n - k) = n := by omega
    refine ⟨s', ?_⟩
    rw [← heq]
    exact ArmStepsN_trans hK hDiv'

end PivotProbePF1
