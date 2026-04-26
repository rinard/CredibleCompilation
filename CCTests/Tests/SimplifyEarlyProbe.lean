import CredibleCompilation.ExecChecker

/-!
# Probe — early-terminating simplify equivalence

The checker speedup work (see `plans/compiler-performance-2026-04-26.md`)
introduced `Expr.simplifyDeepFastEarly`, an early-terminating mirror of
`Expr.simplifyDeepFast`. The proofs in `SoundnessBridge.lean` for
`checkInvariantsPreservedExec` / `checkAllTransitionsExec` /
`checkRelConsistency` need the equivalence

  `e.simplifyDeepFastEarly n m  =  e.simplifyDeepFast n m`

to bridge from the new (live) checker bodies back to the old (proven)
helpers. This probe verifies that the equivalence proof actually goes
through cleanly. If it does, the rest of the proof-repair plan
(checkInvAtomFast = checkInvAtom, BoolExpr.normalizeFast = normalize,
etc.) follows the same template and should be mechanical.
-/

namespace SimplifyEarlyProbe

open Expr

/-- **Probe 1**: applying `simplifyFast` to a fixpoint stays at the
    fixpoint, so `simplifyDeepFast n m e = e` for any `n`. -/
theorem simplifyDeepFast_idempotent_at_fp
    (m : FastVarMap) (e : Expr) (hfp : e.simplifyFast m = e) :
    ∀ n, e.simplifyDeepFast n m = e := by
  intro n
  induction n with
  | zero => exact hfp
  | succ n ih =>
    show (e.simplifyFast m).simplifyDeepFast n m = e
    rw [hfp]; exact ih

/-- **Probe 2**: early-terminating and full-fuel `simplifyDeepFast`
    agree at every fuel. -/
theorem simplifyDeepFastEarly_eq_simplifyDeepFast
    (n : Nat) (m : FastVarMap) (e : Expr) :
    e.simplifyDeepFastEarly n m = e.simplifyDeepFast n m := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    show (let e' := e.simplifyFast m
          if e' == e then e' else e'.simplifyDeepFastEarly n m)
         = (e.simplifyFast m).simplifyDeepFast n m
    by_cases hb : e.simplifyFast m == e
    · -- Fixpoint case: e' == e ⇒ both sides equal e.
      have hfp : e.simplifyFast m = e := by
        exact (beq_iff_eq).mp hb
      simp only [hb, ↓reduceIte]
      rw [hfp]
      exact (simplifyDeepFast_idempotent_at_fp m e hfp n).symm
    · -- Non-fixpoint case: both recurse on `e' := e.simplifyFast m` with fuel `n`.
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ih (e.simplifyFast m)

/-- **Probe 3**: equivalence specialised to the actual call shape used
    in the checker (`FastVarMap.ofList inv` and `sdFuel inv`). This is
    the rewrite the failing proofs need. -/
theorem simplifyDeepFastEarly_eq_simplifyDeep
    (inv : EInv) (e : Expr) :
    e.simplifyDeepFastEarly (sdFuel inv) (FastVarMap.ofList inv)
      = e.simplifyDeep (sdFuel inv) inv := by
  rw [simplifyDeepFastEarly_eq_simplifyDeepFast]
  exact Expr.simplifyDeepFast_eq_simplifyDeep _ e inv

end SimplifyEarlyProbe
