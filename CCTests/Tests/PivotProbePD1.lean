/-
# PD1 — Opaque function interaction probe

Tests whether `opaque` declarations in Lean 4 play nicely with the
tactics we'll need for the deterministic havoc pivot:
  - `rfl` on goals involving opaque applications
  - `simp` over opaque terms
  - `exact h` with opaque-type hypotheses
  - Case analysis and substitution through opaque-dependent values

If any of these misbehave, we'll fall back to `noncomputable def`
via `Classical.choice` or parameterized `ArmStep`.
-/

import CredibleCompilation.ArmDefs

namespace PivotProbePD1

/-- Opaque havoc functions, modeled after what the pivot will add to
    ArmDefs.lean.  Takes an ArmState and returns a register→value
    mapping.  Deterministic given input state, but the function itself
    is unknown. -/
opaque havocRegsFn : ArmState → ArmReg → BitVec 64
opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64

/-- Test 1: `rfl` on a goal with opaque application.  This must work
    because it's reflexivity — same syntactic term on both sides.  If
    this fails, we have a fundamental problem. -/
example (s : ArmState) (r : ArmReg) :
    havocRegsFn s r = havocRegsFn s r := by
  rfl

/-- Test 2: opaque term under a state transformer (mimicking what
    `ArmStep.printCall` will produce).  Two applications with the
    same state should compare equal. -/
example (s : ArmState) :
    s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) =
    s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) := by
  rfl

/-- Test 3: nextPC composition.  The pivot will produce states shaped
    like `(s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).nextPC`
    both sides of an equality. -/
example (s : ArmState) :
    (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).nextPC =
    (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).nextPC := by
  rfl

/-- Test 4: `simp` over a goal that requires unfolding the `nextPC`
    structure but leaving opaque applications alone.  This mirrors the
    projection-style proof `ArmStep.eq_armStepResult` will need. -/
example (s : ArmState) :
    ((s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).nextPC).pc =
    s.pc + 1 := by
  simp [ArmState.nextPC, ArmState.havocCallerSaved_pc]

/-- Test 5: opaque term in a hypothesis, used by `exact`.  Mirrors the
    projection approach where we extract an opaque-dependent expression
    and then use it to close a goal. -/
example (s : ArmState) (h : havocRegsFn s .x3 = (42 : BitVec 64)) :
    havocRegsFn s .x3 = (42 : BitVec 64) := by
  exact h

/-- Test 6: can we rewrite over opaque equalities? -/
example (s s' : ArmState) (heq : s = s') :
    havocRegsFn s .x3 = havocRegsFn s' .x3 := by
  rw [heq]

/-- Test 7: opaque application in the state record, after multiple
    setReg/setFReg operations.  Mimics `callBinF`'s target shape. -/
example (s : ArmState) (fd : ArmFReg) (val : BitVec 64) :
    ((s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).setFReg fd val).nextPC.pc =
    s.pc + 1 := by
  simp [ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved_pc]

-- Test 8 (Lean comment, not `example`): is the opaque function truly
-- opaque? Can Lean guess its value?  Expected: no — the function is
-- irreducible, so this should fail:
--     example (s : ArmState) : havocRegsFn s .x3 = (0 : BitVec 64) := by rfl
-- Uncomment to verify it fails (confirms opaqueness preserved).

/-- Test 9: existential witness with opaque.  Can we claim
    `∃ v, havocRegsFn s r = v` and provide a witness? -/
example (s : ArmState) (r : ArmReg) : ∃ v, havocRegsFn s r = v := by
  exact ⟨havocRegsFn s r, rfl⟩

/-- Test 10: anonymous constructor with opaque applications.  Mimics
    what `ArmStep.eq_armStepResult`'s witness construction will do. -/
example (s : ArmState) : ∃ r v, havocRegsFn s r = v := by
  exact ⟨.x3, havocRegsFn s .x3, rfl⟩

end PivotProbePD1
