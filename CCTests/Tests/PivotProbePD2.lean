/-
# PD2 — Minimal `arm_step_det` probe

Defines a miniature deterministic-havoc `ArmStepDet` inductive with
5 representative rules covering all the relevant constructor shapes:
  - sequential non-branch (`mov`)
  - two-branch with reg-based condition (`cbz_taken`, `cbz_fall`)
  - havoc rule (`printCall`)
  - havoc + result-write rule (`callBinF`)

Proves `arm_step_det : ArmStepDet prog s s₁ ∧ ArmStepDet prog s s₂ →
s₁ = s₂` via the projection trick.  This validates whether the same
approach used in `arm_step_pc_det` (Nat-valued projection) scales to
full state equality (ArmState record).
-/

import CredibleCompilation.ArmSemantics

namespace PivotProbePD2

open ArmState

opaque havocRegsFn : ArmState → ArmReg → BitVec 64
opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64

/-- Miniature deterministic ArmStep: 5 rules covering every structural
    shape the full refactor will need.  The key difference from the
    real `ArmStep`: libcall constructors don't take `newRegs`/`newFregs`
    args — they use `havocRegsFn s` and `havocFRegsFn s` instead. -/
inductive ArmStepDet (prog : ArmProg) : ArmState → ArmState → Prop where
  | mov (rd : ArmReg) (imm : BitVec 64) :
      prog[s.pc]? = some (.mov rd imm) →
      ArmStepDet prog s (s.setReg rd imm |>.nextPC)
  | cbz_taken (rn : ArmReg) (lbl : Nat) :
      prog[s.pc]? = some (.cbz rn lbl) →
      s.regs rn = (0 : BitVec 64) →
      ArmStepDet prog s { s with pc := lbl }
  | cbz_fall (rn : ArmReg) (lbl : Nat) :
      prog[s.pc]? = some (.cbz rn lbl) →
      s.regs rn ≠ (0 : BitVec 64) →
      ArmStepDet prog s s.nextPC
  | printCall (lines : List String) :
      prog[s.pc]? = some (.printCall lines) →
      ArmStepDet prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
        |>.nextPC)
  | callBinF (fop : FloatBinOp) (fd fn fm : ArmFReg) :
      prog[s.pc]? = some (.callBinF fop fd fn fm) →
      ArmStepDet prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
        |>.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC)

/-- Pure function computing the deterministic successor state from
    state + instruction.  Mimics what the full `armStepResult` will
    look like; only covers the 5 instructions `ArmStepDet` handles. -/
def armStepResult (s : ArmState) (i : ArmInstr) : ArmState :=
  match i with
  | .mov rd imm => s.setReg rd imm |>.nextPC
  | .cbz rn lbl =>
      if s.regs rn = (0 : BitVec 64) then { s with pc := lbl } else s.nextPC
  | .printCall _ =>
      s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .callBinF fop fd fn fm =>
      s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
        |>.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC
  | _ => s.nextPC  -- placeholder; irrelevant because ArmStepDet's other
                   -- cases don't fire on other instructions.

/-- Projection: every ArmStepDet fires with a specific instruction at
    s.pc, and the successor is armStepResult applied to s and that
    instruction. -/
theorem ArmStepDet.eq_armStepResult {prog s s'} (h : ArmStepDet prog s s') :
    ∃ i, prog[s.pc]? = some i ∧ s' = armStepResult s i := by
  cases h with
  | mov rd imm hi => exact ⟨_, hi, rfl⟩
  | cbz_taken rn lbl hi hz =>
      exact ⟨_, hi, by simp only [armStepResult, if_pos hz]⟩
  | cbz_fall rn lbl hi hnz =>
      exact ⟨_, hi, by simp only [armStepResult, if_neg hnz]⟩
  | printCall lines hi => exact ⟨_, hi, rfl⟩
  | callBinF fop fd fn fm hi => exact ⟨_, hi, rfl⟩

/-- **PD2 main result**: two ArmStepDet from the same state produce
    the same next state.  Full state equality, not just PC. -/
theorem arm_step_det {prog : ArmProg} {s s₁ s₂ : ArmState}
    (h1 : ArmStepDet prog s s₁) (h2 : ArmStepDet prog s s₂) : s₁ = s₂ := by
  obtain ⟨i1, hi1, he1⟩ := h1.eq_armStepResult
  obtain ⟨i2, hi2, he2⟩ := h2.eq_armStepResult
  have : i1 = i2 := Option.some.inj (hi1 ▸ hi2)
  rw [he1, he2, this]

/-- Verify arm_step_det composes cleanly into a step_count_state_uniqueness
    by direct induction — the Step 4 target shape. -/
def ArmStepsN_det (prog : ArmProg) : ArmState → ArmState → Nat → Prop
  | s, s', 0     => s = s'
  | s, s', n + 1 => ∃ s'', ArmStepDet prog s s'' ∧ ArmStepsN_det prog s'' s' n

theorem step_count_state_uniqueness_mini {prog : ArmProg} {s₀ : ArmState} :
    ∀ n (s₁ s₂ : ArmState),
      ArmStepsN_det prog s₀ s₁ n → ArmStepsN_det prog s₀ s₂ n → s₁ = s₂ := by
  intro n
  induction n generalizing s₀ with
  | zero =>
      intro s₁ s₂ h1 h2
      change s₀ = s₁ at h1
      change s₀ = s₂ at h2
      subst h1; subst h2; rfl
  | succ n ih =>
      intro s₁ s₂ h1 h2
      obtain ⟨m₁, hs₁, hr₁⟩ := h1
      obtain ⟨m₂, hs₂, hr₂⟩ := h2
      have hmid : m₁ = m₂ := arm_step_det hs₁ hs₂
      subst hmid
      exact ih _ _ hr₁ hr₂

end PivotProbePD2
