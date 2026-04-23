/-
# FA1 — Flavor A Phase B signature probe

Validates that the new length-tracked return type planned for
`verifiedGenInstr_correct` (Flavor A Phase B) works end-to-end for a
representative `.run` case: `.const x (Value.int n)` with `x` on the stack.

New sig template (per plans/flavor-a-signatures.md § Phase B):
```
∃ s' k, ArmStepsN prog s s' k ∧
    (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
    ExtSimRel layout pcMap divLabel boundsLabel cfg' s'
```

The `.const` stack case exercises the core pattern Phase B will repeat:
- chain a helper (`loadImm64_fregs_preserved`) with a direct ArmStep (`.str`)
- compute total k from helper's hk equality + the +1 for the store step
- discharge `k = instrs.length` under the `.run` implication
- preserve `ExtSimRel` via `.update_stack.nextPC`

If this probe builds green, Phase B's chain pattern is validated and the
remaining ~60 cases are mechanical applications of the same template.

Confidence before probe: medium (A.15's flit+flit fcmp case exercised a
longer chain, but under a different return type without `ExtSimRel`'s
per-cfg' implication).

Build status: TBD — see lake build output after landing this file.
-/

import CredibleCompilation.ArmCorrectness
import CredibleCompilation.CodeGen

namespace PivotProbeFA1

/-- **Probe**: re-prove the `.const` stack sub-case of `verifiedGenInstr_correct`
    under the Flavor A length-tracked return type.

    Preconditions are hand-assembled to match the `.const` case at
    [ArmCorrectness.lean:2219-2247](../../CredibleCompilation/ArmCorrectness.lean#L2219),
    with simplifications: we skip the `match hLocX : layout x with` layer
    and supply `layout x = some (.stack off)` directly.

    The return type differs from the in-file case by replacing
    `∃ s', ArmSteps prog s s' ∧ ExtSimRel ...` with the Phase B form:
    `∃ s' k, ArmStepsN prog s s' k ∧ (cfg' = .run → k = instrs.length) ∧ ExtSimRel ...`.
-/
theorem const_stack_runCase_fa
    (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (_haltLabel divLabel boundsLabel : Nat)
    (pc : Nat) (σ : Store) (am : ArrayMem) (s : ArmState)
    (x : Var) (n : BitVec 64)
    (off : Nat) (hLocX : layout x = some (.stack off))
    (hInjective : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
    (hStateRel : ExtStateRel layout σ s)
    (hPcRel : s.pc = pcMap pc) (hArrayMem : s.arrayMem = am)
    (hCodeInstr : CodeAt prog (pcMap pc)
      (formalLoadImm64 .x0 n ++ vStoreVar layout x .x0))
    (hPcNext : ∀ pc' σ' am',
      (Cfg.run (pc + 1) (σ[x ↦ Value.int n]) am : Cfg) = Cfg.run pc' σ' am' →
      pcMap pc + (formalLoadImm64 .x0 n ++ vStoreVar layout x .x0).length = pcMap pc') :
    let cfg' : Cfg := Cfg.run (pc + 1) (σ[x ↦ Value.int n]) am
    let instrs := formalLoadImm64 .x0 n ++ vStoreVar layout x .x0
    ∃ s' k, ArmStepsN prog s s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
      ExtSimRel layout pcMap divLabel boundsLabel cfg' s' := by
  -- Destructure the block into its two chunks
  have hCodeL := hCodeInstr.append_left
  have hCodeR := hCodeInstr.append_right
  -- Step 1: loadImm64_fregs_preserved — gives k1 = formalLoadImm64.length
  obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
    loadImm64_fregs_preserved prog .x0 n s (pcMap pc) hCodeL hPcRel
  have hRel1 : ExtStateRel layout σ s1 :=
    ExtStateRel.preserved_by_ireg_only hStateRel hRegConv hStack1 hFregs1
      (fun r h0 _ _ => hRegs1 r h0)
  -- Step 2: direct .str step (1 step)
  have hStore := vStoreVar_stack layout x .x0 off hLocX
  rw [hStore] at hCodeR
  have hStr := hCodeR.head; rw [← hPC1] at hStr
  let s2 := s1.setStack off (s1.regs .x0) |>.nextPC
  have hStepStrN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.str .x0 off hStr)
  -- Chain: total k = k1 + 1
  have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hStepsN1 hStepStrN
  refine ⟨s2, k1 + 1, hChain, ?_, ?_, ?_, ?_⟩
  · -- k = instrs.length: only applies when cfg' = .run
    intro pc' σ' am' hCfg
    -- hCfg : Cfg.run (pc+1) ... = Cfg.run pc' σ' am', so by injectivity pc' = pc+1
    rw [hk1]
    simp [List.length_append, hStore]
  · -- ExtStateRel on σ[x ↦ Value.int n]
    show ExtStateRel layout (σ[x ↦ Value.int n]) s2
    have : s1.regs .x0 = (Value.int n).encode := by rw [hx0]; rfl
    rw [show s2 = (s1.setStack off (Value.int n).encode).nextPC from by simp [s2, this]]
    exact (ExtStateRel.update_stack hRel1 hInjective hLocX).nextPC
  · -- s2.pc = pcMap (pc + 1) via hPcNext
    show s2.pc = pcMap (pc + 1)
    have hpcn := hPcNext _ _ _ rfl
    simp [s2, ArmState.nextPC]
    rw [hPC1]
    simp [List.length_append, hStore] at hpcn
    omega
  · -- arrayMem
    show s2.arrayMem = am
    simp [s2, hAM1, hArrayMem]

/- **Outcome**: if this theorem compiles, the Flavor A Phase B return type
   is validated for chain-of-helpers cases. The remaining ~60 cases in
   `verifiedGenInstr_correct` follow the same template with variations:

   - Terminal cases (halt, errorDiv, errorBounds): discharge length claim
     vacuously since `cfg' ≠ .run`.
   - Multi-helper chains (`.binop` normal, `.fbinop` normal): compose
     3-4 helper k-equalities into `k = k_total` with `omega`.
   - Complex FP cases (`.floatUnary` via `fp_exec_and_store`): reuse
     A.11's k = `1 + vStoreVarFP.length`.

   Phase B.0: change the signature, sorry all cases. Phase B.1+: fill
   each case using this template. -/
end PivotProbeFA1
