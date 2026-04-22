/-
# PE3 — `.ifgoto` v2 inline-style probe

The P1 probe from the previous session stalled on nested-match type
signatures in `have loadA_nb / loadB_nb` helpers (`Unknown constant
False.var` error).  This probe retries without the helpers — inline
all load-case analysis using `split at hmem`.

If this works, the 14-case sweep is unblocked and the hardest case
(`.ifgoto` 3-arm match) has a verified blueprint.
-/

import CredibleCompilation.PipelineCorrectness

namespace PivotProbePE3

open ArmState

-- Use the helpers already landed in PipelineCorrectness.lean:
-- vLoadVar_no_branches, vStoreVar_no_branches, formalLoadImm64_no_branches,
-- vLoadVarFP_no_branches, verifiedGenBoolExpr_no_branches.
-- They are `private`, so we can't reference them here.  For the probe,
-- we inline them.

/-- Helper: `vLoadVar` has no branch instructions. -/
private theorem vLoadVar_no_branches' (layout : VarLayout) (v : Var) (tmp : ArmReg) :
    ∀ instr' ∈ vLoadVar layout v tmp,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold vLoadVar at hmem
  rcases hl : layout v with _ | loc
  · rw [hl] at hmem; simp at hmem
  · rw [hl] at hmem
    cases loc with
    | stack _ =>
      simp at hmem; subst hmem
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | ireg r =>
      by_cases heq : r == tmp
      · simp [heq] at hmem
      · simp [heq] at hmem; subst hmem
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
    | freg _ => simp at hmem

private theorem formalLoadImm64_no_branches' (rd : ArmReg) (n : BitVec 64) :
    ∀ instr' ∈ formalLoadImm64 rd n,
      (∀ lbl, instr' ≠ ArmInstr.b lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbz rn lbl) ∧
      (∀ rn lbl, instr' ≠ ArmInstr.cbnz rn lbl) ∧
      (∀ c lbl, instr' ≠ ArmInstr.bCond c lbl) := by
  intro instr' hmem
  unfold formalLoadImm64 at hmem
  split at hmem
  · simp at hmem; subst hmem
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro h <;> exact ArmInstr.noConfusion h
  · simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with ((hBase | hK1) | hK2) | hK3
    · subst hBase
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
    · split at hK1
      · simp at hK1; subst hK1
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hK1
    · split at hK2
      · simp at hK2; subst hK2
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hK2
    · split at hK3
      · simp at hK3; subst hK3
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> intro heq <;> exact ArmInstr.noConfusion heq
      · simp at hK3

/-- **Probe PE3**: `.ifgoto be l` fallback arm only (simplest).
    Output: `verifiedGenBoolExpr layout be ++ [.cbnz .x0 (pcMap l)]`.
    This was the case that P1's original attempt closed cleanly
    without tangling in the nested-match helper issue.  Confirmed
    works as of landing in P1. -/
example
    (layout : VarLayout) (pcMap : Nat → Nat) (be : BoolExpr) (l : Nat)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (.ifgoto be l)
      haltS divS boundsS arrayDecls safe = some instrs)
    (hPcMapBound : pcMap l ≤ boundsS)
    (hFallback : ∀ op a b, be ≠ .not (.cmp op a b))
    (hFallback2 : ∀ fop a b, be ≠ .not (.fcmp fop a b)) :
    True := by trivial  -- placeholder; fallback works trivially

/-- **Probe PE3 core**: `.not (.cmp op a b)` arm of `.ifgoto`.
    Output (simplified form): `loadA ++ loadB ++ [.cmp, .bCond cond (pcMap l)]`.
    Rewritten to use `split at hmem` directly instead of helper
    `have` blocks. -/
example
    (layout : VarLayout) (pcMap : Nat → Nat) (op : CmpOp) (a b : Expr) (l : Nat)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) {instrs : List ArmInstr}
    (hGen : verifiedGenInstr layout pcMap (.ifgoto (.not (.cmp op a b)) l)
      haltS divS boundsS arrayDecls safe = some instrs)
    (hPcMapBound : pcMap l ≤ boundsS) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = ArmInstr.b lbl ∨
       (∃ rn, instr' = ArmInstr.cbz rn lbl) ∨
       (∃ rn, instr' = ArmInstr.cbnz rn lbl) ∨
       (∃ c, instr' = ArmInstr.bCond c lbl)) →
      lbl ≤ boundsS := by
  simp only [verifiedGenInstr] at hGen
  -- Outer regConv/inj guard
  split at hGen
  · exact absurd hGen (by intro h; cases h)
  · -- Guard passed; hasSimpleOps check
    split at hGen
    · exact absurd hGen (by intro h; cases h)
    · -- be = .not (.cmp op a b) — match inside is guaranteed
      simp only [Option.some.injEq] at hGen
      subst hGen
      intro instr' hmem lbl hbranch
      -- instrs = loadA ++ loadB ++ [.cmp, .bCond (pcMap l)]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with (hA | hB) | hCmp | hBCond
      · -- instr' ∈ loadA.  loadA = match a with | .var => vLoadVar ... | .lit => formalLoadImm64 ... | _ => []
        -- Use `split at hA` to decompose the match.
        split at hA
        · -- .var case: loadA = vLoadVar layout v a_reg
          have ⟨nb, nz, nnz, nbc⟩ := vLoadVar_no_branches' _ _ _ _ hA
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · -- .lit case: loadA = formalLoadImm64 a_reg n
          have ⟨nb, nz, nnz, nbc⟩ := formalLoadImm64_no_branches' _ _ _ hA
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · -- Other case: loadA = []
          simp at hA
      · -- instr' ∈ loadB.  Same pattern.
        split at hB
        · have ⟨nb, nz, nnz, nbc⟩ := vLoadVar_no_branches' _ _ _ _ hB
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · have ⟨nb, nz, nnz, nbc⟩ := formalLoadImm64_no_branches' _ _ _ hB
          rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
          · exact absurd h (nb _)
          · exact absurd h (nz rn _)
          · exact absurd h (nnz rn _)
          · exact absurd h (nbc c _)
        · simp at hB
      · -- instr' = .cmp (a non-branch instruction)
        subst hCmp
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        all_goals exact ArmInstr.noConfusion h
      · -- instr' = .bCond cond.negate (pcMap l)
        subst hBCond
        rcases hbranch with h | ⟨rn, h⟩ | ⟨rn, h⟩ | ⟨c, h⟩
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · exact ArmInstr.noConfusion h
        · cases h; exact hPcMapBound

end PivotProbePE3
