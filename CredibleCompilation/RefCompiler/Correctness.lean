import CredibleCompilation.RefCompiler.Defs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-- Extract value from `if c then some (a, b) else none = some (a', b')`. -/
private theorem ite_some_eq_some_pair {c : Bool} {a₁ b₁ : α} {a₂ b₂ : β}
    (h : (if c then some (a₁, a₂) else none) = some (b₁, b₂)) : c = true ∧ a₁ = b₁ ∧ a₂ = b₂ := by
  cases c <;> simp_all

/-!
# Reference Compiler: Correctness Proofs

Monotonicity bounds, expression/boolean/statement compilation correctness,
top-level correctness theorem, and determinism infrastructure.
-/

-- ============================================================
-- § 8. Monotonicity and result bounds
-- ============================================================

theorem refCompileExpr_nextTmp_ge (e : SExpr) (offset nextTmp : Nat) :
    nextTmp ≤ (refCompileExpr e offset nextTmp).2.2 := by
  induction e generalizing offset nextTmp with
  | lit _ => show nextTmp ≤ nextTmp + 1; omega
  | var _ => exact Nat.le_refl _
  | arrRead arr idx ih =>
    dsimp only [refCompileExpr]
    have hi := ih offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hi ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hi ⊢
    omega
  | bin op a b iha ihb =>
    dsimp only [refCompileExpr]
    have ha := iha offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length) tmp1
    generalize refCompileExpr b (offset + codeA.length) tmp1 = rb at hb ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | flit _ => show nextTmp ≤ nextTmp + 1; omega
  | fbin _ a b iha ihb =>
    dsimp only [refCompileExpr]
    have ha := iha offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length) tmp1
    generalize refCompileExpr b (offset + codeA.length) tmp1 = rb at hb ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | intToFloat _ ih =>
    dsimp only [refCompileExpr]
    have hi := ih offset nextTmp
    generalize refCompileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hi ⊢
    omega
  | floatToInt _ ih =>
    dsimp only [refCompileExpr]
    have hi := ih offset nextTmp
    generalize refCompileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hi ⊢
    omega
  | floatExp _ ih =>
    dsimp only [refCompileExpr]
    have hi := ih offset nextTmp
    generalize refCompileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hi ⊢
    omega
  | farrRead _ _ ih =>
    dsimp only [refCompileExpr]
    have hi := ih offset nextTmp
    generalize refCompileExpr _ offset nextTmp = ri at hi ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hi ⊢
    omega

theorem refCompileBool_nextTmp_ge (sb : SBool) (offset nextTmp : Nat) :
    nextTmp ≤ (refCompileBool sb offset nextTmp).2.2 := by
  induction sb generalizing offset nextTmp with
  | lit _ => simp [refCompileBool]
  | bvar x => simp [refCompileBool]
  | cmp _ a b =>
    dsimp only [refCompileBool]
    have ha := refCompileExpr_nextTmp_ge a offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    exact Nat.le_trans ha (refCompileExpr_nextTmp_ge b _ _)
  | not e ih => exact ih offset nextTmp
  | and a b iha ihb =>
    dsimp only [refCompileBool]
    have ha := iha offset nextTmp
    generalize refCompileBool a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length + 1) (tmp1 + 1)
    generalize refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hb ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | or a b iha ihb =>
    dsimp only [refCompileBool]
    have ha := iha offset nextTmp
    generalize refCompileBool a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra; simp at ha ⊢
    have hb := ihb (offset + codeA.length + 1) (tmp1 + 1)
    generalize refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hb ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb; simp at hb ⊢
    omega
  | barrRead arr idx =>
    dsimp only [refCompileBool]
    have hi := refCompileExpr_nextTmp_ge idx offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hi ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hi ⊢
    omega
  | fcmp _ a b =>
    dsimp only [refCompileBool]
    have ha := refCompileExpr_nextTmp_ge a offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at ha ⊢
    exact Nat.le_trans ha (refCompileExpr_nextTmp_ge b _ _)

theorem refCompileExpr_result_bound (e : SExpr) (offset nextTmp : Nat)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    let r := refCompileExpr e offset nextTmp
    (r.2.1.isTmp = false) ∨ (∃ k, nextTmp ≤ k ∧ k < r.2.2 ∧ r.2.1 = tmpName k) := by
  induction e generalizing offset nextTmp with
  | lit _ => right; exact ⟨nextTmp, Nat.le_refl _, by show nextTmp < nextTmp + 1; omega, rfl⟩
  | var x => left; exact htf x (by simp [SExpr.freeVars])
  | arrRead arr idx ih =>
    right
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | bin op a b _ _ =>
    right
    dsimp only [refCompileExpr]
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize refCompileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact ⟨tmp2, Nat.le_trans hge_a hge_b, by omega, rfl⟩
  | flit _ => left; exact ftmpName_not_isTmp nextTmp
  | fbin _ a b _ _ =>
    left
    dsimp only [refCompileExpr]
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize refCompileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact ftmpName_not_isTmp tmp2
  | intToFloat e _ =>
    left
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge e offset nextTmp
    generalize refCompileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ftmpName_not_isTmp tmp1
  | floatToInt e _ =>
    right
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge e offset nextTmp
    generalize refCompileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | floatExp e _ =>
    left
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge e offset nextTmp
    generalize refCompileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ftmpName_not_isTmp tmp1
  | farrRead arr idx _ =>
    left
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact ftmpName_not_isTmp tmp1

theorem refCompileExpr_result_ftmp_bound (e : SExpr) (offset nextTmp : Nat)
    (hftf : ∀ v ∈ e.freeVars, v.isFTmp = false) :
    let r := refCompileExpr e offset nextTmp
    (r.2.1.isFTmp = false) ∨ (∃ k, nextTmp ≤ k ∧ k < r.2.2 ∧ r.2.1 = ftmpName k) := by
  induction e generalizing offset nextTmp with
  | lit _ => left; exact tmpName_not_isFTmp nextTmp
  | var x => left; exact hftf x (by simp [SExpr.freeVars])
  | arrRead arr idx ih =>
    left
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact tmpName_not_isFTmp tmp1
  | bin op a b _ _ =>
    left
    dsimp only [refCompileExpr]
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize refCompileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact tmpName_not_isFTmp tmp2
  | flit _ => right; exact ⟨nextTmp, Nat.le_refl _, by show nextTmp < nextTmp + 1; omega, rfl⟩
  | fbin _ a b _ _ =>
    right
    dsimp only [refCompileExpr]
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    generalize refCompileExpr a offset nextTmp = ra at hge_a ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra; simp at hge_a ⊢
    have hge_b := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    generalize refCompileExpr b (offset + codeA.length) tmp1 = rb at hge_b ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb; simp at hge_b ⊢
    exact ⟨tmp2, Nat.le_trans hge_a hge_b, by omega, rfl⟩
  | intToFloat e _ =>
    right
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge e offset nextTmp
    generalize refCompileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | floatToInt e _ =>
    left
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge e offset nextTmp
    generalize refCompileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact tmpName_not_isFTmp tmp1
  | floatExp e _ =>
    right
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge e offset nextTmp
    generalize refCompileExpr e offset nextTmp = ri at hge ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩
  | farrRead arr idx _ =>
    right
    dsimp only [refCompileExpr]
    have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    exact ⟨tmp1, hge, by omega, rfl⟩

theorem refCompileBool_vars_bound (sb : SBool) (offset nextTmp : Nat)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false) :
    let r := refCompileBool sb offset nextTmp
    ∀ v ∈ r.2.1.vars,
      (v.isTmp = false) ∨ (∃ k, nextTmp ≤ k ∧ k < r.2.2 ∧ v = tmpName k) := by
  induction sb generalizing offset nextTmp with
  | lit _ =>
    simp only [refCompileBool, BoolExpr.vars]
    intro v hv; simp at hv
  | bvar x =>
    simp only [refCompileBool, BoolExpr.vars, List.mem_singleton]
    intro v hv; subst hv
    left; exact htf v (by simp [SBool.freeVars])
  | cmp _ a b =>
    dsimp only [refCompileBool]
    generalize hra : refCompileExpr a offset nextTmp = ra
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [BoolExpr.vars, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
    intro v hv; cases hv with
    | inl h =>
      subst h
      have := refCompileExpr_result_bound a offset nextTmp
        (fun v hv => htf v (List.mem_append_left _ hv))
      rw [hra] at this; simp at this
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        have hge := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
        rw [hrb] at hge; simp at hge
        exact ⟨k, hle, by omega, heq⟩
    | inr h =>
      subst h
      have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
      rw [hra] at hge_a; simp at hge_a
      have := refCompileExpr_result_bound b (offset + codeA.length) tmp1
        (fun v hv => htf v (List.mem_append_right _ hv))
      rw [hrb] at this; simp at this
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        exact ⟨k, by omega, hlt, heq⟩
  | not e ih => exact ih offset nextTmp htf
  | and a b iha ihb =>
    dsimp only [refCompileBool]
    generalize hra : refCompileBool a offset nextTmp = ra
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [BoolExpr.vars, List.mem_singleton]
    intro v hv; subst hv
    right
    have hge_a := refCompileBool_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    have hge_b := refCompileBool_nextTmp_ge b (offset + codeA.length + 1) (tmp1 + 1)
    rw [hrb] at hge_b; simp at hge_b
    exact ⟨tmp1, by omega, by omega, rfl⟩
  | or a b iha ihb =>
    dsimp only [refCompileBool]
    generalize hra : refCompileBool a offset nextTmp = ra
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [BoolExpr.vars, List.mem_singleton]
    intro v hv; subst hv
    right
    have hge_a := refCompileBool_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    have hge_b := refCompileBool_nextTmp_ge b (offset + codeA.length + 1) (tmp1 + 1)
    rw [hrb] at hge_b; simp at hge_b
    exact ⟨tmp1, by omega, by omega, rfl⟩
  | barrRead arr idx =>
    dsimp only [refCompileBool]
    have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
    generalize refCompileExpr idx offset nextTmp = ri at hge ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp at hge ⊢
    simp only [BoolExpr.vars, List.mem_singleton]
    intro v hv; subst hv
    right
    exact ⟨tmp1, hge, by omega, rfl⟩
  | fcmp _ a b =>
    dsimp only [refCompileBool]
    generalize hra : refCompileExpr a offset nextTmp = ra
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [BoolExpr.vars, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
    intro v hv; cases hv with
    | inl h =>
      subst h
      have := refCompileExpr_result_bound a offset nextTmp
        (fun v hv => htf v (List.mem_append_left _ hv))
      rw [hra] at this; simp at this
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        have hge := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
        rw [hrb] at hge; simp at hge
        exact ⟨k, hle, by omega, heq⟩
    | inr h =>
      subst h
      have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
      rw [hra] at hge_a; simp at hge_a
      have := refCompileExpr_result_bound b (offset + codeA.length) tmp1
        (fun v hv => htf v (List.mem_append_right _ hv))
      rw [hrb] at this; simp at this
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        exact ⟨k, by omega, hlt, heq⟩

-- ============================================================
-- § 9. Expression compilation correctness
-- ============================================================

theorem refCompileExpr_correct (e : SExpr) (offset nextTmp : Nat)
    (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ e.freeVars, v.isFTmp = false)
    (htypedv : e.typedVars σ am)
    (hsafe : e.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    let r := refCompileExpr e offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' am am ∧
      σ' r.2.1 = e.wrapEval σ am ∧
      (∀ w, w.isTmp = false → w.isFTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) ∧
      (∀ k, k < nextTmp → σ' (ftmpName k) = σ_tac (ftmpName k)) := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n =>
    simp only [refCompileExpr] at hcode ⊢
    refine ⟨σ_tac[tmpName nextTmp ↦ .int (BitVec.ofInt 64 n)], FragExec.single_const (am := am) hcode.head, ?_, ?_, ?_, ?_⟩
    · exact Store.update_self _ _ _
    · intro w hw1 hw2; exact Store.update_isTmp_ne (tmpName_isTmp nextTmp) hw1
    · intro k hk; exact Store.update_tmpName_ne (by omega)
    · intro k hk
      exact Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)
  | var x =>
    simp only [refCompileExpr] at hcode ⊢
    refine ⟨σ_tac, FragExec.rfl' _ _ _ _, ?_, fun w _ _ => rfl, fun k _ => rfl, fun k _ => rfl⟩
    simp only [SExpr.wrapEval]
    exact hagree x (htf x (by simp [SExpr.freeVars])) (hftf x (by simp [SExpr.freeVars]))
  | bin op a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
      show a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) ∧
           a.typedVars σ am ∧ b.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    have hbinop : p[offset + codeA.length + codeB.length]? =
        some (.binop (tmpName tmp2) op va vb) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeA.length + codeB.length) =
          offset + codeA.length + codeB.length from by omega] at this
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htv_a (SExpr.safe_bin_left hsafe) hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
      intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hftf_b htv_b (SExpr.safe_bin_right hsafe) hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    have hva_b : σ_b va = σ_a va := by
      rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    -- Extract int values for Step.binop
    have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
    have hvb : σ_b vb = .int (b.eval σ am) := by rw [hval_b, hwrap_b]
    have hbsafe : op.safe (a.eval σ am) (b.eval σ am) := SExpr.safe_bin_safe hsafe
    have hexec_binop := FragExec.single_binop (am := am) hbinop hva hvb hbsafe
    refine ⟨σ_b[tmpName tmp2 ↦ .int (op.eval (a.eval σ am) (b.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_binop
      have hlen : offset + (codeA ++ codeB ++ [TAC.binop (tmpName tmp2) op va vb]).length =
          offset + codeA.length + codeB.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp2) hw1, hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := refCompileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_tmpName_ne (by omega)]
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := refCompileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)]
      rw [hfprev_b k (by omega), hfprev_a k hk]
  | arrRead arr idx ih =>
    have hsafe_idx : idx.safe σ am p.arrayDecls := by
      simp [SExpr.safe] at hsafe; exact hsafe.1
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx⟩ :=
      ih offset nextTmp σ_tac htf hftf_idx htv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hval_idx_int : σ_idx vIdx = .int (idx.eval σ am) := by rw [hval_idx, hwrap_idx]
    have hbounds : (SExpr.eval σ am idx) < p.arraySizeBv arr := by
      simp only [SExpr.safe] at hsafe; exact hsafe.2
    have hexec_arrLoad := FragExec.single_arrLoad (am := am) harrLoad hval_idx_int hbounds
    refine ⟨σ_idx[tmpName tmp1 ↦ .int (am.read arr (idx.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2; rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_idx w hw1 hw2]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_tmpName_ne (by omega), hprev_idx k hk]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)]
      exact hfprev_idx k hk
  | flit f =>
    simp only [refCompileExpr] at hcode ⊢
    refine ⟨σ_tac[ftmpName nextTmp ↦ .float (floatToBits f)], FragExec.single_const (am := am) hcode.head, ?_, ?_, ?_, ?_⟩
    · exact Store.update_self _ _ _
    · intro w hw1 hw2; exact Store.update_isFTmp_ne (ftmpName_isFTmp nextTmp) hw2
    · intro k hk
      exact Store.update_other _ _ _ _ (tmpName_ne_ftmpName)
    · intro k hk; exact Store.update_ftmpName_ne (by omega)
  | fbin fop a b iha ihb =>
    obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
      show a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) ∧
           a.typedVars σ am ∧ b.typedVars σ am from htypedv
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    have hfbinop : p[offset + codeA.length + codeB.length]? =
        some (.fbinop (ftmpName tmp2) fop va vb) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeA.length + codeB.length) =
          offset + codeA.length + codeB.length from by omega] at this
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htv_a (SExpr.safe_fbin_left hsafe) hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
      intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hftf_b htv_b (SExpr.safe_fbin_right hsafe) hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- Preserve a's result through b's execution
    have hva_b : σ_b va = σ_a va := by
      rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases refCompileExpr_result_bound a offset nextTmp htf_a with h2 | ⟨j, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2; exact hntmp_b va h2 h
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hprev_b j (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hfprev_b k (by omega)]
    have hva : σ_b va = .float (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
    have hvb : σ_b vb = .float (b.eval σ am) := by rw [hval_b, hwrap_b]
    have hexec_fbinop := FragExec.single_fbinop (am := am) hfbinop hva hvb
    refine ⟨σ_b[ftmpName tmp2 ↦ .float (fop.eval (a.eval σ am) (b.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_fbinop
      have hlen : offset + (codeA ++ codeB ++ [TAC.fbinop (ftmpName tmp2) fop va vb]).length =
          offset + codeA.length + codeB.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp2) hw2, hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := refCompileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := refCompileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_ftmpName_ne (by omega)]
      rw [hfprev_b k (by omega), hfprev_a k hk]
  | intToFloat e ih =>
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .int (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr e offset nextTmp = ri at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileExpr e offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have hconv : p[offset + codeE.length]? = some (.intToFloat (ftmpName tmp1) ve) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e (by simp [SExpr.safe] at hsafe ⊢; exact hsafe) hagree hcodeE
    rw [hri] at hexec_e hval_e; simp at hexec_e hval_e
    have hval_e_int : σ_e ve = .int (e.eval σ am) := by rw [hval_e, hwrap_e]
    have hexec_conv := FragExec.single_intToFloat (am := am) hconv hval_e_int
    refine ⟨σ_e[ftmpName tmp1 ↦ .float (intToFloatBv (e.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_e hexec_conv
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp1) hw2, hntmp_e w hw1 hw2]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      exact hprev_e k hk
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_ftmpName_ne (by omega)]
      exact hfprev_e k hk
  | floatToInt e ih =>
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr e offset nextTmp = ri at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileExpr e offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have hconv : p[offset + codeE.length]? = some (.floatToInt (tmpName tmp1) ve) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e (by simp [SExpr.safe] at hsafe ⊢; exact hsafe) hagree hcodeE
    rw [hri] at hexec_e hval_e; simp at hexec_e hval_e
    have hval_e_float : σ_e ve = .float (e.eval σ am) := by rw [hval_e, hwrap_e]
    have hexec_conv := FragExec.single_floatToInt (am := am) hconv hval_e_float
    refine ⟨σ_e[tmpName tmp1 ↦ .int (floatToIntBv (e.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_e hexec_conv
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_e w hw1 hw2]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_tmpName_ne (by omega)]
      exact hprev_e k hk
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName)]
      exact hfprev_e k hk
  | floatExp e ih =>
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr e offset nextTmp = ri at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileExpr e offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have hconv : p[offset + codeE.length]? = some (.floatExp (ftmpName tmp1) ve) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e (by simp [SExpr.safe] at hsafe ⊢; exact hsafe) hagree hcodeE
    rw [hri] at hexec_e hval_e; simp at hexec_e hval_e
    have hval_e_float : σ_e ve = .float (e.eval σ am) := by rw [hval_e, hwrap_e]
    have hexec_conv := FragExec.single_floatExp (am := am) hconv hval_e_float
    refine ⟨σ_e[ftmpName tmp1 ↦ .float (floatExpBv (e.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_e hexec_conv
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2
      rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp1) hw2, hntmp_e w hw1 hw2]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      exact hprev_e k hk
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge e offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_ftmpName_ne (by omega)]
      exact hfprev_e k hk
  | farrRead arr idx ih =>
    have hsafe_idx : idx.safe σ am p.arrayDecls := by
      simp [SExpr.safe] at hsafe; exact hsafe.1
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (ftmpName tmp1) arr vIdx .float) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx⟩ :=
      ih offset nextTmp σ_tac htf hftf_idx htv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hval_idx_int : σ_idx vIdx = .int (idx.eval σ am) := by rw [hval_idx, hwrap_idx]
    have hbounds : (SExpr.eval σ am idx) < p.arraySizeBv arr := by
      simp only [SExpr.safe] at hsafe; exact hsafe.2
    have hexec_arrLoad := FragExec.single_arrLoad_float (am := am) harrLoad hval_idx_int hbounds
    refine ⟨σ_idx[ftmpName tmp1 ↦ .float (am.read arr (idx.eval σ am))],
            ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.wrapEval]; rw [Store.update_self]
    · intro w hw1 hw2; rw [Store.update_isFTmp_ne (ftmpName_isFTmp tmp1) hw2, hntmp_idx w hw1 hw2]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_other _ _ _ _ (tmpName_ne_ftmpName)]
      exact hprev_idx k hk
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_ftmpName_ne (by omega)]
      exact hfprev_idx k hk

-- ============================================================
-- § 10. Boolean expression compilation correctness
-- ============================================================

theorem refCompileBool_correct (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ sb.freeVars, v.isFTmp = false)
    (htypedv : sb.typedVars σ am)
    (hbsafe : sb.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    let r := refCompileBool sb offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' am am ∧
      r.2.1.eval σ' = sb.eval σ am ∧
      (∀ w, w.isTmp = false → w.isFTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) ∧
      (∀ k, k < nextTmp → σ' (ftmpName k) = σ_tac (ftmpName k)) := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit b =>
    simp only [refCompileBool] at hcode ⊢
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, by simp [BoolExpr.eval, SBool.eval], fun w _ _ => rfl, fun k _ => rfl, fun k _ => rfl⟩
  | bvar x =>
    simp only [refCompileBool] at hcode ⊢
    refine ⟨σ_tac, FragExec.rfl' _ _ _ _, ?_, fun w _ _ => rfl, fun k _ => rfl, fun k _ => rfl⟩
    simp only [BoolExpr.eval, SBool.eval]
    rw [hagree x (htf x (by simp [SBool.freeVars])) (hftf x (by simp [SBool.freeVars]))]
  | cmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    obtain ⟨htv_a, htv_b, hwrap_a, hwrap_b⟩ :=
      show a.typedVars σ am ∧ b.typedVars σ am ∧
           a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) from htypedv
    simp only [SBool.safe] at hbsafe; obtain ⟨hsa, hsb⟩ := hbsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a⟩ :=
      refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a hsa hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
      intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
      refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hsb hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- va preserved through b's execution
    have hva_b : σ_b va = σ_a va := by
      rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨k, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2
          rw [heq2, hfprev_b k (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    refine ⟨σ_b, ?_, ?_, ?_, ?_, ?_⟩
    · have := FragExec.trans' hexec_a hexec_b
      simp only [List.length_append] at this ⊢; rwa [Nat.add_assoc] at this
    · simp only [BoolExpr.eval, SBool.eval]
      have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
      have hvb : σ_b vb = .int (b.eval σ am) := by rw [hval_b, hwrap_b]
      rw [hva, hvb]; simp [Value.toInt]
    · intro w hw1 hw2; rw [hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hfprev_b k (by omega), hfprev_a k hk]
  | not e ih =>
    simp only [SBool.safe] at hbsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hrc : refCompileBool e offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileBool e offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode
    obtain ⟨σ', hexec, heval, hntmp, hprev, hfprev⟩ := ih offset nextTmp σ_tac htf hftf htypedv hbsafe hagree hcodeE
    rw [hrc] at hexec heval; simp at hexec heval
    exact ⟨σ', hexec, by simp [BoolExpr.eval, SBool.eval, heval], hntmp, hprev, hfprev⟩
  | and a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have ⟨htypedv_a, htypedv_b⟩ : a.typedVars σ am ∧ b.typedVars σ am := htypedv
    unfold SBool.safe at hbsafe
    obtain ⟨hbsafe_a, hbsafe_b_imp⟩ := hbsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto (.not ba) (offset + codeA.length + 1 + codeB.length + 3)) := by
      exact hcode.left.left.right.head
    have hcodeB : CodeAt (refCompileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
        (offset + codeA.length + 1) := by
      rw [hrb]
      have h := hcode.left.right
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rwa [show offset + (codeA.length + 1) = offset + codeA.length + 1 from by omega] at h
    have htail := hcode.right
    simp only [List.length_append, List.length_cons, List.length_nil] at htail
    have hifgB : p[offset + codeA.length + 1 + codeB.length]? =
        some (TAC.ifgoto (.not bb) (offset + codeA.length + 1 + codeB.length + 3)) := by
      have h := htail 0 (by simp)
      simp only [List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 0 = offset + codeA.length + 1 + codeB.length from by omega] at h
    have hconst1 : p[offset + codeA.length + 1 + codeB.length + 1]? =
        some (TAC.const (tmpName tmp1) (.int 1)) := by
      have h := htail 1 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 1 = offset + codeA.length + 1 + codeB.length + 1 from by omega] at h
    have hgoto_end : p[offset + codeA.length + 1 + codeB.length + 2]? =
        some (TAC.goto (offset + codeA.length + 1 + codeB.length + 3 + 1)) := by
      have h := htail 2 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 2 = offset + codeA.length + 1 + codeB.length + 2 from by omega] at h
    have hconst0 : p[offset + codeA.length + 1 + codeB.length + 3]? =
        some (TAC.const (tmpName tmp1) (.int 0)) := by
      have h := htail 3 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 3 = offset + codeA.length + 1 + codeB.length + 3 from by omega] at h
    have hge_a : nextTmp ≤ tmp1 := by
      have := refCompileBool_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
    have hge_b : tmp1 + 1 ≤ tmp2 := by
      have := refCompileBool_nextTmp_ge b (offset + codeA.length + 1) (tmp1 + 1)
      rw [hrb] at this; simpa using this
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, hprev_a, hfprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htypedv_a hbsafe_a hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
      intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
    by_cases ha_eval : a.eval σ am = true
    · have hbsafe_b : b.safe σ am p.arrayDecls := hbsafe_b_imp ha_eval
      have hba_true : ba.eval σ_a = true := by rw [heval_a, ha_eval]
      have hnot_ba_false : (BoolExpr.not ba).eval σ_a = false := by
        simp [BoolExpr.eval, hba_true]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hnot_ba_false
      obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hftf_b htypedv_b hbsafe_b hagree_a hcodeB
      rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
      by_cases hb_eval : b.eval σ am = true
      · have hbb_true : bb.eval σ_b = true := by rw [heval_b, hb_eval]
        have hnot_bb_false : (BoolExpr.not bb).eval σ_b = false := by
          simp [BoolExpr.eval, hbb_true]
        have hexec_ifB := FragExec.single_iffalse (am := am) hifgB hnot_bb_false
        have hexec_c1 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_const (am := am) hconst1
        have hexec_goto : FragExec p _ (σ_b[tmpName tmp1 ↦ .int 1]) _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_goto (am := am) hgoto_end
        let σ_final := σ_b[tmpName tmp1 ↦ .int 1]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) (FragExec.trans' hexec_c1 hexec_goto)
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_eval, hb_eval]
        · intro w hw1 hw2
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
      · have hb_false : b.eval σ am = false := Bool.eq_false_iff.mpr hb_eval
        have hbb_false : bb.eval σ_b = false := by rw [heval_b, hb_false]
        have hnot_bb_true : (BoolExpr.not bb).eval σ_b = true := by
          simp [BoolExpr.eval, hbb_false]
        have hexec_ifB := FragExec.single_iftrue (am := am) hifgB hnot_bb_true
        have hexec_c0 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_const (am := am) hconst0
        let σ_final := σ_b[tmpName tmp1 ↦ .int 0]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) hexec_c0
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_eval, hb_false]
        · intro w hw1 hw2
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
    · have ha_false : a.eval σ am = false := Bool.eq_false_iff.mpr ha_eval
      have hba_false : ba.eval σ_a = false := by rw [heval_a, ha_false]
      have hnot_ba_true : (BoolExpr.not ba).eval σ_a = true := by
        simp [BoolExpr.eval, hba_false]
      have hexec_ifA := FragExec.single_iftrue (am := am) hifgA hnot_ba_true
      have hexec_c0 : FragExec p _ σ_a _ (σ_a[tmpName tmp1 ↦ .int 0]) am am :=
        FragExec.single_const (am := am) hconst0
      let σ_final := σ_a[tmpName tmp1 ↦ .int 0]
      refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_c0
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
        simp [SBool.eval, ha_false]
      · intro w hw1 hw2
        simp only [σ_final]
        rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_a w hw1 hw2]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_tmpName_ne (by omega), hprev_a k hk]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_a k hk]
  | or a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    have ⟨htypedv_a, htypedv_b⟩ : a.typedVars σ am ∧ b.typedVars σ am := htypedv
    unfold SBool.safe at hbsafe
    obtain ⟨hbsafe_a, hbsafe_b_imp⟩ := hbsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto ba (offset + codeA.length + 1 + codeB.length + 3)) := by
      exact hcode.left.left.right.head
    have hcodeB : CodeAt (refCompileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
        (offset + codeA.length + 1) := by
      rw [hrb]
      have h := hcode.left.right
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rwa [show offset + (codeA.length + 1) = offset + codeA.length + 1 from by omega] at h
    have htail := hcode.right
    simp only [List.length_append, List.length_cons, List.length_nil] at htail
    have hifgB : p[offset + codeA.length + 1 + codeB.length]? =
        some (TAC.ifgoto bb (offset + codeA.length + 1 + codeB.length + 3)) := by
      have h := htail 0 (by simp)
      simp only [List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 0 = offset + codeA.length + 1 + codeB.length from by omega] at h
    have hconst0 : p[offset + codeA.length + 1 + codeB.length + 1]? =
        some (TAC.const (tmpName tmp1) (.int 0)) := by
      have h := htail 1 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 1 = offset + codeA.length + 1 + codeB.length + 1 from by omega] at h
    have hgoto_end : p[offset + codeA.length + 1 + codeB.length + 2]? =
        some (TAC.goto (offset + codeA.length + 1 + codeB.length + 3 + 1)) := by
      have h := htail 2 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 2 = offset + codeA.length + 1 + codeB.length + 2 from by omega] at h
    have hconst1 : p[offset + codeA.length + 1 + codeB.length + 3]? =
        some (TAC.const (tmpName tmp1) (.int 1)) := by
      have h := htail 3 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil] at h
      rwa [show offset + (codeA.length + 1 + codeB.length) + 3 = offset + codeA.length + 1 + codeB.length + 3 from by omega] at h
    have hge_a : nextTmp ≤ tmp1 := by
      have := refCompileBool_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
    have hge_b : tmp1 + 1 ≤ tmp2 := by
      have := refCompileBool_nextTmp_ge b (offset + codeA.length + 1) (tmp1 + 1)
      rw [hrb] at this; simpa using this
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, hprev_a, hfprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hftf_a htypedv_a hbsafe_a hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
      intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
    by_cases ha_eval : a.eval σ am = true
    · have hba_true : ba.eval σ_a = true := by rw [heval_a, ha_eval]
      have hexec_ifA := FragExec.single_iftrue (am := am) hifgA hba_true
      have hexec_c1 : FragExec p _ σ_a _ (σ_a[tmpName tmp1 ↦ .int 1]) am am :=
        FragExec.single_const (am := am) hconst1
      let σ_final := σ_a[tmpName tmp1 ↦ .int 1]
      refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_c1
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
        simp [SBool.eval, ha_eval]
      · intro w hw1 hw2
        simp only [σ_final]
        rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_a w hw1 hw2]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_tmpName_ne (by omega), hprev_a k hk]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_a k hk]
    · have ha_false : a.eval σ am = false := Bool.eq_false_iff.mpr ha_eval
      have hbsafe_b : b.safe σ am p.arrayDecls := hbsafe_b_imp ha_false
      have hba_false : ba.eval σ_a = false := by rw [heval_a, ha_false]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hba_false
      obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hftf_b htypedv_b hbsafe_b hagree_a hcodeB
      rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
      by_cases hb_eval : b.eval σ am = true
      · have hbb_true : bb.eval σ_b = true := by rw [heval_b, hb_eval]
        have hexec_ifB := FragExec.single_iftrue (am := am) hifgB hbb_true
        have hexec_c1 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_const (am := am) hconst1
        let σ_final := σ_b[tmpName tmp1 ↦ .int 1]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) hexec_c1
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_false, hb_eval]
        · intro w hw1 hw2
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
      · have hb_false : b.eval σ am = false := Bool.eq_false_iff.mpr hb_eval
        have hbb_false : bb.eval σ_b = false := by rw [heval_b, hb_false]
        have hexec_ifB := FragExec.single_iffalse (am := am) hifgB hbb_false
        have hexec_c0 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_const (am := am) hconst0
        have hexec_goto : FragExec p _ (σ_b[tmpName tmp1 ↦ .int 0]) _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_goto (am := am) hgoto_end
        let σ_final := σ_b[tmpName tmp1 ↦ .int 0]
        refine ⟨σ_final, ?_, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) (FragExec.trans' hexec_c0 hexec_goto)
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_false, hb_false]
        · intro w hw1 hw2
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_b k (by omega), hfprev_a k hk]
  | barrRead arr idx =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v hv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftf v hv
    obtain ⟨htv_idx, hwrap_idx⟩ : idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am) := htypedv
    have hsafe_idx : idx.safe σ am p.arrayDecls := hbsafe.1
    dsimp only [refCompileBool] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx⟩ :=
      refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    rw [hwrap_idx] at hval_idx
    have hbounds : (SExpr.eval σ am idx) < p.arraySizeBv arr := by
      simp only [SBool.safe] at hbsafe; exact hbsafe.2
    have hexec_arrLoad := FragExec.single_arrLoad (am := am) harrLoad hval_idx hbounds
    set σ_load := σ_idx[tmpName tmp1 ↦ .int (am.read arr (idx.eval σ am))]
    have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
    rw [hri] at hge; simp at hge
    refine ⟨σ_load, ?_, ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [BoolExpr.eval, CmpOp.eval, σ_load, Store.update_self, Value.toInt, SBool.eval]
    · intro w hw1 hw2
      simp only [σ_load]
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw1, hntmp_idx w hw1 hw2]
    · intro k hk
      simp only [σ_load]
      rw [Store.update_tmpName_ne (by omega), hprev_idx k hk]
    · intro k hk
      simp only [σ_load]
      rw [Store.update_other _ _ _ _ (Ne.symm tmpName_ne_ftmpName), hfprev_idx k hk]
  | fcmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    obtain ⟨htv_a, htv_b, hwrap_a, hwrap_b⟩ :=
      show a.typedVars σ am ∧ b.typedVars σ am ∧
           a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) from htypedv
    simp only [SBool.safe] at hbsafe; obtain ⟨hsa, hsb⟩ := hbsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, hfprev_a⟩ :=
      refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a hsa hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
      intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
      refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hsb hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- va preserved through b's execution (va may be source var, tmpName, or ftmpName)
    have hva_b : σ_b va = σ_a va := by
      rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h
        rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨k, _, hlt2, heq2⟩
        · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
        · rw [hra] at hlt2 heq2; simp at hlt2 heq2
          rw [heq2, hfprev_b k (by omega)]
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    refine ⟨σ_b, ?_, ?_, ?_, ?_, ?_⟩
    · have := FragExec.trans' hexec_a hexec_b
      simp only [List.length_append] at this ⊢; rwa [Nat.add_assoc] at this
    · simp only [BoolExpr.eval, SBool.eval]
      have hva : σ_b va = .float (a.eval σ am) := by rw [hva_b, hval_a, hwrap_a]
      have hvb : σ_b vb = .float (b.eval σ am) := by rw [hval_b, hwrap_b]
      rw [hva, hvb]; simp [Value.toFloat]
    · intro w hw1 hw2; rw [hntmp_b w hw1 hw2, hntmp_a w hw1 hw2]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hprev_b k (by omega), hprev_a k hk]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hfprev_b k (by omega), hfprev_a k hk]

-- ============================================================
-- § 11. Statement compilation correctness
-- ============================================================

theorem refCompileStmt_correct (s : Stmt) (fuel : Nat) (σ σ' : Store) (am am' : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ am p.arrayDecls = some (σ', am'))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hsafe : s.safe fuel σ am p.arrayDecls)
    (htypedv : s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ σ_tac', FragExec p offset σ_tac
        (offset + (refCompileStmt s offset nextTmp).1.length) σ_tac' am am' ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → σ_tac' v = σ' v) := by
  sorry

-- ============================================================
-- § 12. Top-level correctness theorem
-- ============================================================

theorem refCompile_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ ArrayMem.init (refCompile s).arrayDecls = some (σ', ArrayMem.init))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hsafe : s.safe fuel σ ArrayMem.init (refCompile s).arrayDecls)
    (htypedv : s.typedVars fuel σ ArrayMem.init (refCompile s).arrayDecls) :
    ∃ σ_tac am_h am_h', haltsWithResult (refCompile s) 0 σ σ_tac am_h am_h' ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ' v) := by
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    refCompileStmt_correct s fuel σ σ' ArrayMem.init ArrayMem.init 0 0 (refCompile s) σ
      hinterp htmpfree hftmpfree hsafe htypedv (fun _ _ _ => rfl) hcode
  simp only [Nat.zero_add] at hexec
  have hhalt : (refCompile s)[(refCompileStmt s 0 0).1.length]? = some .halt := by
    unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray]
    rw [List.getElem?_append_right (by omega)]; simp
  exact ⟨σ_tac, ArrayMem.init, ArrayMem.init, FragExec.toHalt hexec hhalt, hagree⟩

-- ============================================================
-- § 13. Determinism and stuck-state infrastructure
-- ============================================================

/-- Any two multi-step executions from the same config have one as a prefix
    of the other (i.e. they follow the same deterministic path). -/
theorem Steps.deterministic_reach {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶* c₁) (h₂ : p ⊩ c ⟶* c₂) :
    (p ⊩ c₁ ⟶* c₂) ∨ (p ⊩ c₂ ⟶* c₁) := by
  induction h₁ generalizing c₂ with
  | refl => exact Or.inl h₂
  | step s rest ih =>
    cases h₂ with
    | refl => exact Or.inr (.step s rest)
    | step s' rest' =>
      have := Step.deterministic s s'; subst this; exact ih rest'

/-- A stuck configuration is a terminal point — no further steps possible. -/
theorem Steps.stuck_terminal {p : Prog} {c c' : Cfg}
    (h : p ⊩ c ⟶* c') (hs : ∀ d, ¬ p ⊩ c ⟶ d) : c' = c := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hs _)

/-- Two executions from the same start that both reach stuck endpoints
    must reach the same endpoint. -/
theorem Steps.stuck_det {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶* c₁) (h₂ : p ⊩ c ⟶* c₂)
    (hs₁ : ∀ d, ¬ p ⊩ c₁ ⟶ d) (hs₂ : ∀ d, ¬ p ⊩ c₂ ⟶ d) :
    c₁ = c₂ := by
  cases Steps.deterministic_reach h₁ h₂ with
  | inl h => exact (Steps.stuck_terminal h hs₁).symm
  | inr h => exact Steps.stuck_terminal h hs₂

/-- An error configuration and a halt from the same start are contradictory. -/
theorem error_run_no_halt {p : Prog} {pc : Nat} {σ_start σ_err σ_halt : Store}
    {am₀ am₂ am₃ am₅ : ArrayMem}
    (h_run : p ⊩ Cfg.run 0 σ_start am₀ ⟶* Cfg.run pc σ_err am₂)
    (h_error : Step p (Cfg.run pc σ_err am₂) (Cfg.error σ_err am₃))
    (h_halt : haltsWithResult p 0 σ_start σ_halt am₀ am₅) : False := by
  have herr_reach : p ⊩ Cfg.run 0 σ_start am₀ ⟶* Cfg.error σ_err am₃ :=
    Steps.trans h_run (Steps.step h_error Steps.refl)
  have err_terminal : ∀ d, ¬ Step p (Cfg.error σ_err am₃) d := fun _ h => Step.no_step_from_error h
  have halt_terminal : ∀ d, ¬ Step p (Cfg.halt σ_halt am₅) d := fun _ h => Step.no_step_from_halt h
  have := Steps.stuck_det herr_reach h_halt err_terminal halt_terminal
  exact Cfg.noConfusion this

/-- A binop instruction with an unsafe operation produces an error transition. -/
theorem unsafe_binop_errors {p : Prog} {pc : Nat} {σ : Store}
    {x : Var} {op : BinOp} {y z : Var} {a b : BitVec 64}
    (hinstr : p[pc]? = some (.binop x op y z))
    (hy : σ y = .int a) (hz : σ z = .int b)
    (hunsafe : ¬ op.safe a b) :
    Step p (Cfg.run pc σ _xam) (Cfg.error σ _xam) :=
  Step.error hinstr hy hz hunsafe
