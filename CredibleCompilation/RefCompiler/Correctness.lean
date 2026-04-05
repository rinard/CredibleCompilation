import CredibleCompilation.RefCompiler.Defs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

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

-- ============================================================
-- § 9. Expression compilation correctness
-- ============================================================

theorem refCompileExpr_correct (e : SExpr) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hintv : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n)
    (hsafe : e.divSafe σ am)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    let r := refCompileExpr e offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' am am ∧
      σ' r.2.1 = .int (e.eval σ am) ∧
      (∀ w, w.isTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) := by
  induction e generalizing offset nextTmp σ_tac with
  | arrRead arr idx ih =>
    have hsafe_idx : idx.divSafe σ am := by
      simp [SExpr.divSafe] at hsafe; exact hsafe
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx) := by
      have := hcode.right.head; simpa using this
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx⟩ :=
      ih offset nextTmp σ_tac htf hintv hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    -- TODO: thread arrayDecls through refCompile so bounds proof is available
    have hbounds : (SExpr.eval σ am idx).toNat < p.arraySize arr := sorry
    have hexec_arrLoad := FragExec.single_arrLoad (am := am) harrLoad hval_idx hbounds
    refine ⟨σ_idx[tmpName tmp1 ↦ .int (am.read arr (idx.eval σ am).toNat)],
            ?_, ?_, ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_idx hexec_arrLoad
      simp only [List.length_append, List.length_cons, List.length_nil] at h12 ⊢
      exact h12
    · simp only [SExpr.eval]; rw [Store.update_self]
    · intro w hw; rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_idx w hw]
    · intro k hk
      have hge := refCompileExpr_nextTmp_ge idx offset nextTmp
      rw [hri] at hge; simp at hge
      rw [Store.update_tmpName_ne (by omega), hprev_idx k hk]
  | lit n =>
    simp only [refCompileExpr] at hcode ⊢
    refine ⟨σ_tac[tmpName nextTmp ↦ .int (BitVec.ofInt 64 n)], FragExec.single_const (am := am) hcode.head, ?_, ?_, ?_⟩
    · exact Store.update_self _ _ _
    · intro w hw; exact Store.update_isTmp_ne (tmpName_isTmp nextTmp) hw
    · intro k hk; exact Store.update_tmpName_ne (by omega)
  | var x =>
    simp only [refCompileExpr] at hcode ⊢
    obtain ⟨n, hn⟩ := hintv x (by simp [SExpr.freeVars])
    refine ⟨σ_tac, FragExec.rfl' _ _ _ _, ?_, fun w _ => rfl, fun k _ => rfl⟩
    simp only [SExpr.eval]
    rw [hagree x (htf x (by simp [SExpr.freeVars])), hn]
    simp [Value.toInt]
  | bin op a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hintv_a : ∀ v ∈ a.freeVars, ∃ n, σ v = .int n :=
      fun v hv => hintv v (List.mem_append_left _ hv)
    have hintv_b : ∀ v ∈ b.freeVars, ∃ n, σ v = .int n :=
      fun v hv => hintv v (List.mem_append_right _ hv)
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
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hintv_a (SExpr.divSafe_bin_left hsafe) hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    have hintv_ba : ∀ v ∈ b.freeVars, ∃ n, σ_a v = .int n := by
      intro v hv
      obtain ⟨n, hn⟩ := hintv_b v hv
      exact ⟨n, by rw [hntmp_a v (htf_b v hv), hagree v (htf_b v hv), hn]⟩
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hintv_b (SExpr.divSafe_bin_right hsafe) hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    have hva_b : σ_b va = σ_a va := by
      rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h; exact hntmp_b va h
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
    have hvb : σ_b vb = .int (b.eval σ am) := hval_b
    have hbsafe : op.safe (a.eval σ am) (b.eval σ am) := SExpr.divSafe_bin_safe hsafe
    have hexec_binop := FragExec.single_binop (am := am) hbinop hva hvb hbsafe
    refine ⟨σ_b[tmpName tmp2 ↦ .int (op.eval (a.eval σ am) (b.eval σ am))],
            ?_, ?_, ?_, ?_⟩
    · -- FragExec
      have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_binop
      have hlen : offset + (codeA ++ codeB ++ [TAC.binop (tmpName tmp2) op va vb]).length =
          offset + codeA.length + codeB.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · simp only [SExpr.eval]; rw [Store.update_self]
    · intro w hw
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp2) hw, hntmp_b w hw, hntmp_a w hw]
    · intro k hk
      have hle_a : nextTmp ≤ tmp1 := by
        have := refCompileExpr_nextTmp_ge a offset nextTmp; rw [hra] at this; simpa using this
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [Store.update_tmpName_ne (by omega)]
      rw [hprev_b k (by omega), hprev_a k hk]

-- ============================================================
-- § 10. Boolean expression compilation correctness
-- ============================================================

theorem refCompileBool_correct (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hintv : sb.intTyped σ)
    (hbsafe : sb.divSafe σ am)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    let r := refCompileBool sb offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' am am ∧
      r.2.1.eval σ' = sb.eval σ am ∧
      (∀ w, w.isTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit b =>
    simp only [refCompileBool] at hcode ⊢
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, by simp [BoolExpr.eval, SBool.eval], fun w _ => rfl, fun k _ => rfl⟩
  | bvar x =>
    simp only [refCompileBool] at hcode ⊢
    refine ⟨σ_tac, FragExec.rfl' _ _ _ _, ?_, fun w _ => rfl, fun k _ => rfl⟩
    simp only [BoolExpr.eval, SBool.eval]
    rw [hagree x (htf x (by simp [SBool.freeVars]))]
  | cmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : (∀ v ∈ a.freeVars, ∃ n, σ v = .int n) ∧ (∀ v ∈ b.freeVars, ∃ n, σ v = .int n) := hintv
    simp only [SBool.divSafe] at hbsafe; obtain ⟨hsa, hsb⟩ := hbsafe
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
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
      refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a hsa hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    have hintv_ba : ∀ v ∈ b.freeVars, ∃ n, σ_a v = .int n := by
      intro v hv
      obtain ⟨n, hn⟩ := hintv_b v hv
      exact ⟨n, by rw [hntmp_a v (htf_b v hv), hagree v (htf_b v hv), hn]⟩
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
      refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hsb hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- va preserved through b's execution
    have hva_b : σ_b va = σ_a va := by
      rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
      · rw [hra] at h; simp at h; exact hntmp_b va h
      · rw [hra] at hlt heq; simp at hlt heq
        rw [heq, hprev_b k (by omega)]
    refine ⟨σ_b, ?_, ?_, ?_, ?_⟩
    · have := FragExec.trans' hexec_a hexec_b
      simp only [List.length_append] at this ⊢; rwa [Nat.add_assoc] at this
    · simp only [BoolExpr.eval, SBool.eval]
      have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
      have hvb : σ_b vb = .int (b.eval σ am) := hval_b
      rw [hva, hvb]; simp [Value.toInt]
    · intro w hw; rw [hntmp_b w hw, hntmp_a w hw]
    · intro k hk
      have hle_b : tmp1 ≤ tmp2 := by
        have := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1; rw [hrb] at this; simpa using this
      rw [hprev_b k (by omega), hprev_a k hk]
  | not e ih =>
    simp only [SBool.divSafe] at hbsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hrc : refCompileBool e offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileBool e offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode
    obtain ⟨σ', hexec, heval, hntmp, hprev⟩ := ih offset nextTmp σ_tac htf hintv hbsafe hagree hcodeE
    rw [hrc] at hexec heval; simp at hexec heval
    exact ⟨σ', hexec, by simp [BoolExpr.eval, SBool.eval, heval], hntmp, hprev⟩
  | and a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : a.intTyped σ ∧ b.intTyped σ := hintv
    unfold SBool.divSafe at hbsafe
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
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, hprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hintv_a hbsafe_a hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    by_cases ha_eval : a.eval σ am = true
    · have hbsafe_b : b.divSafe σ am := hbsafe_b_imp ha_eval
      have hba_true : ba.eval σ_a = true := by rw [heval_a, ha_eval]
      have hnot_ba_false : (BoolExpr.not ba).eval σ_a = false := by
        simp [BoolExpr.eval, hba_true]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hnot_ba_false
      obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hintv_b hbsafe_b hagree_a hcodeB
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
        refine ⟨σ_final, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) (FragExec.trans' hexec_c1 hexec_goto)
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_eval, hb_eval]
        · intro w hw
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_b w hw, hntmp_a w hw]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
      · have hb_false : b.eval σ am = false := Bool.eq_false_iff.mpr hb_eval
        have hbb_false : bb.eval σ_b = false := by rw [heval_b, hb_false]
        have hnot_bb_true : (BoolExpr.not bb).eval σ_b = true := by
          simp [BoolExpr.eval, hbb_false]
        have hexec_ifB := FragExec.single_iftrue (am := am) hifgB hnot_bb_true
        have hexec_c0 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_const (am := am) hconst0
        let σ_final := σ_b[tmpName tmp1 ↦ .int 0]
        refine ⟨σ_final, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) hexec_c0
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_eval, hb_false]
        · intro w hw
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_b w hw, hntmp_a w hw]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
    · have ha_false : a.eval σ am = false := Bool.eq_false_iff.mpr ha_eval
      have hba_false : ba.eval σ_a = false := by rw [heval_a, ha_false]
      have hnot_ba_true : (BoolExpr.not ba).eval σ_a = true := by
        simp [BoolExpr.eval, hba_false]
      have hexec_ifA := FragExec.single_iftrue (am := am) hifgA hnot_ba_true
      have hexec_c0 : FragExec p _ σ_a _ (σ_a[tmpName tmp1 ↦ .int 0]) am am :=
        FragExec.single_const (am := am) hconst0
      let σ_final := σ_a[tmpName tmp1 ↦ .int 0]
      refine ⟨σ_final, ?_, ?_, ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_c0
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
        simp [SBool.eval, ha_false]
      · intro w hw
        simp only [σ_final]
        rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_a w hw]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_tmpName_ne (by omega), hprev_a k hk]
  | or a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : a.intTyped σ ∧ b.intTyped σ := hintv
    unfold SBool.divSafe at hbsafe
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
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, hprev_a⟩ :=
      iha offset nextTmp σ_tac htf_a hintv_a hbsafe_a hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    by_cases ha_eval : a.eval σ am = true
    · have hba_true : ba.eval σ_a = true := by rw [heval_a, ha_eval]
      have hexec_ifA := FragExec.single_iftrue (am := am) hifgA hba_true
      have hexec_c1 : FragExec p _ σ_a _ (σ_a[tmpName tmp1 ↦ .int 1]) am am :=
        FragExec.single_const (am := am) hconst1
      let σ_final := σ_a[tmpName tmp1 ↦ .int 1]
      refine ⟨σ_final, ?_, ?_, ?_, ?_⟩
      · have h := FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_c1
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
        simp [SBool.eval, ha_eval]
      · intro w hw
        simp only [σ_final]
        rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_a w hw]
      · intro k hk
        simp only [σ_final]
        rw [Store.update_tmpName_ne (by omega), hprev_a k hk]
    · have ha_false : a.eval σ am = false := Bool.eq_false_iff.mpr ha_eval
      have hbsafe_b : b.divSafe σ am := hbsafe_b_imp ha_false
      have hba_false : ba.eval σ_a = false := by rw [heval_a, ha_false]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hba_false
      obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, hprev_b⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hintv_b hbsafe_b hagree_a hcodeB
      rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
      by_cases hb_eval : b.eval σ am = true
      · have hbb_true : bb.eval σ_b = true := by rw [heval_b, hb_eval]
        have hexec_ifB := FragExec.single_iftrue (am := am) hifgB hbb_true
        have hexec_c1 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 1]) am am :=
          FragExec.single_const (am := am) hconst1
        let σ_final := σ_b[tmpName tmp1 ↦ .int 1]
        refine ⟨σ_final, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) hexec_c1
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_false, hb_eval]
        · intro w hw
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_b w hw, hntmp_a w hw]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]
      · have hb_false : b.eval σ am = false := Bool.eq_false_iff.mpr hb_eval
        have hbb_false : bb.eval σ_b = false := by rw [heval_b, hb_false]
        have hexec_ifB := FragExec.single_iffalse (am := am) hifgB hbb_false
        have hexec_c0 : FragExec p _ σ_b _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_const (am := am) hconst0
        have hexec_goto : FragExec p _ (σ_b[tmpName tmp1 ↦ .int 0]) _ (σ_b[tmpName tmp1 ↦ .int 0]) am am :=
          FragExec.single_goto (am := am) hgoto_end
        let σ_final := σ_b[tmpName tmp1 ↦ .int 0]
        refine ⟨σ_final, ?_, ?_, ?_, ?_⟩
        · have h := FragExec.trans' (FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_a hexec_ifA) hexec_b) hexec_ifB) (FragExec.trans' hexec_c0 hexec_goto)
          simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
          convert h using 1; omega
        · simp only [BoolExpr.eval, CmpOp.eval, σ_final, Store.update_self, Value.toInt]
          simp [SBool.eval, ha_false, hb_false]
        · intro w hw
          simp only [σ_final]
          rw [Store.update_isTmp_ne (tmpName_isTmp tmp1) hw, hntmp_b w hw, hntmp_a w hw]
        · intro k hk
          simp only [σ_final]
          rw [Store.update_tmpName_ne (by omega), hprev_b k (by omega), hprev_a k hk]

-- ============================================================
-- § 11. Statement compilation correctness
-- ============================================================

theorem refCompileStmt_correct (s : Stmt) (fuel : Nat) (σ σ' : Store) (am am' : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ am = some (σ', am'))
    (htmpfree : s.tmpFree)
    (hsafe : s.divSafe fuel σ am)
    (hintv : s.intTyped fuel σ am)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ σ_tac', FragExec p offset σ_tac
        (offset + (refCompileStmt s offset nextTmp).1.length) σ_tac' am am' ∧
      (∀ v, v.isTmp = false → σ_tac' v = σ' v) := by
  induction s generalizing fuel σ σ' am am' offset nextTmp p σ_tac with
  | arrWrite arr idx val =>
    simp only [Stmt.interp, Option.some.injEq, Prod.mk.injEq] at hinterp
    obtain ⟨rfl, ham_eq⟩ := hinterp
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hintv_idx : ∀ v ∈ idx.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hintv_val : ∀ v ∈ val.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.2
    have hsafe_idx : idx.divSafe σ am := by
      simp only [Stmt.divSafe] at hsafe; exact hsafe.1
    have hsafe_val : val.divSafe σ am := by
      simp only [Stmt.divSafe] at hsafe; exact hsafe.2
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrv : refCompileExpr val (offset + codeIdx.length) tmp1 = rv at hcode ⊢
    obtain ⟨codeVal, vVal, tmp2⟩ := rv
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left.left
    have hcodeVal : CodeAt (refCompileExpr val (offset + codeIdx.length) tmp1).1 p
        (offset + codeIdx.length) := by rw [hrv]; exact hcode.left.right
    have harrStore : p[offset + codeIdx.length + codeVal.length]? =
        some (.arrStore arr vIdx vVal) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeIdx.length + codeVal.length) =
          offset + codeIdx.length + codeVal.length from by omega] at this
    -- Execute idx
    obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx⟩ :=
      refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hsafe_idx hagree hcodeIdx
    rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
    have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
      intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
    -- Execute val
    have hge_idx := refCompileExpr_nextTmp_ge idx offset nextTmp
    rw [hri] at hge_idx; simp at hge_idx
    have hintv_val_idx : ∀ v ∈ val.freeVars, ∃ n, σ_idx v = .int n := by
      intro v hv; obtain ⟨n, hn⟩ := hintv_val v hv
      exact ⟨n, by rw [hntmp_idx v (htf_val v hv), hagree v (htf_val v hv), hn]⟩
    obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val⟩ :=
      refCompileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
        htf_val hintv_val hsafe_val hagree_idx hcodeVal
    rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
    -- Get idx value in σ_val
    have hvidx_val : σ_val vIdx = σ_idx vIdx := by
      rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
      · rw [hri] at h; simp at h; exact hntmp_val vIdx h
      · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
    have hvidx : σ_val vIdx = .int (idx.eval σ am) := by rw [hvidx_val, hval_idx]
    have hvval : σ_val vVal = .int (val.eval σ am) := hval_val
    -- Execute arrStore
    -- TODO: thread arrayDecls through refCompile so bounds proof is available
    have hbounds : (SExpr.eval σ am idx).toNat < p.arraySize arr := sorry
    have hexec_store := FragExec.single_arrStore (am := am) harrStore hvidx hvval hbounds
    refine ⟨σ_val, ?_, ?_⟩
    · have h123 := FragExec.trans' (FragExec.trans' hexec_idx hexec_val) hexec_store
      rw [ham_eq] at h123
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at h123 ⊢
      rw [show offset + (codeIdx.length + codeVal.length + 1) =
          offset + codeIdx.length + codeVal.length + 1 from by omega]
      exact h123
    · intro v hv; rw [hntmp_val v hv, hntmp_idx v hv, hagree v hv]
  | skip =>
    simp only [Stmt.interp, Option.some.injEq, Prod.mk.injEq] at hinterp
    obtain ⟨rfl, rfl⟩ := hinterp
    simp only [refCompileStmt, List.length_nil, Nat.add_zero]
    exact ⟨σ_tac, FragExec.rfl' _ _ _ _, fun v hv => hagree v hv⟩
  | assign x e =>
    simp only [Stmt.interp, Option.some.injEq, Prod.mk.injEq] at hinterp
    obtain ⟨rfl, rfl⟩ := hinterp
    have hx_ntmp : x.isTmp = false := htmpfree x (by simp [Stmt.allVars])
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hsafe_e : e.divSafe σ am := by simp only [Stmt.divSafe] at hsafe; exact hsafe
    have hintv_e : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv
    cases e with
    | arrRead arr idx =>
      have hsafe_idx : idx.divSafe σ am := by
        simp [SExpr.divSafe] at hsafe_e; exact hsafe_e
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
      simp only [] at hcode ⊢
      have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      have harrLoad : p[offset + codeIdx.length]? =
          some (.arrLoad (tmpName tmp1) arr vIdx) := by
        have := hcode.right.head; simpa using this
      have hcopy : p[offset + codeIdx.length + 1]? =
          some (.copy x (tmpName tmp1)) := by
        have := hcode.right 1 (by simp); simpa using this
      -- Execute idx expression
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx⟩ :=
        refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_e hintv_e hsafe_idx hagree hcodeIdx
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      -- Execute arrLoad
      -- TODO: thread arrayDecls through refCompile so bounds proof is available
      have hbounds : (SExpr.eval σ am idx).toNat < p.arraySize arr := sorry
      have hexec_arrLoad := FragExec.single_arrLoad (am := am) harrLoad hval_idx hbounds
      -- Execute copy
      set σ_load := σ_idx[tmpName tmp1 ↦ .int (am.read arr (idx.eval σ am).toNat)]
      have hexec_copy := FragExec.single_copy (am := am) hcopy (σ := σ_load)
      refine ⟨σ_load[x ↦ σ_load (tmpName tmp1)], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_idx hexec_arrLoad) hexec_copy
        simp only [List.length_append, List.length_cons, List.length_nil] at h123 ⊢
        exact h123
      · intro v hv
        rw [show σ_load (tmpName tmp1) = .int (am.read arr (idx.eval σ am).toNat)
          from Store.update_self _ _ _]
        simp only [Store.update]
        split
        · -- v = x
          simp [SExpr.eval]
        · -- v ≠ x
          have hne : v ≠ tmpName tmp1 := isTmp_false_ne_tmpName hv
          have : (v == tmpName tmp1) = false := by rw [beq_eq_false_iff_ne]; exact hne
          simp only [σ_load, Store.update, this]
          simp [hntmp_idx v hv, hagree v hv]
    | lit n =>
      dsimp only [refCompileStmt] at hcode ⊢
      refine ⟨σ_tac[x ↦ .int (BitVec.ofInt 64 n)], FragExec.single_const (am := am) hcode.head, ?_⟩
      intro v hv
      simp only [SExpr.eval, Store.update]
      split
      · rfl
      · exact hagree v hv
    | var y =>
      dsimp only [refCompileStmt] at hcode ⊢
      have hintv_y : ∃ n, σ y = .int n := hintv_e y (by simp [SExpr.freeVars])
      obtain ⟨n, hn⟩ := hintv_y
      refine ⟨σ_tac[x ↦ σ_tac y], FragExec.single_copy hcode.head, ?_⟩
      intro v hv
      simp only [SExpr.eval, Store.update]
      split
      · rw [hagree y (htf_e y (by simp [SExpr.freeVars])), hn]; simp [Value.toInt]
      · exact hagree v hv
    | bin op a b =>
      have hintv_a : ∀ v ∈ a.freeVars, ∃ n, σ v = .int n := fun v hv => hintv_e v (List.mem_append_left _ hv)
      have hintv_b : ∀ v ∈ b.freeVars, ∃ n, σ v = .int n := fun v hv => hintv_e v (List.mem_append_right _ hv)
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_right _ hv)
      dsimp only [refCompileStmt] at hcode ⊢
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
          some (.binop x op va vb) := by
        have := hcode.right.head
        simp only [List.length_append] at this
        rwa [show offset + (codeA.length + codeB.length) =
            offset + codeA.length + codeB.length from by omega] at this
      obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a
          (SExpr.divSafe_bin_left hsafe_e) hagree hcodeA
      rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      have hintv_ba : ∀ v ∈ b.freeVars, ∃ n, σ_a v = .int n := by
        intro v hv
        obtain ⟨n, hn⟩ := hintv_b v hv
        exact ⟨n, by rw [hntmp_a v (htf_b v hv), hagree v (htf_b v hv), hn]⟩
      have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
      rw [hra] at hge_a; simp at hge_a
      obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
        refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b
          (SExpr.divSafe_bin_right hsafe_e) hagree_a hcodeB
      rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
      have hva_b : σ_b va = σ_a va := by
        rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
        · rw [hra] at h; simp at h; exact hntmp_b va h
        · rw [hra] at hlt heq; simp at hlt heq
          rw [heq, hprev_b k (by omega)]
      have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
      have hvb : σ_b vb = .int (b.eval σ am) := hval_b
      have hbsafe : op.safe (a.eval σ am) (b.eval σ am) := SExpr.divSafe_bin_safe hsafe_e
      have hexec_binop := FragExec.single_binop (am := am) hbinop hva hvb hbsafe
      refine ⟨σ_b[x ↦ .int (op.eval (a.eval σ am) (b.eval σ am))], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b) hexec_binop
        have hlen : offset + (codeA ++ codeB ++ [TAC.binop x op va vb]).length =
            offset + codeA.length + codeB.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h123
      · intro v hv
        simp only [SExpr.eval, Store.update]
        split
        · rfl
        · rw [hntmp_b v hv, hntmp_a v hv, hagree v hv]
  | bassign x b =>
    simp only [Stmt.interp, Option.some.injEq, Prod.mk.injEq] at hinterp
    obtain ⟨rfl, rfl⟩ := hinterp
    have hx_ntmp : x.isTmp = false := htmpfree x (by simp [Stmt.allVars])
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hsafe_b : b.divSafe σ am := by simp only [Stmt.divSafe] at hsafe; exact hsafe
    have hintv_b : b.intTyped σ := by simp only [Stmt.intTyped] at hintv; exact hintv
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc : refCompileBool b offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeB : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode.left
    obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, _⟩ :=
      refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hsafe_b hagree hcodeB
    rw [hrc] at hexec_b heval_b; simp at hexec_b heval_b
    have hboolop : p[offset + code.length]? = some (.boolop x be) := by
      have := hcode.right.head; simp at this; exact this
    have hexec_boolop : FragExec p (offset + code.length) σ_b (offset + code.length + 1)
        (σ_b[x ↦ .bool (be.eval σ_b)]) am am :=
      Steps.single (Step.boolop hboolop)
    refine ⟨σ_b[x ↦ .bool (be.eval σ_b)], ?_, ?_⟩
    · have h12 := FragExec.trans' hexec_b hexec_boolop
      have hlen : offset + (code ++ [TAC.boolop x be]).length =
          offset + code.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h12
    · intro v hv
      simp only [Store.update]
      split
      · next h => rw [beq_iff_eq] at h; subst h; exact congrArg Value.bool heval_b
      · exact (hntmp_b v hv).trans (hagree v hv)

  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    cases hq₁ : s₁.interp fuel σ am with
    | none => simp [hq₁] at hinterp
    | some p₁ =>
      simp [hq₁] at hinterp
      obtain ⟨σ₁, am₁⟩ := p₁
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hds₁ : s₁.divSafe fuel σ am := by simp only [Stmt.divSafe] at hsafe; exact hsafe.1
      have hds₂ : s₂.divSafe fuel σ₁ am₁ := by
        simp only [Stmt.divSafe] at hsafe; rw [hq₁] at hsafe; exact hsafe.2
      have hintv₁ : s₁.intTyped fuel σ am := by simp only [Stmt.intTyped] at hintv; exact hintv.1
      have hintv₂ : s₂.intTyped fuel σ₁ am₁ := by
        simp only [Stmt.intTyped] at hintv; rw [hq₁] at hintv; exact hintv.2
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
          (offset + code1.length) := by rw [hrc2]; exact hcode.right
      have hq₁' : s₁.interp fuel σ am = some (σ₁, am₁) := by rw [hq₁]
      obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
        ih₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁' htf₁ hds₁ hintv₁ hagree hcode1
      rw [hrc1] at hexec₁; simp at hexec₁
      obtain ⟨σ₂_tac, hexec₂, hagree₂⟩ :=
        ih₂ fuel σ₁ σ' am₁ am' (offset + code1.length) tmp1 p σ₁_tac hinterp htf₂ hds₂ hintv₂ hagree₁ hcode2
      rw [hrc2] at hexec₂; simp at hexec₂
      exact ⟨σ₂_tac, by
        simp only [List.length_append]
        rw [show offset + (code1.length + code2.length) = offset + code1.length + code2.length from by omega]
        exact FragExec.trans' hexec₁ hexec₂, hagree₂⟩

  | ite b s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have htf₁ : s₁.tmpFree :=
      fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
    have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
    obtain ⟨codeBool, be, tmpB⟩ := rcb
    generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
    obtain ⟨codeElse, tmpElse⟩ := rce
    generalize hrct : refCompileStmt s₁
        (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
    obtain ⟨codeThen, tmpThen⟩ := rct
    simp only [] at hcode ⊢
    have hbds : b.divSafe σ am := by
      simp only [Stmt.divSafe] at hsafe; exact hsafe.1
    have hintv_b : b.intTyped σ := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrcb]; exact hcode.left.left.left.left
    obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
      refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
    rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
    have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
      intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
    have hifg : p[offset + codeBool.length]? =
        some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
      have := hcode.left.left.left.right.head
      simp only [List.length_append] at this; exact this
    cases hb : b.eval σ am with
    | true =>
      simp [hb] at hinterp
      have hds₁ : s₁.divSafe fuel σ am := by
        simp only [Stmt.divSafe] at hsafe; simp [hb] at hsafe; exact hsafe.2
      have hintv₁ : s₁.intTyped fuel σ am := by
        simp only [Stmt.intTyped] at hintv; simp [hb] at hintv; exact hintv.2
      have hbe_true : be.eval σ_bool = true := by rw [heval_bool, hb]
      have hexec_if := FragExec.single_iftrue (am := am) hifg hbe_true
      have hct : CodeAt (refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
          (offset + codeBool.length + 1 + codeElse.length + 1) := by
        rw [hrct]; have := hcode.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
            offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
      obtain ⟨σ_then, hexec_then, hagree_then⟩ :=
        ih₁ fuel σ σ' am am' (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p
          σ_bool hinterp htf₁ hds₁ hintv₁ hagree_bool hct
      rw [hrct] at hexec_then; simp at hexec_then
      refine ⟨σ_then, ?_, hagree_then⟩
      have h := FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_then
      simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
      convert h using 1; omega
    | false =>
      simp [hb] at hinterp
      have hds₂ : s₂.divSafe fuel σ am := by
        simp only [Stmt.divSafe] at hsafe; simp [hb] at hsafe; exact hsafe.2
      have hintv₂ : s₂.intTyped fuel σ am := by
        simp only [Stmt.intTyped] at hintv; simp [hb] at hintv; exact hintv.2
      have hbe_false : be.eval σ_bool = false := by rw [heval_bool, hb]
      have hexec_if := FragExec.single_iffalse (am := am) hifg hbe_false
      have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
          (offset + codeBool.length + 1) := by
        rw [hrce]; have := hcode.left.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) =
            offset + codeBool.length + 1 from by omega] at this
      have hgoto_end : p[offset + codeBool.length + 1 + codeElse.length]? =
          some (.goto (offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length)) := by
        have := hcode.left.right.head
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length) =
            offset + codeBool.length + 1 + codeElse.length from by omega] at this
      obtain ⟨σ_else, hexec_else, hagree_else⟩ :=
        ih₂ fuel σ σ' am am' (offset + codeBool.length + 1) tmpB p
          σ_bool hinterp htf₂ hds₂ hintv₂ hagree_bool hce
      rw [hrce] at hexec_else; simp at hexec_else
      have hexec_goto := FragExec.single_goto (am := am') hgoto_end (σ := σ_else)
      refine ⟨σ_else, ?_, hagree_else⟩
      have h := FragExec.trans' (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_else) hexec_goto
      simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
      convert h using 1; omega

  | loop b body ih =>
    induction fuel generalizing σ am σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp only [Stmt.interp] at hinterp
      cases hb : b.eval σ am with
      | false =>
        simp [hb] at hinterp
        obtain ⟨rfl, rfl⟩ := hinterp
        -- Loop exits: eval bool, ifgoto takes exit branch
        have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
          fun v hv => htmpfree v (List.mem_append_left _ hv)
        have hbds : b.divSafe σ am := by
          simp only [Stmt.divSafe] at hsafe; exact hsafe.1
        have hintv_b : b.intTyped σ := by
          simp only [Stmt.intTyped] at hintv; exact hintv.1
        dsimp only [refCompileStmt] at hcode ⊢
        generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmpB⟩ := rcb
        generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody at hcode ⊢
        obtain ⟨codeBody, tmpBody⟩ := rcbody
        simp only [] at hcode ⊢
        have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
          refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        have hifg : p[offset + codeBool.length]? =
            some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
          have := hcode.left.left.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
        have hnotbe_true : (BoolExpr.not be).eval σ_bool = true := by
          simp [BoolExpr.eval, heval_bool, hb]
        have hexec_if := FragExec.single_iftrue (am := am) hifg hnotbe_true
        refine ⟨σ_bool, ?_, fun v hv => by rw [hntmp_bool v hv, hagree v hv]⟩
        have h := FragExec.trans' hexec_bool hexec_if
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        convert h using 1; omega
      | true =>
        simp [hb] at hinterp
        cases hq : body.interp fuel' σ am with
        | none => simp [hq] at hinterp
        | some p₁ =>
          simp [hq] at hinterp
          obtain ⟨σ₁, am₁⟩ := p₁
          have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
            fun v hv => htmpfree v (List.mem_append_left _ hv)
          have htf_body : body.tmpFree :=
            fun v hv => htmpfree v (List.mem_append_right _ hv)
          have hbds : b.divSafe σ am := by
            simp only [Stmt.divSafe] at hsafe; exact hsafe.1
          have hds_body : body.divSafe fuel' σ am := by
            simp only [Stmt.divSafe] at hsafe; simp [hb] at hsafe; exact hsafe.2.1
          have hds_loop : (Stmt.loop b body).divSafe fuel' σ₁ am₁ := by
            simp only [Stmt.divSafe] at hsafe; simp [hb] at hsafe; rw [hq] at hsafe; exact hsafe.2.2
          have hintv_b : b.intTyped σ := by
            simp only [Stmt.intTyped] at hintv; exact hintv.1
          have hintv_body : body.intTyped fuel' σ am := by
            simp only [Stmt.intTyped] at hintv; simp [hb] at hintv; exact hintv.2.1
          have hintv_loop : (Stmt.loop b body).intTyped fuel' σ₁ am₁ := by
            simp only [Stmt.intTyped] at hintv; simp [hb] at hintv; rw [hq] at hintv; exact hintv.2.2
          dsimp only [refCompileStmt] at hcode ⊢
          generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
          obtain ⟨codeBool, be, tmpB⟩ := rcb
          generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody at hcode ⊢
          obtain ⟨codeBody, tmpBody⟩ := rcbody
          simp only [] at hcode ⊢
          have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
            rw [hrcb]; exact hcode.left.left.left
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
            intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
          have hifg : p[offset + codeBool.length]? =
              some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
            have := hcode.left.left.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
          have hnotbe : (BoolExpr.not be).eval σ_bool = false := by
            simp [BoolExpr.eval, heval_bool, hb]
          have hexec_if := FragExec.single_iffalse (am := am) hifg hnotbe
          have hcbody : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
              (offset + codeBool.length + 1) := by
            rw [hrcbody]; have := hcode.left.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1) = offset + codeBool.length + 1 from by omega] at this
          obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
            ih fuel' σ σ₁ am am₁ (offset + codeBool.length + 1) tmpB p
              σ_bool hq htf_body hds_body hintv_body hagree_bool hcbody
          rw [hrcbody] at hexec_body; simp at hexec_body
          have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
              some (.goto offset) := by
            have := hcode.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                offset + codeBool.length + 1 + codeBody.length from by omega] at this
          have hexec_goto := FragExec.single_goto (am := am₁) hgoto_back (σ := σ_body)
          have hexec_iter := FragExec.trans'
            (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body)
            hexec_goto
          -- Use fuel IH to prove the remaining loop iterations
          obtain ⟨σ_final, hexec_loop, hagree_final⟩ :=
            ihf σ₁ am₁ σ_body hinterp hds_loop hintv_loop hagree_body
          dsimp only [refCompileStmt] at hexec_loop; rw [hrcb, hrcbody] at hexec_loop
          simp only [] at hexec_loop
          exact ⟨σ_final, FragExec.trans' hexec_iter hexec_loop, hagree_final⟩

-- ============================================================
-- § 12. Top-level correctness theorem
-- ============================================================

theorem refCompile_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ ArrayMem.init = some (σ', ArrayMem.init))
    (htmpfree : s.tmpFree)
    (hsafe : s.divSafe fuel σ ArrayMem.init)
    (hintv : s.intTyped fuel σ ArrayMem.init) :
    ∃ σ_tac am_h am_h', haltsWithResult (refCompile s) 0 σ σ_tac am_h am_h' ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    refCompileStmt_correct s fuel σ σ' ArrayMem.init ArrayMem.init 0 0 (refCompile s) σ
      hinterp htmpfree hsafe hintv (fun _ _ => rfl) hcode
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
