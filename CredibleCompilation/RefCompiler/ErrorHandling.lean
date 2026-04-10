import CredibleCompilation.RefCompiler.Correctness

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
# Reference Compiler: Error Handling

Stuck theorems for expressions, booleans, and statements.
Unsafe error handling and generalizations.
-/

-- ============================================================
-- § 14. Expression and boolean stuck theorems
-- ============================================================

/-- If an expression is unsafe (`¬ e.safe σ am decls`),
    the compiled code reaches a stuck configuration strictly before the fragment end. -/
theorem refCompileExpr_stuck (e : SExpr) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ e.freeVars, v.isFTmp = false)
    (htypedv : e.typedVars σ am)
    (hunsafe : ¬ e.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s am am ∧
      Step p (Cfg.run pc_s σ_s am) (Cfg.error σ_s am) ∧
      pc_s < offset + (refCompileExpr e offset nextTmp).1.length := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n => simp [SExpr.safe] at hunsafe
  | var x => simp [SExpr.safe] at hunsafe
  | arrRead arr idx ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    by_cases hidx : idx.safe σ am p.arrayDecls
    · -- idx safe, bounds fail
      have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
        exact fun h => hunsafe ⟨hidx, h⟩
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
        refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf hftf htv_idx hidx hagree hcodeIdx
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      rw [hwrap_idx] at hval_idx
      have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
        have := hcode.right.head; simpa using this
      exact ⟨offset + codeIdx.length, σ_idx,
        hexec_idx,
        Step.arrLoad_boundsError harrLoad hval_idx hbounds,
        by simp [List.length_append, List.length_cons, List.length_nil]⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ih offset nextTmp σ_tac htf hftf htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
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
    by_cases ha : a.safe σ am p.arrayDecls
    · by_cases hb : b.safe σ am p.arrayDecls
      · -- Both safe, operation is unsafe
        have hop : ¬ op.safe (a.eval σ am) (b.eval σ am) := by
          intro h
          apply hunsafe
          cases op <;> simp_all [SExpr.safe, BinOp.safe]
        -- Execute a
        obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, _⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
        rw [hwrap_a] at hval_a
        have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
          intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
        -- Execute b
        obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
          refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
        rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
        rw [hwrap_b] at hval_b
        -- Show va and vb in σ_b
        have hva_b : σ_b va = σ_a va := by
          rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
          · rw [hra] at h; simp at h
            rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
            · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
          · rw [hra] at hlt heq; simp at hlt heq
            rw [heq, hprev_b k (by omega)]
        have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
        have hvb : σ_b vb = .int (b.eval σ am) := hval_b
        -- Binop errors
        exact ⟨offset + codeA.length + codeB.length, σ_b,
          FragExec.trans' hexec_a hexec_b,
          unsafe_binop_errors hbinop hva hvb hop,
          by simp [List.length_append]; omega⟩
      · -- b unsafe, a safe: execute a, then get stuck on b
        obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hexec_a; simp at hexec_a
        have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
          intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ihb (offset + codeA.length) tmp1 σ_a htf_b hftf_b htv_b hb hagree_a hcodeB
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- a unsafe: get stuck on a's code
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | flit _ => exact absurd trivial hunsafe
  | fbin fop a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_left _ hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftf v (List.mem_append_right _ hv)
    obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
      show a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) ∧
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
    simp only [SExpr.safe] at hunsafe
    by_cases ha : a.safe σ am p.arrayDecls
    · by_cases hb : b.safe σ am p.arrayDecls
      · exact absurd ⟨ha, hb⟩ hunsafe
      · -- b unsafe, a safe: execute a, then get stuck on b
        obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hexec_a; simp at hexec_a
        have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
          intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ihb (offset + codeA.length) tmp1 σ_a htf_b hftf_b htv_b hb hagree_a hcodeB
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- a unsafe: get stuck on a's code
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append]; omega⟩
  | intToFloat e ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .int (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hre : refCompileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileExpr e offset nextTmp).1 p offset := by
      rw [hre]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e hunsafe hagree hcodeE
    rw [hre] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck,
      by simp [List.length_append]; omega⟩
  | floatToInt e ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hre : refCompileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileExpr e offset nextTmp).1 p offset := by
      rw [hre]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e hunsafe hagree hcodeE
    rw [hre] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck,
      by simp [List.length_append]; omega⟩
  | floatExp e ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hre : refCompileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileExpr e offset nextTmp).1 p offset := by
      rw [hre]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e hunsafe hagree hcodeE
    rw [hre] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck,
      by simp [List.length_append]; omega⟩
  | farrRead arr idx ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    by_cases hidx : idx.safe σ am p.arrayDecls
    · -- idx safe, bounds fail
      have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
        exact fun h => hunsafe ⟨hidx, h⟩
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
        refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf hftf htv_idx hidx hagree hcodeIdx
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      rw [hwrap_idx] at hval_idx
      have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (ftmpName tmp1) arr vIdx .float) := by
        have := hcode.right.head; simpa using this
      exact ⟨offset + codeIdx.length, σ_idx,
        hexec_idx,
        Step.arrLoad_boundsError harrLoad hval_idx hbounds,
        by simp [List.length_append, List.length_cons, List.length_nil]⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ih offset nextTmp σ_tac htf hftf htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

/-- Boolean expression stuck theorem: if `¬ sb.safe σ am p.arrayDecls`, the compiled boolean code
    reaches a stuck configuration. -/
theorem refCompileBool_stuck (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ sb.freeVars, v.isFTmp = false)
    (htypedv : sb.typedVars σ am)
    (hunsafe : ¬ sb.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s am am ∧
      Step p (Cfg.run pc_s σ_s am) (Cfg.error σ_s am) ∧
      pc_s < offset + (refCompileBool sb offset nextTmp).1.length := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit _ => exact absurd trivial hunsafe
  | bvar x => exact absurd trivial hunsafe
  | barrRead arr idx =>
    simp only [SBool.safe] at hunsafe
    obtain ⟨htv_idx, hwrap_idx⟩ :=
      show idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am) from htypedv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf
    dsimp only [refCompileBool] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    by_cases hidx : idx.safe σ am p.arrayDecls
    · -- idx safe, bounds fail
      have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
        exact fun h => hunsafe ⟨hidx, h⟩
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
        refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      rw [hwrap_idx] at hval_idx
      have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
        have := hcode.right.head; simpa using this
      exact ⟨offset + codeIdx.length, σ_idx,
        hexec_idx,
        Step.arrLoad_boundsError harrLoad hval_idx hbounds,
        by simp [List.length_append, List.length_cons, List.length_nil]⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
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
    simp only [SBool.safe] at hunsafe
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
    by_cases ha : a.safe σ am p.arrayDecls
    · have hb : ¬ b.safe σ am p.arrayDecls := fun h => hunsafe ⟨ha, h⟩
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | not e ih =>
    simp only [SBool.safe] at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hrc : refCompileBool e offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileBool e offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ := ih offset nextTmp σ_tac htf hftf htypedv hunsafe hagree hcodeE
    rw [hrc] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩
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
    unfold SBool.safe at hunsafe
    push_neg at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    by_cases ha : a.safe σ am p.arrayDecls
    · have ⟨ha_eval, hb_unsafe⟩ := hunsafe ha
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htypedv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      have hba_true : ba.eval σ_a = true := by rw [heval_a, ha_eval]
      have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto (.not ba) (offset + codeA.length + 1 + codeB.length + 3)) :=
        hcode.left.left.right.head
      have hnot_ba_false : (BoolExpr.not ba).eval σ_a = false := by
        simp [BoolExpr.eval, hba_true]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hnot_ba_false
      have hcodeB : CodeAt (refCompileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
          (offset + codeA.length + 1) := by
        rw [hrb]
        have h := hcode.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        rwa [show offset + (codeA.length + 1) = offset + codeA.length + 1 from by omega] at h
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hftf_b htypedv_b hb_unsafe hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a (FragExec.trans' hexec_ifA hfrag), hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hftf_a htypedv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
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
    unfold SBool.safe at hunsafe
    push_neg at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    by_cases ha : a.safe σ am p.arrayDecls
    · have ⟨ha_eval, hb_unsafe⟩ := hunsafe ha
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htypedv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      have hba_false : ba.eval σ_a = false := by rw [heval_a, ha_eval]
      have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto ba (offset + codeA.length + 1 + codeB.length + 3)) :=
        hcode.left.left.right.head
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hba_false
      have hcodeB : CodeAt (refCompileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
          (offset + codeA.length + 1) := by
        rw [hrb]
        have h := hcode.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        rwa [show offset + (codeA.length + 1) = offset + codeA.length + 1 from by omega] at h
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hftf_b htypedv_b hb_unsafe hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a (FragExec.trans' hexec_ifA hfrag), hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hftf_a htypedv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | fcmp fcop a b =>
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
    simp only [SBool.safe] at hunsafe
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
    by_cases ha : a.safe σ am p.arrayDecls
    · have hb : ¬ b.safe σ am p.arrayDecls := fun h => hunsafe ⟨ha, h⟩
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩

-- ============================================================
-- § 15. Statement stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but `safe` fails, the compiled
    statement code reaches a stuck configuration (division by zero). -/
theorem refCompileStmt_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store) (am am' : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ am p.arrayDecls = some (σ', am'))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hunsafe : ¬ s.safe fuel σ am p.arrayDecls)
    (htypedv : s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ pc_s σ_s am_s, FragExec p offset σ_tac pc_s σ_s am am_s ∧
      Step p (Cfg.run pc_s σ_s am_s) (Cfg.error σ_s am_s) ∧
      pc_s < offset + (refCompileStmt s offset nextTmp).1.length := by
  sorry

#check @refCompileStmt_stuck  -- sanity: theorem registered

-- ============================================================
-- § 16. Top-level stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but division safety fails,
    the compiled program does **not** halt. -/
theorem refCompile_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ ArrayMem.init (refCompile s).arrayDecls = some (σ', ArrayMem.init))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hunsafe : ¬ s.safe fuel σ ArrayMem.init (refCompile s).arrayDecls)
    (htypedv : s.typedVars fuel σ ArrayMem.init (refCompile s).arrayDecls) :
    ¬ ∃ σ_tac am', haltsWithResult (refCompile s) 0 σ σ_tac ArrayMem.init am' := by
  intro ⟨σ_tac, am', hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    refCompileStmt_stuck s fuel σ σ' ArrayMem.init ArrayMem.init 0 0 (refCompile s) σ hinterp htmpfree hftmpfree hunsafe htypedv
      (fun _ _ _ => rfl) hcode
  exact error_run_no_halt hfrag herror hhalt

-- ============================================================
-- § 16b. Statement unsafe theorem (generalises stuck)
-- ============================================================

/-- If `¬ s.safe fuel σ am p.arrayDecls`, the compiled statement code reaches a stuck
    configuration (division by zero), regardless of whether `interp` terminates.
    This generalises `refCompileStmt_stuck` by dropping the `hinterp` hypothesis. -/
theorem refCompileStmt_unsafe (s : Stmt) (fuel : Nat) (σ : Store) (am : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hunsafe : ¬ s.safe fuel σ am p.arrayDecls)
    (htypedv : s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ pc_s σ_s am_s, FragExec p offset σ_tac pc_s σ_s am am_s ∧
      Step p (Cfg.run pc_s σ_s am_s) (Cfg.error σ_s am_s) ∧
      pc_s < offset + (refCompileStmt s offset nextTmp).1.length := by
  sorry

/-- If `¬ s.safe fuel σ am decls` holds for some fuel, the compiled program
    does **not** halt — it reaches a division-by-zero error. -/
theorem refCompile_unsafe (s : Stmt) (fuel : Nat) (σ : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hunsafe : ¬ s.safe fuel σ ArrayMem.init (refCompile s).arrayDecls)
    (htypedv : s.typedVars fuel σ ArrayMem.init (refCompile s).arrayDecls) :
    ¬ ∃ σ_tac am', haltsWithResult (refCompile s) 0 σ σ_tac ArrayMem.init am' := by
  intro ⟨σ_tac, am', hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe s fuel σ ArrayMem.init 0 0 (refCompile s) σ
      htmpfree hftmpfree hunsafe htypedv (fun _ _ _ => rfl) hcode
  exact error_run_no_halt hfrag herror hhalt
