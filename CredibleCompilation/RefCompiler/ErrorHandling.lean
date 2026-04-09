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
  induction s generalizing fuel σ σ' am am' offset nextTmp p σ_tac with
  | skip => simp [Stmt.safe] at hunsafe
  | barrWrite arr idx bval =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_bval : ∀ v ∈ bval.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inl hv)
    have hftf_bval : ∀ v ∈ bval.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htypedv_bval⟩ :=
      show (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧ bval.typedVars σ am by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    simp only [Stmt.safe] at hunsafe
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrb : refCompileBool bval (offset + codeIdx.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeBool, be, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left.left.left
    have hcodeBool : CodeAt (refCompileBool bval (offset + codeIdx.length) tmp1).1 p
        (offset + codeIdx.length) := by rw [hrb]; exact hcode.left.left.right
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hbval : bval.safe σ am p.arrayDecls
      · -- idx safe, bval safe, bounds fail → contradiction with hinterp
        have hsafe := Stmt.interp_some_implies_safe _ _ _ _ _ _ _ hinterp
        simp only [Stmt.safe] at hsafe
        exact absurd hsafe hunsafe
      · -- idx safe, bval unsafe
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hftf_bval htypedv_bval hbval hagree_idx hcodeBool
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | arrWrite arr idx val =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inl hv)
    have hftf_val : ∀ v ∈ val.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    obtain ⟨⟨htv_idx, hwrap_idx⟩, ⟨htv_val, hwrap_val⟩⟩ :=
      show (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
           (val.typedVars σ am ∧ val.wrapEval σ am = .int (val.eval σ am)) by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    simp only [Stmt.safe] at hunsafe
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
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hval : val.safe σ am p.arrayDecls
      · -- idx safe, val safe, bounds fail → contradiction with hinterp
        have hsafe := Stmt.interp_some_implies_safe _ _ _ _ _ _ _ hinterp
        simp only [Stmt.safe] at hsafe
        exact absurd hsafe hunsafe
      · -- idx safe, val unsafe
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | assign x e =>
    simp only [Stmt.safe] at hunsafe
    obtain ⟨htv_e, hwrap_e⟩ :=
      show e.typedVars σ am ∧ e.wrapEval σ am = .int (e.eval σ am) by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    cases e with
    | lit n => simp [SExpr.safe] at hunsafe
    | var y => simp [SExpr.safe] at hunsafe
    | arrRead arr idx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htv_e
      have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false := htf_e
      have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf_e
      dsimp only [refCompileStmt] at hcode ⊢
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
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
          have := hcode.right.head; simpa using this
        exact ⟨offset + codeIdx.length, σ_idx, am,
          hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]⟩
      · -- idx unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | bin op a b =>
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) ∧
             a.typedVars σ am ∧ b.typedVars σ am from htv_e
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_right _ hv)
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
      by_cases ha : a.safe σ am p.arrayDecls
      · by_cases hb : b.safe σ am p.arrayDecls
        · -- Both safe, operation is unsafe
          have hop : ¬ op.safe (a.eval σ am) (b.eval σ am) := by
            intro h; apply hunsafe; cases op <;> simp_all [SExpr.safe, BinOp.safe]
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
          rw [hwrap_a] at hval_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
            intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
            refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
          rw [hwrap_b] at hval_b
          have hva_b : σ_b va = σ_a va := by
            rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
            · rw [hra] at h; simp at h
              rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
              · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
              · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
            · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
          have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
          have hvb : σ_b vb = .int (b.eval σ am) := hval_b
          exact ⟨offset + codeA.length + codeB.length, σ_b, am,
            FragExec.trans' hexec_a hexec_b,
            unsafe_binop_errors hbinop hva hvb hop,
            by simp [List.length_append]; omega⟩
        · -- b unsafe
          obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
            intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · -- a unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | flit _ => simp [SExpr.safe] at hunsafe
    | fbin fop fa fb =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.fbin fop fa fb) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.fbin fop fa fb) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.fbin fop fa fb) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | intToFloat ie =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.intToFloat ie) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.intToFloat ie) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.intToFloat ie) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | floatToInt fe =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.floatToInt fe) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.floatToInt fe) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.floatToInt fe) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | farrRead farr fidx =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.farrRead farr fidx) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.farrRead farr fidx) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.farrRead farr fidx) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | bassign x b =>
    simp only [Stmt.safe] at hunsafe
    have htypedv_b : b.typedVars σ am := by simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc : refCompileBool b offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeB : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hunsafe hagree hcodeB
    rw [hrc] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, am, hfrag, hstuck,
      by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    cases hq₁ : s₁.interp fuel σ am p.arrayDecls with
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
      have hftf₁ : s₁.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have hftf₂ : s₂.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
          (offset + code1.length) := by rw [hrc2]; exact hcode.right
      have htypedv₁ : s₁.typedVars fuel σ am p.arrayDecls := by simp only [Stmt.typedVars] at htypedv; exact htypedv.1
      have htypedv₂ : s₂.typedVars fuel σ₁ am₁ p.arrayDecls := by
        simp only [Stmt.typedVars] at htypedv; rw [hq₁] at htypedv; exact htypedv.2
      by_cases hds₁ : s₁.safe fuel σ am p.arrayDecls
      · -- s₁ safe; s₂ unsafe
        have hds₂ : ¬ s₂.safe fuel σ₁ am₁ p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, hds₁, hq₁, h])
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁ htf₁ hftf₁ hds₁ htypedv₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ σ' am₁ am' (offset + code1.length) tmp1 p σ₁_tac hinterp htf₂ hftf₂ hds₂ htypedv₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · -- s₁ unsafe
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁ htf₁ hftf₁ hds₁ htypedv₁ hagree hcode1
        rw [hrc1] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, hfrag, hstuck,
          by simp [List.length_append]; omega⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    have hbisSafe : b.isSafe σ am p.arrayDecls = true := by
      by_contra h; simp [h] at hinterp
    simp only [hbisSafe, ite_true] at hinterp
    cases hb : b.eval σ am with
      | true =>
        simp only [hb, ite_true] at hinterp
        dsimp only [refCompileStmt] at hcode ⊢
        generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmpB⟩ := rcb
        generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
        obtain ⟨codeElse, tmpElse⟩ := rce
        generalize hrct : refCompileStmt s₁
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
        obtain ⟨codeThen, tmpThen⟩ := rct
        simp only [] at hcode ⊢
        have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
        have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
          fun v hv => hftmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
        have htf₁ : s₁.tmpFree :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hftf₁ : s₁.ftmpFree :=
          fun v hv => hftmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left.left
        have htypedv_b : b.typedVars σ am := by
          simp only [Stmt.typedVars, hb, ite_true] at htypedv; exact htypedv.1
        have htypedv₁ : s₁.typedVars fuel σ am p.arrayDecls := by
          simp only [Stmt.typedVars, hb, ite_true] at htypedv; exact htypedv.2
        by_cases hbds : b.safe σ am p.arrayDecls
        · have hds₁ : ¬ s₁.safe fuel σ am p.arrayDecls := by
            intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, h])
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
            intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
          have hifg : p[offset + codeBool.length]? =
              some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
            have := hcode.left.left.left.right.head
            simp only [List.length_append] at this; exact this
          have hexec_if := FragExec.single_iftrue (am := am) hifg (by rw [heval_bool, hb])
          have hct : CodeAt (refCompileStmt s₁
              (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
              (offset + codeBool.length + 1 + codeElse.length + 1) := by
            rw [hrct]; have := hcode.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
                offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
          obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
            ih₁ fuel σ σ' am am' (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p
              σ_bool hinterp htf₁ hftf₁ hds₁ htypedv₁ hagree_bool hct
          rw [hrct] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am_s,
            FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
          rw [hrcb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | false =>
        simp only [hb, Bool.false_eq_true, ite_false] at hinterp
        dsimp only [refCompileStmt] at hcode ⊢
        generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmpB⟩ := rcb
        generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
        obtain ⟨codeElse, tmpElse⟩ := rce
        generalize hrct : refCompileStmt s₁
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
        obtain ⟨codeThen, tmpThen⟩ := rct
        simp only [] at hcode ⊢
        have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
        have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
          fun v hv => hftmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
        have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hftf₂ : s₂.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
        have htypedv_b : b.typedVars σ am := by
          simp only [Stmt.typedVars, hb, Bool.false_eq_true, ite_false] at htypedv; exact htypedv.1
        have htypedv₂ : s₂.typedVars fuel σ am p.arrayDecls := by
          simp only [Stmt.typedVars, hb, Bool.false_eq_true, ite_false] at htypedv; exact htypedv.2
        have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left.left
        by_cases hbds : b.safe σ am p.arrayDecls
        · have hds₂ : ¬ s₂.safe fuel σ am p.arrayDecls := by
            intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, h])
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
            intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
          have hifg : p[offset + codeBool.length]? =
              some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
            have := hcode.left.left.left.right.head
            simp only [List.length_append] at this; exact this
          have hexec_if := FragExec.single_iffalse (am := am) hifg (by rw [heval_bool, hb])
          have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
              (offset + codeBool.length + 1) := by
            rw [hrce]; have := hcode.left.left.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1) =
                offset + codeBool.length + 1 from by omega] at this
          obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
            ih₂ fuel σ σ' am am' (offset + codeBool.length + 1) tmpB p
              σ_bool hinterp htf₂ hftf₂ hds₂ htypedv₂ hagree_bool hce
          rw [hrce] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am_s,
            FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
          rw [hrcb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | loop b body ih =>
    induction fuel generalizing σ σ' am am' σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp only [Stmt.interp] at hinterp
      have hbisSafe : b.isSafe σ am p.arrayDecls = true := by
        by_contra h; simp [h] at hinterp
      simp only [hbisSafe, ite_true] at hinterp
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody
          at hcode ⊢
      obtain ⟨codeBody, tmpBody⟩ := rcbody
      simp only [] at hcode ⊢
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
        fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have htf_body : body.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf_body : body.ftmpFree :=
        fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      have htypedv_b : b.typedVars σ am := by
        unfold Stmt.typedVars at htypedv; exact htypedv.1
      cases hb : b.eval σ am with
      | false =>
        simp [hb] at hinterp; obtain ⟨rfl, rfl⟩ := hinterp
        have hbds : ¬ b.safe σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | true =>
        simp [hb] at hinterp
        cases hq : body.interp fuel' σ am p.arrayDecls with
        | none => simp [hq] at hinterp
        | some p₁ =>
          obtain ⟨σ₁, am₁⟩ := p₁
          simp [hq] at hinterp
          by_cases hbds : b.safe σ am p.arrayDecls
          · by_cases hds_body : body.safe fuel' σ am p.arrayDecls
            · -- Both safe; unsafety in remaining loop iterations
              have hds_loop : ¬ (Stmt.loop b body).safe fuel' σ₁ am₁ p.arrayDecls := by
                intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, hds_body, hq, h])
              have htypedv_body : body.typedVars fuel' σ am p.arrayDecls := by
                unfold Stmt.typedVars at htypedv; simp [hb] at htypedv; exact htypedv.2.1
              have htypedv_loop : (Stmt.loop b body).typedVars fuel' σ₁ am₁ p.arrayDecls := by
                unfold Stmt.typedVars at htypedv; simp [hb] at htypedv; rw [hq] at htypedv; exact htypedv.2.2
              -- Execute one full iteration
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
                intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
              have hifg : p[offset + codeBool.length]? =
                  some (.ifgoto (.not be)
                    (offset + codeBool.length + 1 + codeBody.length + 1)) := by
                have := hcode.left.left.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                exact this
              have hexec_if : FragExec p _ σ_bool _ σ_bool _ _ :=
                FragExec.single_iffalse (am := am) hifg (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
              have hcbody : CodeAt (refCompileStmt body
                  (offset + codeBool.length + 1) tmpB).1 p
                  (offset + codeBool.length + 1) := by
                rw [hrcbody]; have := hcode.left.right
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1) =
                    offset + codeBool.length + 1 from by omega] at this
              obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
                refCompileStmt_correct body fuel' σ σ₁ am am₁ (offset + codeBool.length + 1)
                  tmpB p σ_bool hq htf_body hftf_body hds_body htypedv_body hagree_bool hcbody
              rw [hrcbody] at hexec_body; simp at hexec_body
              have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
                  some (.goto offset) := by
                have := hcode.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                    offset + codeBool.length + 1 + codeBody.length from by omega] at this
              have hexec_goto : FragExec p _ σ_body _ σ_body _ _ :=
                FragExec.single_goto (am := am₁) hgoto_back
              have hexec_iter := FragExec.trans'
                (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body)
                hexec_goto
              -- Use fuel IH: loop from σ₁ is unsafe
              obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
                ihf σ₁ σ' am₁ am' σ_body hinterp hds_loop htypedv_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
            · -- Body unsafe
              have htypedv_body : body.typedVars fuel' σ am p.arrayDecls := by
                unfold Stmt.typedVars at htypedv; simp [hb] at htypedv; exact htypedv.2.1
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
                intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
              have hifg : p[offset + codeBool.length]? =
                  some (.ifgoto (.not be)
                    (offset + codeBool.length + 1 + codeBody.length + 1)) := by
                have := hcode.left.left.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                exact this
              have hexec_if : FragExec p _ σ_bool _ σ_bool _ _ :=
                FragExec.single_iffalse (am := am) hifg (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
              have hcbody : CodeAt (refCompileStmt body
                  (offset + codeBool.length + 1) tmpB).1 p
                  (offset + codeBool.length + 1) := by
                rw [hrcbody]; have := hcode.left.right
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1) =
                    offset + codeBool.length + 1 from by omega] at this
              obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
                ih fuel' σ σ₁ am am₁ (offset + codeBool.length + 1) tmpB p σ_bool hq
                  htf_body hftf_body hds_body htypedv_body hagree_bool hcbody
              rw [hrcbody] at hlt; simp at hlt
              exact ⟨pc_s, σ_s, am_s,
                FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
                by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
          · -- Bool unsafe
            obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
              refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
            rw [hrcb] at hlt; simp at hlt
            exact ⟨pc_s, σ_s, am, hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | fassign x e =>
    simp only [Stmt.safe] at hunsafe
    obtain ⟨htv_e, hwrap_e⟩ :=
      show e.typedVars σ am ∧ e.wrapEval σ am = .float (e.eval σ am) by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    cases e with
    | flit _ => simp [SExpr.safe] at hunsafe
    | var _ => simp [SExpr.safe] at hunsafe
    | fbin fop fa fb =>
      -- Specialized: codeA ++ codeB ++ [.fbinop x fop va vb]
      have htf_a : ∀ v ∈ fa.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ fb.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a : ∀ v ∈ fa.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ fb.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_right _ hv)
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show fa.wrapEval σ am = .float (fa.eval σ am) ∧ fb.wrapEval σ am = .float (fb.eval σ am) ∧
             fa.typedVars σ am ∧ fb.typedVars σ am from htv_e
      simp only [SExpr.safe] at hunsafe
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hra : refCompileExpr fa offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : refCompileExpr fb (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      have hcodeA : CodeAt (refCompileExpr fa offset nextTmp).1 p offset := by
        rw [hra]; exact hcode.left.left
      have hcodeB : CodeAt (refCompileExpr fb (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
      by_cases ha : fa.safe σ am p.arrayDecls
      · have hb : ¬ fb.safe σ am p.arrayDecls := fun h => hunsafe ⟨ha, h⟩
        obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
          refCompileExpr_correct fa offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hexec_a; simp at hexec_a
        have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
          intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck fb (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck fa offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | intToFloat ie =>
      -- Specialized: codeE ++ [.intToFloat x ve]
      have htv_ie : ie.typedVars σ am := by simp [SExpr.typedVars] at htv_e; exact htv_e.2
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr ie offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr ie offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck ie offset nextTmp σ σ_tac am p htf_e hftf_e htv_ie hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | farrRead farr fidx =>
      -- Specialized: codeIdx ++ [.arrLoad t arr vIdx .float, .copy x t]
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show fidx.wrapEval σ am = .int (fidx.eval σ am) ∧ fidx.typedVars σ am from htv_e
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hri : refCompileExpr fidx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp only [] at hcode ⊢
      have hcodeIdx : CodeAt (refCompileExpr fidx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      by_cases hidx : fidx.safe σ am p.arrayDecls
      · have hbounds : ¬ (fidx.eval σ am) < arraySizeBv p.arrayDecls farr := by
          exact fun h => hunsafe ⟨hidx, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, _, _, _⟩ :=
          refCompileExpr_correct fidx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (ftmpName tmp1) farr vIdx .float) := by
          have := hcode.right.head; simpa using this
        exact ⟨offset + codeIdx.length, σ_idx, am,
          hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck fidx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | lit n =>
      -- Wildcard fallback
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.lit n) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.lit n) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.lit n) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | bin bop ba bb =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.bin bop ba bb) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.bin bop ba bb) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.bin bop ba bb) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | arrRead aarr aidx =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.arrRead aarr aidx) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.arrRead aarr aidx) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.arrRead aarr aidx) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | floatToInt fe =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.floatToInt fe) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.floatToInt fe) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.floatToInt fe) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | farrWrite arr idx val =>
    simp only [Stmt.safe] at hunsafe
    have ⟨⟨htv_idx, hwrap_idx⟩, ⟨htv_val, hwrap_val⟩⟩ :
      (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
      (val.typedVars σ am ∧ val.wrapEval σ am = .float (val.eval σ am)) := by
      simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars]; exact Or.inl hv)
    have hftf_val : ∀ v ∈ val.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
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
        some (.arrStore arr vIdx vVal .float) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeIdx.length + codeVal.length) =
          offset + codeIdx.length + codeVal.length from by omega] at this
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hval : val.safe σ am p.arrayDecls
      · -- Both safe, bounds fail
        have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
          exact fun h => hunsafe ⟨hidx, hval, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val⟩ :=
          refCompileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
        rw [hwrap_val] at hval_val
        have hvidx_val : σ_val vIdx = σ_idx vIdx := by
          rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases refCompileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_val vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
        have hvidx : σ_val vIdx = .int (idx.eval σ am) := by rw [hvidx_val, hval_idx]
        have hvval_ty : (σ_val vVal).typeOf = .float := by rw [hval_val]; simp [Value.typeOf]
        exact ⟨offset + codeIdx.length + codeVal.length, σ_val, am,
          FragExec.trans' hexec_idx hexec_val,
          Step.arrStore_boundsError harrStore hvidx hvval_ty hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · -- val unsafe
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩

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
  induction s generalizing fuel σ am offset nextTmp p σ_tac with
  | skip => simp [Stmt.safe] at hunsafe
  | barrWrite arr idx bval =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_bval : ∀ v ∈ bval.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inl hv)
    have hftf_bval : ∀ v ∈ bval.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htypedv_bval⟩ :=
      show (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧ bval.typedVars σ am by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrb : refCompileBool bval (offset + codeIdx.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeBool, be, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left.left.left
    have hcodeBool : CodeAt (refCompileBool bval (offset + codeIdx.length) tmp1).1 p
        (offset + codeIdx.length) := by rw [hrb]; exact hcode.left.left.right
    simp only [Stmt.safe] at hunsafe
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hbval : bval.safe σ am p.arrayDecls
      · -- idx safe, bval safe, bounds fail → bounds error on arrStore
        have hbounds_fail : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, hbval, h⟩
        -- Execute idx
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        -- Execute codeBool
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, hprev_bool, hfprev_bool⟩ :=
          refCompileBool_correct bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hftf_bval htypedv_bval hbval hagree_idx hcodeBool
        rw [hrb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        -- vIdx preserved through bool compilation
        have hvidx_bool : σ_bool vIdx = σ_idx vIdx := by
          rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases refCompileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_bool vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_bool j (by omega)]
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_bool k (by omega)]
        have hvidx : σ_bool vIdx = .int (idx.eval σ am) := by rw [hvidx_bool, hval_idx]
        have hge_bool := refCompileBool_nextTmp_ge bval (offset + codeIdx.length) tmp1
        rw [hrb] at hge_bool; simp at hge_bool
        -- Extract tail instructions (convCode ++ [arrStore])
        have htail := hcode.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at htail
        have hifgoto : p[offset + codeIdx.length + codeBool.length]? =
            some (.ifgoto be (offset + codeIdx.length + codeBool.length + 3)) := by
          have h := htail 0 (by simp)
          simp only [List.getElem?_cons_zero] at h
          rwa [show offset + (codeIdx.length + codeBool.length) + 0 =
              offset + codeIdx.length + codeBool.length from by omega] at h
        have hconst0 : p[offset + codeIdx.length + codeBool.length + 1]? =
            some (.const (tmpName tmp2) (.int (0 : BitVec 64))) := by
          have h := htail 1 (by simp)
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
          rwa [show offset + (codeIdx.length + codeBool.length) + 1 =
              offset + codeIdx.length + codeBool.length + 1 from by omega] at h
        have hgoto_end : p[offset + codeIdx.length + codeBool.length + 2]? =
            some (.goto (offset + codeIdx.length + codeBool.length + 3 + 1)) := by
          have h := htail 2 (by simp)
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
          rwa [show offset + (codeIdx.length + codeBool.length) + 2 =
              offset + codeIdx.length + codeBool.length + 2 from by omega] at h
        have hconst1 : p[offset + codeIdx.length + codeBool.length + 3]? =
            some (.const (tmpName tmp2) (.int (1 : BitVec 64))) := by
          have h := htail 3 (by simp)
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_nil] at h
          rwa [show offset + (codeIdx.length + codeBool.length) + 3 =
              offset + codeIdx.length + codeBool.length + 3 from by omega] at h
        have harrStore : p[offset + codeIdx.length + codeBool.length + 4]? =
            some (.arrStore arr vIdx (tmpName tmp2) .int) := by
          have h := hcode.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at h
          rwa [show offset + (codeIdx.length + codeBool.length + 4) =
              offset + codeIdx.length + codeBool.length + 4 from by omega] at h
        have hbf : ¬ (idx.eval σ am) < p.arraySizeBv arr := by
          rw [Prog.arraySizeBv]; exact hbounds_fail
        -- Case split on bool value to execute through convCode
        by_cases hb : bval.eval σ am = true
        · -- true: ifgoto taken → const 1 → arrStore boundsError
          have hbe_true : be.eval σ_bool = true := by rw [heval_bool, hb]
          have hexec_if := FragExec.single_iftrue (am := am) hifgoto hbe_true
          have hexec_c1 : FragExec p _ σ_bool _ (σ_bool[tmpName tmp2 ↦ .int 1]) am am :=
            FragExec.single_const (am := am) hconst1
          set σ_conv := σ_bool[tmpName tmp2 ↦ .int 1]
          have hvidx_conv : σ_conv vIdx = .int (idx.eval σ am) := by
            have hne : vIdx ≠ tmpName tmp2 := by
              rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
              · rw [hri] at h; simp at h; exact isTmp_false_ne_tmpName h
              · rw [hri] at hlt heq; simp at hlt heq; rw [heq]; exact tmpName_ne (by omega)
            simp only [σ_conv]; rw [Store.update_other _ _ _ _ hne, hvidx]
          have htint_ty : (σ_conv (tmpName tmp2)).typeOf = .int := by
            simp [σ_conv, Store.update_self]
          exact ⟨offset + codeIdx.length + codeBool.length + 4, σ_conv, am,
            FragExec.trans' (FragExec.trans' hexec_idx hexec_bool) (FragExec.trans' hexec_if hexec_c1),
            Step.arrStore_boundsError harrStore hvidx_conv htint_ty hbf,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · -- false: ifgoto falls through → const 0 → goto → arrStore boundsError
          have hb_false : bval.eval σ am = false := Bool.eq_false_iff.mpr hb
          have hbe_false : be.eval σ_bool = false := by rw [heval_bool, hb_false]
          have hexec_if := FragExec.single_iffalse (am := am) hifgoto hbe_false
          have hexec_c0 : FragExec p _ σ_bool _ (σ_bool[tmpName tmp2 ↦ .int 0]) am am :=
            FragExec.single_const (am := am) hconst0
          have hexec_goto : FragExec p _ (σ_bool[tmpName tmp2 ↦ .int 0]) _ (σ_bool[tmpName tmp2 ↦ .int 0]) am am :=
            FragExec.single_goto (am := am) hgoto_end
          set σ_conv := σ_bool[tmpName tmp2 ↦ .int 0]
          have hvidx_conv : σ_conv vIdx = .int (idx.eval σ am) := by
            have hne : vIdx ≠ tmpName tmp2 := by
              rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
              · rw [hri] at h; simp at h; exact isTmp_false_ne_tmpName h
              · rw [hri] at hlt heq; simp at hlt heq; rw [heq]; exact tmpName_ne (by omega)
            simp only [σ_conv]; rw [Store.update_other _ _ _ _ hne, hvidx]
          have htint_ty : (σ_conv (tmpName tmp2)).typeOf = .int := by
            simp [σ_conv, Store.update_self]
          exact ⟨offset + codeIdx.length + codeBool.length + 4, σ_conv, am,
            FragExec.trans' (FragExec.trans' hexec_idx hexec_bool)
              (FragExec.trans' (FragExec.trans' hexec_if hexec_c0) hexec_goto),
            Step.arrStore_boundsError harrStore hvidx_conv htint_ty hbf,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · -- idx safe, bval unsafe
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hftf_bval htypedv_bval hbval hagree_idx hcodeBool
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | arrWrite arr idx val =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inl hv)
    have hftf_val : ∀ v ∈ val.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    obtain ⟨⟨htv_idx, hwrap_idx⟩, ⟨htv_val, hwrap_val⟩⟩ :=
      show (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
           (val.typedVars σ am ∧ val.wrapEval σ am = .int (val.eval σ am)) by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
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
    simp only [Stmt.safe] at hunsafe
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hval : val.safe σ am p.arrayDecls
      · -- idx safe, val safe, bounds fail → bounds error on arrStore
        have hbounds_fail : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, hval, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val⟩ :=
          refCompileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
        rw [hwrap_val] at hval_val
        have hvidx_val : σ_val vIdx = σ_idx vIdx := by
          rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases refCompileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_val vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
        have hvidx : σ_val vIdx = .int (idx.eval σ am) := by rw [hvidx_val, hval_idx]
        have harrStore : p[offset + codeIdx.length + codeVal.length]? =
            some (.arrStore arr vIdx vVal .int) := by
          have := hcode.right.head
          simp only [List.length_append] at this
          rwa [show offset + (codeIdx.length + codeVal.length) =
              offset + codeIdx.length + codeVal.length from by omega] at this
        have hbf : ¬ (idx.eval σ am) < p.arraySizeBv arr := by
          rw [Prog.arraySizeBv]; exact hbounds_fail
        have hvval_ty : (σ_val vVal).typeOf = .int := by simp [hval_val, Value.typeOf]
        exact ⟨offset + codeIdx.length + codeVal.length, σ_val, am,
          FragExec.trans' hexec_idx hexec_val,
          Step.arrStore_boundsError harrStore hvidx hvval_ty hbf,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · -- idx safe, val unsafe
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | assign x e =>
    simp only [Stmt.safe] at hunsafe
    obtain ⟨htv_e, hwrap_e⟩ :=
      show e.typedVars σ am ∧ e.wrapEval σ am = .int (e.eval σ am) by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    cases e with
    | lit n => simp [SExpr.safe] at hunsafe
    | var y => simp [SExpr.safe] at hunsafe
    | arrRead arr idx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htv_e
      have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false := htf_e
      have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf_e
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
      simp only [] at hcode ⊢
      have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      simp only [SExpr.safe] at hunsafe; push_neg at hunsafe
      by_cases hidx : idx.safe σ am p.arrayDecls
      · -- idx safe, bounds fail → bounds error on arrLoad
        have hbounds_fail := hunsafe hidx
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
          have := hcode.right.head; simpa using this
        have hbf : ¬ (idx.eval σ am) < p.arraySizeBv arr := by
          rw [Prog.arraySizeBv]; exact hbounds_fail
        have hlt : offset + codeIdx.length <
            offset + (codeIdx ++ [TAC.arrLoad (tmpName tmp1) arr vIdx .int, .copy x (tmpName tmp1)]).length := by
          simp [List.length_append]
        exact ⟨offset + codeIdx.length, σ_idx, am, hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbf, hlt⟩
      · -- idx unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | bin op a b =>
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) ∧
             a.typedVars σ am ∧ b.typedVars σ am from htv_e
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a : ∀ v ∈ a.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_right _ hv)
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
      by_cases ha : a.safe σ am p.arrayDecls
      · by_cases hb : b.safe σ am p.arrayDecls
        · -- Both safe, operation is unsafe
          have hop : ¬ op.safe (a.eval σ am) (b.eval σ am) := by
            intro h; apply hunsafe; cases op <;> simp_all [SExpr.safe, BinOp.safe]
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
          rw [hwrap_a] at hval_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
            intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
            refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
          rw [hwrap_b] at hval_b
          have hva_b : σ_b va = σ_a va := by
            rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
            · rw [hra] at h; simp at h
              rcases refCompileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
              · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
              · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
            · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
          have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
          have hvb : σ_b vb = .int (b.eval σ am) := hval_b
          exact ⟨offset + codeA.length + codeB.length, σ_b, am,
            FragExec.trans' hexec_a hexec_b,
            unsafe_binop_errors hbinop hva hvb hop,
            by simp [List.length_append]; omega⟩
        · -- b unsafe
          obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
            intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · -- a unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | flit _ => simp [SExpr.safe] at hunsafe
    | fbin fop fa fb =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.fbin fop fa fb) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.fbin fop fa fb) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.fbin fop fa fb) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | intToFloat ie =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.intToFloat ie) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.intToFloat ie) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.intToFloat ie) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | floatToInt fe =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.floatToInt fe) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.floatToInt fe) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.floatToInt fe) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | farrRead farr fidx =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.farrRead farr fidx) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.farrRead farr fidx) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.farrRead farr fidx) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | bassign x b =>
    simp only [Stmt.safe] at hunsafe
    have htypedv_b : b.typedVars σ am := by simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc : refCompileBool b offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeB : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hunsafe hagree hcodeB
    rw [hrc] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, am, hfrag, hstuck,
      by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.safe] at hunsafe
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
    obtain ⟨code1, tmp1⟩ := rc1
    generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
    obtain ⟨code2, tmp2⟩ := rc2
    simp only [] at hcode ⊢
    have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf₁ : s₁.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
    have hftf₂ : s₂.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
      rw [hrc1]; exact hcode.left
    have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
        (offset + code1.length) := by rw [hrc2]; exact hcode.right
    have htypedv₁ : s₁.typedVars fuel σ am p.arrayDecls := by simp only [Stmt.typedVars] at htypedv; exact htypedv.1
    by_cases hds₁ : s₁.safe fuel σ am p.arrayDecls
    · -- s₁ safe; s₂ unsafe
      push_neg at hunsafe
      have hds₂_raw := hunsafe hds₁
      cases hq₁ : s₁.interp fuel σ am p.arrayDecls with
      | none =>
        exfalso
        simp [Stmt.safe, hds₁, hq₁] at hunsafe
      | some p₁ =>
        obtain ⟨σ₁, am₁⟩ := p₁
        have hds₂ : ¬ s₂.safe fuel σ₁ am₁ p.arrayDecls := by
          rw [hq₁] at hds₂_raw; exact hds₂_raw
        have htypedv₂ : s₂.typedVars fuel σ₁ am₁ p.arrayDecls := by
          simp only [Stmt.typedVars] at htypedv; rw [hq₁] at htypedv; exact htypedv.2
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁ htf₁ hftf₁ hds₁ htypedv₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ am₁ (offset + code1.length) tmp1 p σ₁_tac htf₂ hftf₂ hds₂ htypedv₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- s₁ unsafe
      obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
        ih₁ fuel σ am offset nextTmp p σ_tac htf₁ hftf₁ hds₁ htypedv₁ hagree hcode1
      rw [hrc1] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am_s, hfrag, hstuck,
        by simp [List.length_append]; omega⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
    obtain ⟨codeBool, be, tmpB⟩ := rcb
    generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
    obtain ⟨codeElse, tmpElse⟩ := rce
    generalize hrct : refCompileStmt s₁
        (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
    obtain ⟨codeThen, tmpThen⟩ := rct
    simp only [] at hcode ⊢
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrcb]; exact hcode.left.left.left.left
    have htypedv_b : b.typedVars σ am := by
      cases heval : b.eval σ am <;> simp only [Stmt.typedVars, heval] at htypedv <;> exact htypedv.1
    by_cases hbds : b.safe σ am p.arrayDecls
    · -- Bool safe; branch is unsafe
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
        intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      cases hbv : b.eval σ am with
      | true =>
        have htf₁ : s₁.tmpFree :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hftf₁ : s₁.ftmpFree :=
          fun v hv => hftmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hds₁ : ¬ s₁.safe fuel σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, hbds, hbv, h])
        have htypedv₁ : s₁.typedVars fuel σ am p.arrayDecls := by
          simp only [Stmt.typedVars, hbv] at htypedv; exact htypedv.2
        have hexec_if := FragExec.single_iftrue (am := am) hifg (by rw [heval_bool, hbv])
        have hct : CodeAt (refCompileStmt s₁
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
            (offset + codeBool.length + 1 + codeElse.length + 1) := by
          rw [hrct]; have := hcode.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
              offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ am (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p
            σ_bool htf₁ hftf₁ hds₁ htypedv₁ hagree_bool hct
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | false =>
        have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hftf₂ : s₂.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
        have hds₂ : ¬ s₂.safe fuel σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, hbds, hbv, h])
        have htypedv₂ : s₂.typedVars fuel σ am p.arrayDecls := by
          simp only [Stmt.typedVars, hbv, Bool.false_eq_true, ite_false] at htypedv; exact htypedv.2
        have hexec_if := FragExec.single_iffalse (am := am) hifg (by rw [heval_bool, hbv])
        have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ am (offset + codeBool.length + 1) tmpB p
            σ_bool htf₂ hftf₂ hds₂ htypedv₂ hagree_bool hce
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · -- Bool unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
      rw [hrcb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | loop b body ih =>
    induction fuel generalizing σ am σ_tac with
    | zero =>
      simp [Stmt.safe] at hunsafe
    | succ fuel' ihf =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody
          at hcode ⊢
      obtain ⟨codeBody, tmpBody⟩ := rcbody
      simp only [] at hcode ⊢
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
        fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have htf_body : body.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf_body : body.ftmpFree :=
        fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      have htypedv_b : b.typedVars σ am := by
        unfold Stmt.typedVars at htypedv; exact htypedv.1
      cases hb : b.eval σ am with
      | false =>
        have hbds : ¬ b.safe σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | true =>
        by_cases hbds : b.safe σ am p.arrayDecls
        · by_cases hds_body : body.safe fuel' σ am p.arrayDecls
          · -- Both safe; unsafety in remaining loop iterations
            have htypedv_body : body.typedVars fuel' σ am p.arrayDecls := by
              unfold Stmt.typedVars at htypedv; simp [hb] at htypedv; exact htypedv.2.1
            cases hq : body.interp fuel' σ am p.arrayDecls with
            | none =>
              exfalso
              simp [Stmt.safe, hbds, hb, hds_body, hq] at hunsafe
            | some p₁ =>
              obtain ⟨σ₁, am₁⟩ := p₁
              have hds_loop : ¬ (Stmt.loop b body).safe fuel' σ₁ am₁ p.arrayDecls := by
                intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, hds_body, hq, h])
              have htypedv_loop : (Stmt.loop b body).typedVars fuel' σ₁ am₁ p.arrayDecls := by
                unfold Stmt.typedVars at htypedv; simp [hb] at htypedv; rw [hq] at htypedv; exact htypedv.2.2
              -- Execute one full iteration
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
                intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
              have hifg : p[offset + codeBool.length]? =
                  some (.ifgoto (.not be)
                    (offset + codeBool.length + 1 + codeBody.length + 1)) := by
                have := hcode.left.left.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                exact this
              have hexec_if : FragExec p _ σ_bool _ σ_bool _ _ :=
                FragExec.single_iffalse (am := am) hifg (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
              have hcbody : CodeAt (refCompileStmt body
                  (offset + codeBool.length + 1) tmpB).1 p
                  (offset + codeBool.length + 1) := by
                rw [hrcbody]; have := hcode.left.right
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1) =
                    offset + codeBool.length + 1 from by omega] at this
              obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
                refCompileStmt_correct body fuel' σ σ₁ am am₁ (offset + codeBool.length + 1)
                  tmpB p σ_bool hq htf_body hftf_body hds_body htypedv_body hagree_bool hcbody
              rw [hrcbody] at hexec_body; simp at hexec_body
              have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
                  some (.goto offset) := by
                have := hcode.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                    offset + codeBool.length + 1 + codeBody.length from by omega] at this
              have hexec_goto : FragExec p _ σ_body _ σ_body _ _ :=
                FragExec.single_goto (am := am₁) hgoto_back
              have hexec_iter := FragExec.trans'
                (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body)
                hexec_goto
              -- Use fuel IH: loop from σ₁ is unsafe
              obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
                ihf σ₁ am₁ σ_body hds_loop htypedv_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
          · -- Body unsafe
            have htypedv_body : body.typedVars fuel' σ am p.arrayDecls := by
              unfold Stmt.typedVars at htypedv; simp [hb] at htypedv; exact htypedv.2.1
            obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
              refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
            rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
            have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
              intro v hv1 hv2; rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
            have hifg : p[offset + codeBool.length]? =
                some (.ifgoto (.not be)
                  (offset + codeBool.length + 1 + codeBody.length + 1)) := by
              have := hcode.left.left.right.head
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              exact this
            have hexec_if : FragExec p _ σ_bool _ σ_bool _ _ :=
              FragExec.single_iffalse (am := am) hifg (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
            have hcbody : CodeAt (refCompileStmt body
                (offset + codeBool.length + 1) tmpB).1 p
                (offset + codeBool.length + 1) := by
              rw [hrcbody]; have := hcode.left.right
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              rwa [show offset + (codeBool.length + 1) =
                  offset + codeBool.length + 1 from by omega] at this
            obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
              ih fuel' σ am (offset + codeBool.length + 1) tmpB p σ_bool
                htf_body hftf_body hds_body htypedv_body hagree_bool hcbody
            rw [hrcbody] at hlt; simp at hlt
            exact ⟨pc_s, σ_s, am_s,
              FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · -- Bool unsafe
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
          rw [hrcb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | fassign x e =>
    simp only [Stmt.safe] at hunsafe
    obtain ⟨htv_e, hwrap_e⟩ :=
      show e.typedVars σ am ∧ e.wrapEval σ am = .float (e.eval σ am) by
        simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars, Stmt.ftmpFree]; exact Or.inr hv)
    cases e with
    | flit _ => simp [SExpr.safe] at hunsafe
    | var _ => simp [SExpr.safe] at hunsafe
    | fbin fop fa fb =>
      have htf_a : ∀ v ∈ fa.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ fb.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a : ∀ v ∈ fa.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ fb.freeVars, v.isFTmp = false :=
        fun v hv => hftf_e v (List.mem_append_right _ hv)
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show fa.wrapEval σ am = .float (fa.eval σ am) ∧ fb.wrapEval σ am = .float (fb.eval σ am) ∧
             fa.typedVars σ am ∧ fb.typedVars σ am from htv_e
      simp only [SExpr.safe] at hunsafe
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hra : refCompileExpr fa offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : refCompileExpr fb (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      have hcodeA : CodeAt (refCompileExpr fa offset nextTmp).1 p offset := by
        rw [hra]; exact hcode.left.left
      have hcodeB : CodeAt (refCompileExpr fb (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
      by_cases ha : fa.safe σ am p.arrayDecls
      · have hb : ¬ fb.safe σ am p.arrayDecls := fun h => hunsafe ⟨ha, h⟩
        obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
          refCompileExpr_correct fa offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hexec_a; simp at hexec_a
        have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
          intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck fb (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck fa offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | intToFloat ie =>
      have htv_ie : ie.typedVars σ am := by simp [SExpr.typedVars] at htv_e; exact htv_e.2
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr ie offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr ie offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck ie offset nextTmp σ σ_tac am p htf_e hftf_e htv_ie hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | farrRead farr fidx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show fidx.wrapEval σ am = .int (fidx.eval σ am) ∧ fidx.typedVars σ am from htv_e
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hri : refCompileExpr fidx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp only [] at hcode ⊢
      have hcodeIdx : CodeAt (refCompileExpr fidx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      by_cases hidx : fidx.safe σ am p.arrayDecls
      · have hbounds : ¬ (fidx.eval σ am) < arraySizeBv p.arrayDecls farr := by
          exact fun h => hunsafe ⟨hidx, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, _, _, _⟩ :=
          refCompileExpr_correct fidx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (ftmpName tmp1) farr vIdx .float) := by
          have := hcode.right.head; simpa using this
        exact ⟨offset + codeIdx.length, σ_idx, am,
          hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck fidx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | lit n =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.lit n) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.lit n) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.lit n) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | bin bop ba bb =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.bin bop ba bb) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.bin bop ba bb) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.bin bop ba bb) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | arrRead aarr aidx =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.arrRead aarr aidx) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.arrRead aarr aidx) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.arrRead aarr aidx) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | floatToInt fe =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hre : refCompileExpr (.floatToInt fe) offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      have hcodeE : CodeAt (refCompileExpr (.floatToInt fe) offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck (.floatToInt fe) offset nextTmp σ σ_tac am p htf_e hftf_e htv_e hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | farrWrite arr idx val =>
    simp only [Stmt.safe] at hunsafe
    have ⟨⟨htv_idx, hwrap_idx⟩, ⟨htv_val, hwrap_val⟩⟩ :
      (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
      (val.typedVars σ am ∧ val.wrapEval σ am = .float (val.eval σ am)) := by
      simp only [Stmt.typedVars] at htypedv; exact htypedv
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars]; exact Or.inl hv)
    have hftf_val : ∀ v ∈ val.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
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
        some (.arrStore arr vIdx vVal .float) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rwa [show offset + (codeIdx.length + codeVal.length) =
          offset + codeIdx.length + codeVal.length from by omega] at this
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hval : val.safe σ am p.arrayDecls
      · have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
          exact fun h => hunsafe ⟨hidx, hval, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        rw [hwrap_idx] at hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val⟩ :=
          refCompileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
        rw [hwrap_val] at hval_val
        have hvidx_val : σ_val vIdx = σ_idx vIdx := by
          rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases refCompileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_val vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
        have hvidx : σ_val vIdx = .int (idx.eval σ am) := by rw [hvidx_val, hval_idx]
        have hvval_ty : (σ_val vVal).typeOf = .float := by rw [hval_val]; simp [Value.typeOf]
        exact ⟨offset + codeIdx.length + codeVal.length, σ_val, am,
          FragExec.trans' hexec_idx hexec_val,
          Step.arrStore_boundsError harrStore hvidx hvval_ty hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩

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
