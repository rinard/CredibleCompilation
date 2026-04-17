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
theorem compileExpr_stuck (e : SExpr) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ e.freeVars, v.isFTmp = false)
    (htypedv : e.typedVars σ am)
    (hunsafe : ¬ e.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : RC.CodeAt (compileExpr e offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s am am ∧
      Step p (Cfg.run pc_s σ_s am) (Cfg.error σ_s am) ∧
      pc_s < offset + (compileExpr e offset nextTmp).1.length := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n => simp [SExpr.safe] at hunsafe
  | var x => simp [SExpr.safe] at hunsafe
  | arrRead arr idx ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_idx, htv_idx⟩ :=
      show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htypedv
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    by_cases hidx : idx.safe σ am p.arrayDecls
    · -- idx safe, bounds fail
      have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
        exact fun h => hunsafe ⟨hidx, h⟩
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
        compileExpr_correct idx offset nextTmp σ σ_tac am p htf hftf htv_idx hidx hagree hcodeIdx
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
    dsimp only [compileExpr] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
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
          compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
        rw [hwrap_a] at hval_a
        have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
          intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
        -- Execute b
        obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
          compileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
        rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
        rw [hwrap_b] at hval_b
        -- Show va and vb in σ_b
        have hva_b : σ_b va = σ_a va := by
          rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
          · rw [hra] at h; simp at h
            rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with h2 | ⟨j, _, hlt2, heq2⟩
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
          compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
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
    dsimp only [compileExpr] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    simp only [SExpr.safe] at hunsafe
    by_cases ha : a.safe σ am p.arrayDecls
    · by_cases hb : b.safe σ am p.arrayDecls
      · exact absurd ⟨ha, hb⟩ hunsafe
      · -- b unsafe, a safe: execute a, then get stuck on b
        obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
          compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
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
    dsimp only [compileExpr] at hcode ⊢
    generalize hre : compileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
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
    dsimp only [compileExpr] at hcode ⊢
    generalize hre : compileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
      rw [hre]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      ih offset nextTmp σ_tac htf hftf htv_e hunsafe hagree hcodeE
    rw [hre] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck,
      by simp [List.length_append]; omega⟩
  | floatUnary op e ih =>
    simp only [SExpr.safe] at hunsafe
    obtain ⟨hwrap_e, htv_e⟩ :=
      show e.wrapEval σ am = .float (e.eval σ am) ∧ e.typedVars σ am from htypedv
    dsimp only [compileExpr] at hcode ⊢
    generalize hre : compileExpr e offset nextTmp = re at hcode ⊢
    obtain ⟨codeE, ve, tmp1⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileExpr e offset nextTmp).1 p offset := by
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
    dsimp only [compileExpr] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    by_cases hidx : idx.safe σ am p.arrayDecls
    · -- idx safe, bounds fail
      have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
        exact fun h => hunsafe ⟨hidx, h⟩
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
        compileExpr_correct idx offset nextTmp σ σ_tac am p htf hftf htv_idx hidx hagree hcodeIdx
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
theorem compileBool_stuck (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hftf : ∀ v ∈ sb.freeVars, v.isFTmp = false)
    (htypedv : sb.typedVars σ am)
    (hunsafe : ¬ sb.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : RC.CodeAt (compileBool sb offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s am am ∧
      Step p (Cfg.run pc_s σ_s am) (Cfg.error σ_s am) ∧
      pc_s < offset + (compileBool sb offset nextTmp).1.length := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit _ => exact absurd trivial hunsafe
  | bvar x => exact absurd trivial hunsafe
  | barrRead arr idx =>
    simp only [SBool.safe] at hunsafe
    obtain ⟨htv_idx, hwrap_idx⟩ :=
      show idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am) from htypedv
    have hftf_idx : ∀ v ∈ idx.freeVars, v.isFTmp = false := hftf
    dsimp only [compileBool] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left
    by_cases hidx : idx.safe σ am p.arrayDecls
    · -- idx safe, bounds fail
      have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr := by
        exact fun h => hunsafe ⟨hidx, h⟩
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
        compileExpr_correct idx offset nextTmp σ σ_tac am p htf hftf_idx htv_idx hidx hagree hcodeIdx
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
        compileExpr_stuck idx offset nextTmp σ σ_tac am p htf hftf_idx htv_idx hidx hagree hcodeIdx
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
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    by_cases ha : a.safe σ am p.arrayDecls
    · have hb : ¬ b.safe σ am p.arrayDecls := fun h => hunsafe ⟨ha, h⟩
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
        compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | not e ih =>
    simp only [SBool.safe] at hunsafe
    dsimp only [compileBool] at hcode ⊢
    generalize hrc : compileBool e offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeE : RC.CodeAt (compileBool e offset nextTmp).1 p offset := by
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
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : compileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    by_cases ha : a.safe σ am p.arrayDecls
    · have ⟨ha_eval, hb_unsafe⟩ := hunsafe ha
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _, _⟩ :=
        compileBool_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htypedv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      have hba_true : ba.eval σ_a am = true := by rw [heval_a, ha_eval]
      have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto (.not ba) (offset + codeA.length + 1 + codeB.length + 3)) :=
        hcode.left.left.right.head
      have hnot_ba_false : (BoolExpr.not ba).eval σ_a am = false := by
        simp [BoolExpr.eval, hba_true]
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hnot_ba_false
      have hcodeB : RC.CodeAt (compileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
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
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : compileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    by_cases ha : a.safe σ am p.arrayDecls
    · have ⟨ha_eval, hb_unsafe⟩ := hunsafe ha
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _, _⟩ :=
        compileBool_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htypedv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      have hba_false : ba.eval σ_a am = false := by rw [heval_a, ha_eval]
      have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto ba (offset + codeA.length + 1 + codeB.length + 3)) :=
        hcode.left.left.right.head
      have hexec_ifA := FragExec.single_iffalse (am := am) hifgA hba_false
      have hcodeB : RC.CodeAt (compileBool b (offset + codeA.length + 1) (tmp1 + 1)).1 p
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
    dsimp only [compileBool] at hcode ⊢
    generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    by_cases ha : a.safe σ am p.arrayDecls
    · have hb : ¬ b.safe σ am p.arrayDecls := fun h => hunsafe ⟨ha, h⟩
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
        compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v := by
        intro v hv1 hv2; rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hftf_b htv_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩

-- ============================================================
-- § 15. Statement stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but `safe` fails, the compiled
    statement code reaches a stuck configuration (division by zero). -/
theorem compileStmt_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store) (am am' : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ am p.arrayDecls = some (σ', am'))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hNoGoto : s.noGoto)
    (hunsafe : ¬ s.safe fuel σ am p.arrayDecls)
    (htypedv : s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (labels : List (String × Nat) := [])
    (hcode : RC.CodeAt (compileStmt s offset nextTmp labels).1 p offset) :
    ∃ pc_s σ_s am_s, FragExec p offset σ_tac pc_s σ_s am am_s ∧
      Step p (Cfg.run pc_s σ_s am_s) (Cfg.error σ_s am_s) ∧
      pc_s < offset + (compileStmt s offset nextTmp labels).1.length := by
  induction s generalizing fuel σ σ' am am' offset nextTmp σ_tac with
  | skip => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
  | label _ => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
  | goto _ => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
  | print _ _ => exact sorry  -- unverified: print not modeled in RefCompiler
  | ifgoto b _ =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · exact absurd (SBool.isSafe_implies_safe b σ am p.arrayDecls ‹_›) hunsafe
    · simp at hinterp
  | assign x e =>
    simp only [Stmt.safe] at hunsafe; simp only [Stmt.interp] at hinterp
    split at hinterp
    · exact absurd (SExpr.isSafe_implies_safe e σ am p.arrayDecls ‹_›) hunsafe
    · simp at hinterp
  | bassign x b =>
    simp only [Stmt.safe] at hunsafe; simp only [Stmt.interp] at hinterp
    split at hinterp
    · exact absurd (SBool.isSafe_implies_safe b σ am p.arrayDecls ‹_›) hunsafe
    · simp at hinterp
  | fassign x e =>
    simp only [Stmt.safe] at hunsafe; simp only [Stmt.interp] at hinterp
    split at hinterp
    · exact absurd (SExpr.isSafe_implies_safe e σ am p.arrayDecls ‹_›) hunsafe
    · simp at hinterp
  | arrWrite arr idx val =>
    simp only [Stmt.safe] at hunsafe; simp only [Stmt.interp] at hinterp
    split at hinterp
    · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact absurd ⟨SExpr.isSafe_implies_safe idx σ am _ h.1.1,
        SExpr.isSafe_implies_safe val σ am _ h.1.2, h.2⟩ hunsafe
    · simp at hinterp
  | barrWrite arr idx bval =>
    simp only [Stmt.safe] at hunsafe; simp only [Stmt.interp] at hinterp
    split at hinterp
    · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact absurd ⟨SExpr.isSafe_implies_safe idx σ am _ h.1.1,
        SBool.isSafe_implies_safe bval σ am _ h.1.2, h.2⟩ hunsafe
    · simp at hinterp
  | farrWrite arr idx val =>
    simp only [Stmt.safe] at hunsafe; simp only [Stmt.interp] at hinterp
    split at hinterp
    · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact absurd ⟨SExpr.isSafe_implies_safe idx σ am _ h.1.1,
        SExpr.isSafe_implies_safe val σ am _ h.1.2, h.2⟩ hunsafe
    · simp at hinterp
  | seq s1 s2 ih1 ih2 =>
    simp only [Stmt.interp, bind, Option.bind] at hinterp
    cases h1 : s1.interp fuel σ am p.arrayDecls with
    | none => simp [h1] at hinterp
    | some p1 =>
      obtain ⟨σ₁, am₁⟩ := p1; simp [h1] at hinterp
      simp only [Stmt.safe] at hunsafe
      simp only [Stmt.typedVars] at htypedv
      obtain ⟨htv1, htv2⟩ := htypedv; rw [h1] at htv2
      have htf1 : s1.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf1 : s1.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
      have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
      dsimp only [compileStmt] at hcode ⊢
      generalize hrc1 : compileStmt s1 offset nextTmp labels = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : compileStmt s2 (offset + code1.length) tmp1 labels = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      by_cases h_s1_safe : s1.safe fuel σ am p.arrayDecls
      · -- s1 safe → s2 unsafe
        rw [h1] at hunsafe
        have h_s2_unsafe : ¬ s2.safe fuel σ₁ am₁ p.arrayDecls := fun h => hunsafe ⟨h_s1_safe, h⟩
        obtain ⟨σ_1, hexec_1, hagree_1⟩ :=
          compileStmt_correct s1 fuel σ σ₁ am am₁ offset nextTmp p σ_tac h1 htf1 hftf1 hng1
            h_s1_safe htv1 hagree (labels := labels) (by rw [hrc1]; exact hcode.left)
        rw [hrc1] at hexec_1; simp at hexec_1
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih2 fuel σ₁ σ' am₁ am' (offset + code1.length) tmp1 σ_1 hinterp htf2 hftf2 hng2
            h_s2_unsafe htv2 hagree_1 (by rw [hrc2]; exact hcode.right)
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_1 hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · -- s1 unsafe
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih1 fuel σ σ₁ am am₁ offset nextTmp σ_tac h1 htf1 hftf1 hng1 h_s1_safe htv1 hagree
            (by rw [hrc1]; exact hcode.left)
        rw [hrc1] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | ite b s1 s2 ih1 ih2 =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · rename_i hbs
      simp only [Stmt.safe] at hunsafe
      simp only [Stmt.typedVars] at htypedv
      obtain ⟨htv_b, htv_branch⟩ := htypedv
      have hbsafe := SBool.isSafe_implies_safe b σ am p.arrayDecls hbs
      have hbranch_unsafe : ¬ (if b.eval σ am then s1.safe fuel σ am p.arrayDecls
          else s2.safe fuel σ am p.arrayDecls) := fun h => hunsafe ⟨hbsafe, h⟩
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false := fun v hv =>
        htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
      have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false := fun v hv =>
        hftmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
      have htf1 : s1.tmpFree := fun v hv =>
        htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf1 : s1.ftmpFree := fun v hv =>
        hftmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
      have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
      dsimp only [compileStmt] at hcode ⊢
      generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrce : compileStmt s2 (offset + codeBool.length + 1) tmpB labels = rce at hcode ⊢
      obtain ⟨codeElse, tmpElse⟩ := rce
      generalize hrct : compileStmt s1 (offset + codeBool.length + 1 + codeElse.length + 1)
          tmpElse labels = rct at hcode ⊢
      obtain ⟨codeThen, tmpThen⟩ := rct
      simp only [] at hcode ⊢
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
        compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htv_b hbsafe hagree
          (by rw [hrcb]; exact hcode.left.left.left.left)
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v :=
        fun v hv1 hv2 => by rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
      have hifgoto_instr : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head; simpa using this
      cases heval : b.eval σ am
      · -- false → else branch
        simp [heval] at hinterp hbranch_unsafe htv_branch
        have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr
          (by rw [heval_bool, heval])
        have hcode_else : RC.CodeAt (compileStmt s2 (offset + codeBool.length + 1) tmpB labels).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih2 fuel σ σ' am am' (offset + codeBool.length + 1) tmpB σ_bool hinterp htf2 hftf2 hng2
            hbranch_unsafe htv_branch hagree_bool hcode_else
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · -- true → then branch
        simp [heval] at hinterp hbranch_unsafe htv_branch
        have hexec_if := FragExec.single_iftrue (am := am) hifgoto_instr
          (by rw [heval_bool, heval])
        have hcode_then : RC.CodeAt (compileStmt s1
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse labels).1 p
            (offset + codeBool.length + 1 + codeElse.length + 1) := by
          rw [hrct]; have := hcode.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
              offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih1 fuel σ σ' am am' (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse
            σ_bool hinterp htf1 hftf1 hng1 hbranch_unsafe htv_branch hagree_bool hcode_then
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · simp at hinterp
  | loop b body ihb =>
    induction fuel generalizing σ am σ' am' σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ih_fuel =>
      rw [Stmt.interp.eq_9] at hinterp
      rw [Stmt.safe.eq_9] at hunsafe
      rw [Stmt.typedVars.eq_9] at htypedv
      split at hinterp
      · rename_i hbs
        obtain ⟨htv_bsafe, htv_branch⟩ := htypedv
        have hbsafe := SBool.isSafe_implies_safe b σ am p.arrayDecls hbs
        have htf_b := fun v hv => htmpfree v (List.mem_append_left _ hv)
        have hftf_b := fun v hv => hftmpfree v (List.mem_append_left _ hv)
        have htf_body : body.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hftf_body : body.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
        have hng_body : body.noGoto := hNoGoto
        have hbranch_unsafe : ¬ (if b.eval σ am then
            body.safe fuel' σ am p.arrayDecls ∧
            match body.interp fuel' σ am p.arrayDecls with
            | some (σ', am') => (Stmt.loop b body).safe fuel' σ' am' p.arrayDecls
            | none => True
          else True) := fun h => hunsafe ⟨hbsafe, h⟩
        cases heval : b.eval σ am
        · simp [heval] at hbranch_unsafe
        · simp [heval] at hinterp hbranch_unsafe htv_branch
          cases h_body : body.interp fuel' σ am p.arrayDecls with
          | none => simp [h_body] at hinterp
          | some p1 =>
            obtain ⟨σ₁, am₁⟩ := p1; simp [h_body] at hinterp htv_branch
            dsimp only [compileStmt] at hcode ⊢
            generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
            obtain ⟨codeBool, be, tmpB⟩ := rcb
            generalize hrcbody : compileStmt body (offset + codeBool.length + 1) tmpB labels = rcbody
                at hcode ⊢
            obtain ⟨codeBody, tmpBody⟩ := rcbody
            simp only [] at hcode ⊢
            obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
              compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htv_bsafe
                hbsafe hagree (by rw [hrcb]; exact hcode.left.left.left)
            rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
            have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v :=
              fun v hv1 hv2 => by rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
            have hifgoto_instr : p[offset + codeBool.length]? =
                some (.ifgoto (.not be)
                  (offset + codeBool.length + 1 + codeBody.length + 1)) := by
              have := hcode.left.left.right.head
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              exact this
            have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr
              (by simp only [BoolExpr.eval]; rw [heval_bool, heval]; decide)
            have hcode_body : RC.CodeAt (compileStmt body
                (offset + codeBool.length + 1) tmpB labels).1 p
                (offset + codeBool.length + 1) := by
              rw [hrcbody]; have := hcode.left.right
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              rwa [show offset + (codeBool.length + 1) =
                  offset + codeBool.length + 1 from by omega] at this
            by_cases h_body_safe : body.safe fuel' σ am p.arrayDecls
            · -- body safe, loop rest unsafe
              have h_loop_unsafe : ¬ (Stmt.loop b body).safe fuel' σ₁ am₁ p.arrayDecls := by
                intro h; have := hbranch_unsafe h_body_safe; rw [h_body] at this; exact this h
              obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
                compileStmt_correct body fuel' σ σ₁ am am₁
                  (offset + codeBool.length + 1) tmpB p σ_bool
                  h_body htf_body hftf_body hng_body h_body_safe htv_branch.1 hagree_bool (labels := labels) hcode_body
              rw [hrcbody] at hexec_body; simp at hexec_body
              have hgoto_instr : p[offset + codeBool.length + 1 + codeBody.length]? =
                  some (.goto offset) := by
                have := hcode.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                    offset + codeBool.length + 1 + codeBody.length from by omega] at this
              have hexec_goto := FragExec.single_goto (am := am₁) hgoto_instr (σ := σ_body)
              have hexec_iter := FragExec.trans'
                (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body) hexec_goto
              obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
                ih_fuel σ₁ σ' am₁ am' σ_body hinterp h_loop_unsafe htv_branch.2 hagree_body
              refine ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_iter hfrag, hstuck, ?_⟩
              simp only [compileStmt, hrcb, hrcbody,
                List.length_append, List.length_cons, List.length_nil] at hlt ⊢
              exact hlt
            · -- body unsafe
              obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
                ihb fuel' σ σ₁ am am₁ (offset + codeBool.length + 1) tmpB σ_bool
                  h_body htf_body hftf_body hng_body h_body_safe htv_branch.1 hagree_bool hcode_body
              rw [hrcbody] at hlt; simp at hlt
              exact ⟨pc_s, σ_s, am_s,
                FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
                by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · simp at hinterp

#check @compileStmt_stuck  -- sanity: theorem registered

-- ============================================================
-- § 16. Top-level stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but division safety fails,
    the compiled program does **not** halt. -/
theorem compileStmtToProg_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls = some (σ', ArrayMem.init))
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hNoGoto : s.noGoto)
    (hunsafe : ¬ s.safe fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls)
    (htypedv : s.typedVars fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls) :
    ¬ ∃ σ_tac am', haltsWithResult (compileStmtToProg s) 0 σ σ_tac ArrayMem.init am' := by
  intro ⟨σ_tac, am', hhalt⟩
  have hcode : RC.CodeAt (compileStmt s 0 0).1 (compileStmtToProg s) 0 := by
    intro i hi; unfold compileStmtToProg; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    compileStmt_stuck s fuel σ σ' ArrayMem.init ArrayMem.init 0 0 (compileStmtToProg s) σ hinterp htmpfree hftmpfree hNoGoto hunsafe htypedv
      (fun _ _ _ => rfl) (labels := []) hcode
  exact error_run_no_halt hfrag herror hhalt

-- ============================================================
-- § 16b. Statement unsafe theorem (generalises stuck)
-- ============================================================

/-- If `¬ s.safe fuel σ am p.arrayDecls`, the compiled statement code reaches a stuck
    configuration (division by zero), regardless of whether `interp` terminates.
    This generalises `compileStmt_stuck` by dropping the `hinterp` hypothesis. -/
theorem compileStmt_unsafe (s : Stmt) (fuel : Nat) (σ : Store) (am : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hNoGoto : s.noGoto)
    (hunsafe : ¬ s.safe fuel σ am p.arrayDecls)
    (htypedv : s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (labels : List (String × Nat) := [])
    (hcode : RC.CodeAt (compileStmt s offset nextTmp labels).1 p offset) :
    ∃ pc_s σ_s am_s, FragExec p offset σ_tac pc_s σ_s am am_s ∧
      Step p (Cfg.run pc_s σ_s am_s) (Cfg.error σ_s am_s) ∧
      pc_s < offset + (compileStmt s offset nextTmp labels).1.length := by
  induction s generalizing fuel σ am offset nextTmp σ_tac with
  | skip => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
  | label _ => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
  | goto _ => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
  | print _ _ => exact sorry  -- unverified: print not modeled in RefCompiler
  | ifgoto b _ =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false := fun v hv => htmpfree v hv
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false := fun v hv => hftmpfree v hv
    dsimp only [compileStmt] at hcode ⊢
    generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
    obtain ⟨codeB, be, tmpB⟩ := rcb; simp only [] at hcode ⊢
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      compileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv hunsafe hagree
        (by rw [hrcb]; exact hcode.left)
    rw [hrcb] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | bassign x b =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (List.mem_cons_of_mem x hv)
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (List.mem_cons_of_mem x hv)
    dsimp only [compileStmt] at hcode ⊢
    generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
    obtain ⟨codeB, be, tmpB⟩ := rcb; simp only [] at hcode ⊢
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      compileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv hunsafe hagree
        (by rw [hrcb]; exact hcode.left)
    rw [hrcb] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | assign x e =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨htv_e, hwrap_e⟩ := htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (List.mem_cons_of_mem x hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (List.mem_cons_of_mem x hv)
    cases e with
    | lit _ => exact absurd trivial hunsafe
    | var _ => exact absurd trivial hunsafe
    | flit _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | fbin _ _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | intToFloat _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | floatUnary _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | farrRead _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | floatToInt e' =>
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr (.floatToInt e') offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck (.floatToInt e') offset nextTmp σ σ_tac am p
          htf_e hftf_e htv_e hunsafe hagree (by rw [hre]; exact hcode.left)
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | bin op a b =>
      have htf_a := fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b := fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a := fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b := fun v hv => hftf_e v (List.mem_append_right _ hv)
      obtain ⟨hwrap_a, hwrap_b, htv_a, htv_b⟩ :=
        show a.wrapEval σ am = .int (a.eval σ am) ∧ b.wrapEval σ am = .int (b.eval σ am) ∧
             a.typedVars σ am ∧ b.typedVars σ am from htv_e
      dsimp only [compileStmt] at hcode ⊢
      generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb; simp only [] at hcode ⊢
      have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
        rw [hra]; exact hcode.left.left
      have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
      by_cases ha : a.safe σ am p.arrayDecls
      · by_cases hb : b.safe σ am p.arrayDecls
        · have hop : ¬ op.safe (a.eval σ am) (b.eval σ am) := by
            intro h; apply hunsafe; cases op <;> simp_all [SExpr.safe, BinOp.safe]
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, _, _⟩ :=
            compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a; rw [hwrap_a] at hval_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v :=
            fun v hv1 hv2 => by rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b, hfprev_b⟩ :=
            compileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p
              htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b; rw [hwrap_b] at hval_b
          have hva_b : σ_b va = σ_a va := by
            rcases compileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
            · rw [hra] at h; simp at h
              rcases compileExpr_result_ftmp_bound a offset nextTmp hftf_a with
                h2 | ⟨j, _, hlt2, heq2⟩
              · rw [hra] at h2; simp at h2; exact hntmp_b va h h2
              · rw [hra] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_b j (by omega)]
            · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
          have hbinop : p[offset + codeA.length + codeB.length]? =
              some (.binop x op va vb) := by
            have := hcode.right.head; simp only [List.length_append] at this
            rwa [show offset + (codeA.length + codeB.length) =
                offset + codeA.length + codeB.length from by omega] at this
          exact ⟨offset + codeA.length + codeB.length, σ_b, am,
            FragExec.trans' hexec_a hexec_b,
            unsafe_binop_errors hbinop (by rw [hva_b, hval_a]) hval_b hop,
            by simp [List.length_append]; omega⟩
        · obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
            compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v :=
            fun v hv1 hv2 => by rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            compileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p
              htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | arrRead arr idx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htv_e
      dsimp only [compileStmt] at hcode ⊢
      generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp only [] at hcode ⊢
      have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      by_cases hidx : idx.safe σ am p.arrayDecls
      · have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, _, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx; rw [hwrap_idx] at hval_idx
        have harrLoad : p[offset + codeIdx.length]? =
            some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
          have := hcode.right.head; simpa using this
        exact ⟨offset + codeIdx.length, σ_idx, am, hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileExpr_stuck idx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | fassign x e =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨htv_e, hwrap_e⟩ := htypedv
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (List.mem_cons_of_mem x hv)
    have hftf_e : ∀ v ∈ e.freeVars, v.isFTmp = false :=
      fun v hv => hftmpfree v (List.mem_cons_of_mem x hv)
    cases e with
    | flit _ => exact absurd trivial hunsafe
    | var _ => exact absurd trivial hunsafe
    | lit _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | bin _ _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | arrRead _ _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | floatToInt _ => exact absurd hwrap_e (by simp [SExpr.wrapEval])
    | intToFloat e' =>
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr e' offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      simp only [SExpr.safe] at hunsafe
      simp only [SExpr.typedVars] at htv_e
      obtain ⟨_, htv_inner⟩ := htv_e
      have hcodeE : RC.CodeAt (compileExpr e' offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck e' offset nextTmp σ σ_tac am p
          htf_e hftf_e htv_inner hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | floatUnary op' e' =>
      dsimp only [compileStmt] at hcode ⊢
      generalize hre : compileExpr e' offset nextTmp = re at hcode ⊢
      obtain ⟨codeE, ve, tmp1⟩ := re; simp only [] at hcode ⊢
      simp only [SExpr.safe] at hunsafe
      simp only [SExpr.typedVars] at htv_e
      obtain ⟨_, htv_inner⟩ := htv_e
      have hcodeE : RC.CodeAt (compileExpr e' offset nextTmp).1 p offset := by
        rw [hre]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck e' offset nextTmp σ σ_tac am p
          htf_e hftf_e htv_inner hunsafe hagree hcodeE
      rw [hre] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | fbin fop a b =>
      have htf_a := fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b := fun v hv => htf_e v (List.mem_append_right _ hv)
      have hftf_a := fun v hv => hftf_e v (List.mem_append_left _ hv)
      have hftf_b := fun v hv => hftf_e v (List.mem_append_right _ hv)
      obtain ⟨_, _, htv_a, htv_b⟩ :=
        show a.wrapEval σ am = .float (a.eval σ am) ∧ b.wrapEval σ am = .float (b.eval σ am) ∧
             a.typedVars σ am ∧ b.typedVars σ am from htv_e
      simp only [SExpr.safe] at hunsafe
      dsimp only [compileStmt] at hcode ⊢
      generalize hra : compileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : compileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb; simp only [] at hcode ⊢
      have hcodeA : RC.CodeAt (compileExpr a offset nextTmp).1 p offset := by
        rw [hra]; exact hcode.left.left
      have hcodeB : RC.CodeAt (compileExpr b (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
      by_cases ha : a.safe σ am p.arrayDecls
      · by_cases hb : b.safe σ am p.arrayDecls
        · exact absurd ⟨ha, hb⟩ hunsafe
        · obtain ⟨σ_a, hexec_a, _, hntmp_a, _, _⟩ :=
            compileExpr_correct a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → v.isFTmp = false → σ_a v = σ v :=
            fun v hv1 hv2 => by rw [hntmp_a v hv1 hv2]; exact hagree v hv1 hv2
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            compileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p
              htf_b hftf_b htv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hftf_a htv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | farrRead arr idx =>
      obtain ⟨hwrap_idx, htv_idx⟩ :=
        show idx.wrapEval σ am = .int (idx.eval σ am) ∧ idx.typedVars σ am from htv_e
      simp only [SExpr.safe] at hunsafe
      dsimp only [compileStmt] at hcode ⊢
      generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp only [] at hcode ⊢
      have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      by_cases hidx : idx.safe σ am p.arrayDecls
      · have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, _, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx; rw [hwrap_idx] at hval_idx
        have harrLoad : p[offset + codeIdx.length]? =
            some (.arrLoad (ftmpName tmp1) arr vIdx .float) := by
          have := hcode.right.head; simpa using this
        exact ⟨offset + codeIdx.length, σ_idx, am, hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileExpr_stuck idx offset nextTmp σ σ_tac am p htf_e hftf_e htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | arrWrite arr idx val =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htv_val, hwrap_val⟩ := htypedv
    have htf_idx := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf_val := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf_idx := fun v hv => hftmpfree v (List.mem_append_left _ hv)
    have hftf_val := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    dsimp only [compileStmt] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrv : compileExpr val (offset + codeIdx.length) tmp1 = rv at hcode ⊢
    obtain ⟨codeVal, vVal, tmp2⟩ := rv; simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left.left
    have hcodeVal : RC.CodeAt (compileExpr val (offset + codeIdx.length) tmp1).1 p
        (offset + codeIdx.length) := by rw [hrv]; exact hcode.left.right
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hval : val.safe σ am p.arrayDecls
      · have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, hval, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx; rw [hwrap_idx] at hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v :=
          fun v hv1 hv2 => by rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val⟩ :=
          compileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val; rw [hwrap_val] at hval_val
        have hvIdx_val : σ_val vIdx = σ_idx vIdx := by
          rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases compileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with
              h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_val vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
        have hidx_int : σ_val vIdx = .int (idx.eval σ am) := by rw [hvIdx_val, hval_idx]
        have hstore_instr : p[offset + codeIdx.length + codeVal.length]? =
            some (.arrStore arr vIdx vVal .int) := by
          have := hcode.right.head; simp only [List.length_append] at this
          rwa [show offset + (codeIdx.length + codeVal.length) =
              offset + codeIdx.length + codeVal.length from by omega] at this
        exact ⟨offset + codeIdx.length + codeVal.length, σ_val, am,
          FragExec.trans' hexec_idx hexec_val,
          Step.arrStore_boundsError hstore_instr hidx_int
            (by rw [hval_val]; simp [Value.typeOf]) hbounds,
          by simp [List.length_append]; omega⟩
      · obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v :=
          fun v hv1 hv2 => by rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
          hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | barrWrite arr idx bval =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htv_bval⟩ := htypedv
    have htf_idx := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf_bval := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf_idx := fun v hv => hftmpfree v (List.mem_append_left _ hv)
    have hftf_bval := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    by_cases hidx : (idx : SExpr).safe σ am p.arrayDecls
    · by_cases hbval : bval.safe σ am p.arrayDecls
      · -- Both safe, bounds fail: execute idx + bval + convCode, then arrStore errors
        have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, hbval, h⟩
        dsimp only [compileStmt] at hcode ⊢
        generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
        obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
        generalize hrcb : compileBool bval (offset + codeIdx.length) tmp1 = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmp2⟩ := rcb
        simp only [] at hcode ⊢
        -- Execute idx
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx, hfprev_idx⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx
            hidx hagree (by rw [hri]; exact hcode.left.left.left)
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v := by
          intro v hv1 hv2; rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        -- Execute bval
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, hprev_bool, hfprev_bool⟩ :=
          compileBool_correct bval (offset + codeIdx.length) tmp1 σ σ_idx am p htf_bval hftf_bval
            htv_bval hbval hagree_idx (by rw [hrcb]; exact hcode.left.left.right)
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        -- vIdx preserved through bool execution
        have hvIdx_bool : σ_bool vIdx = σ_idx vIdx := by
          rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases compileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_bool vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2]; exact hfprev_bool j (by omega)
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq]; exact hprev_bool k (by omega)
        have hvIdx_int : σ_bool vIdx = .int (idx.eval σ am) := by rw [hvIdx_bool, hval_idx, hwrap_idx]
        -- Code positions
        set afterCB := offset + codeIdx.length + codeBool.length with afterCB_def
        set tInt := tmpName tmp2
        -- Extract instructions
        have hconv_adj : RC.CodeAt [TAC.ifgoto be (afterCB + 3), TAC.const tInt (.int 0),
            TAC.goto (afterCB + 3 + 1), TAC.const tInt (.int 1)] p afterCB := by
          have := hcode.left.right
          simp only [List.length_append] at this; rwa [show offset + (codeIdx.length + codeBool.length) = afterCB from by omega] at this
        have h_ifg : p[afterCB]? = some (.ifgoto be (afterCB + 3)) := hconv_adj.head
        have h_const0 : p[afterCB + 1]? = some (.const tInt (.int 0)) := by
          have := hconv_adj 1 (by simp); simpa using this
        have h_goto_end : p[afterCB + 2]? = some (.goto (afterCB + 4)) := by
          have := hconv_adj 2 (by simp); simpa [show afterCB + 3 + 1 = afterCB + 4 from by omega] using this
        have h_const1 : p[afterCB + 3]? = some (.const tInt (.int 1)) := by
          have := hconv_adj 3 (by simp); simpa using this
        have h_arrStore : p[afterCB + 4]? = some (.arrStore arr vIdx tInt .int) := by
          have := hcode.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeIdx.length + codeBool.length + 4) = afterCB + 4 from by omega] at this
        -- Helper: tInt update doesn't affect vIdx
        have hvIdx_update (val : Value) : (σ_bool[tInt ↦ val]) vIdx = σ_bool vIdx := by
          rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, hge, hlt, heq⟩
          · rw [hri] at h; simp at h; exact Store.update_isTmp_ne (tmpName_isTmp tmp2) h
          · rw [hri] at hlt heq; simp at hlt heq
            have hge_b := compileBool_nextTmp_ge bval (offset + codeIdx.length) tmp1
            rw [hrcb] at hge_b; simp at hge_b
            rw [heq]; exact Store.update_tmpName_ne (by omega)
        -- Case split on bool value
        cases hbv : bval.eval σ am
        · -- false → ifgoto falls through, const 0, goto endL, arrStore errors
          have hexec_ifg := FragExec.single_iffalse (am := am) h_ifg (by rw [heval_bool, hbv])
          have hexec_c0 := FragExec.single_const (am := am) h_const0 (σ := σ_bool)
          have hexec_goto := FragExec.single_goto (am := am) h_goto_end (σ := σ_bool[tInt ↦ .int 0])
          have hfrag := FragExec.trans' (FragExec.trans' (FragExec.trans'
              (FragExec.trans' hexec_idx hexec_bool)
              hexec_ifg) hexec_c0) hexec_goto
          exact ⟨afterCB + 4, σ_bool[tInt ↦ .int (0 : BitVec 64)], am,
            by simp only [afterCB_def, List.length_append, List.length_cons, List.length_nil] at hfrag ⊢; convert hfrag using 1,
            Step.arrStore_boundsError h_arrStore
              (by rw [hvIdx_update, hvIdx_int])
              (by simp [Store.update_self, Value.typeOf]) hbounds,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · -- true → ifgoto jumps to trueL, const 1, arrStore errors
          have hexec_ifg := FragExec.single_iftrue (am := am) h_ifg (by rw [heval_bool, hbv])
          have hexec_c1 := FragExec.single_const (am := am) h_const1 (σ := σ_bool)
          have hfrag := FragExec.trans' (FragExec.trans'
              (FragExec.trans' hexec_idx hexec_bool)
              hexec_ifg) hexec_c1
          exact ⟨afterCB + 4, σ_bool[tInt ↦ .int (1 : BitVec 64)], am,
            by simp only [afterCB_def, List.length_append, List.length_cons, List.length_nil] at hfrag ⊢; convert hfrag using 1,
            Step.arrStore_boundsError h_arrStore
              (by rw [hvIdx_update, hvIdx_int])
              (by simp [Store.update_self, Value.typeOf]) hbounds,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · -- bval unsafe, idx safe: execute idx, then compileBool_stuck on bval
        dsimp only [compileStmt] at hcode ⊢
        generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
        obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
        generalize hrcb : compileBool bval (offset + codeIdx.length) tmp1 = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmp2⟩ := rcb; simp only [] at hcode ⊢
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
            hagree (by rw [hri]; exact hcode.left.left.left)
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v :=
          fun v hv1 hv2 => by rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileBool_stuck bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hftf_bval htv_bval hbval hagree_idx
            (by rw [hrcb]; exact hcode.left.left.right)
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · -- idx unsafe
      dsimp only [compileStmt] at hcode ⊢
      generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri; simp only [] at hcode ⊢
      have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left.left.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
          hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | farrWrite arr idx val =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨⟨htv_idx, hwrap_idx⟩, htv_val, hwrap_val⟩ := htypedv
    have htf_idx := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf_val := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf_idx := fun v hv => hftmpfree v (List.mem_append_left _ hv)
    have hftf_val := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    dsimp only [compileStmt] at hcode ⊢
    generalize hri : compileExpr idx offset nextTmp = ri at hcode ⊢
    obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
    generalize hrv : compileExpr val (offset + codeIdx.length) tmp1 = rv at hcode ⊢
    obtain ⟨codeVal, vVal, tmp2⟩ := rv; simp only [] at hcode ⊢
    have hcodeIdx : RC.CodeAt (compileExpr idx offset nextTmp).1 p offset := by
      rw [hri]; exact hcode.left.left
    have hcodeVal : RC.CodeAt (compileExpr val (offset + codeIdx.length) tmp1).1 p
        (offset + codeIdx.length) := by rw [hrv]; exact hcode.left.right
    by_cases hidx : idx.safe σ am p.arrayDecls
    · by_cases hval : val.safe σ am p.arrayDecls
      · have hbounds : ¬ (idx.eval σ am) < arraySizeBv p.arrayDecls arr :=
          fun h => hunsafe ⟨hidx, hval, h⟩
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx; rw [hwrap_idx] at hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v :=
          fun v hv1 hv2 => by rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val, hfprev_val⟩ :=
          compileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val; rw [hwrap_val] at hval_val
        have hvIdx_val : σ_val vIdx = σ_idx vIdx := by
          rcases compileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h
            rcases compileExpr_result_ftmp_bound idx offset nextTmp hftf_idx with
              h2 | ⟨j, _, hlt2, heq2⟩
            · rw [hri] at h2; simp at h2; exact hntmp_val vIdx h h2
            · rw [hri] at hlt2 heq2; simp at hlt2 heq2; rw [heq2, hfprev_val j (by omega)]
          · rw [hri] at hlt heq; simp at hlt heq; rw [heq, hprev_val k (by omega)]
        have hidx_int : σ_val vIdx = .int (idx.eval σ am) := by rw [hvIdx_val, hval_idx]
        have hstore_instr : p[offset + codeIdx.length + codeVal.length]? =
            some (.arrStore arr vIdx vVal .float) := by
          have := hcode.right.head; simp only [List.length_append] at this
          rwa [show offset + (codeIdx.length + codeVal.length) =
              offset + codeIdx.length + codeVal.length from by omega] at this
        exact ⟨offset + codeIdx.length + codeVal.length, σ_val, am,
          FragExec.trans' hexec_idx hexec_val,
          Step.arrStore_boundsError hstore_instr hidx_int
            (by rw [hval_val]; simp [Value.typeOf]) hbounds,
          by simp [List.length_append]; omega⟩
      · obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _, _⟩ :=
          compileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
            hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → v.isFTmp = false → σ_idx v = σ v :=
          fun v hv1 hv2 => by rw [hntmp_idx v hv1 hv2]; exact hagree v hv1 hv2
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hftf_val htv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hftf_idx htv_idx hidx
          hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | seq s1 s2 ih1 ih2 =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    have htf1 : s1.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf1 : s1.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
    have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
    have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
    dsimp only [compileStmt] at hcode ⊢
    generalize hrc1 : compileStmt s1 offset nextTmp labels = rc1 at hcode ⊢
    obtain ⟨code1, tmp1⟩ := rc1
    generalize hrc2 : compileStmt s2 (offset + code1.length) tmp1 labels = rc2 at hcode ⊢
    obtain ⟨code2, tmp2⟩ := rc2; simp only [] at hcode ⊢
    by_cases h_s1_safe : s1.safe fuel σ am p.arrayDecls
    · -- s1 safe → need s1.interp
      cases h1 : s1.interp fuel σ am p.arrayDecls with
      | none =>
        -- s1.safe ∧ interp=none → seq.safe = s1.safe ∧ True = True, contradicts hunsafe
        rw [h1] at hunsafe; exact absurd ⟨h_s1_safe, trivial⟩ hunsafe
      | some p1 =>
        obtain ⟨σ₁, am₁⟩ := p1
        have htv1 := htypedv.1; rw [h1] at htypedv; have htv2 := htypedv.2
        rw [h1] at hunsafe
        have h_s2_unsafe : ¬ s2.safe fuel σ₁ am₁ p.arrayDecls := fun h => hunsafe ⟨h_s1_safe, h⟩
        obtain ⟨σ_1, hexec_1, hagree_1⟩ :=
          compileStmt_correct s1 fuel σ σ₁ am am₁ offset nextTmp p σ_tac h1 htf1 hftf1 hng1
            h_s1_safe htv1 hagree (labels := labels) (by rw [hrc1]; exact hcode.left)
        rw [hrc1] at hexec_1; simp at hexec_1
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih2 fuel σ₁ am₁ (offset + code1.length) tmp1 σ_1 htf2 hftf2 hng2
            h_s2_unsafe htv2 hagree_1 (by rw [hrc2]; exact hcode.right)
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_1 hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- s1 unsafe
      have htv1 := htypedv.1
      obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
        ih1 fuel σ am offset nextTmp σ_tac htf1 hftf1 hng1 h_s1_safe htv1 hagree
          (by rw [hrc1]; exact hcode.left)
      rw [hrc1] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | ite b s1 s2 ih1 ih2 =>
    simp only [Stmt.safe] at hunsafe
    simp only [Stmt.typedVars] at htypedv
    obtain ⟨htv_b, htv_branch⟩ := htypedv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false := fun v hv =>
      htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false := fun v hv =>
      hftmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
    have htf1 : s1.tmpFree := fun v hv =>
      htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
    have htf2 : s2.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    have hftf1 : s1.ftmpFree := fun v hv =>
      hftmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
    have hftf2 : s2.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
    have hng1 : s1.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).1
    have hng2 : s2.noGoto := (hNoGoto : s1.noGoto ∧ s2.noGoto).2
    by_cases hbsafe : b.safe σ am p.arrayDecls
    · have hbranch_unsafe : ¬ (if b.eval σ am then s1.safe fuel σ am p.arrayDecls
          else s2.safe fuel σ am p.arrayDecls) := fun h => hunsafe ⟨hbsafe, h⟩
      dsimp only [compileStmt] at hcode ⊢
      generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrce : compileStmt s2 (offset + codeBool.length + 1) tmpB labels = rce at hcode ⊢
      obtain ⟨codeElse, tmpElse⟩ := rce
      generalize hrct : compileStmt s1 (offset + codeBool.length + 1 + codeElse.length + 1)
          tmpElse labels = rct at hcode ⊢
      obtain ⟨codeThen, tmpThen⟩ := rct; simp only [] at hcode ⊢
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
        compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htv_b hbsafe hagree
          (by rw [hrcb]; exact hcode.left.left.left.left)
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v :=
        fun v hv1 hv2 => by rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
      have hifgoto_instr : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head; simpa using this
      cases heval : b.eval σ am
      · simp [heval] at hbranch_unsafe htv_branch
        have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr
          (by rw [heval_bool, heval])
        have hcode_else : RC.CodeAt (compileStmt s2 (offset + codeBool.length + 1) tmpB labels).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih2 fuel σ am (offset + codeBool.length + 1) tmpB σ_bool htf2 hftf2 hng2
            hbranch_unsafe htv_branch hagree_bool hcode_else
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · simp [heval] at hbranch_unsafe htv_branch
        have hexec_if := FragExec.single_iftrue (am := am) hifgoto_instr
          (by rw [heval_bool, heval])
        have hcode_then : RC.CodeAt (compileStmt s1
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse labels).1 p
            (offset + codeBool.length + 1 + codeElse.length + 1) := by
          rw [hrct]; have := hcode.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
              offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih1 fuel σ am (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse
            σ_bool htf1 hftf1 hng1 hbranch_unsafe htv_branch hagree_bool hcode_then
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · -- b unsafe: error in bool code
      dsimp only [compileStmt] at hcode ⊢
      generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb; simp only [] at hcode ⊢
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        compileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htv_b hbsafe hagree
          (by rw [hrcb]; exact hcode.left.left.left.left)
      rw [hrcb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | loop b body ihb =>
    induction fuel generalizing σ am σ_tac with
    | zero => simp only [Stmt.safe] at hunsafe; exact absurd trivial hunsafe
    | succ fuel' ih_fuel =>
      rw [Stmt.safe.eq_9] at hunsafe
      rw [Stmt.typedVars.eq_9] at htypedv
      have htf_b := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have hftf_b := fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have htf_body : body.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf_body : body.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hng_body : body.noGoto := hNoGoto
      by_cases hbsafe : b.safe σ am p.arrayDecls
      · obtain ⟨htv_bsafe, htv_branch⟩ := htypedv
        have hbranch_unsafe : ¬ (if b.eval σ am then
            body.safe fuel' σ am p.arrayDecls ∧
            match body.interp fuel' σ am p.arrayDecls with
            | some (σ', am') => (Stmt.loop b body).safe fuel' σ' am' p.arrayDecls
            | none => True
          else True) := fun h => hunsafe ⟨hbsafe, h⟩
        cases heval : b.eval σ am
        · simp [heval] at hbranch_unsafe
        · simp [heval] at hbranch_unsafe htv_branch
          dsimp only [compileStmt] at hcode ⊢
          generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
          obtain ⟨codeBool, be, tmpB⟩ := rcb
          generalize hrcbody : compileStmt body (offset + codeBool.length + 1) tmpB labels = rcbody
              at hcode ⊢
          obtain ⟨codeBody, tmpBody⟩ := rcbody; simp only [] at hcode ⊢
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _, _⟩ :=
            compileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htv_bsafe
              hbsafe hagree (by rw [hrcb]; exact hcode.left.left.left)
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v :=
            fun v hv1 hv2 => by rw [hntmp_bool v hv1 hv2]; exact hagree v hv1 hv2
          have hifgoto_instr : p[offset + codeBool.length]? =
              some (.ifgoto (.not be)
                (offset + codeBool.length + 1 + codeBody.length + 1)) := by
            have := hcode.left.left.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            exact this
          have hexec_if := FragExec.single_iffalse (am := am) hifgoto_instr
            (by simp only [BoolExpr.eval]; rw [heval_bool, heval]; decide)
          have hcode_body : RC.CodeAt (compileStmt body
              (offset + codeBool.length + 1) tmpB labels).1 p
              (offset + codeBool.length + 1) := by
            rw [hrcbody]; have := hcode.left.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1) =
                offset + codeBool.length + 1 from by omega] at this
          by_cases h_body_safe : body.safe fuel' σ am p.arrayDecls
          · -- body safe, need body.interp
            cases h_body : body.interp fuel' σ am p.arrayDecls with
            | none =>
              -- body.safe ∧ interp=none → match gives True, contradicts hbranch_unsafe
              have : body.safe fuel' σ am p.arrayDecls →
                  ¬ match body.interp fuel' σ am p.arrayDecls with
                  | some (σ', am') => (Stmt.loop b body).safe fuel' σ' am' p.arrayDecls
                  | none => True := hbranch_unsafe
              rw [h_body] at this; exact absurd trivial (this h_body_safe)
            | some p1 =>
              obtain ⟨σ₁, am₁⟩ := p1
              have h_loop_unsafe : ¬ (Stmt.loop b body).safe fuel' σ₁ am₁ p.arrayDecls := by
                have := hbranch_unsafe h_body_safe; rw [h_body] at this; exact this
              rw [h_body] at htv_branch
              obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
                compileStmt_correct body fuel' σ σ₁ am am₁
                  (offset + codeBool.length + 1) tmpB p σ_bool
                  h_body htf_body hftf_body hng_body h_body_safe htv_branch.1 hagree_bool (labels := labels) hcode_body
              rw [hrcbody] at hexec_body; simp at hexec_body
              have hgoto_instr : p[offset + codeBool.length + 1 + codeBody.length]? =
                  some (.goto offset) := by
                have := hcode.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                    offset + codeBool.length + 1 + codeBody.length from by omega] at this
              have hexec_goto := FragExec.single_goto (am := am₁) hgoto_instr (σ := σ_body)
              have hexec_iter := FragExec.trans'
                (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body) hexec_goto
              obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
                ih_fuel σ₁ am₁ σ_body h_loop_unsafe htv_branch.2 hagree_body
              refine ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_iter hfrag, hstuck, ?_⟩
              simp only [compileStmt, hrcb, hrcbody,
                List.length_append, List.length_cons, List.length_nil] at hlt ⊢
              exact hlt
          · -- body unsafe
            obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
              ihb fuel' σ am (offset + codeBool.length + 1) tmpB σ_bool
                htf_body hftf_body hng_body h_body_safe htv_branch.1 hagree_bool hcode_body
            rw [hrcbody] at hlt; simp at hlt
            exact ⟨pc_s, σ_s, am_s,
              FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · -- b unsafe: error in bool code
        dsimp only [compileStmt] at hcode ⊢
        generalize hrcb : compileBool b offset nextTmp = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmpB⟩ := rcb; simp only [] at hcode ⊢
        obtain ⟨htv_bsafe, _⟩ := htypedv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          compileBool_stuck b offset nextTmp σ σ_tac am p htf_b hftf_b htv_bsafe hbsafe
            hagree (by rw [hrcb]; exact hcode.left.left.left)
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

/-- If `¬ s.safe fuel σ am decls` holds for some fuel, the compiled program
    does **not** halt — it reaches a division-by-zero error. -/
theorem compileStmtToProg_unsafe (s : Stmt) (fuel : Nat) (σ : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hNoGoto : s.noGoto)
    (hunsafe : ¬ s.safe fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls)
    (htypedv : s.typedVars fuel σ ArrayMem.init (compileStmtToProg s).arrayDecls) :
    ¬ ∃ σ_tac am', haltsWithResult (compileStmtToProg s) 0 σ σ_tac ArrayMem.init am' := by
  intro ⟨σ_tac, am', hhalt⟩
  have hcode : RC.CodeAt (compileStmt s 0 0).1 (compileStmtToProg s) 0 := by
    intro i hi; unfold compileStmtToProg; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    compileStmt_unsafe s fuel σ ArrayMem.init 0 0 (compileStmtToProg s) σ
      htmpfree hftmpfree hNoGoto hunsafe htypedv (fun _ _ _ => rfl) (labels := []) hcode
  exact error_run_no_halt hfrag herror hhalt
