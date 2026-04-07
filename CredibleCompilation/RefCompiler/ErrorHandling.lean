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
    (hintv : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n)
    (hunsafe : ¬ e.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s am am ∧
      Step p (Cfg.run pc_s σ_s am) (Cfg.error σ_s am) ∧
      pc_s < offset + (refCompileExpr e offset nextTmp).1.length := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n => simp [SExpr.safe] at hunsafe
  | var x => simp [SExpr.safe] at hunsafe
  | arrRead arr idx ih =>
    simp only [SExpr.safe] at hunsafe
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
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _⟩ :=
        refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf hintv hidx hagree hcodeIdx
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
        have := hcode.right.head; simpa using this
      exact ⟨offset + codeIdx.length, σ_idx,
        hexec_idx,
        Step.arrLoad_boundsError harrLoad hval_idx hbounds,
        by simp [List.length_append, List.length_cons, List.length_nil]⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ih offset nextTmp σ_tac htf hintv hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
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
    by_cases ha : a.safe σ am p.arrayDecls
    · by_cases hb : b.safe σ am p.arrayDecls
      · -- Both safe, operation is unsafe
        have hop : ¬ op.safe (a.eval σ am) (b.eval σ am) := by
          intro h
          apply hunsafe
          cases op <;> simp_all [SExpr.safe, BinOp.safe]
        -- Execute a
        obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
        rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
        have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
          intro v hv; rw [hntmp_a v hv]; exact hagree v hv
        have hintv_ba : ∀ v ∈ b.freeVars, ∃ n, σ_a v = .int n := by
          intro v hv
          obtain ⟨n, hn⟩ := hintv_b v hv
          exact ⟨n, by rw [hntmp_a v (htf_b v hv), hagree v (htf_b v hv), hn]⟩
        -- Execute b
        obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
          refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hb hagree_a hcodeB
        rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
        -- Show va and vb in σ_b
        have hva_b : σ_b va = σ_a va := by
          rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
          · rw [hra] at h; simp at h; exact hntmp_b va h
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
        obtain ⟨σ_a, hexec_a, _, hntmp_a, hprev_a⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
        rw [hra] at hexec_a; simp at hexec_a
        have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
          intro v hv; rw [hntmp_a v hv]; exact hagree v hv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ihb (offset + codeA.length) tmp1 σ_a htf_b hintv_b hb hagree_a hcodeB
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- a unsafe: get stuck on a's code
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hintv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩

/-- Boolean expression stuck theorem: if `¬ sb.safe σ am p.arrayDecls`, the compiled boolean code
    reaches a stuck configuration. -/
theorem refCompileBool_stuck (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (am : ArrayMem) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hintv : sb.intTyped σ)
    (hunsafe : ¬ sb.safe σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s am am ∧
      Step p (Cfg.run pc_s σ_s am) (Cfg.error σ_s am) ∧
      pc_s < offset + (refCompileBool sb offset nextTmp).1.length := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit _ => exact absurd trivial hunsafe
  | bvar x => exact absurd trivial hunsafe
  | barrRead arr idx =>
    simp only [SBool.safe] at hunsafe
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
      obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _⟩ :=
        refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf hintv hidx hagree hcodeIdx
      rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
      have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
        have := hcode.right.head; simpa using this
      exact ⟨offset + codeIdx.length, σ_idx,
        hexec_idx,
        Step.arrLoad_boundsError harrLoad hval_idx hbounds,
        by simp [List.length_append, List.length_cons, List.length_nil]⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf hintv hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | cmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : (∀ v ∈ a.freeVars, ∃ n, σ v = .int n) ∧ (∀ v ∈ b.freeVars, ∃ n, σ v = .int n) := hintv
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
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
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
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ := ih offset nextTmp σ_tac htf hintv hunsafe hagree hcodeE
    rw [hrc] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩
  | and a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : a.intTyped σ ∧ b.intTyped σ := hintv
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
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
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
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hintv_b hb_unsafe hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a (FragExec.trans' hexec_ifA hfrag), hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hintv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | or a b iha ihb =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : a.intTyped σ ∧ b.intTyped σ := hintv
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
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
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
        ihb (offset + codeA.length + 1) (tmp1 + 1) σ_a htf_b hintv_b hb_unsafe hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a (FragExec.trans' hexec_ifA hfrag), hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hintv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

-- ============================================================
-- § 15. Statement stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but `safe` fails, the compiled
    statement code reaches a stuck configuration (division by zero). -/
theorem refCompileStmt_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store) (am am' : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ am p.arrayDecls = some (σ', am'))
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.safe fuel σ am p.arrayDecls)
    (hintv : s.intTyped fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
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
    have hintv_idx : ∀ v ∈ idx.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hintv_bval : SBool.intTyped σ bval := by
      simp only [Stmt.intTyped] at hintv; exact hintv.2
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
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
          intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hintv_bval hbval hagree_idx hcodeBool
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | arrWrite arr idx val =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hintv_idx : ∀ v ∈ idx.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hintv_val : ∀ v ∈ val.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.2
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
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
          intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hintv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | assign x e =>
    simp only [Stmt.safe] at hunsafe
    have hintv_e : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv
    cases e with
    | lit n => simp [SExpr.safe] at hunsafe
    | var y => simp [SExpr.safe] at hunsafe
    | arrRead arr idx =>
      have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp [Stmt.allVars, SExpr.freeVars]; exact Or.inr hv)
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
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_e hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        have harrLoad : p[offset + codeIdx.length]? = some (.arrLoad (tmpName tmp1) arr vIdx .int) := by
          have := hcode.right.head; simpa using this
        exact ⟨offset + codeIdx.length, σ_idx, am,
          hexec_idx,
          Step.arrLoad_boundsError harrLoad hval_idx hbounds,
          by simp [List.length_append, List.length_cons, List.length_nil]⟩
      · -- idx unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hintv_e hidx hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | bin op a b =>
      have hintv_a : ∀ v ∈ a.freeVars, ∃ n, σ v = .int n := fun v hv => hintv_e v (List.mem_append_left _ hv)
      have hintv_b : ∀ v ∈ b.freeVars, ∃ n, σ v = .int n := fun v hv => hintv_e v (List.mem_append_right _ hv)
      have htf_e : ∀ v ∈ (SExpr.bin op a b).freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
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
      by_cases ha : a.safe σ am p.arrayDecls
      · by_cases hb : b.safe σ am p.arrayDecls
        · -- Both safe, operation is unsafe
          have hop : ¬ op.safe (a.eval σ am) (b.eval σ am) := by
            intro h; apply hunsafe; cases op <;> simp_all [SExpr.safe, BinOp.safe]
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
            refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
          have hva_b : σ_b va = σ_a va := by
            rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
            · rw [hra] at h; simp at h; exact hntmp_b va h
            · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
          have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
          have hvb : σ_b vb = .int (b.eval σ am) := hval_b
          exact ⟨offset + codeA.length + codeB.length, σ_b, am,
            FragExec.trans' hexec_a hexec_b,
            unsafe_binop_errors hbinop hva hvb hop,
            by simp [List.length_append]; omega⟩
        · -- b unsafe
          obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · -- a unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | bassign x b =>
    simp only [Stmt.safe] at hunsafe
    have hintv_b : b.intTyped σ := by simp only [Stmt.intTyped] at hintv; exact hintv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc : refCompileBool b offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeB : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hunsafe hagree hcodeB
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
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
          (offset + code1.length) := by rw [hrc2]; exact hcode.right
      have hintv₁ : s₁.intTyped fuel σ am p.arrayDecls := by simp only [Stmt.intTyped] at hintv; exact hintv.1
      have hintv₂ : s₂.intTyped fuel σ₁ am₁ p.arrayDecls := by
        simp only [Stmt.intTyped] at hintv; rw [hq₁] at hintv; exact hintv.2
      by_cases hds₁ : s₁.safe fuel σ am p.arrayDecls
      · -- s₁ safe; s₂ unsafe
        have hds₂ : ¬ s₂.safe fuel σ₁ am₁ p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, hds₁, hq₁, h])
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ σ' am₁ am' (offset + code1.length) tmp1 p σ₁_tac hinterp htf₂ hds₂ hintv₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · -- s₁ unsafe
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, hfrag, hstuck,
          by simp [List.length_append]; omega⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    -- The new interp has: if b.isSafe then (if b.eval then s₁.interp else s₂.interp) else none
    -- Split the outer isSafe check
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
        have htf₁ : s₁.tmpFree :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left.left
        have hintv_b : b.intTyped σ := by
          simp only [Stmt.intTyped, hbisSafe, hb, ite_true] at hintv; exact hintv.1
        have hintv₁ : s₁.intTyped fuel σ am p.arrayDecls := by
          simp only [Stmt.intTyped, hbisSafe, hb, ite_true] at hintv; exact hintv.2
        by_cases hbds : b.safe σ am p.arrayDecls
        · have hds₁ : ¬ s₁.safe fuel σ am p.arrayDecls := by
            intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, h])
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
            intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
              σ_bool hinterp htf₁ hds₁ hintv₁ hagree_bool hct
          rw [hrct] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am_s,
            FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
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
        have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hintv_b : b.intTyped σ := by
          simp only [Stmt.intTyped, hbisSafe, hb, Bool.false_eq_true, ite_false] at hintv; exact hintv.1
        have hintv₂ : s₂.intTyped fuel σ am p.arrayDecls := by
          simp only [Stmt.intTyped, hbisSafe, hb, Bool.false_eq_true, ite_false] at hintv; exact hintv.2
        have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left.left
        by_cases hbds : b.safe σ am p.arrayDecls
        · have hds₂ : ¬ s₂.safe fuel σ am p.arrayDecls := by
            intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, h])
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
            intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
              σ_bool hinterp htf₂ hds₂ hintv₂ hagree_bool hce
          rw [hrce] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am_s,
            FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | loop b body ih =>
    induction fuel generalizing σ σ' am am' σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp only [Stmt.interp] at hinterp
      -- Extract isSafe = true from hinterp (new interp checks safety)
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
      have htf_body : body.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      have hintv_b : b.intTyped σ := by
        unfold Stmt.intTyped at hintv; exact hintv.1
      cases hb : b.eval σ am with
      | false =>
        simp [hb] at hinterp; obtain ⟨rfl, rfl⟩ := hinterp
        have hbds : ¬ b.safe σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
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
              have hintv_body : body.intTyped fuel' σ am p.arrayDecls := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
              have hintv_loop : (Stmt.loop b body).intTyped fuel' σ₁ am₁ p.arrayDecls := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; rw [hq] at hintv; exact hintv.2.2
              -- Execute one full iteration
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
                intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
                  tmpB p σ_bool hq htf_body hds_body hintv_body hagree_bool hcbody
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
                ihf σ₁ σ' am₁ am' σ_body hinterp hds_loop hintv_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
            · -- Body unsafe
              have hintv_body : body.intTyped fuel' σ am p.arrayDecls := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
                intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
                  htf_body hds_body hintv_body hagree_bool hcbody
              rw [hrcbody] at hlt; simp at hlt
              exact ⟨pc_s, σ_s, am_s,
                FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
                by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
          · -- Bool unsafe
            obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
              refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
            rw [hrcb] at hlt; simp at hlt
            exact ⟨pc_s, σ_s, am, hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

#check @refCompileStmt_stuck  -- sanity: theorem registered

-- ============================================================
-- § 16. Top-level stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but division safety fails,
    the compiled program does **not** halt. -/
theorem refCompile_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ ArrayMem.init (refCompile s).arrayDecls = some (σ', ArrayMem.init))
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.safe fuel σ ArrayMem.init (refCompile s).arrayDecls)
    (hintv : s.intTyped fuel σ ArrayMem.init (refCompile s).arrayDecls) :
    ¬ ∃ σ_tac am', haltsWithResult (refCompile s) 0 σ σ_tac ArrayMem.init am' := by
  intro ⟨σ_tac, am', hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    refCompileStmt_stuck s fuel σ σ' ArrayMem.init ArrayMem.init 0 0 (refCompile s) σ hinterp htmpfree hunsafe hintv
      (fun _ _ => rfl) hcode
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
    (hunsafe : ¬ s.safe fuel σ am p.arrayDecls)
    (hintv : s.intTyped fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
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
    have hintv_idx : ∀ v ∈ idx.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hintv_bval : SBool.intTyped σ bval := by
      simp only [Stmt.intTyped] at hintv; exact hintv.2
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
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
          intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
        -- Execute codeBool
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, hprev_bool⟩ :=
          refCompileBool_correct bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hintv_bval hbval hagree_idx hcodeBool
        rw [hrb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        -- vIdx preserved through bool compilation
        have hvidx_bool : σ_bool vIdx = σ_idx vIdx := by
          rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h; exact hntmp_bool vIdx h
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
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
          intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck bval (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_bval hintv_bval hbval hagree_idx hcodeBool
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | arrWrite arr idx val =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inl hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars, Stmt.tmpFree]; exact Or.inr hv)
    have hintv_idx : ∀ v ∈ idx.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hintv_val : ∀ v ∈ val.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv.2
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
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, hprev_idx⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
        have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
          intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
        obtain ⟨σ_val, hexec_val, hval_val, hntmp_val, hprev_val⟩ :=
          refCompileExpr_correct val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hintv_val hval hagree_idx hcodeVal
        rw [hrv] at hexec_val hval_val; simp at hexec_val hval_val
        have hvidx_val : σ_val vIdx = σ_idx vIdx := by
          rcases refCompileExpr_result_bound idx offset nextTmp htf_idx with h | ⟨k, _, hlt, heq⟩
          · rw [hri] at h; simp at h; exact hntmp_val vIdx h
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
        obtain ⟨σ_idx, hexec_idx, _, hntmp_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
        rw [hri] at hexec_idx; simp at hexec_idx
        have hagree_idx : ∀ v, v.isTmp = false → σ_idx v = σ v := by
          intro v hv; rw [hntmp_idx v hv]; exact hagree v hv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck val (offset + codeIdx.length) tmp1 σ σ_idx am p
            htf_val hintv_val hval hagree_idx hcodeVal
        rw [hrv] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_idx hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- idx unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_idx hintv_idx hidx hagree hcodeIdx
      rw [hri] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | assign x e =>
    simp only [Stmt.safe] at hunsafe
    have hintv_e : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv
    cases e with
    | lit n => simp [SExpr.safe] at hunsafe
    | var y => simp [SExpr.safe] at hunsafe
    | arrRead arr idx =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hri : refCompileExpr idx offset nextTmp = ri at hcode ⊢
      obtain ⟨codeIdx, vIdx, tmp1⟩ := ri
      simp only [] at hcode ⊢
      have htf_e : ∀ v ∈ idx.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp [Stmt.allVars, SExpr.freeVars]; exact Or.inr hv)
      have hcodeIdx : CodeAt (refCompileExpr idx offset nextTmp).1 p offset := by
        rw [hri]; exact hcode.left
      simp only [SExpr.safe] at hunsafe; push_neg at hunsafe
      by_cases hidx : idx.safe σ am p.arrayDecls
      · -- idx safe, bounds fail → bounds error on arrLoad
        have hbounds_fail := hunsafe hidx
        obtain ⟨σ_idx, hexec_idx, hval_idx, hntmp_idx, _⟩ :=
          refCompileExpr_correct idx offset nextTmp σ σ_tac am p htf_e hintv_e hidx hagree hcodeIdx
        rw [hri] at hexec_idx hval_idx; simp at hexec_idx hval_idx
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
          refCompileExpr_stuck idx offset nextTmp σ σ_tac am p htf_e hintv_e hidx hagree hcodeIdx
        rw [hri] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | bin op a b =>
      have htf_e : ∀ v ∈ (SExpr.bin op a b).freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf_e v (List.mem_append_right _ hv)
      have hintv_a : ∀ v ∈ a.freeVars, ∃ n, σ v = .int n :=
        fun v hv => hintv_e v (List.mem_append_left _ hv)
      have hintv_b : ∀ v ∈ b.freeVars, ∃ n, σ v = .int n :=
        fun v hv => hintv_e v (List.mem_append_right _ hv)
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
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
            refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
          have hva_b : σ_b va = σ_a va := by
            rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
            · rw [hra] at h; simp at h; exact hntmp_b va h
            · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
          have hva : σ_b va = .int (a.eval σ am) := by rw [hva_b, hval_a]
          have hvb : σ_b vb = .int (b.eval σ am) := hval_b
          exact ⟨offset + codeA.length + codeB.length, σ_b, am,
            FragExec.trans' hexec_a hexec_b,
            unsafe_binop_errors hbinop hva hvb hop,
            by simp [List.length_append]; omega⟩
        · -- b unsafe
          obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a am p htf_b hintv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · -- a unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck a offset nextTmp σ σ_tac am p htf_a hintv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | bassign x b =>
    simp only [Stmt.safe] at hunsafe
    have hintv_b : b.intTyped σ := by simp only [Stmt.intTyped] at hintv; exact hintv
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc : refCompileBool b offset nextTmp = rc at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := rc
    simp only [] at hcode ⊢
    have hcodeB : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrc]; exact hcode.left
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
      refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hunsafe hagree hcodeB
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
    have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
      rw [hrc1]; exact hcode.left
    have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
        (offset + code1.length) := by rw [hrc2]; exact hcode.right
    have hintv₁ : s₁.intTyped fuel σ am p.arrayDecls := by simp only [Stmt.intTyped] at hintv; exact hintv.1
    by_cases hds₁ : s₁.safe fuel σ am p.arrayDecls
    · -- s₁ safe; s₂ unsafe
      push_neg at hunsafe
      have hds₂_raw := hunsafe hds₁
      cases hq₁ : s₁.interp fuel σ am p.arrayDecls with
      | none =>
        -- s₁ doesn't terminate but is safe; intTyped should give us the rest
        simp only [Stmt.intTyped] at hintv; rw [hq₁] at hintv
        -- hintv.2 is about (s₂.intTyped fuel σ₁ am₁ p.arrayDecls) where interp is none
        -- This can't happen: safe + intTyped should guarantee termination
        -- Actually looking at the definitions more carefully:
        -- Stmt.safe for seq: s₁.safe ∧ (match s₁.interp with some => s₂.safe | none => True)
        -- So if s₁.interp = none, then safe for seq is hds₁ ∧ True, meaning hunsafe is False
        exfalso
        simp [Stmt.safe, hds₁, hq₁] at hunsafe
      | some p₁ =>
        obtain ⟨σ₁, am₁⟩ := p₁
        have hds₂ : ¬ s₂.safe fuel σ₁ am₁ p.arrayDecls := by
          rw [hq₁] at hds₂_raw; exact hds₂_raw
        have hintv₂ : s₂.intTyped fuel σ₁ am₁ p.arrayDecls := by
          simp only [Stmt.intTyped] at hintv; rw [hq₁] at hintv; exact hintv.2
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ am am₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ am₁ (offset + code1.length) tmp1 p σ₁_tac htf₂ hds₂ hintv₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- s₁ unsafe
      obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
        ih₁ fuel σ am offset nextTmp p σ_tac htf₁ hds₁ hintv₁ hagree hcode1
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
    have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrcb]; exact hcode.left.left.left.left
    have hintv_b : b.intTyped σ := by
      cases heval : b.eval σ am <;> simp only [Stmt.intTyped, heval] at hintv <;> exact hintv.1
    by_cases hbds : b.safe σ am p.arrayDecls
    · -- Bool safe; branch is unsafe
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      cases hbv : b.eval σ am with
      | true =>
        have htf₁ : s₁.tmpFree :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hds₁ : ¬ s₁.safe fuel σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, hbds, hbv, h])
        have hintv₁ : s₁.intTyped fuel σ am p.arrayDecls := by
          simp only [Stmt.intTyped, hbv] at hintv; exact hintv.2
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
            σ_bool htf₁ hds₁ hintv₁ hagree_bool hct
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | false =>
        have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hds₂ : ¬ s₂.safe fuel σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, hbds, hbv, h])
        have hintv₂ : s₂.intTyped fuel σ am p.arrayDecls := by
          simp only [Stmt.intTyped, hbv, Bool.false_eq_true, ite_false] at hintv; exact hintv.2
        have hexec_if := FragExec.single_iffalse (am := am) hifg (by rw [heval_bool, hbv])
        have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, am_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ am (offset + codeBool.length + 1) tmpB p
            σ_bool htf₂ hds₂ hintv₂ hagree_bool hce
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · -- Bool unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
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
      have htf_body : body.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      have hintv_b : b.intTyped σ := by
        unfold Stmt.intTyped at hintv; exact hintv.1
      cases hb : b.eval σ am with
      | false =>
        have hbds : ¬ b.safe σ am p.arrayDecls := by
          intro h; exact hunsafe (by simp [Stmt.safe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, am, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | true =>
        by_cases hbds : b.safe σ am p.arrayDecls
        · by_cases hds_body : body.safe fuel' σ am p.arrayDecls
          · -- Both safe; unsafety in remaining loop iterations
            have hintv_body : body.intTyped fuel' σ am p.arrayDecls := by
              unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
            cases hq : body.interp fuel' σ am p.arrayDecls with
            | none =>
              -- Body safe + intTyped but doesn't terminate; safe for loop = True when interp = none
              exfalso
              simp [Stmt.safe, hbds, hb, hds_body, hq] at hunsafe
            | some p₁ =>
              obtain ⟨σ₁, am₁⟩ := p₁
              have hds_loop : ¬ (Stmt.loop b body).safe fuel' σ₁ am₁ p.arrayDecls := by
                intro h; exact hunsafe (by simp [Stmt.safe, hbds, hb, hds_body, hq, h])
              have hintv_loop : (Stmt.loop b body).intTyped fuel' σ₁ am₁ p.arrayDecls := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; rw [hq] at hintv; exact hintv.2.2
              -- Execute one full iteration
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
                intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
                  tmpB p σ_bool hq htf_body hds_body hintv_body hagree_bool hcbody
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
                ihf σ₁ am₁ σ_body hds_loop hintv_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, am_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
          · -- Body unsafe
            have hintv_body : body.intTyped fuel' σ am p.arrayDecls := by
              unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
            obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
              refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
            rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
            have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
              intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
                htf_body hds_body hintv_body hagree_bool hcbody
            rw [hrcbody] at hlt; simp at hlt
            exact ⟨pc_s, σ_s, am_s,
              FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · -- Bool unsafe
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, am, hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

/-- If `¬ s.safe fuel σ am decls` holds for some fuel, the compiled program
    does **not** halt — it reaches a division-by-zero error. -/
theorem refCompile_unsafe (s : Stmt) (fuel : Nat) (σ : Store)
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.safe fuel σ ArrayMem.init (refCompile s).arrayDecls)
    (hintv : s.intTyped fuel σ ArrayMem.init (refCompile s).arrayDecls) :
    ¬ ∃ σ_tac am', haltsWithResult (refCompile s) 0 σ σ_tac ArrayMem.init am' := by
  intro ⟨σ_tac, am', hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe s fuel σ ArrayMem.init 0 0 (refCompile s) σ
      htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  exact error_run_no_halt hfrag herror hhalt
