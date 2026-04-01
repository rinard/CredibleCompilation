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

/-- If an expression has a division-by-zero on the evaluation path (`¬ e.divSafe σ`),
    the compiled code reaches a stuck configuration strictly before the fragment end. -/
theorem refCompileExpr_stuck (e : SExpr) (offset nextTmp : Nat) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hintv : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n)
    (hunsafe : ¬ e.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      Step p (Cfg.run pc_s σ_s) (Cfg.error σ_s) ∧
      pc_s < offset + (refCompileExpr e offset nextTmp).1.length := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n => simp [SExpr.divSafe] at hunsafe
  | var x => simp [SExpr.divSafe] at hunsafe
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
    by_cases ha : a.divSafe σ
    · by_cases hb : b.divSafe σ
      · -- Both safe, operation is unsafe
        have hop : ¬ op.safe (a.eval σ) (b.eval σ) := by
          intro h
          apply hunsafe
          cases op <;> simp_all [SExpr.divSafe, BinOp.safe]
        -- Execute a
        obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
        rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
        have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
          intro v hv; rw [hntmp_a v hv]; exact hagree v hv
        have hintv_ba : ∀ v ∈ b.freeVars, ∃ n, σ_a v = .int n := by
          intro v hv
          obtain ⟨n, hn⟩ := hintv_b v hv
          exact ⟨n, by rw [hntmp_a v (htf_b v hv), hagree v (htf_b v hv), hn]⟩
        -- Execute b
        obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
          refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a p htf_b hintv_b hb hagree_a hcodeB
        rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
        -- Show va and vb in σ_b
        have hva_b : σ_b va = σ_a va := by
          rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
          · rw [hra] at h; simp at h; exact hntmp_b va h
          · rw [hra] at hlt heq; simp at hlt heq
            rw [heq, hprev_b k (by omega)]
        have hva : σ_b va = .int (a.eval σ) := by rw [hva_b, hval_a]
        have hvb : σ_b vb = .int (b.eval σ) := hval_b
        -- Binop errors
        exact ⟨offset + codeA.length + codeB.length, σ_b,
          FragExec.trans' hexec_a hexec_b,
          unsafe_binop_errors hbinop hva hvb hop,
          by simp [List.length_append]; omega⟩
      · -- b unsafe, a safe: execute a, then get stuck on b
        obtain ⟨σ_a, hexec_a, _, hntmp_a, hprev_a⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
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

/-- Boolean expression stuck theorem: if `¬ sb.divSafe σ`, the compiled boolean code
    reaches a stuck configuration. -/
theorem refCompileBool_stuck (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hintv : sb.intTyped σ)
    (hunsafe : ¬ sb.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      Step p (Cfg.run pc_s σ_s) (Cfg.error σ_s) ∧
      pc_s < offset + (refCompileBool sb offset nextTmp).1.length := by
  induction sb generalizing offset nextTmp σ_tac with
  | lit _ => exact absurd trivial hunsafe
  | bvar x => exact absurd trivial hunsafe
  | cmp cop a b =>
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have ⟨hintv_a, hintv_b⟩ : (∀ v ∈ a.freeVars, ∃ n, σ v = .int n) ∧ (∀ v ∈ b.freeVars, ∃ n, σ v = .int n) := hintv
    simp only [SBool.divSafe] at hunsafe
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
    by_cases ha : a.divSafe σ
    · have hb : ¬ b.divSafe σ := fun h => hunsafe ⟨ha, h⟩
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a p htf_b hintv_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | not e ih =>
    simp only [SBool.divSafe] at hunsafe
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
    unfold SBool.divSafe at hunsafe
    push_neg at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    by_cases ha : a.divSafe σ
    · -- a safe, so ¬(a.eval σ = true → b.divSafe σ), i.e. a.eval σ = true ∧ ¬b.divSafe σ
      have ⟨ha_eval, hb_unsafe⟩ := hunsafe ha
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      -- ifgoto (.not ba) falls through since a.eval σ = true
      have hba_true : ba.eval σ_a = true := by rw [heval_a, ha_eval]
      have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto (.not ba) (offset + codeA.length + 1 + codeB.length + 3)) :=
        hcode.left.left.right.head
      have hnot_ba_false : (BoolExpr.not ba).eval σ_a = false := by
        simp [BoolExpr.eval, hba_true]
      have hexec_ifA := FragExec.single_iffalse hifgA hnot_ba_false
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
    · -- a unsafe: stuck in codeA
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
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
    unfold SBool.divSafe at hunsafe
    push_neg at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length + 1) (tmp1 + 1) = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left.left
    by_cases ha : a.divSafe σ
    · -- a safe, so ¬(a.eval σ = false → b.divSafe σ), i.e. a.eval σ = false ∧ ¬b.divSafe σ
      have ⟨ha_eval, hb_unsafe⟩ := hunsafe ha
      obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
      rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      -- ifgoto ba falls through since a.eval σ = false
      have hba_false : ba.eval σ_a = false := by rw [heval_a, ha_eval]
      have hifgA : p[offset + codeA.length]? = some (TAC.ifgoto ba (offset + codeA.length + 1 + codeB.length + 3)) :=
        hcode.left.left.right.head
      have hexec_ifA := FragExec.single_iffalse hifgA hba_false
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
    · -- a unsafe: stuck in codeA
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a hintv_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

-- ============================================================
-- § 15. Statement stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but `divSafe` fails, the compiled
    statement code reaches a stuck configuration (division by zero). -/
theorem refCompileStmt_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ = some σ')
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.divSafe fuel σ)
    (hintv : s.intTyped fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      Step p (Cfg.run pc_s σ_s) (Cfg.error σ_s) ∧
      pc_s < offset + (refCompileStmt s offset nextTmp).1.length := by
  induction s generalizing fuel σ σ' offset nextTmp p σ_tac with
  | skip => simp [Stmt.divSafe] at hunsafe
  | assign x e =>
    simp only [Stmt.divSafe] at hunsafe
    have hintv_e : ∀ v ∈ e.freeVars, ∃ n, σ v = .int n := by
      simp only [Stmt.intTyped] at hintv; exact hintv
    cases e with
    | lit n => simp [SExpr.divSafe] at hunsafe
    | var y => simp [SExpr.divSafe] at hunsafe
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
      by_cases ha : a.divSafe σ
      · by_cases hb : b.divSafe σ
        · -- Both safe, operation is unsafe
          have hop : ¬ op.safe (a.eval σ) (b.eval σ) := by
            intro h; apply hunsafe; cases op <;> simp_all [SExpr.divSafe, BinOp.safe]
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, hprev_a⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, hprev_b⟩ :=
            refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a p htf_b hintv_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
          have hva_b : σ_b va = σ_a va := by
            rcases refCompileExpr_result_bound a offset nextTmp htf_a with h | ⟨k, _, hlt, heq⟩
            · rw [hra] at h; simp at h; exact hntmp_b va h
            · rw [hra] at hlt heq; simp at hlt heq; rw [heq, hprev_b k (by omega)]
          have hva : σ_b va = .int (a.eval σ) := by rw [hva_b, hval_a]
          have hvb : σ_b vb = .int (b.eval σ) := hval_b
          exact ⟨offset + codeA.length + codeB.length, σ_b,
            FragExec.trans' hexec_a hexec_b,
            unsafe_binop_errors hbinop hva hvb hop,
            by simp [List.length_append]; omega⟩
        · -- b unsafe
          obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a p htf_b hintv_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · -- a unsafe
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck a offset nextTmp σ σ_tac p htf_a hintv_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | bassign x b =>
    simp only [Stmt.divSafe] at hunsafe
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
      refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hunsafe hagree hcodeB
    rw [hrc] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck,
      by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    cases hq₁ : s₁.interp fuel σ with
    | none => simp [hq₁] at hinterp
    | some σ₁ =>
      simp [hq₁] at hinterp
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
      have hintv₁ : s₁.intTyped fuel σ := by simp only [Stmt.intTyped] at hintv; exact hintv.1
      have hintv₂ : s₂.intTyped fuel σ₁ := by
        simp only [Stmt.intTyped] at hintv; rw [hq₁] at hintv; exact hintv.2
      by_cases hds₁ : s₁.divSafe fuel σ
      · have hds₂ : ¬ s₂.divSafe fuel σ₁ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hds₁, hq₁, h])
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ σ' (offset + code1.length) tmp1 p σ₁_tac hinterp htf₂ hds₂ hintv₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ σ₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    cases hb : b.eval σ with
    | true =>
      simp only [Stmt.interp, hb] at hinterp
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
        simp only [Stmt.intTyped, hb] at hintv; exact hintv.1
      have hintv₁ : s₁.intTyped fuel σ := by
        simp only [Stmt.intTyped, hb] at hintv; exact hintv.2
      by_cases hbds : b.divSafe σ
      · have hds₁ : ¬ s₁.divSafe fuel σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h])
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
          refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
          intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
        have hifg : p[offset + codeBool.length]? =
            some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
          have := hcode.left.left.left.right.head
          simp only [List.length_append] at this; exact this
        have hexec_if := FragExec.single_iftrue hifg (by rw [heval_bool, hb])
        have hct : CodeAt (refCompileStmt s₁
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
            (offset + codeBool.length + 1 + codeElse.length + 1) := by
          rw [hrct]; have := hcode.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
              offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ σ' (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p
            σ_bool hinterp htf₁ hds₁ hintv₁ hagree_bool hct
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    | false =>
      simp only [Stmt.interp, hb, Bool.false_eq_true, ite_false] at hinterp
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
        simp only [Stmt.intTyped, hb] at hintv; exact hintv.1
      have hintv₂ : s₂.intTyped fuel σ := by
        simp only [Stmt.intTyped, hb, Bool.false_eq_true, ite_false] at hintv; exact hintv.2
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left.left
      by_cases hbds : b.divSafe σ
      · have hds₂ : ¬ s₂.divSafe fuel σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h])
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
          refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
          intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
        have hifg : p[offset + codeBool.length]? =
            some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
          have := hcode.left.left.left.right.head
          simp only [List.length_append] at this; exact this
        have hexec_if := FragExec.single_iffalse hifg (by rw [heval_bool, hb])
        have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ σ' (offset + codeBool.length + 1) tmpB p
            σ_bool hinterp htf₂ hds₂ hintv₂ hagree_bool hce
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | loop b body ih =>
    induction fuel generalizing σ σ' σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp only [Stmt.interp] at hinterp
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
      cases hb : b.eval σ with
      | false =>
        simp [hb] at hinterp; subst hinterp
        have hbds : ¬ b.divSafe σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | true =>
        simp [hb] at hinterp
        cases hq : body.interp fuel' σ with
        | none => simp [hq] at hinterp
        | some σ₁ =>
          simp [hq] at hinterp
          by_cases hbds : b.divSafe σ
          · by_cases hds_body : body.divSafe fuel' σ
            · -- Both safe; unsafety in remaining loop iterations
              have hds_loop : ¬ (Stmt.loop b body).divSafe fuel' σ₁ := by
                intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, hds_body, hq, h])
              have hintv_body : body.intTyped fuel' σ := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
              have hintv_loop : (Stmt.loop b body).intTyped fuel' σ₁ := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; rw [hq] at hintv; exact hintv.2.2
              -- Execute one full iteration
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
                intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
              have hifg : p[offset + codeBool.length]? =
                  some (.ifgoto (.not be)
                    (offset + codeBool.length + 1 + codeBody.length + 1)) := by
                have := hcode.left.left.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                exact this
              have hexec_if : FragExec p _ σ_bool _ σ_bool :=
                FragExec.single_iffalse hifg (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
              have hcbody : CodeAt (refCompileStmt body
                  (offset + codeBool.length + 1) tmpB).1 p
                  (offset + codeBool.length + 1) := by
                rw [hrcbody]; have := hcode.left.right
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1) =
                    offset + codeBool.length + 1 from by omega] at this
              obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
                refCompileStmt_correct body fuel' σ σ₁ (offset + codeBool.length + 1)
                  tmpB p σ_bool hq htf_body hds_body hintv_body hagree_bool hcbody
              rw [hrcbody] at hexec_body; simp at hexec_body
              have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
                  some (.goto offset) := by
                have := hcode.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                    offset + codeBool.length + 1 + codeBody.length from by omega] at this
              have hexec_goto : FragExec p _ σ_body _ σ_body :=
                FragExec.single_goto hgoto_back
              have hexec_iter := FragExec.trans'
                (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body)
                hexec_goto
              -- Use fuel IH: loop from σ₁ is unsafe
              obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
                ihf σ₁ σ' σ_body hinterp hds_loop hintv_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
            · -- Body unsafe
              have hintv_body : body.intTyped fuel' σ := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
              rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
              have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
                intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
              have hifg : p[offset + codeBool.length]? =
                  some (.ifgoto (.not be)
                    (offset + codeBool.length + 1 + codeBody.length + 1)) := by
                have := hcode.left.left.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                exact this
              have hexec_if : FragExec p _ σ_bool _ σ_bool :=
                FragExec.single_iffalse hifg (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
              have hcbody : CodeAt (refCompileStmt body
                  (offset + codeBool.length + 1) tmpB).1 p
                  (offset + codeBool.length + 1) := by
                rw [hrcbody]; have := hcode.left.right
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1) =
                    offset + codeBool.length + 1 from by omega] at this
              obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
                ih fuel' σ σ₁ (offset + codeBool.length + 1) tmpB p σ_bool hq
                  htf_body hds_body hintv_body hagree_bool hcbody
              rw [hrcbody] at hlt; simp at hlt
              exact ⟨pc_s, σ_s,
                FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
                by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
          · -- Bool unsafe
            obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
              refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
            rw [hrcb] at hlt; simp at hlt
            exact ⟨pc_s, σ_s, hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

-- ============================================================
-- § 16. Top-level stuck theorem
-- ============================================================

/-- If the source interpreter succeeds but division safety fails,
    the compiled program does **not** halt. -/
theorem refCompile_stuck (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ = some σ')
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.divSafe fuel σ)
    (hintv : s.intTyped fuel σ) :
    ¬ ∃ σ_tac, haltsWithResult (refCompile s) 0 σ σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, hfrag, herror, _⟩ :=
    refCompileStmt_stuck s fuel σ σ' 0 0 (refCompile s) σ hinterp htmpfree hunsafe hintv
      (fun _ _ => rfl) hcode
  exact error_run_no_halt hfrag herror hhalt

-- ============================================================
-- § 16b. Statement unsafe theorem (generalises stuck)
-- ============================================================

/-- If `¬ s.divSafe fuel σ`, the compiled statement code reaches a stuck
    configuration (division by zero), regardless of whether `interp` terminates.
    This generalises `refCompileStmt_stuck` by dropping the `hinterp` hypothesis. -/
theorem refCompileStmt_unsafe (s : Stmt) (fuel : Nat) (σ : Store)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.divSafe fuel σ)
    (hintv : s.intTyped fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      Step p (Cfg.run pc_s σ_s) (Cfg.error σ_s) ∧
      pc_s < offset + (refCompileStmt s offset nextTmp).1.length := by
  induction s generalizing fuel σ offset nextTmp p σ_tac with
  | skip => simp [Stmt.divSafe] at hunsafe
  | assign x e =>
    exact refCompileStmt_stuck _ fuel σ (σ[x ↦ .int (e.eval σ)]) offset nextTmp p σ_tac
      (by simp [Stmt.interp]) htmpfree hunsafe hintv hagree hcode
  | bassign x b =>
    exact refCompileStmt_stuck _ fuel σ (σ[x ↦ .bool (b.eval σ)]) offset nextTmp p σ_tac
      (by simp [Stmt.interp]) htmpfree hunsafe hintv hagree hcode
  | seq s₁ s₂ ih₁ ih₂ =>
    have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
    have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
    simp only [Stmt.intTyped] at hintv
    have hintv₁ : s₁.intTyped fuel σ := hintv.1
    dsimp only [refCompileStmt] at hcode ⊢
    generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
    obtain ⟨code1, tmp1⟩ := rc1
    generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
    obtain ⟨code2, tmp2⟩ := rc2
    simp only [] at hcode ⊢
    have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
      rw [hrc1]; exact hcode.left
    have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
        (offset + code1.length) := by rw [hrc2]; exact hcode.right
    cases hq₁ : s₁.interp fuel σ with
    | none =>
      have : ¬ s₁.divSafe fuel σ := by
        intro h; exact hunsafe (by simp [Stmt.divSafe, hq₁, h])
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ih₁ fuel σ offset nextTmp p σ_tac htf₁ this hintv₁ hagree hcode1
      rw [hrc1] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
    | some σ₁ =>
      rw [hq₁] at hintv
      have hintv₂ : s₂.intTyped fuel σ₁ := hintv.2
      by_cases hds₁ : s₁.divSafe fuel σ
      · have hds₂ : ¬ s₂.divSafe fuel σ₁ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hq₁, hds₁, h])
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ offset nextTmp p σ_tac
            hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ (offset + code1.length) tmp1 p σ₁_tac
            htf₂ hds₂ hintv₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileStmt_stuck s₁ fuel σ σ₁ offset nextTmp p σ_tac
            hq₁ htf₁ hds₁ hintv₁ hagree hcode1
        rw [hrc1] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
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
    have hintv_b : b.intTyped σ := by
      simp only [Stmt.intTyped] at hintv; exact hintv.1
    have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrcb]; exact hcode.left.left.left.left
    by_cases hbds : b.divSafe σ
    · obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      cases hb : b.eval σ with
      | true =>
        have htf₁ : s₁.tmpFree :=
          fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
        have hintv₁ : s₁.intTyped fuel σ := by
          simp only [Stmt.intTyped, hb] at hintv; exact hintv.2
        have hds₁ : ¬ s₁.divSafe fuel σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h])
        have hexec_if := FragExec.single_iftrue hifg (by rw [heval_bool, hb])
        have hct : CodeAt (refCompileStmt s₁
            (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
            (offset + codeBool.length + 1 + codeElse.length + 1) := by
          rw [hrct]; have := hcode.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
              offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p
            σ_bool htf₁ hds₁ hintv₁ hagree_bool hct
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | false =>
        have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
        have hintv₂ : s₂.intTyped fuel σ := by
          simp only [Stmt.intTyped, hb, Bool.false_eq_true, ite_false] at hintv; exact hintv.2
        have hds₂ : ¬ s₂.divSafe fuel σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h])
        have hexec_if := FragExec.single_iffalse hifg (by rw [heval_bool, hb])
        have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
            (offset + codeBool.length + 1) := by
          rw [hrce]; have := hcode.left.left.right
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          rwa [show offset + (codeBool.length + 1) =
              offset + codeBool.length + 1 from by omega] at this
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ (offset + codeBool.length + 1) tmpB p
            σ_bool htf₂ hds₂ hintv₂ hagree_bool hce
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
    · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
      rw [hrcb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck,
        by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
  | loop b body ih =>
    induction fuel generalizing σ σ_tac with
    | zero => simp [Stmt.divSafe] at hunsafe
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
      cases hb : b.eval σ with
      | false =>
        have hbds : ¬ b.divSafe σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
        rw [hrcb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      | true =>
        by_cases hbds : b.divSafe σ
        · -- Guard safe: execute guard, enter body
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
            intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
          have hifg : p[offset + codeBool.length]? =
              some (.ifgoto (.not be)
                (offset + codeBool.length + 1 + codeBody.length + 1)) := by
            have := hcode.left.left.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            exact this
          have hexec_if : FragExec p _ σ_bool _ σ_bool :=
            FragExec.single_iffalse hifg
              (by simp only [BoolExpr.eval]; rw [heval_bool, hb]; decide)
          have hcbody : CodeAt (refCompileStmt body
              (offset + codeBool.length + 1) tmpB).1 p
              (offset + codeBool.length + 1) := by
            rw [hrcbody]; have := hcode.left.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1) =
                offset + codeBool.length + 1 from by omega] at this
          have hintv_body : body.intTyped fuel' σ := by
            unfold Stmt.intTyped at hintv; simp [hb] at hintv; exact hintv.2.1
          cases hq : body.interp fuel' σ with
          | none =>
            -- Body diverges → body must be unsafe
            have hds_body : ¬ body.divSafe fuel' σ := by
              intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h, hq])
            obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
              ih fuel' σ (offset + codeBool.length + 1) tmpB p σ_bool
                htf_body hds_body hintv_body hagree_bool hcbody
            rw [hrcbody] at hlt; simp at hlt
            exact ⟨pc_s, σ_s,
              FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
              by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
          | some σ₁ =>
            by_cases hds_body : body.divSafe fuel' σ
            · -- Body safe: execute body, recurse on loop via fuel IH
              obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
                refCompileStmt_correct body fuel' σ σ₁ (offset + codeBool.length + 1)
                  tmpB p σ_bool hq htf_body hds_body hintv_body hagree_bool hcbody
              rw [hrcbody] at hexec_body; simp at hexec_body
              have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
                  some (.goto offset) := by
                have := hcode.right.head
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                    offset + codeBool.length + 1 + codeBody.length from by omega] at this
              have hexec_goto : FragExec p _ σ_body _ σ_body :=
                FragExec.single_goto hgoto_back
              have hexec_iter := FragExec.trans'
                (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body)
                hexec_goto
              have hds_loop : ¬ (Stmt.loop b body).divSafe fuel' σ₁ := by
                intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, hds_body, hq, h])
              have hintv_loop : (Stmt.loop b body).intTyped fuel' σ₁ := by
                unfold Stmt.intTyped at hintv; simp [hb] at hintv
                rw [hq] at hintv; exact hintv.2.2
              obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
                ihf σ₁ σ_body hds_loop hintv_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
            · -- Body unsafe: IH on body
              obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
                ih fuel' σ (offset + codeBool.length + 1) tmpB p σ_bool
                  htf_body hds_body hintv_body hagree_bool hcbody
              rw [hrcbody] at hlt; simp at hlt
              exact ⟨pc_s, σ_s,
                FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
                by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · -- Guard unsafe
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
          rw [hrcb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, hfrag, hstuck,
            by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩

/-- If `¬ s.divSafe fuel σ` holds for some fuel, the compiled program
    does **not** halt — it reaches a division-by-zero error. -/
theorem refCompile_unsafe (s : Stmt) (fuel : Nat) (σ : Store)
    (htmpfree : s.tmpFree)
    (hunsafe : ¬ s.divSafe fuel σ)
    (hintv : s.intTyped fuel σ) :
    ¬ ∃ σ_tac, haltsWithResult (refCompile s) 0 σ σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe s fuel σ 0 0 (refCompile s) σ
      htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  exact error_run_no_halt hfrag herror hhalt

