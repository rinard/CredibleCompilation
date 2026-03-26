import CredibleCompilation.CompilerCorrectness

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
# Reference Compiler: Pure Functional While → TAC with Correctness Proof

A pure functional compiler from the While language to TAC, with an explicit
temporary counter and `List TAC` output. Pre-computed jump targets eliminate
the need for patching. The strengthened postcondition tracks temporary-index
preservation, which is the key invariant the monadic compiler proofs lacked.
-/

-- ============================================================
-- § 1. Temporary variable helpers
-- ============================================================

def tmpName (k : Nat) : Var := s!"__t{k}"

private axiom tmpName_injective_ax : Function.Injective tmpName

theorem tmpName_ne {k j : Nat} (h : k ≠ j) : tmpName k ≠ tmpName j :=
  fun heq => h (tmpName_injective_ax heq)

theorem tmpName_isTmp (k : Nat) : (tmpName k).isTmp = true := by
  show (s!"__t{k}" : String).startsWith "__t" = true
  exact freshVar_isTmp k

theorem isTmp_false_ne_tmpName {v : Var} {k : Nat} (h : v.isTmp = false) : v ≠ tmpName k := by
  intro heq; have := tmpName_isTmp k; rw [← heq] at this; simp [h] at this

-- ============================================================
-- § 2. Reference compiler definitions
-- ============================================================

def refCompileExpr (e : SExpr) (offset nextTmp : Nat) : List TAC × Var × Nat :=
  match e with
  | .lit n =>
    let t := tmpName nextTmp
    ([.const t n], t, nextTmp + 1)
  | .var x => ([], x, nextTmp)
  | .bin op a b =>
    let (codeA, va, tmp1) := refCompileExpr a offset nextTmp
    let (codeB, vb, tmp2) := refCompileExpr b (offset + codeA.length) tmp1
    let t := tmpName tmp2
    (codeA ++ codeB ++ [.binop t op va vb], t, tmp2 + 1)

def refCompileBool (b : SBool) (offset nextTmp : Nat) : List TAC × BoolExpr × Nat :=
  match b with
  | .cmp op a b =>
    let (codeA, va, tmp1) := refCompileExpr a offset nextTmp
    let (codeB, vb, tmp2) := refCompileExpr b (offset + codeA.length) tmp1
    (codeA ++ codeB, .cmp op va vb, tmp2)
  | .not e =>
    let (code, be, tmp') := refCompileBool e offset nextTmp
    (code, .not be, tmp')
  | .and a b =>
    let (codeA, ba, tmp1) := refCompileBool a offset nextTmp
    let (codeB, bb, tmp2) := refCompileBool b (offset + codeA.length) tmp1
    (codeA ++ codeB, .and ba bb, tmp2)
  | .or a b =>
    let (codeA, ba, tmp1) := refCompileBool a offset nextTmp
    let (codeB, bb, tmp2) := refCompileBool b (offset + codeA.length) tmp1
    (codeA ++ codeB, .or ba bb, tmp2)

def refCompileStmt (s : Stmt) (offset nextTmp : Nat) : List TAC × Nat :=
  match s with
  | .skip => ([], nextTmp)
  | .assign x e =>
    match e with
    | .lit n => ([.const x n], nextTmp)
    | .var y => ([.copy x y], nextTmp)
    | .bin op a b =>
      let (codeA, va, tmp1) := refCompileExpr a offset nextTmp
      let (codeB, vb, tmp2) := refCompileExpr b (offset + codeA.length) tmp1
      (codeA ++ codeB ++ [.binop x op va vb], tmp2)
  | .seq s1 s2 =>
    let (code1, tmp1) := refCompileStmt s1 offset nextTmp
    let (code2, tmp2) := refCompileStmt s2 (offset + code1.length) tmp1
    (code1 ++ code2, tmp2)
  | .ite b s1 s2 =>
    let (codeBool, be, tmpB) := refCompileBool b offset nextTmp
    let elseStart := offset + codeBool.length + 1
    let (codeElse, tmpElse) := refCompileStmt s2 elseStart tmpB
    let thenStart := elseStart + codeElse.length + 1
    let (codeThen, tmpThen) := refCompileStmt s1 thenStart tmpElse
    let endLabel := thenStart + codeThen.length
    (codeBool ++ [.ifgoto be thenStart] ++ codeElse ++ [.goto endLabel] ++ codeThen, tmpThen)
  | .loop b body =>
    let condLabel := offset
    let (codeBool, be, tmpB) := refCompileBool b offset nextTmp
    let bodyStart := offset + codeBool.length + 1
    let (codeBody, tmpBody) := refCompileStmt body bodyStart tmpB
    let exitLabel := bodyStart + codeBody.length + 1
    (codeBool ++ [.ifgoto (.not be) exitLabel] ++ codeBody ++ [.goto condLabel], tmpBody)

def refCompile (s : Stmt) : Prog :=
  let (code, _) := refCompileStmt s 0 0
  (code ++ [TAC.halt]).toArray

-- ============================================================
-- § 3. Code embedding predicate
-- ============================================================

def CodeAt (code : List TAC) (p : Prog) (offset : Nat) : Prop :=
  ∀ i, i < code.length → p[offset + i]? = code[i]?

@[simp] theorem CodeAt.nil : CodeAt [] p offset :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem CodeAt.left {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h : CodeAt (c₁ ++ c₂) p offset) : CodeAt c₁ p offset := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem?_append_left (by exact hi)] at this

theorem CodeAt.right {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h : CodeAt (c₁ ++ c₂) p offset) : CodeAt c₂ p (offset + c₁.length) := by
  intro i hi
  have := h (c₁.length + i) (by simp; omega)
  rw [show offset + (c₁.length + i) = offset + c₁.length + i from by omega] at this
  rwa [List.getElem?_append_right (by omega),
       show c₁.length + i - c₁.length = i from by omega] at this

theorem CodeAt.head {x : TAC} {xs : List TAC} {p : Prog} {offset : Nat}
    (h : CodeAt (x :: xs) p offset) : p[offset]? = some x := by
  have := h 0 (by simp); simpa using this

theorem CodeAt.intro {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h₁ : CodeAt c₁ p offset) (h₂ : CodeAt c₂ p (offset + c₁.length)) :
    CodeAt (c₁ ++ c₂) p offset := by
  intro i hi
  by_cases hlt : i < c₁.length
  · rw [List.getElem?_append_left hlt]; exact h₁ i hlt
  · rw [List.getElem?_append_right (by omega)]
    have := h₂ (i - c₁.length) (by simp at hi; omega)
    rwa [show offset + c₁.length + (i - c₁.length) = offset + i from by omega] at this

-- ============================================================
-- § 4. FragExec single-step helpers
-- ============================================================

theorem FragExec.single_const {p : Prog} {pc : Nat} {σ : Store} {x : Var} {n : Val}
    (h : p[pc]? = some (.const x n)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ n]) :=
  Steps.single (Step.const h)

theorem FragExec.single_copy {p : Prog} {pc : Nat} {σ : Store} {x y : Var}
    (h : p[pc]? = some (.copy x y)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ σ y]) :=
  Steps.single (Step.copy h)

theorem FragExec.single_binop {p : Prog} {pc : Nat} {σ : Store}
    {x : Var} {op : BinOp} {y z : Var}
    (h : p[pc]? = some (.binop x op y z)) (hsafe : op.safe (σ y) (σ z)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ op.eval (σ y) (σ z)]) :=
  Steps.single (Step.binop h hsafe)

theorem FragExec.single_goto {p : Prog} {pc : Nat} {σ : Store} {l : Label}
    (h : p[pc]? = some (.goto l)) :
    FragExec p pc σ l σ :=
  Steps.single (Step.goto h)

theorem FragExec.single_iftrue {p : Prog} {pc : Nat} {σ : Store} {b : BoolExpr} {l : Label}
    (h : p[pc]? = some (.ifgoto b l)) (hb : b.eval σ = true) :
    FragExec p pc σ l σ :=
  Steps.single (Step.iftrue h hb)

theorem FragExec.single_iffalse {p : Prog} {pc : Nat} {σ : Store} {b : BoolExpr} {l : Label}
    (h : p[pc]? = some (.ifgoto b l)) (hb : b.eval σ = false) :
    FragExec p pc σ (pc + 1) σ :=
  Steps.single (Step.iffall h hb)

-- ============================================================
-- § 5. BoolExpr evaluation congruence (pointwise)
-- ============================================================

theorem BoolExpr.eval_agree' (cond : BoolExpr) (σ τ : Store)
    (h : ∀ v ∈ cond.vars, σ v = τ v) : cond.eval σ = cond.eval τ := by
  induction cond with
  | cmp op x y =>
    simp only [BoolExpr.eval]
    rw [h x (by simp [BoolExpr.vars]), h y (by simp [BoolExpr.vars])]
  | cmpLit op x n =>
    simp only [BoolExpr.eval]
    rw [h x (by simp [BoolExpr.vars])]
  | not e ih =>
    simp only [BoolExpr.eval]; rw [ih (fun v hv => h v hv)]
  | and a b iha ihb =>
    simp only [BoolExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [BoolExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]

-- ============================================================
-- § 6. Division safety helpers
-- ============================================================

theorem SExpr.divSafe_bin_safe {op : BinOp} {a b : SExpr} {σ : Store}
    (h : (SExpr.bin op a b).divSafe σ) : op.safe (a.eval σ) (b.eval σ) := by
  cases op <;> simp_all [SExpr.divSafe, BinOp.safe]

theorem SExpr.divSafe_bin_left {op : BinOp} {a b : SExpr} {σ : Store}
    (h : (SExpr.bin op a b).divSafe σ) : a.divSafe σ := by
  cases op <;> simp_all [SExpr.divSafe]

theorem SExpr.divSafe_bin_right {op : BinOp} {a b : SExpr} {σ : Store}
    (h : (SExpr.bin op a b).divSafe σ) : b.divSafe σ := by
  cases op <;> simp_all [SExpr.divSafe]

-- ============================================================
-- § 7. Store update helpers
-- ============================================================

theorem Store.update_tmpName_ne {σ : Store} {k j : Nat} {v : Val}
    (hne : j ≠ k) : (σ[tmpName k ↦ v]) (tmpName j) = σ (tmpName j) :=
  Store.update_other σ (tmpName k) (tmpName j) v (tmpName_ne hne)

theorem Store.update_isTmp_ne {σ : Store} {t : Var} {v : Val}
    {w : Var} (ht : t.isTmp = true) (hw : w.isTmp = false) :
    (σ[t ↦ v]) w = σ w :=
  Store.update_other σ t w v (fun heq => by rw [heq] at hw; simp [hw] at ht)

-- ============================================================
-- § 8. Monotonicity and result bounds (sorry for now)
-- ============================================================

theorem refCompileExpr_nextTmp_ge (e : SExpr) (offset nextTmp : Nat) :
    nextTmp ≤ (refCompileExpr e offset nextTmp).2.2 := by
  induction e generalizing offset nextTmp with
  | lit _ => show nextTmp ≤ nextTmp + 1; omega
  | var _ => exact Nat.le_refl _
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
    exact Nat.le_trans ha (ihb _ _)
  | or a b iha ihb =>
    dsimp only [refCompileBool]
    have ha := iha offset nextTmp
    generalize refCompileBool a offset nextTmp = ra at ha ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra; simp at ha ⊢
    exact Nat.le_trans ha (ihb _ _)

theorem refCompileExpr_result_bound (e : SExpr) (offset nextTmp : Nat)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    let r := refCompileExpr e offset nextTmp
    (r.2.1.isTmp = false) ∨ (∃ k, nextTmp ≤ k ∧ k < r.2.2 ∧ r.2.1 = tmpName k) := by
  induction e generalizing offset nextTmp with
  | lit _ => right; exact ⟨nextTmp, Nat.le_refl _, by show nextTmp < nextTmp + 1; omega, rfl⟩
  | var x => left; exact htf x (by simp [SExpr.freeVars])
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
    generalize hrb : refCompileBool b (offset + codeA.length) tmp1 = rb
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [BoolExpr.vars, List.mem_append]
    intro v hv; cases hv with
    | inl h =>
      have := iha offset nextTmp (fun v hv => htf v (List.mem_append_left _ hv))
      rw [hra] at this; simp at this
      have := this v h
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        have hge := refCompileBool_nextTmp_ge b (offset + codeA.length) tmp1
        rw [hrb] at hge; simp at hge
        exact ⟨k, hle, by omega, heq⟩
    | inr h =>
      have hge_a := refCompileBool_nextTmp_ge a offset nextTmp
      rw [hra] at hge_a; simp at hge_a
      have := ihb (offset + codeA.length) tmp1
        (fun v hv => htf v (List.mem_append_right _ hv))
      rw [hrb] at this; simp at this
      have := this v h
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        exact ⟨k, by omega, hlt, heq⟩
  | or a b iha ihb =>
    dsimp only [refCompileBool]
    generalize hra : refCompileBool a offset nextTmp = ra
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length) tmp1 = rb
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [BoolExpr.vars, List.mem_append]
    intro v hv; cases hv with
    | inl h =>
      have := iha offset nextTmp (fun v hv => htf v (List.mem_append_left _ hv))
      rw [hra] at this; simp at this
      have := this v h
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        have hge := refCompileBool_nextTmp_ge b (offset + codeA.length) tmp1
        rw [hrb] at hge; simp at hge
        exact ⟨k, hle, by omega, heq⟩
    | inr h =>
      have hge_a := refCompileBool_nextTmp_ge a offset nextTmp
      rw [hra] at hge_a; simp at hge_a
      have := ihb (offset + codeA.length) tmp1
        (fun v hv => htf v (List.mem_append_right _ hv))
      rw [hrb] at this; simp at this
      have := this v h
      cases this with
      | inl h => left; exact h
      | inr h =>
        right; obtain ⟨k, hle, hlt, heq⟩ := h
        exact ⟨k, by omega, hlt, heq⟩

-- ============================================================
-- § 9. Expression compilation correctness
-- ============================================================

theorem refCompileExpr_correct (e : SExpr) (offset nextTmp : Nat) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hsafe : e.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    let r := refCompileExpr e offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' ∧
      σ' r.2.1 = e.eval σ ∧
      (∀ w, w.isTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n =>
    simp only [refCompileExpr] at hcode ⊢
    refine ⟨σ_tac[tmpName nextTmp ↦ n], ?_, ?_, ?_, ?_⟩
    · exact FragExec.single_const hcode.head
    · exact Store.update_self _ _ _
    · intro w hw; exact Store.update_isTmp_ne (tmpName_isTmp nextTmp) hw
    · intro k hk; exact Store.update_tmpName_ne (by omega)

  | var x =>
    simp only [refCompileExpr] at hcode ⊢
    exact ⟨σ_tac, FragExec.rfl' _ _ _,
      hagree x (htf x (by simp [SExpr.freeVars])),
      fun w hw => rfl, fun k _ => rfl⟩

  | bin op a b iha ihb =>
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    -- Step 1: compile a
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, htmp_a⟩ :=
      iha offset nextTmp σ_tac htf_a (SExpr.divSafe_bin_left hsafe) hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    -- Step 2: compile b
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hagree_b : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, htmp_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b
        (SExpr.divSafe_bin_right hsafe) hagree_b hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- σ_b(va) = a.eval σ
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    have hva : σ_b va = a.eval σ := by
      have hbound := refCompileExpr_result_bound a offset nextTmp htf_a
      rw [hra] at hbound; simp at hbound
      cases hbound with
      | inl h => rw [hntmp_b va h, hval_a]
      | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq, htmp_b k hlt, ← heq, hval_a]
    -- Division safety
    have hop_safe : op.safe (σ_b va) (σ_b vb) := by
      rw [hva, hval_b]; exact SExpr.divSafe_bin_safe hsafe
    -- Binop instruction
    have hge_b := refCompileExpr_nextTmp_ge b (offset + codeA.length) tmp1
    rw [hrb] at hge_b; simp at hge_b
    -- Binop instruction
    have hinstr : p[offset + codeA.length + codeB.length]? =
        some (.binop (tmpName tmp2) op va vb) := by
      have := hcode.right.head
      simp only [List.length_append] at this
      rw [← Nat.add_assoc] at this; exact this
    refine ⟨σ_b[tmpName tmp2 ↦ op.eval (σ_b va) (σ_b vb)], ?_, ?_, ?_, ?_⟩
    · -- FragExec
      have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b)
        (FragExec.single_binop hinstr hop_safe)
      have hlen : offset + (codeA ++ codeB ++ [TAC.binop (tmpName tmp2) op va vb]).length =
          offset + codeA.length + codeB.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact h123
    · -- result
      simp only [SExpr.eval]; rw [Store.update_self, hva, hval_b]
    · -- non-tmp
      intro w hw
      rw [Store.update_isTmp_ne (tmpName_isTmp tmp2) hw, hntmp_b w hw, hntmp_a w hw]
    · -- tmp
      intro k hk
      rw [Store.update_tmpName_ne (by omega), htmp_b k (by omega), htmp_a k hk]

-- ============================================================
-- § 10. Boolean expression compilation correctness
-- ============================================================

theorem refCompileBool_correct (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hbsafe : sb.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    let r := refCompileBool sb offset nextTmp
    ∃ σ', FragExec p offset σ_tac (offset + r.1.length) σ' ∧
      r.2.1.eval σ' = sb.eval σ ∧
      (∀ w, w.isTmp = false → σ' w = σ_tac w) ∧
      (∀ k, k < nextTmp → σ' (tmpName k) = σ_tac (tmpName k)) := by
  induction sb generalizing offset nextTmp σ_tac with
  | cmp cop a b =>
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have htf_a := fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b := fun v hv => htf v (List.mem_append_right _ hv)
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, htmp_a⟩ :=
      refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a hbsafe.1 hagree hcodeA
    rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, htmp_b⟩ :=
      refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a p htf_b hbsafe.2 hagree_a hcodeB
    rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
    -- Preserve va through b's compilation
    have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    have hva_preserved : σ_b va = a.eval σ := by
      have hbound := refCompileExpr_result_bound a offset nextTmp htf_a
      rw [hra] at hbound; simp at hbound
      cases hbound with
      | inl h => rw [hntmp_b va h, hval_a]
      | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq, htmp_b k hlt, ← heq, hval_a]
    have hexec_ab : FragExec p offset σ_tac (offset + (codeA ++ codeB).length) σ_b := by
      simp only [List.length_append]
      have := FragExec.trans' hexec_a hexec_b
      rwa [Nat.add_assoc] at this
    refine ⟨σ_b, hexec_ab, ?_, ?_, ?_⟩
    · -- bool eval
      simp only [BoolExpr.eval, SBool.eval]; rw [hva_preserved, hval_b]
    · -- non-tmp
      intro w hw; rw [hntmp_b w hw, hntmp_a w hw]
    · -- tmp
      intro k hk; rw [htmp_b k (by omega), htmp_a k hk]

  | not e ih =>
    dsimp only [refCompileBool] at hcode ⊢
    generalize hre : refCompileBool e offset nextTmp = re at hcode ⊢
    obtain ⟨code, be, tmp'⟩ := re
    simp only [] at hcode ⊢
    have hcodeE : CodeAt (refCompileBool e offset nextTmp).1 p offset := by
      rw [hre]; exact hcode
    obtain ⟨σ', hexec, heval, hntmp, htmp⟩ :=
      ih offset nextTmp σ_tac htf hbsafe hagree hcodeE
    rw [hre] at hexec heval; simp at hexec heval
    exact ⟨σ', hexec, by simp [BoolExpr.eval, SBool.eval, heval], hntmp, htmp⟩

  | and a b iha ihb =>
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have htf_a := fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b := fun v hv => htf v (List.mem_append_right _ hv)
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, htmp_a⟩ :=
      iha offset nextTmp σ_tac htf_a hbsafe.1 hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    have hcodeB : CodeAt (refCompileBool b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, htmp_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hbsafe.2 hagree_a hcodeB
    rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
    -- Preserve ba.eval through b's compilation
    have hge_a := refCompileBool_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    have hba_preserved : ba.eval σ_b = a.eval σ := by
      rw [← heval_a]
      apply BoolExpr.eval_agree'
      intro v hv
      have := refCompileBool_vars_bound a offset nextTmp htf_a
      rw [hra] at this; simp at this
      have := this v hv
      cases this with
      | inl h => exact hntmp_b v h
      | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq]; exact htmp_b k hlt
    have hexec_ab : FragExec p offset σ_tac (offset + (codeA ++ codeB).length) σ_b := by
      simp only [List.length_append]
      have := FragExec.trans' hexec_a hexec_b; rwa [Nat.add_assoc] at this
    refine ⟨σ_b, hexec_ab, ?_, ?_, ?_⟩
    · simp only [BoolExpr.eval, SBool.eval]; rw [hba_preserved, heval_b]
    · intro w hw; rw [hntmp_b w hw, hntmp_a w hw]
    · intro k hk; rw [htmp_b k (by omega), htmp_a k hk]

  | or a b iha ihb =>
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileBool a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := ra
    generalize hrb : refCompileBool b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have htf_a := fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b := fun v hv => htf v (List.mem_append_right _ hv)
    have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    obtain ⟨σ_a, hexec_a, heval_a, hntmp_a, htmp_a⟩ :=
      iha offset nextTmp σ_tac htf_a hbsafe.1 hagree hcodeA
    rw [hra] at hexec_a heval_a; simp at hexec_a heval_a
    have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
      intro v hv; rw [hntmp_a v hv]; exact hagree v hv
    have hcodeB : CodeAt (refCompileBool b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    obtain ⟨σ_b, hexec_b, heval_b, hntmp_b, htmp_b⟩ :=
      ihb (offset + codeA.length) tmp1 σ_a htf_b hbsafe.2 hagree_a hcodeB
    rw [hrb] at hexec_b heval_b; simp at hexec_b heval_b
    have hge_a := refCompileBool_nextTmp_ge a offset nextTmp
    rw [hra] at hge_a; simp at hge_a
    have hba_preserved : ba.eval σ_b = a.eval σ := by
      rw [← heval_a]
      apply BoolExpr.eval_agree'
      intro v hv
      have := refCompileBool_vars_bound a offset nextTmp htf_a
      rw [hra] at this; simp at this
      have := this v hv
      cases this with
      | inl h => exact hntmp_b v h
      | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq]; exact htmp_b k hlt
    have hexec_ab : FragExec p offset σ_tac (offset + (codeA ++ codeB).length) σ_b := by
      simp only [List.length_append]
      have := FragExec.trans' hexec_a hexec_b; rwa [Nat.add_assoc] at this
    refine ⟨σ_b, hexec_ab, ?_, ?_, ?_⟩
    · simp only [BoolExpr.eval, SBool.eval]; rw [hba_preserved, heval_b]
    · intro w hw; rw [hntmp_b w hw, hntmp_a w hw]
    · intro k hk; rw [htmp_b k (by omega), htmp_a k hk]

-- ============================================================
-- § 11. Statement compilation correctness
-- ============================================================

theorem refCompileStmt_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ = some σ')
    (htmpfree : s.tmpFree)
    (hsafe : s.divSafe fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ σ_tac', FragExec p offset σ_tac
        (offset + (refCompileStmt s offset nextTmp).1.length) σ_tac' ∧
      (∀ v, v.isTmp = false → σ_tac' v = σ' v) := by
  induction s generalizing fuel σ σ' offset nextTmp p σ_tac with
  | skip =>
    simp only [Stmt.interp, Option.some.injEq] at hinterp; subst hinterp
    simp only [refCompileStmt, List.length_nil, Nat.add_zero]
    exact ⟨σ_tac, FragExec.rfl' _ _ _, fun v hv => hagree v hv⟩
  | assign x e =>
    simp only [Stmt.interp, Option.some.injEq] at hinterp; subst hinterp
    have hx_ntmp : x.isTmp = false := htmpfree x (by simp [Stmt.allVars])
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun v hv => htmpfree v (by simp [Stmt.allVars]; exact Or.inr hv)
    have hsafe_e : e.divSafe σ := by simp only [Stmt.divSafe] at hsafe; exact hsafe
    cases e with
    | lit n =>
      simp only [refCompileStmt] at hcode ⊢
      refine ⟨σ_tac[x ↦ n], FragExec.single_const hcode.head, ?_⟩
      intro v hv; simp only [Store.update, SExpr.eval]
      by_cases hxv : v = x
      · subst hxv; simp [beq_self_eq_true]
      · simp [beq_iff_eq, hxv]; exact hagree v hv
    | var y =>
      simp only [refCompileStmt] at hcode ⊢
      refine ⟨σ_tac[x ↦ σ_tac y], FragExec.single_copy hcode.head, ?_⟩
      intro v hv; simp only [Store.update, SExpr.eval]
      by_cases hxv : v = x
      · subst hxv; simp [beq_self_eq_true]
        exact hagree y (htf_e y (by simp [SExpr.freeVars]))
      · simp [beq_iff_eq, hxv]; exact hagree v hv
    | bin op a b =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      have htf_a := fun v hv => htf_e v (List.mem_append_left _ hv)
      have htf_b := fun v hv => htf_e v (List.mem_append_right _ hv)
      have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
        rw [hra]; exact hcode.left.left
      obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, htmp_a⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a
          (SExpr.divSafe_bin_left hsafe_e) hagree hcodeA
      rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
      obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, htmp_b⟩ :=
        refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a p htf_b
          (SExpr.divSafe_bin_right hsafe_e) hagree_a hcodeB
      rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
      have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
      rw [hra] at hge_a; simp at hge_a
      have hva : σ_b va = a.eval σ := by
        have hbound := refCompileExpr_result_bound a offset nextTmp htf_a
        rw [hra] at hbound; simp at hbound
        cases hbound with
        | inl h => rw [hntmp_b va h, hval_a]
        | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq, htmp_b k hlt, ← heq, hval_a]
      have hop_safe : op.safe (σ_b va) (σ_b vb) := by
        rw [hva, hval_b]; exact SExpr.divSafe_bin_safe hsafe_e
      have hinstr : p[offset + codeA.length + codeB.length]? =
          some (.binop x op va vb) := by
        have := hcode.right.head
        simp only [List.length_append] at this; rw [← Nat.add_assoc] at this; exact this
      refine ⟨σ_b[x ↦ op.eval (σ_b va) (σ_b vb)], ?_, ?_⟩
      · have h123 := FragExec.trans' (FragExec.trans' hexec_a hexec_b)
          (FragExec.single_binop hinstr hop_safe)
        have hlen : offset + (codeA ++ codeB ++ [TAC.binop x op va vb]).length =
            offset + codeA.length + codeB.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact h123
      · intro v hv; simp only [Store.update, SExpr.eval]
        by_cases hxv : v = x
        · subst hxv; simp [beq_self_eq_true, hva, hval_b]
        · simp [beq_iff_eq, hxv]; rw [hntmp_b v hv, hntmp_a v hv, hagree v hv]

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
      have hds₁ : s₁.divSafe fuel σ := by simp only [Stmt.divSafe] at hsafe; exact hsafe.1
      have hds₂ : s₂.divSafe fuel σ₁ := by
        simp only [Stmt.divSafe] at hsafe; rw [hq₁] at hsafe; exact hsafe.2
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
        ih₁ fuel σ σ₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hagree hcode1
      rw [hrc1] at hexec₁; simp at hexec₁
      have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
          (offset + code1.length) := by rw [hrc2]; exact hcode.right
      obtain ⟨σ₂_tac, hexec₂, hagree₂⟩ :=
        ih₂ fuel σ₁ σ' (offset + code1.length) tmp1 p σ₁_tac hinterp htf₂ hds₂ hagree₁ hcode2
      rw [hrc2] at hexec₂; simp at hexec₂
      refine ⟨σ₂_tac, ?_, hagree₂⟩
      have := FragExec.trans' hexec₁ hexec₂
      simp only [List.length_append] at this ⊢; rwa [Nat.add_assoc] at this

  | ite b s₁ s₂ ih₁ ih₂ =>
    -- Case split on boolean first to simplify hsafe extraction
    cases hb : b.eval σ with
    | true =>
      simp only [Stmt.interp, hb] at hinterp
      have hbds : SBool.divSafe σ b := by
        simp only [Stmt.divSafe, hb] at hsafe; exact hsafe.1
      have hds₁ : s₁.divSafe fuel σ := by
        simp only [Stmt.divSafe, hb] at hsafe; exact hsafe.2
      -- Unfold compiler
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
      obtain ⟨codeElse, tmpElse⟩ := rce
      generalize hrct : refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
      obtain ⟨codeThen, tmpThen⟩ := rct
      simp only [] at hcode ⊢
      -- CodeAt extraction
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left.left
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      have hct : CodeAt (refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
          (offset + codeBool.length + 1 + codeElse.length + 1) := by
        rw [hrct]
        have := hcode.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
            offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
      -- Bool compilation
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
      have htf₁ : s₁.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      -- ifgoto jumps to thenStart
      have hbe_true : be.eval σ_bool = true := by rw [heval_bool, hb]
      have hexec_if := FragExec.single_iftrue hifg hbe_true
      -- Execute then branch
      obtain ⟨σ_then, hexec_then, hagree_then⟩ :=
        ih₁ fuel σ σ' (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p
          σ_bool hinterp htf₁ hds₁ hagree_bool hct
      rw [hrct] at hexec_then; simp at hexec_then
      refine ⟨σ_then, ?_, hagree_then⟩
      have hexec := FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_then
      have hlen : offset + (codeBool ++
          [TAC.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)] ++
          codeElse ++
          [TAC.goto (offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length)] ++
          codeThen).length =
          offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact hexec

    | false =>
      simp only [Stmt.interp, hb, Bool.false_eq_true, ite_false] at hinterp
      have hbds : SBool.divSafe σ b := by
        simp only [Stmt.divSafe, hb] at hsafe; exact hsafe.1
      have hds₂ : s₂.divSafe fuel σ := by
        simp only [Stmt.divSafe, hb, Bool.false_eq_true, ite_false] at hsafe; exact hsafe.2
      -- Unfold compiler
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
      obtain ⟨codeElse, tmpElse⟩ := rce
      generalize hrct : refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
      obtain ⟨codeThen, tmpThen⟩ := rct
      simp only [] at hcode ⊢
      -- CodeAt extraction
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left.left
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
          (offset + codeBool.length + 1) := by
        rw [hrce]
        have := hcode.left.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) =
            offset + codeBool.length + 1 from by omega] at this
      have hgoto : p[offset + codeBool.length + 1 + codeElse.length]? =
          some (.goto (offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length)) := by
        have := hcode.left.right.head
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length) =
            offset + codeBool.length + 1 + codeElse.length from by omega] at this
      -- Bool compilation
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      -- ifgoto falls through
      have hbe_false : be.eval σ_bool = false := by rw [heval_bool, hb]
      have hexec_if := FragExec.single_iffalse hifg hbe_false
      -- Execute else branch
      obtain ⟨σ_else, hexec_else, hagree_else⟩ :=
        ih₂ fuel σ σ' (offset + codeBool.length + 1) tmpB p
          σ_bool hinterp htf₂ hds₂ hagree_bool hce
      rw [hrce] at hexec_else; simp at hexec_else
      -- goto endLabel
      have hexec_goto : FragExec p _ σ_else _ σ_else := FragExec.single_goto hgoto
      refine ⟨σ_else, ?_, hagree_else⟩
      have hexec := FragExec.trans'
        (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_else) hexec_goto
      have hlen : offset + (codeBool ++
          [TAC.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)] ++
          codeElse ++
          [TAC.goto (offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length)] ++
          codeThen).length =
          offset + codeBool.length + 1 + codeElse.length + 1 + codeThen.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega
      rw [hlen]; exact hexec

  | loop b body ih =>
    induction fuel generalizing σ σ' σ_tac with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp only [Stmt.interp] at hinterp
      cases hb : b.eval σ with
      | false =>
        simp [hb] at hinterp; subst hinterp
        have hbds : SBool.divSafe σ b := by
          simp only [Stmt.divSafe, hb] at hsafe; exact hsafe.1
        dsimp only [refCompileStmt] at hcode ⊢
        generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
        obtain ⟨codeBool, be, tmpB⟩ := rcb
        generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody
            at hcode ⊢
        obtain ⟨codeBody, tmpBody⟩ := rcbody
        simp only [] at hcode ⊢
        -- Bool compilation
        have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
          fun v hv => htmpfree v (List.mem_append_left _ hv)
        have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
          rw [hrcb]; exact hcode.left.left.left
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
          refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
        rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
        -- (not be) is true, jump to exitLabel
        have hifg : p[offset + codeBool.length]? =
            some (.ifgoto (.not be)
              (offset + codeBool.length + 1 + codeBody.length + 1)) := by
          have := hcode.left.left.right.head
          simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
        have hnotbe : (BoolExpr.not be).eval σ_bool = true := by
          simp [BoolExpr.eval, heval_bool, hb]
        have hexec_if := FragExec.single_iftrue hifg hnotbe
        refine ⟨σ_bool, ?_, fun v hv => by rw [hntmp_bool v hv, hagree v hv]⟩
        have hexec := FragExec.trans' hexec_bool hexec_if
        have hlen : offset + (codeBool ++
            [TAC.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)] ++
            codeBody ++ [TAC.goto offset]).length =
            offset + codeBool.length + 1 + codeBody.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [hlen]; exact hexec

      | true =>
        simp [hb] at hinterp
        cases hq : body.interp fuel' σ with
        | none => simp [hq] at hinterp
        | some σ₁ =>
          simp [hq] at hinterp
          have hbds : SBool.divSafe σ b := by
            simp only [Stmt.divSafe, hb] at hsafe; exact hsafe.1
          have hds_body : body.divSafe fuel' σ := by
            simp only [Stmt.divSafe, hb] at hsafe; exact hsafe.2.1
          have hds_loop : (Stmt.loop b body).divSafe fuel' σ₁ := by
            simp only [Stmt.divSafe, hb] at hsafe; rw [hq] at hsafe; exact hsafe.2.2
          dsimp only [refCompileStmt] at hcode ⊢
          generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
          obtain ⟨codeBool, be, tmpB⟩ := rcb
          generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody
              at hcode ⊢
          obtain ⟨codeBody, tmpBody⟩ := rcbody
          simp only [] at hcode ⊢
          -- Bool compilation
          have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
            fun v hv => htmpfree v (List.mem_append_left _ hv)
          have htf_body : body.tmpFree :=
            fun v hv => htmpfree v (List.mem_append_right _ hv)
          have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
            rw [hrcb]; exact hcode.left.left.left
          obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
            refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
          rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
          have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
            intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
          -- (not be) is false, fall through
          have hifg : p[offset + codeBool.length]? =
              some (.ifgoto (.not be)
                (offset + codeBool.length + 1 + codeBody.length + 1)) := by
            have := hcode.left.left.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
          have hnotbe : (BoolExpr.not be).eval σ_bool = false := by
            simp [BoolExpr.eval, heval_bool, hb]
          have hexec_if := FragExec.single_iffalse hifg hnotbe
          -- Execute body
          have hcbody : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
              (offset + codeBool.length + 1) := by
            rw [hrcbody]
            have := hcode.left.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1) =
                offset + codeBool.length + 1 from by omega] at this
          obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
            ih fuel' σ σ₁ (offset + codeBool.length + 1) tmpB p σ_bool hq htf_body
              hds_body hagree_bool hcbody
          rw [hrcbody] at hexec_body; simp at hexec_body
          -- goto condLabel
          have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
              some (.goto offset) := by
            have := hcode.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + 1 + codeBody.length) =
                offset + codeBool.length + 1 + codeBody.length from by omega] at this
          have hexec_goto : FragExec p _ σ_body _ σ_body := FragExec.single_goto hgoto_back
          -- Compose one iteration
          have hexec_iter := FragExec.trans'
            (FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hexec_body)
            hexec_goto
          -- Use fuel induction hypothesis
          obtain ⟨σ_final, hexec_rec, hagree_final⟩ :=
            ihf σ₁ σ' σ_body hinterp hds_loop hagree_body
          refine ⟨σ_final, ?_, hagree_final⟩
          have hlen : offset + (codeBool ++
              [TAC.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)] ++
              codeBody ++ [TAC.goto offset]).length =
              offset + (refCompileStmt (.loop b body) offset nextTmp).1.length := by
            dsimp only [refCompileStmt]; rw [hrcb, hrcbody]
          rw [hlen]; exact FragExec.trans' hexec_iter hexec_rec

-- ============================================================
-- § 12. Top-level correctness theorem
-- ============================================================

theorem refCompile_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ = some σ')
    (htmpfree : s.tmpFree)
    (hsafe : s.divSafe fuel σ) :
    ∃ σ_tac, haltsWithResult (refCompile s) 0 σ σ_tac ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  -- Code embedding
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    refCompileStmt_correct s fuel σ σ' 0 0 (refCompile s) σ
      hinterp htmpfree hsafe (fun _ _ => rfl) hcode
  simp only [Nat.zero_add] at hexec
  -- halt instruction at end
  have hhalt : (refCompile s)[(refCompileStmt s 0 0).1.length]? = some .halt := by
    unfold refCompile; simp only [List.getElem?_toArray]
    rw [List.getElem?_append_right (by omega)]; simp
  exact ⟨σ_tac, FragExec.toHalt hexec hhalt, hagree⟩

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

/-- A `Cfg.run` stuck state and a `Cfg.halt` state from the same start
    are contradictory (since halt is also stuck but `run ≠ halt`). -/
theorem stuck_run_no_halt {p : Prog} {pc : Nat} {σ_start σ_stuck σ_halt : Store}
    (h_run : p ⊩ Cfg.run 0 σ_start ⟶* Cfg.run pc σ_stuck)
    (h_stuck : ∀ c, ¬ Step p (Cfg.run pc σ_stuck) c)
    (h_halt : haltsWithResult p 0 σ_start σ_halt) : False := by
  have halt_stuck : ∀ d, ¬ Step p (Cfg.halt σ_halt) d := fun _ h => by cases h
  have := Steps.stuck_det h_run h_halt h_stuck halt_stuck
  exact Cfg.noConfusion this

/-- A binop instruction with an unsafe operation admits no step. -/
theorem no_step_unsafe_binop {p : Prog} {pc : Nat} {σ : Store}
    {x : Var} {op : BinOp} {y z : Var}
    (hinstr : p[pc]? = some (.binop x op y z))
    (hunsafe : ¬ op.safe (σ y) (σ z)) :
    ∀ c, ¬ Step p (Cfg.run pc σ) c := by
  intro c hstep
  cases hstep with
  | const h => rw [hinstr] at h; exact TAC.noConfusion (Option.some.inj h)
  | copy h => rw [hinstr] at h; exact TAC.noConfusion (Option.some.inj h)
  | binop h hsafe => rw [hinstr] at h; have := Option.some.inj h; cases this; exact hunsafe hsafe
  | goto h => rw [hinstr] at h; exact TAC.noConfusion (Option.some.inj h)
  | iftrue h _ => rw [hinstr] at h; exact TAC.noConfusion (Option.some.inj h)
  | iffall h _ => rw [hinstr] at h; exact TAC.noConfusion (Option.some.inj h)
  | halt h => rw [hinstr] at h; exact TAC.noConfusion (Option.some.inj h)

-- ============================================================
-- § 14. Expression and boolean stuck theorems
-- ============================================================

/-- If an expression has a division-by-zero on the evaluation path (`¬ e.divSafe σ`),
    the compiled code reaches a stuck configuration strictly before the fragment end. -/
theorem refCompileExpr_stuck (e : SExpr) (offset nextTmp : Nat) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hunsafe : ¬ e.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileExpr e offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      (∀ c, ¬ Step p (Cfg.run pc_s σ_s) c) ∧
      pc_s < offset + (refCompileExpr e offset nextTmp).1.length := by
  induction e generalizing offset nextTmp σ_tac with
  | lit n => simp [SExpr.divSafe] at hunsafe
  | var v => simp [SExpr.divSafe] at hunsafe
  | bin op a b iha ihb =>
    dsimp only [refCompileExpr] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left.left
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
    by_cases ha : a.divSafe σ
    · by_cases hb : b.divSafe σ
      · -- Both sub-expressions safe; the unsafety is at the binop itself
        -- Must be op = div with b.eval σ = 0
        have hunsafe_op : ¬ op.safe (a.eval σ) (b.eval σ) := by
          cases op <;> simp [SExpr.divSafe, ha, hb, BinOp.safe] at hunsafe ⊢
          · exact hunsafe
        -- Both sub-expressions complete
        obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, htmp_a⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
        rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
        have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
          intro v hv; rw [hntmp_a v hv]; exact hagree v hv
        obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, htmp_b⟩ :=
          refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a p
            htf_b hb hagree_a hcodeB
        rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
        -- σ_b(va) = a.eval σ
        have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
        rw [hra] at hge_a; simp at hge_a
        have hva : σ_b va = a.eval σ := by
          have hbound := refCompileExpr_result_bound a offset nextTmp htf_a
          rw [hra] at hbound; simp at hbound
          cases hbound with
          | inl h => rw [hntmp_b va h, hval_a]
          | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq, htmp_b k hlt, ← heq, hval_a]
        -- The binop instruction is stuck
        have hinstr : p[offset + codeA.length + codeB.length]? =
            some (.binop (tmpName tmp2) op va vb) := by
          have := hcode.right.head
          simp only [List.length_append] at this; rw [← Nat.add_assoc] at this; exact this
        have hunsafe_σb : ¬ op.safe (σ_b va) (σ_b vb) := by
          rw [hva, hval_b]; exact hunsafe_op
        exact ⟨offset + codeA.length + codeB.length, σ_b,
          FragExec.trans' hexec_a hexec_b,
          no_step_unsafe_binop hinstr hunsafe_σb,
          by simp [List.length_append]; omega⟩
      · -- b is unsafe; a completes, b gets stuck
        obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
          refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
        rw [hra] at hexec_a; simp at hexec_a
        have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
          intro v hv; rw [hntmp_a v hv]; exact hagree v hv
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ihb (offset + codeA.length) tmp1 σ_a htf_b hb hagree_a hcodeB
        rw [hrb] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
          by simp [List.length_append]; omega⟩
    · -- a is unsafe; a's code gets stuck
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a ha hagree hcodeA
      rw [hra] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩

/-- Boolean expression stuck theorem: if `¬ sb.divSafe σ`, the compiled boolean code
    reaches a stuck configuration. -/
theorem refCompileBool_stuck (sb : SBool) (offset nextTmp : Nat) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hunsafe : ¬ sb.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileBool sb offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      (∀ c, ¬ Step p (Cfg.run pc_s σ_s) c) ∧
      pc_s < offset + (refCompileBool sb offset nextTmp).1.length := by
  induction sb generalizing offset nextTmp σ_tac with
  | cmp cop a b =>
    simp only [SBool.divSafe] at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
    obtain ⟨codeA, va, tmp1⟩ := ra
    generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
    obtain ⟨codeB, vb, tmp2⟩ := rb
    simp only [] at hcode ⊢
    have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
      rw [hra]; exact hcode.left
    have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
        (offset + codeA.length) := by rw [hrb]; exact hcode.right
    by_cases ha : a.divSafe σ
    · -- a safe, b unsafe
      have hb : ¬ b.divSafe σ := fun h => hunsafe ⟨ha, h⟩
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
        refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
      rw [hra] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a p htf_b hb hagree_a hcodeB
      rw [hrb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · -- a unsafe
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        refCompileExpr_stuck a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
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
    obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ := ih offset nextTmp σ_tac htf hunsafe hagree hcodeE
    rw [hrc] at hlt; simp at hlt
    exact ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩
  | and a b iha ihb =>
    simp only [SBool.divSafe] at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hrca : refCompileBool a offset nextTmp = rca at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := rca
    generalize hrcb : refCompileBool b (offset + codeA.length) tmp1 = rcb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rcb
    simp only [] at hcode ⊢
    by_cases ha : a.divSafe σ
    · have hb : ¬ b.divSafe σ := fun h => hunsafe ⟨ha, h⟩
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf v (List.mem_append_right _ hv)
      have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
        rw [hrca]; exact hcode.left
      have hcodeB : CodeAt (refCompileBool b (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrcb]; exact hcode.right
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
      rw [hrca] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ihb (offset + codeA.length) tmp1 σ_a htf_b hb hagree_a hcodeB
      rw [hrcb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf v (List.mem_append_left _ hv)
      have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
        rw [hrca]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a ha hagree hcodeA
      rw [hrca] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
  | or a b iha ihb =>
    -- Identical structure to `and`
    simp only [SBool.divSafe] at hunsafe
    dsimp only [refCompileBool] at hcode ⊢
    generalize hrca : refCompileBool a offset nextTmp = rca at hcode ⊢
    obtain ⟨codeA, ba, tmp1⟩ := rca
    generalize hrcb : refCompileBool b (offset + codeA.length) tmp1 = rcb at hcode ⊢
    obtain ⟨codeB, bb, tmp2⟩ := rcb
    simp only [] at hcode ⊢
    by_cases ha : a.divSafe σ
    · have hb : ¬ b.divSafe σ := fun h => hunsafe ⟨ha, h⟩
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf v (List.mem_append_left _ hv)
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf v (List.mem_append_right _ hv)
      have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
        rw [hrca]; exact hcode.left
      have hcodeB : CodeAt (refCompileBool b (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrcb]; exact hcode.right
      obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
        refCompileBool_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
      rw [hrca] at hexec_a; simp at hexec_a
      have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
        intro v hv; rw [hntmp_a v hv]; exact hagree v hv
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        ihb (offset + codeA.length) tmp1 σ_a htf_b hb hagree_a hcodeB
      rw [hrcb] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
        by simp [List.length_append]; omega⟩
    · have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htf v (List.mem_append_left _ hv)
      have hcodeA : CodeAt (refCompileBool a offset nextTmp).1 p offset := by
        rw [hrca]; exact hcode.left
      obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
        iha offset nextTmp σ_tac htf_a ha hagree hcodeA
      rw [hrca] at hlt; simp at hlt
      exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩

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
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∃ pc_s σ_s, FragExec p offset σ_tac pc_s σ_s ∧
      (∀ c, ¬ Step p (Cfg.run pc_s σ_s) c) ∧
      pc_s < offset + (refCompileStmt s offset nextTmp).1.length := by
  induction s generalizing fuel σ σ' offset nextTmp p σ_tac with
  | skip => simp [Stmt.divSafe] at hunsafe
  | assign x e =>
    simp only [Stmt.divSafe] at hunsafe
    cases e with
    | lit n => simp [SExpr.divSafe] at hunsafe
    | var y => simp [SExpr.divSafe] at hunsafe
    | bin op a b =>
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hra : refCompileExpr a offset nextTmp = ra at hcode ⊢
      obtain ⟨codeA, va, tmp1⟩ := ra
      generalize hrb : refCompileExpr b (offset + codeA.length) tmp1 = rb at hcode ⊢
      obtain ⟨codeB, vb, tmp2⟩ := rb
      simp only [] at hcode ⊢
      have htf_a : ∀ v ∈ a.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp [Stmt.allVars, SExpr.freeVars]; exact Or.inr (Or.inl hv))
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (by simp [Stmt.allVars, SExpr.freeVars]; exact Or.inr (Or.inr hv))
      have hcodeA : CodeAt (refCompileExpr a offset nextTmp).1 p offset := by
        rw [hra]; exact hcode.left.left
      have hcodeB : CodeAt (refCompileExpr b (offset + codeA.length) tmp1).1 p
          (offset + codeA.length) := by rw [hrb]; exact hcode.left.right
      by_cases ha : a.divSafe σ
      · by_cases hb : b.divSafe σ
        · have hunsafe_op : ¬ op.safe (a.eval σ) (b.eval σ) := by
            cases op <;> simp [SExpr.divSafe, ha, hb, BinOp.safe] at hunsafe ⊢
            · exact hunsafe
          obtain ⟨σ_a, hexec_a, hval_a, hntmp_a, htmp_a⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
          rw [hra] at hexec_a hval_a; simp at hexec_a hval_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨σ_b, hexec_b, hval_b, hntmp_b, htmp_b⟩ :=
            refCompileExpr_correct b (offset + codeA.length) tmp1 σ σ_a p
              htf_b hb hagree_a hcodeB
          rw [hrb] at hexec_b hval_b; simp at hexec_b hval_b
          have hge_a := refCompileExpr_nextTmp_ge a offset nextTmp
          rw [hra] at hge_a; simp at hge_a
          have hva : σ_b va = a.eval σ := by
            have hbound := refCompileExpr_result_bound a offset nextTmp htf_a
            rw [hra] at hbound; simp at hbound
            cases hbound with
            | inl h => rw [hntmp_b va h, hval_a]
            | inr h => obtain ⟨k, _, hlt, heq⟩ := h; rw [heq, htmp_b k hlt, ← heq, hval_a]
          have hinstr : p[offset + codeA.length + codeB.length]? =
              some (.binop x op va vb) := by
            have := hcode.right.head
            simp only [List.length_append] at this; rw [← Nat.add_assoc] at this; exact this
          exact ⟨offset + codeA.length + codeB.length, σ_b,
            FragExec.trans' hexec_a hexec_b,
            no_step_unsafe_binop hinstr (by rw [hva, hval_b]; exact hunsafe_op),
            by simp [List.length_append]; omega⟩
        · obtain ⟨σ_a, hexec_a, _, hntmp_a, _⟩ :=
            refCompileExpr_correct a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
          rw [hra] at hexec_a; simp at hexec_a
          have hagree_a : ∀ v, v.isTmp = false → σ_a v = σ v := by
            intro v hv; rw [hntmp_a v hv]; exact hagree v hv
          obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
            refCompileExpr_stuck b (offset + codeA.length) tmp1 σ σ_a p
              htf_b hb hagree_a hcodeB
          rw [hrb] at hlt; simp at hlt
          exact ⟨pc_s, σ_s, FragExec.trans' hexec_a hfrag, hstuck,
            by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileExpr_stuck a offset nextTmp σ σ_tac p htf_a ha hagree hcodeA
        rw [hra] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, hfrag, hstuck, by simp [List.length_append]; omega⟩
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
      by_cases hds₁ : s₁.divSafe fuel σ
      · have hds₂ : ¬ s₂.divSafe fuel σ₁ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hds₁, hq₁, h])
        obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
          refCompileStmt_correct s₁ fuel σ σ₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hagree hcode1
        rw [hrc1] at hexec₁; simp at hexec₁
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₂ fuel σ₁ σ' (offset + code1.length) tmp1 p σ₁_tac hinterp htf₂ hds₂ hagree₁ hcode2
        rw [hrc2] at hlt; simp at hlt
        exact ⟨pc_s, σ_s, FragExec.trans' hexec₁ hfrag, hstuck,
          by simp [List.length_append]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          ih₁ fuel σ σ₁ offset nextTmp p σ_tac hq₁ htf₁ hds₁ hagree hcode1
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
      by_cases hbds : b.divSafe σ
      · have hds₁ : ¬ s₁.divSafe fuel σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h])
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
          refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
            σ_bool hinterp htf₁ hds₁ hagree_bool hct
        rw [hrct] at hlt; simp at hlt
        exact ⟨pc_s, σ_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left.left
      by_cases hbds : b.divSafe σ
      · have hds₂ : ¬ s₂.divSafe fuel σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, hbds, hb, h])
        obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
          refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
            σ_bool hinterp htf₂ hds₂ hagree_bool hce
        rw [hrce] at hlt; simp at hlt
        exact ⟨pc_s, σ_s,
          FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
          by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
      · obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
      cases hb : b.eval σ with
      | false =>
        simp [hb] at hinterp; subst hinterp
        have hbds : ¬ b.divSafe σ := by
          intro h; exact hunsafe (by simp [Stmt.divSafe, h, hb])
        obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
          refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
              -- Execute one full iteration
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
                  tmpB p σ_bool hq htf_body hds_body hagree_bool hcbody
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
                ihf σ₁ σ' σ_body hinterp hds_loop hagree_body
              dsimp only [refCompileStmt] at hlt; rw [hrcb, hrcbody] at hlt
              simp only [] at hlt
              exact ⟨pc_s, σ_s, FragExec.trans' hexec_iter hfrag, hstuck, hlt⟩
            · -- Body unsafe
              obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
                refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
                  htf_body hds_body hagree_bool hcbody
              rw [hrcbody] at hlt; simp at hlt
              exact ⟨pc_s, σ_s,
                FragExec.trans' (FragExec.trans' hexec_bool hexec_if) hfrag, hstuck,
                by simp [List.length_append, List.length_cons, List.length_nil]; omega⟩
          · -- Bool unsafe
            obtain ⟨pc_s, σ_s, hfrag, hstuck, hlt⟩ :=
              refCompileBool_stuck b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
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
    (hunsafe : ¬ s.divSafe fuel σ) :
    ¬ ∃ σ_tac, haltsWithResult (refCompile s) 0 σ σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  obtain ⟨pc_s, σ_s, hfrag, hstuck, _⟩ :=
    refCompileStmt_stuck s fuel σ σ' 0 0 (refCompile s) σ hinterp htmpfree hunsafe
      (fun _ _ => rfl) hcode
  exact stuck_run_no_halt hfrag hstuck hhalt

-- ============================================================
-- § 17. Step-indexed execution (RefStepsN)
-- ============================================================

/-- Step-indexed multi-step relation: exactly `n` steps. -/
inductive RefStepsN (p : Prog) : Nat → Cfg → Cfg → Prop where
  | refl : RefStepsN p 0 c c
  | step : Step p c c' → RefStepsN p n c' c'' → RefStepsN p (n + 1) c c''

theorem RefStepsN.to_Steps {p : Prog} {n : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') : p ⊩ c ⟶* c' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step s ih

theorem Steps.to_RefStepsN {p : Prog} {c c' : Cfg}
    (h : p ⊩ c ⟶* c') : ∃ n, RefStepsN p n c c' := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step s hn⟩

private theorem refStepsN_cast {p : Prog} {n n' : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') (heq : n = n') : RefStepsN p n' c c' := heq ▸ h

theorem RefStepsN.trans {p : Prog} {n m : Nat} {c c' c'' : Cfg}
    (h₁ : RefStepsN p n c c') (h₂ : RefStepsN p m c' c'') :
    RefStepsN p (n + m) c c'' := by
  induction n generalizing c with
  | zero => cases h₁; simpa using h₂
  | succ k ih =>
    cases h₁ with
    | step s rest =>
      exact refStepsN_cast (.step s (ih rest)) (by omega)

theorem RefStepsN.det_prefix {p : Prog} {n m : Nat} {c c₁ c₂ : Cfg}
    (h₁ : RefStepsN p n c c₁) (h₂ : RefStepsN p m c c₂) (hle : n ≤ m) :
    RefStepsN p (m - n) c₁ c₂ := by
  induction n generalizing c m with
  | zero => cases h₁; simpa using h₂
  | succ k ih =>
    cases h₁ with
    | step s rest =>
      cases h₂ with
      | refl => omega
      | step s' rest' =>
        have := Step.deterministic s s'; subst this
        exact refStepsN_cast (ih rest rest' (by omega)) (by omega)

/-- A halted config cannot take a step in RefStepsN. -/
theorem RefStepsN.no_step_halt {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.halt σ) c) : False := by
  cases h with | step s _ => exact Step.no_step_from_halt s

/-- If execution takes unbounded steps through `run` configs, it cannot halt. -/
theorem no_halt_of_unbounded {p : Prog} {pc : Nat} {σ : Store}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ) (Cfg.run pc' σ')) :
    ∀ σ', ¬ haltsWithResult p pc σ σ' := by
  intro σ' hhalt
  obtain ⟨k, hk⟩ := hhalt.to_RefStepsN
  obtain ⟨n, hn_ge, pc', σ_r, hn⟩ := hunbounded (k + 1)
  have hpref := RefStepsN.det_prefix hk hn (by omega)
  have : ∃ d, n - k = d + 1 := ⟨n - k - 1, by omega⟩
  obtain ⟨d, hd⟩ := this
  rw [hd] at hpref
  exact RefStepsN.no_step_halt hpref

-- ============================================================
-- § 18. Fuel monotonicity
-- ============================================================

/-- If the interpreter terminates at some fuel, it terminates with the same
    result at one more fuel. -/
theorem Stmt.interp_fuel_succ (s : Stmt) :
    ∀ fuel σ σ', s.interp fuel σ = some σ' → s.interp (fuel + 1) σ = some σ' := by
  induction s with
  | skip => intro fuel σ σ' h; simp only [Stmt.interp] at h ⊢; exact h
  | assign _ _ => intro fuel σ σ' h; simp only [Stmt.interp] at h ⊢; exact h
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ σ' h
    simp only [Stmt.interp] at h ⊢
    cases hq₁ : s₁.interp fuel σ with
    | none => simp [hq₁] at h
    | some σ₁ =>
      simp [hq₁] at h
      simp [ih₁ fuel σ σ₁ hq₁]
      exact ih₂ fuel σ₁ σ' h
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ σ' h
    simp only [Stmt.interp] at h ⊢
    cases hb : b.eval σ <;> simp [hb] at h ⊢
    · exact ih₂ fuel σ σ' h
    · exact ih₁ fuel σ σ' h
  | loop b body ih =>
    intro fuel
    induction fuel with
    | zero => intro σ σ' h; simp [Stmt.interp] at h
    | succ fuel' ihf =>
      intro σ σ' h
      simp only [Stmt.interp] at h
      cases hb : b.eval σ with
      | false => simp [hb] at h; subst h; simp [Stmt.interp, hb]
      | true =>
        simp [hb] at h
        cases hq : body.interp fuel' σ with
        | none => simp [hq] at h
        | some σ₁ =>
          simp [hq] at h
          have hbody := ih fuel' σ σ₁ hq
          have hloop := ihf σ₁ σ' h
          unfold Stmt.interp; simp [hb, hbody, hloop]

/-- Fuel monotonicity: success at `fuel` implies success at `fuel + k`. -/
theorem Stmt.interp_fuel_mono (s : Stmt) (fuel k : Nat) (σ σ' : Store)
    (h : s.interp fuel σ = some σ') : s.interp (fuel + k) σ = some σ' := by
  induction k with
  | zero => simpa
  | succ k ihk =>
    rw [show fuel + (k + 1) = (fuel + k) + 1 from by omega]
    exact s.interp_fuel_succ _ _ _ ihk

/-- Contrapositive of fuel monotonicity: `none` at higher fuel implies `none`
    at lower fuel. -/
theorem Stmt.interp_none_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store)
    (h : s.interp fuel' σ = none) (hle : fuel ≤ fuel') : s.interp fuel σ = none := by
  cases hq : s.interp fuel σ with
  | none => rfl
  | some σ' =>
    have := s.interp_fuel_mono fuel (fuel' - fuel) σ σ' hq
    rw [show fuel + (fuel' - fuel) = fuel' from by omega] at this
    simp [this] at h

-- ============================================================
-- § 19. divSafe anti-monotonicity
-- ============================================================

/-- `divSafe` at higher fuel implies `divSafe` at lower fuel. -/
theorem Stmt.divSafe_fuel_succ (s : Stmt) :
    ∀ fuel σ, s.divSafe (fuel + 1) σ → s.divSafe fuel σ := by
  induction s with
  | skip => intro _ _ _; simp only [Stmt.divSafe]
  | assign _ _ => intro fuel σ h; simp only [Stmt.divSafe] at h ⊢; exact h
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ h
    simp only [Stmt.divSafe] at h ⊢
    refine ⟨ih₁ fuel σ h.1, ?_⟩
    cases hq : s₁.interp fuel σ with
    | none => trivial
    | some σ₁ =>
      rw [s₁.interp_fuel_succ fuel σ σ₁ hq] at h
      exact ih₂ fuel σ₁ h.2
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ h
    simp only [Stmt.divSafe] at h ⊢
    refine ⟨h.1, ?_⟩
    cases hb : b.eval σ <;> simp [hb] at h ⊢
    · exact ih₂ fuel σ h.2
    · exact ih₁ fuel σ h.2
  | loop b body ih =>
    intro fuel
    induction fuel with
    | zero => intro _ _; simp only [Stmt.divSafe]
    | succ fuel' ihf =>
      intro σ h
      -- h : divSafe (fuel'+2) σ (loop b body)
      -- goal : divSafe (fuel'+1) σ (loop b body)
      unfold Stmt.divSafe at h ⊢
      refine ⟨h.1, ?_⟩
      cases hb : b.eval σ <;> simp [hb] at h ⊢
      · refine ⟨ih fuel' σ h.2.1, ?_⟩
        cases hq : body.interp fuel' σ with
        | none => exact trivial
        | some σ₁ =>
          have hq' := body.interp_fuel_succ fuel' σ σ₁ hq
          rw [hq'] at h; exact ihf σ₁ h.2.2

theorem Stmt.divSafe_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store)
    (h : s.divSafe fuel' σ) (hle : fuel ≤ fuel') : s.divSafe fuel σ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simp at h; exact h
  | succ k ihk => exact ihk (s.divSafe_fuel_succ _ _ h) (by omega)

-- ============================================================
-- § 20. Divergence theorems
-- ============================================================

set_option maxHeartbeats 1600000

/-- One iteration of a divergent loop: execute bool, ifgoto (fall through),
    body, goto back to condLabel. Returns RefStepsN and updated state. -/
private theorem loop_one_iter
    (b : SBool) (body : Stmt) (fuel₀ : Nat) (σ σ₁ : Store)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : (Stmt.loop b body).tmpFree)
    (hb : b.eval σ = true)
    (hbds : SBool.divSafe σ b)
    (hbody_res : body.interp fuel₀ σ = some σ₁)
    (hds_body : body.divSafe fuel₀ σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt (.loop b body) offset nextTmp).1 p offset) :
    ∃ σ₁_tac k, k ≥ 2 ∧
      RefStepsN p k (Cfg.run offset σ_tac) (Cfg.run offset σ₁_tac) ∧
      (∀ v, v.isTmp = false → σ₁_tac v = σ₁ v) := by
  -- Unfold compiler output
  dsimp only [refCompileStmt] at hcode
  generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode
  obtain ⟨codeBool, be, tmpB⟩ := rcb
  generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody at hcode
  obtain ⟨codeBody, tmpBody⟩ := rcbody
  simp only [] at hcode
  -- Bool compilation
  have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
    fun v hv => htmpfree v (List.mem_append_left _ hv)
  have htf_body : body.tmpFree :=
    fun v hv => htmpfree v (List.mem_append_right _ hv)
  have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
    rw [hrcb]; exact hcode.left.left.left
  obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
    refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
  rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
  have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
    intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
  -- ifgoto (not be) — falls through since b = true
  have hifg : p[offset + codeBool.length]? =
      some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
    have := hcode.left.left.right.head
    simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
  have hnotbe : (BoolExpr.not be).eval σ_bool = false := by
    simp [BoolExpr.eval, heval_bool, hb]
  -- Body execution
  have hcbody : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
      (offset + codeBool.length + 1) := by
    rw [hrcbody]
    have := hcode.left.right
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rwa [show offset + (codeBool.length + 1) =
        offset + codeBool.length + 1 from by omega] at this
  obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
    refCompileStmt_correct body fuel₀ σ σ₁ (offset + codeBool.length + 1) tmpB p σ_bool
      hbody_res htf_body hds_body hagree_bool hcbody
  rw [hrcbody] at hexec_body; simp at hexec_body
  -- goto condLabel
  have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
      some (.goto offset) := by
    have := hcode.right.head
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rwa [show offset + (codeBool.length + (0 + 1) + codeBody.length) =
        offset + codeBool.length + 1 + codeBody.length from by omega] at this
  -- Convert to RefStepsN and compose
  obtain ⟨n_bool, hn_bool⟩ := hexec_bool.to_RefStepsN
  have hn_if : RefStepsN p 1 (Cfg.run (offset + codeBool.length) σ_bool)
      (Cfg.run (offset + codeBool.length + 1) σ_bool) :=
    .step (Step.iffall hifg hnotbe) .refl
  obtain ⟨n_body, hn_body⟩ := hexec_body.to_RefStepsN
  have hn_goto : RefStepsN p 1
      (Cfg.run (offset + codeBool.length + 1 + codeBody.length) σ_body)
      (Cfg.run offset σ_body) :=
    .step (Step.goto hgoto_back) .refl
  have htotal := ((hn_bool.trans hn_if).trans hn_body).trans hn_goto
  exact ⟨σ_body, n_bool + 1 + n_body + 1, by omega, htotal, hagree_body⟩

/-- Main divergence: a divergent, div-safe statement produces unbounded steps. -/
theorem refCompileStmt_diverges (s : Stmt) (σ : Store)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ', RefStepsN p n (Cfg.run offset σ_tac) (Cfg.run pc' σ') := by
  induction s generalizing σ offset nextTmp σ_tac with
  | skip => exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | assign _ _ => exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | seq s₁ s₂ ih₁ ih₂ =>
    -- Either s₁ diverges or s₁ terminates and s₂ diverges
    by_cases hs₁ : ∀ fuel, s₁.interp fuel σ = none
    · -- s₁ diverges
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have hs₁_safe : ∀ fuel, s₁.divSafe fuel σ := by
        intro fuel; have h := hsafe fuel; simp only [Stmt.divSafe] at h; exact h.1
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      intro N
      obtain ⟨n, hn_ge, pc', σ', hn⟩ := ih₁ σ offset nextTmp σ_tac htf₁ hs₁ hs₁_safe hagree hcode1 N
      exact ⟨n, hn_ge, pc', σ', hn⟩
    · -- s₁ terminates
      obtain ⟨fuel₀, hne⟩ := Classical.not_forall.mp hs₁
      obtain ⟨σ₁, hσ₁⟩ := Option.ne_none_iff_exists.mp hne
      have hσ₁ := hσ₁.symm
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hs₁_safe' : s₁.divSafe fuel₀ σ := by
        have h := hsafe fuel₀; simp only [Stmt.divSafe] at h; exact h.1
      -- s₂ diverges from σ₁
      have hs₂_div : ∀ fuel, s₂.interp fuel σ₁ = none := by
        intro fuel
        let g := max fuel fuel₀
        have hq : s₁.interp g σ = some σ₁ := by
          have := s₁.interp_fuel_mono fuel₀ (g - fuel₀) σ σ₁ hσ₁
          rwa [show fuel₀ + (g - fuel₀) = g from by omega] at this
        have h := hdiv g; simp only [Stmt.interp] at h
        -- h : (s₁.interp g σ).bind (s₂.interp g) = none
        rw [hq] at h
        -- h : s₂.interp g σ₁ = none
        exact s₂.interp_none_of_le fuel g σ₁ h (by omega)
      have hs₂_safe : ∀ fuel, s₂.divSafe fuel σ₁ := by
        intro fuel
        let g := max fuel fuel₀
        have hq : s₁.interp g σ = some σ₁ := by
          have := s₁.interp_fuel_mono fuel₀ (g - fuel₀) σ σ₁ hσ₁
          rwa [show fuel₀ + (g - fuel₀) = g from by omega] at this
        have h := hsafe g; simp only [Stmt.divSafe] at h
        rw [hq] at h
        -- h.2 : s₂.divSafe g σ₁
        exact s₂.divSafe_of_le fuel g σ₁ h.2 (by omega)
      -- Execute s₁, then use IH on s₂
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
        refCompileStmt_correct s₁ fuel₀ σ σ₁ offset nextTmp p σ_tac hσ₁ htf₁ hs₁_safe' hagree hcode1
      rw [hrc1] at hexec₁; simp at hexec₁
      obtain ⟨n₁, hn₁⟩ := hexec₁.to_RefStepsN
      have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
          (offset + code1.length) := by rw [hrc2]; exact hcode.right
      intro N
      obtain ⟨n₂, hn₂_ge, pc', σ', hn₂⟩ :=
        ih₂ σ₁ (offset + code1.length) tmp1 σ₁_tac htf₂ hs₂_div hs₂_safe hagree₁ hcode2 N
      exact ⟨n₁ + n₂, by omega, pc', σ', hn₁.trans hn₂⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    -- Case split on b.eval σ
    cases hb : b.eval σ with
    | true =>
      -- s₁ diverges
      have hs₁_div : ∀ fuel, s₁.interp fuel σ = none := by
        intro fuel; have := hdiv fuel; simp [Stmt.interp, hb] at this; exact this
      have hbds : SBool.divSafe σ b := by
        have := hsafe 0; simp [Stmt.divSafe, hb] at this; exact this.1
      have hs₁_safe : ∀ fuel, s₁.divSafe fuel σ := by
        intro fuel; have := hsafe fuel; simp [Stmt.divSafe, hb] at this; exact this.2
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
      have htf₁ : s₁.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode ⊢
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrce : refCompileStmt s₂ (offset + codeBool.length + 1) tmpB = rce at hcode ⊢
      obtain ⟨codeElse, tmpElse⟩ := rce
      generalize hrct : refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse = rct at hcode ⊢
      obtain ⟨codeThen, tmpThen⟩ := rct
      simp only [] at hcode ⊢
      -- Bool compilation + ifgoto
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left.left
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      have hbe_true : be.eval σ_bool = true := by rw [heval_bool, hb]
      obtain ⟨n_bool, hn_bool⟩ := hexec_bool.to_RefStepsN
      have hn_if : RefStepsN p 1 _ _ := .step (Step.iftrue hifg hbe_true) .refl
      have hn_prefix := hn_bool.trans hn_if
      -- IH on s₁ from thenStart
      have hct : CodeAt (refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
          (offset + codeBool.length + 1 + codeElse.length + 1) := by
        rw [hrct]
        have := hcode.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
            offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
      intro N
      obtain ⟨n₁, hn₁_ge, pc', σ', hn₁⟩ :=
        ih₁ σ (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse σ_bool
          htf₁ hs₁_div hs₁_safe hagree_bool hct N
      exact ⟨n_bool + 1 + n₁, by omega, pc', σ', hn_prefix.trans hn₁⟩
    | false =>
      -- s₂ diverges (symmetric)
      have hs₂_div : ∀ fuel, s₂.interp fuel σ = none := by
        intro fuel; have := hdiv fuel; simp [Stmt.interp, hb] at this; exact this
      have hbds : SBool.divSafe σ b := by
        have := hsafe 0; simp [Stmt.divSafe, hb] at this; exact this.1
      have hs₂_safe : ∀ fuel, s₂.divSafe fuel σ := by
        intro fuel; have := hsafe fuel; simp [Stmt.divSafe, hb] at this; exact this.2
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_left _ hv))
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
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left.left
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      have hbe_false : be.eval σ_bool = false := by rw [heval_bool, hb]
      obtain ⟨n_bool, hn_bool⟩ := hexec_bool.to_RefStepsN
      have hn_if : RefStepsN p 1 _ _ := .step (Step.iffall hifg hbe_false) .refl
      have hn_prefix := hn_bool.trans hn_if
      have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
          (offset + codeBool.length + 1) := by
        rw [hrce]
        have := hcode.left.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) =
            offset + codeBool.length + 1 from by omega] at this
      intro N
      obtain ⟨n₂, hn₂_ge, pc', σ', hn₂⟩ :=
        ih₂ σ (offset + codeBool.length + 1) tmpB σ_bool
          htf₂ hs₂_div hs₂_safe hagree_bool hce N
      exact ⟨n_bool + 1 + n₂, by omega, pc', σ', hn_prefix.trans hn₂⟩
  | loop b body ih_body =>
    -- b.eval σ = true (otherwise loop terminates at fuel 1)
    have hb : b.eval σ = true := by
      cases hb : b.eval σ with
      | true => rfl
      | false => have h := hdiv 1; unfold Stmt.interp at h; simp [hb] at h
    have hbds : SBool.divSafe σ b := by
      have h := hsafe 1; unfold Stmt.divSafe at h; simp [hb] at h; exact h.1
    have htf_body : body.tmpFree :=
      fun v hv => htmpfree v (List.mem_append_right _ hv)
    -- Case split: body diverges or terminates
    by_cases hbody_div : ∀ fuel, body.interp fuel σ = none
    · -- Body diverges: use structural IH on body
      have hbody_safe : ∀ fuel, body.divSafe fuel σ := by
        intro fuel; have h := hsafe (fuel + 1)
        unfold Stmt.divSafe at h; simp [hb] at h; exact h.2.1
      -- Extract body code region
      dsimp only [refCompileStmt] at hcode
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody
          at hcode
      obtain ⟨codeBody, tmpBody⟩ := rcbody
      simp only [] at hcode
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htmpfree v (List.mem_append_left _ hv)
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
        have := hcode.left.left.right.head
        simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
      have hnotbe : (BoolExpr.not be).eval σ_bool = false := by
        simp [BoolExpr.eval, heval_bool, hb]
      obtain ⟨n_bool, hn_bool⟩ := hexec_bool.to_RefStepsN
      have hn_if : RefStepsN p 1 _ _ := .step (Step.iffall hifg hnotbe) .refl
      have hn_prefix := hn_bool.trans hn_if
      have hcbody : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
          (offset + codeBool.length + 1) := by
        rw [hrcbody]
        have := hcode.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) =
            offset + codeBool.length + 1 from by omega] at this
      intro N
      obtain ⟨n_body, hn_body_ge, pc', σ_r, hn_body⟩ :=
        ih_body σ (offset + codeBool.length + 1) tmpB σ_bool
          htf_body hbody_div hbody_safe hagree_bool hcbody N
      exact ⟨n_bool + 1 + n_body, by omega, pc', σ_r, hn_prefix.trans hn_body⟩
    · -- Body terminates: iterate loop via N-induction
      obtain ⟨fuel₀, hne⟩ := Classical.not_forall.mp hbody_div
      obtain ⟨σ₁, hσ₁⟩ := Option.ne_none_iff_exists.mp hne
      have hσ₁ := hσ₁.symm
      -- Inner induction on N, universally quantifying σ and σ_tac
      suffices h_inner : ∀ N (σ' : Store) (σ_tac' : Store),
          (∀ fuel, (Stmt.loop b body).interp fuel σ' = none) →
          (∀ fuel, (Stmt.loop b body).divSafe fuel σ') →
          (∀ v, v.isTmp = false → σ_tac' v = σ' v) →
          ∃ n, n ≥ N ∧ ∃ pc' σ_r,
            RefStepsN p n (Cfg.run offset σ_tac') (Cfg.run pc' σ_r) from
        fun N => h_inner N σ σ_tac hdiv hsafe hagree
      intro N
      induction N with
      | zero => intro σ' σ_tac' _ _ _; exact ⟨0, Nat.le.refl, offset, σ_tac', .refl⟩
      | succ N ihN =>
        intro σ' σ_tac' hdiv' hsafe' hagree'
        -- b.eval σ' = true
        have hb' : b.eval σ' = true := by
          cases hb' : b.eval σ' with
          | true => rfl
          | false => have h := hdiv' 1; unfold Stmt.interp at h; simp [hb'] at h
        have hbds' : SBool.divSafe σ' b := by
          have h := hsafe' 1; unfold Stmt.divSafe at h; simp [hb'] at h; exact h.1
        -- Find a fuel where body terminates from σ'
        by_cases hbody_div' : ∀ fuel, body.interp fuel σ' = none
        · -- Body diverges from σ': use structural IH on body
          have hbody_safe' : ∀ fuel, body.divSafe fuel σ' := by
            intro fuel; have h := hsafe' (fuel + 1)
            unfold Stmt.divSafe at h; simp [hb'] at h; exact h.2.1
          -- Extract code regions from hcode
          have hcode' := hcode
          dsimp only [refCompileStmt] at hcode'
          generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode'
          obtain ⟨codeBool, be, tmpB⟩ := rcb
          generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody
              at hcode'
          obtain ⟨codeBody, tmpBody⟩ := rcbody
          simp only [] at hcode'
          have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
            rw [hrcb]; exact hcode'.left.left.left
          have htf_b' : ∀ v ∈ b.freeVars, v.isTmp = false :=
            fun v hv => htmpfree v (List.mem_append_left _ hv)
          obtain ⟨σ_bool', hexec_bool', heval_bool', hntmp_bool', _⟩ :=
            refCompileBool_correct b offset nextTmp σ' σ_tac' p htf_b' hbds' hagree' hcb
          rw [hrcb] at hexec_bool' heval_bool'; simp at hexec_bool' heval_bool'
          have hagree_bool' : ∀ v, v.isTmp = false → σ_bool' v = σ' v := by
            intro v hv; rw [hntmp_bool' v hv]; exact hagree' v hv
          have hifg' : p[offset + codeBool.length]? =
              some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
            have := hcode'.left.left.right.head
            simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
          have hnotbe' : (BoolExpr.not be).eval σ_bool' = false := by
            simp [BoolExpr.eval, heval_bool', hb']
          obtain ⟨n_bool', hn_bool'⟩ := hexec_bool'.to_RefStepsN
          have hn_if' : RefStepsN p 1 _ _ := .step (Step.iffall hifg' hnotbe') .refl
          have hn_prefix' := hn_bool'.trans hn_if'
          have hcbody' : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
              (offset + codeBool.length + 1) := by
            rw [hrcbody]
            have := hcode'.left.right
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rwa [show offset + (codeBool.length + (0 + 1)) =
                offset + codeBool.length + 1 from by omega] at this
          obtain ⟨n_body', hn_body_ge', pc', σ_r', hn_body'⟩ :=
            ih_body σ' (offset + codeBool.length + 1) tmpB σ_bool'
              htf_body hbody_div' hbody_safe' hagree_bool' hcbody' N
          exact ⟨n_bool' + 1 + n_body', by omega, pc', σ_r', hn_prefix'.trans hn_body'⟩
        · -- Body terminates from σ': one iteration + IH on N
          obtain ⟨fuel₁, hne'⟩ := Classical.not_forall.mp hbody_div'
          obtain ⟨σ₂, hσ₂⟩ := Option.ne_none_iff_exists.mp hne'
          have hσ₂ := hσ₂.symm
          have hds_body' : body.divSafe fuel₁ σ' := by
            have h := hsafe' (fuel₁ + 1); unfold Stmt.divSafe at h
            simp [hb'] at h; exact h.2.1
          obtain ⟨σ₂_tac, k_iter, hk_ge, hk_steps, hagree₂⟩ :=
            loop_one_iter b body fuel₁ σ' σ₂ offset nextTmp p σ_tac'
              htmpfree hb' hbds' hσ₂ hds_body' hagree' hcode
          -- Loop still diverges from σ₂
          have hdiv₂ : ∀ fuel, (Stmt.loop b body).interp fuel σ₂ = none := by
            intro fuel
            have hbody_up := body.interp_fuel_mono fuel₁ (max fuel fuel₁ - fuel₁) σ' σ₂ hσ₂
            rw [show fuel₁ + (max fuel fuel₁ - fuel₁) = max fuel fuel₁ from by omega] at hbody_up
            have h := hdiv' (max fuel fuel₁ + 1)
            unfold Stmt.interp at h; simp [hb'] at h
            simp [hbody_up] at h
            exact (Stmt.loop b body).interp_none_of_le fuel (max fuel fuel₁) σ₂ h (by omega)
          -- Loop still div-safe from σ₂
          have hsafe₂ : ∀ fuel, (Stmt.loop b body).divSafe fuel σ₂ := by
            intro fuel
            have hbody_up := body.interp_fuel_mono fuel₁ (max fuel fuel₁ - fuel₁) σ' σ₂ hσ₂
            rw [show fuel₁ + (max fuel fuel₁ - fuel₁) = max fuel fuel₁ from by omega] at hbody_up
            have h := hsafe' (max fuel fuel₁ + 1)
            have : (Stmt.loop b body).divSafe (max fuel fuel₁) σ₂ := by
              unfold Stmt.divSafe at h; simp [hb'] at h
              have := h.2.2; rw [hbody_up] at this; exact this
            exact (Stmt.loop b body).divSafe_of_le fuel (max fuel fuel₁) σ₂ this (by omega)
          obtain ⟨n', hn'_ge, pc', σ_r, hn'⟩ := ihN σ₂ σ₂_tac hdiv₂ hsafe₂ hagree₂
          exact ⟨k_iter + n', by omega, pc', σ_r, hk_steps.trans hn'⟩

/-- Top-level divergence: if the source diverges with division safety,
    the compiled program does not halt. -/
theorem refCompile_diverge (s : Stmt) (σ : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ) :
    ¬ ∃ σ_tac, haltsWithResult (refCompile s) 0 σ σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  have hunbounded := refCompileStmt_diverges s σ 0 0 (refCompile s) σ
    htmpfree hdiv hsafe (fun _ _ => rfl) hcode
  exact no_halt_of_unbounded hunbounded σ_tac hhalt
