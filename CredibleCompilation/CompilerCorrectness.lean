import CredibleCompilation.WhileLang

set_option linter.unusedSimpArgs false

/-!
# Compiler Infrastructure: Variable Classification, Congruence, and Division Safety

Shared infrastructure for reasoning about the While→TAC compiler:
- Variable classification (`isTmp`, `freeVars`, `allVars`, `tmpFree`)
- Expression/boolean evaluation congruence under store agreement
- Interpreter congruence on tmp-free programs
- Division safety predicates

These definitions and lemmas are used by `RefCompiler.lean` for the
verified compiler correctness proof.
-/

-- ============================================================
-- § 1. Variable classification
-- ============================================================

def Var.isTmp (v : Var) : Bool := v.startsWith "__t"

def SExpr.freeVars : SExpr → List Var
  | .lit _ => []
  | .var x => [x]
  | .bin _ a b => a.freeVars ++ b.freeVars

def SBool.freeVars : SBool → List Var
  | .bvar x => [x]
  | .cmp _ a b => a.freeVars ++ b.freeVars
  | .not e => e.freeVars
  | .and a b => a.freeVars ++ b.freeVars
  | .or a b => a.freeVars ++ b.freeVars

def Stmt.allVars : Stmt → List Var
  | .skip => []
  | .assign x e => x :: e.freeVars
  | .bassign x b => x :: b.freeVars
  | .seq s₁ s₂ => s₁.allVars ++ s₂.allVars
  | .ite b s₁ s₂ => b.freeVars ++ s₁.allVars ++ s₂.allVars
  | .loop b body => b.freeVars ++ body.allVars

def Stmt.tmpFree (s : Stmt) : Prop := ∀ v ∈ s.allVars, v.isTmp = false

-- ============================================================
-- § 2. Expression evaluation congruence
-- ============================================================

theorem SExpr.eval_agree (e : SExpr) (σ τ : Store)
    (h : ∀ v ∈ e.freeVars, σ v = τ v) : e.eval σ = e.eval τ := by
  induction e with
  | lit _ => rfl
  | var x =>
    simp only [SExpr.eval, SExpr.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | bin op a b iha ihb =>
    simp only [SExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]

theorem SBool.eval_agree (sb : SBool) (σ τ : Store)
    (h : ∀ v ∈ sb.freeVars, σ v = τ v) : sb.eval σ = sb.eval τ := by
  induction sb with
  | bvar x =>
    simp only [SBool.eval, SBool.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | cmp op a b =>
    simp only [SBool.eval]
    rw [SExpr.eval_agree a σ τ (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.eval_agree b σ τ (fun v hv => h v (List.mem_append_right _ hv))]
  | not e ih => simp only [SBool.eval]; rw [ih h]
  | and a b iha ihb =>
    simp only [SBool.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [SBool.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]

theorem SExpr.eval_tmpAgree (e : SExpr) (σ τ : Store)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    e.eval σ = e.eval τ :=
  SExpr.eval_agree e σ τ (fun v hv => hagree v (htf v hv))

theorem SBool.eval_tmpAgree (sb : SBool) (σ τ : Store)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false) :
    sb.eval σ = sb.eval τ :=
  SBool.eval_agree sb σ τ (fun v hv => hagree v (htf v hv))

-- ============================================================
-- § 2a. String helpers
-- ============================================================

private axiom string_startsWith_append_left (s t : String) :
    (s ++ t).startsWith s = true

theorem freshVar_isTmp (n : Nat) : (s!"__t{n}" : String).startsWith "__t" = true :=
  string_startsWith_append_left "__t" (toString n)

-- ============================================================
-- § 3. Interpreter congruence on tmp-free programs
-- ============================================================

theorem Stmt.interp_tmpAgree (s : Stmt) (fuel : Nat) (σ τ : Store)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : s.tmpFree)
    (σ' : Store) (h : s.interp fuel σ = some σ') :
    ∃ τ', s.interp fuel τ = some τ' ∧
      (∀ v, v.isTmp = false → σ' v = τ' v) := by
  induction s generalizing fuel σ τ σ' with
  | skip =>
    simp only [Stmt.interp, Option.some.injEq] at h; subst h
    exact ⟨τ, by simp [Stmt.interp], hagree⟩
  | assign x e =>
    simp only [Stmt.interp, Option.some.injEq] at h; subst h
    refine ⟨τ[x ↦ .int (e.eval τ)], by simp [Stmt.interp], ?_⟩
    intro v hv; simp only [Store.update]
    split
    · exact congrArg (Value.int ·) (SExpr.eval_tmpAgree e σ τ hagree
        (fun w hw => htf w (List.mem_cons_of_mem x hw)))
    · exact hagree v hv
  | bassign x b =>
    simp only [Stmt.interp, Option.some.injEq] at h; subst h
    refine ⟨τ[x ↦ .bool (b.eval τ)], by simp [Stmt.interp], ?_⟩
    intro v hv; simp only [Store.update]
    split
    · exact congrArg (Value.bool ·) (SBool.eval_tmpAgree b σ τ hagree
        (fun w hw => htf w (List.mem_cons_of_mem x hw)))
    · exact hagree v hv
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at h
    cases hq : s₁.interp fuel σ with
    | none => simp [hq] at h
    | some σ₁ =>
      simp [hq] at h
      have htf₁ : s₁.tmpFree := fun v hv => htf v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htf v (List.mem_append_right _ hv)
      obtain ⟨τ₁, hτ₁, hagree₁⟩ := ih₁ fuel σ τ hagree htf₁ σ₁ hq
      obtain ⟨τ', hτ', hagree'⟩ := ih₂ fuel σ₁ τ₁ hagree₁ htf₂ σ' h
      refine ⟨τ', ?_, hagree'⟩
      simp only [Stmt.interp]; rw [hτ₁]; simp [hτ']
  | ite b s₁ s₂ ih₁ ih₂ =>
    have hbool : b.eval σ = b.eval τ := SBool.eval_tmpAgree b σ τ hagree
      (fun v hv => htf v (List.mem_append_left _ (List.mem_append_left _ hv)))
    cases hb : b.eval σ with
    | true =>
      simp only [Stmt.interp, hb] at h
      have htf₁ : s₁.tmpFree :=
        fun v hv => htf v (List.mem_append_left _ (List.mem_append_right _ hv))
      obtain ⟨τ', hτ', hagree'⟩ := ih₁ fuel σ τ hagree htf₁ σ' h
      exact ⟨τ', by simp [Stmt.interp, ← hbool, hb, hτ'], hagree'⟩
    | false =>
      simp only [Stmt.interp, hb, Bool.false_eq_true, ite_false] at h
      have htf₂ : s₂.tmpFree :=
        fun v hv => htf v (List.mem_append_right _ hv)
      obtain ⟨τ', hτ', hagree'⟩ := ih₂ fuel σ τ hagree htf₂ σ' h
      refine ⟨τ', ?_, hagree'⟩
      simp only [Stmt.interp, ← hbool, hb, Bool.false_eq_true, ite_false]
      exact hτ'
  | loop b body ih =>
    induction fuel generalizing σ τ σ' with
    | zero => simp [Stmt.interp] at h
    | succ fuel' ihf =>
      have hbool : b.eval σ = b.eval τ := SBool.eval_tmpAgree b σ τ hagree
        (fun v hv => htf v (List.mem_append_left _ hv))
      cases hb : b.eval σ with
      | true =>
        simp only [Stmt.interp, hb] at h
        cases hq : body.interp fuel' σ with
        | none => simp [hq] at h
        | some σ₁ =>
          simp [hq] at h
          have htf_body : body.tmpFree :=
            fun v hv => htf v (List.mem_append_right _ hv)
          obtain ⟨τ₁, hτ₁, hagree₁⟩ := ih fuel' σ τ hagree htf_body σ₁ hq
          obtain ⟨τ', hτ', hagree'⟩ := ihf σ₁ τ₁ hagree₁ σ' h
          refine ⟨τ', ?_, hagree'⟩
          simp only [Stmt.interp, ← hbool, hb]; rw [hτ₁]; simp [hτ']
      | false =>
        simp only [Stmt.interp, hb, Bool.false_eq_true, ite_false, Option.some.injEq] at h
        subst h
        refine ⟨τ, ?_, hagree⟩
        simp only [Stmt.interp, ← hbool, hb, Bool.false_eq_true, ite_false]

-- ============================================================
-- § 4. Division safety
-- ============================================================

def SExpr.divSafe (σ : Store) : SExpr → Prop
  | .lit _ => True
  | .var _ => True
  | .bin .div a b => a.divSafe σ ∧ b.divSafe σ ∧ b.eval σ ≠ 0
  | .bin _ a b => a.divSafe σ ∧ b.divSafe σ

def SBool.divSafe (σ : Store) : SBool → Prop
  | .bvar _ => True
  | .cmp _ a b => a.divSafe σ ∧ b.divSafe σ
  | .not e => e.divSafe σ
  | .and a b => a.divSafe σ ∧ b.divSafe σ
  | .or a b => a.divSafe σ ∧ b.divSafe σ

def Stmt.divSafe (fuel : Nat) (σ : Store) : Stmt → Prop
  | .skip => True
  | .assign _ e => e.divSafe σ
  | .bassign _ b => b.divSafe σ
  | .seq s₁ s₂ =>
    s₁.divSafe fuel σ ∧
    match s₁.interp fuel σ with
    | some σ' => s₂.divSafe fuel σ'
    | none => True
  | .ite b s₁ s₂ =>
    b.divSafe σ ∧ (if b.eval σ then s₁.divSafe fuel σ else s₂.divSafe fuel σ)
  | .loop b body =>
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      b.divSafe σ ∧
      if b.eval σ then
        body.divSafe fuel' σ ∧
        match body.interp fuel' σ with
        | some σ' => (Stmt.loop b body).divSafe fuel' σ'
        | none => True
      else True

-- ============================================================
-- § 4b. Integer typing (all arithmetic-position variables have int values)
-- ============================================================

/-- All variables in arithmetic subexpressions of a boolean expression have int values. -/
def SBool.intTyped (σ : Store) : SBool → Prop
  | .bvar _ => True
  | .cmp _ a b => (∀ v ∈ a.freeVars, ∃ n, σ v = .int n) ∧
                  (∀ v ∈ b.freeVars, ∃ n, σ v = .int n)
  | .not e => e.intTyped σ
  | .and a b => a.intTyped σ ∧ b.intTyped σ
  | .or a b => a.intTyped σ ∧ b.intTyped σ

/-- All arithmetic-position variables in a statement have int values in σ.
    Mirrors `Stmt.divSafe`: for sequential/branching statements, uses the
    post-execution store for subsequent parts. -/
def Stmt.intTyped (fuel : Nat) (σ : Store) : Stmt → Prop
  | .skip => True
  | .assign _ e => ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .bassign _ b => b.intTyped σ
  | .seq s₁ s₂ =>
    s₁.intTyped fuel σ ∧
    match s₁.interp fuel σ with
    | some σ' => s₂.intTyped fuel σ'
    | none => True
  | .ite b s₁ s₂ =>
    b.intTyped σ ∧ (if b.eval σ then s₁.intTyped fuel σ else s₂.intTyped fuel σ)
  | .loop b body =>
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      b.intTyped σ ∧
      if b.eval σ then
        body.intTyped fuel' σ ∧
        match body.interp fuel' σ with
        | some σ' => (Stmt.loop b body).intTyped fuel' σ'
        | none => True
      else True

-- ============================================================
-- § 5. Fragment execution
-- ============================================================

abbrev FragExec (p : Prog) (pc : Nat) (σ : Store) (pc' : Nat) (σ' : Store) : Prop :=
  p ⊩ Cfg.run pc σ ⟶* Cfg.run pc' σ'

theorem FragExec.rfl' (p : Prog) (pc : Nat) (σ : Store) :
    FragExec p pc σ pc σ := Steps.refl

theorem FragExec.trans' {p : Prog} {pc₁ pc₂ pc₃ : Nat} {σ₁ σ₂ σ₃ : Store}
    (h₁ : FragExec p pc₁ σ₁ pc₂ σ₂) (h₂ : FragExec p pc₂ σ₂ pc₃ σ₃) :
    FragExec p pc₁ σ₁ pc₃ σ₃ := Steps.trans h₁ h₂

theorem FragExec.toHalt {p : Prog} {pc pc' : Nat} {σ σ' : Store}
    (hfrag : FragExec p pc σ pc' σ')
    (hhalt : p[pc']? = some .halt) :
    p ⊩ Cfg.run pc σ ⟶* Cfg.halt σ' :=
  Steps.trans hfrag (Steps.single (.halt hhalt))
