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

def SExpr.freeVars : SExpr → List Var
  | .lit _ => []
  | .var x => [x]
  | .bin _ a b => a.freeVars ++ b.freeVars

def SBool.freeVars : SBool → List Var
  | .lit _ => []
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
  | lit _ => rfl
  | bvar x =>
    simp only [SBool.eval, SBool.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | cmp op a b =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [SExpr.eval_agree a σ τ (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.eval_agree b σ τ (fun v hv => h v (List.mem_append_right _ hv))]
  | not e ih => simp only [SBool.eval]; rw [ih h]
  | and a b iha ihb =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [SBool.eval, SBool.freeVars] at *
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
  | .lit _ => True
  | .bvar _ => True
  | .cmp _ a b => a.divSafe σ ∧ b.divSafe σ
  | .not e => e.divSafe σ
  | .and a b => a.divSafe σ ∧ (a.eval σ = true → b.divSafe σ)
  | .or a b => a.divSafe σ ∧ (a.eval σ = false → b.divSafe σ)

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
  | .lit _ => True
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
-- § 4c. Bridge: typeCheck → tmpFree
-- ============================================================

/-- If `noTmpDecls decls` holds and `v` is found in `decls`, then `v` is not a tmp. -/
private theorem noTmpDecls_not_tmp {decls : List (Var × VarTy)} {v : Var} {ty : VarTy}
    (hnt : Program.noTmpDecls decls = true) (hlook : decls.lookup v = some ty) :
    v.isTmp = false := by
  -- If v.isTmp were true, lookup would return none, contradicting hlook
  cases hv : v.isTmp with
  | false => rfl
  | true =>
    have := lookup_none_of_isTmp_wt hnt hv
    simp [this] at hlook

/-- All variables in a well-typed arithmetic expression are declared. -/
private theorem checkSExpr_declared {lookup : Var → Option VarTy}
    {e : SExpr} (h : Program.checkSExpr lookup e = true) :
    ∀ v ∈ e.freeVars, ∃ ty, lookup v = some ty := by
  induction e with
  | lit _ => intro v hv; simp [SExpr.freeVars] at hv
  | var x =>
    intro v hv; simp [SExpr.freeVars] at hv; subst hv
    simp [Program.checkSExpr] at h; exact ⟨.int, h⟩
  | bin _ a b iha ihb =>
    simp [Program.checkSExpr, Bool.and_eq_true] at h
    intro v hv; simp [SExpr.freeVars] at hv
    rcases hv with ha | hb
    · exact iha h.1 v ha
    · exact ihb h.2 v hb

/-- All variables in a well-typed boolean expression are declared. -/
private theorem checkSBool_declared {lookup : Var → Option VarTy}
    {b : SBool} (h : Program.checkSBool lookup b = true) :
    ∀ v ∈ b.freeVars, ∃ ty, lookup v = some ty := by
  induction b with
  | lit _ => intro v hv; simp [SBool.freeVars] at hv
  | bvar x =>
    intro v hv; simp [SBool.freeVars] at hv; subst hv
    simp [Program.checkSBool] at h; exact ⟨.bool, h⟩
  | cmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact checkSExpr_declared h.1 v ha
    · exact checkSExpr_declared h.2 v hb
  | not e ih =>
    simp [Program.checkSBool] at h
    intro v hv; simp [SBool.freeVars] at hv; exact ih h v hv
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact iha h.1 v ha
    · exact ihb h.2 v hb
  | or a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact iha h.1 v ha
    · exact ihb h.2 v hb

/-- All variables in a well-typed statement are declared. -/
private theorem checkStmt_declared {lookup : Var → Option VarTy}
    {s : Stmt} (h : Program.checkStmt lookup s = true) :
    ∀ v ∈ s.allVars, ∃ ty, lookup v = some ty := by
  induction s with
  | skip => intro v hv; simp [Stmt.allVars] at hv
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with rfl | he
    · exact ⟨.int, h.1⟩
    · exact checkSExpr_declared h.2 v he
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with rfl | hb
    · exact ⟨.bool, h.1⟩
    · exact checkSBool_declared h.2 v hb
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with h1 | h2
    · exact ih1 h.1 v h1
    · exact ih2 h.2 v h2
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨hb, h1⟩, h2⟩ := h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with hfb | h1v | h2v
    · exact checkSBool_declared hb v hfb
    · exact ih1 h1 v h1v
    · exact ih2 h2 v h2v
  | loop b body ih =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with hfb | hbv
    · exact checkSBool_declared h.1 v hfb
    · exact ih h.2 v hbv

/-- **Bridge lemma**: A type-checked program's body is tmp-free — no variable
    in the source program uses the compiler-reserved `__t` prefix. -/
theorem Program.typeCheck_tmpFree (prog : Program) (h : prog.typeCheck = true) :
    prog.body.tmpFree := by
  simp [Program.typeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨_, hnt⟩, hchk⟩ := h
  intro v hv
  obtain ⟨ty, hlook⟩ := checkStmt_declared hchk v hv
  exact noTmpDecls_not_tmp hnt hlook

-- ============================================================
-- § 4d. Source-level type preservation
-- ============================================================

/-- Helper: if `Γ x = .int`, then `TypedStore Γ σ` implies `∃ n, σ x = .int n`. -/
private theorem TypedStore.getInt {Γ : TyCtx} {σ : Store} {x : Var}
    (hts : TypedStore Γ σ) (hty : Γ x = .int) : ∃ n, σ x = .int n := by
  have := hts x; rw [hty] at this
  exact Value.int_of_typeOf_int this

/-- Helper: checkStmt-declared variables have their declared type in tyCtx. -/
private theorem lookup_tyCtx {lookup : Var → Option VarTy} {Γ : TyCtx}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty) {x : Var} {ty : VarTy}
    (h : lookup x = some ty) : Γ x = ty := hcompat x ty h

/-- Source-level type preservation: interpreting a well-typed statement
    preserves TypedStore. -/
theorem Stmt.interp_preserves_typedStore
    {s : Stmt} {fuel : Nat} {σ σ' : Store} {Γ : TyCtx}
    {lookup : Var → Option VarTy}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkStmt lookup s = true)
    (hts : TypedStore Γ σ)
    (hinterp : s.interp fuel σ = some σ') :
    TypedStore Γ σ' := by
  induction s generalizing fuel σ σ' with
  | skip =>
    simp [Stmt.interp] at hinterp; subst hinterp; exact hts
  | assign x e =>
    simp [Stmt.interp] at hinterp; subst hinterp
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    intro y; simp [Store.update]; split
    · case isTrue heq => simp [heq, Value.typeOf_int, hcompat _ .int hchk.1]
    · case isFalse => exact hts y
  | bassign x b =>
    simp [Stmt.interp] at hinterp; subst hinterp
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    intro y; simp [Store.update]; split
    · case isTrue heq => simp [heq, Value.typeOf_bool, hcompat _ .bool hchk.1]
    · case isFalse => exact hts y
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp [Stmt.interp] at hinterp
    cases hq : s1.interp fuel σ with
    | none => simp [hq] at hinterp
    | some σ₁ =>
      simp [hq] at hinterp
      exact ih2 hchk.2 (ih1 hchk.1 hts hq) hinterp
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, h1⟩, h2⟩ := hchk
    cases hcond : b.eval σ with
    | true =>
      simp [Stmt.interp, hcond] at hinterp
      exact ih1 h1 hts hinterp
    | false =>
      simp [Stmt.interp, hcond] at hinterp
      exact ih2 h2 hts hinterp
  | loop b body ih =>
    induction fuel generalizing σ σ' with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      cases hcond : b.eval σ with
      | false =>
        simp [Stmt.interp, hcond] at hinterp; subst hinterp; exact hts
      | true =>
        simp [Stmt.interp, hcond] at hinterp
        cases hq : body.interp fuel' σ with
        | none => simp [hq] at hinterp
        | some σ₁ =>
          simp [hq] at hinterp
          exact ihf (ih hchk.2 hts hq) hinterp

-- ============================================================
-- § 4e. Bridge: typeCheck + TypedStore → intTyped
-- ============================================================

/-- If `checkSExpr lookup e = true` and `TypedStore Γ σ` with compatible lookup/Γ,
    then all vars in `e.freeVars` have int values in `σ`. -/
private theorem checkSExpr_intVars
    {lookup : Var → Option VarTy} {Γ : TyCtx} {σ : Store} {e : SExpr}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkSExpr lookup e = true)
    (hts : TypedStore Γ σ) :
    ∀ v ∈ e.freeVars, ∃ n, σ v = .int n := by
  induction e with
  | lit _ => intro v hv; simp [SExpr.freeVars] at hv
  | var x =>
    intro v hv; simp [SExpr.freeVars] at hv; subst hv
    simp [Program.checkSExpr] at hchk
    exact TypedStore.getInt hts (hcompat _ .int hchk)
  | bin _ a b iha ihb =>
    simp [Program.checkSExpr, Bool.and_eq_true] at hchk
    intro v hv; simp [SExpr.freeVars] at hv
    rcases hv with ha | hb
    · exact iha hchk.1 v ha
    · exact ihb hchk.2 v hb

/-- If `checkSBool lookup b = true` and `TypedStore Γ σ` with compatible lookup/Γ,
    then `b.intTyped σ`. -/
private theorem checkSBool_intTyped
    {lookup : Var → Option VarTy} {Γ : TyCtx} {σ : Store} {b : SBool}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkSBool lookup b = true)
    (hts : TypedStore Γ σ) :
    b.intTyped σ := by
  induction b with
  | lit _ => trivial
  | bvar _ => trivial
  | cmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨checkSExpr_intVars hcompat hchk.1 hts, checkSExpr_intVars hcompat hchk.2 hts⟩
  | not e ih => simp [Program.checkSBool] at hchk; exact ih hchk
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨iha hchk.1, ihb hchk.2⟩
  | or a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨iha hchk.1, ihb hchk.2⟩

/-- If `checkStmt lookup s = true`, `TypedStore Γ σ`, and lookup/Γ are compatible,
    then `s.intTyped fuel σ`. -/
theorem checkStmt_intTyped
    (lookup : Var → Option VarTy) (Γ : TyCtx) (σ : Store) (s : Stmt) (fuel : Nat)
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkStmt lookup s = true)
    (hts : TypedStore Γ σ) :
    s.intTyped fuel σ := by
  induction s generalizing fuel σ with
  | skip => simp [Stmt.intTyped]
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp [Stmt.intTyped]
    exact checkSExpr_intVars hcompat hchk.2 hts
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp [Stmt.intTyped]
    exact checkSBool_intTyped hcompat hchk.2 hts
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp only [Stmt.intTyped]
    refine ⟨ih1 σ fuel hchk.1 hts, ?_⟩
    cases hq : s1.interp fuel σ with
    | none => simp [hq]
    | some σ₁ =>
        exact ih2 σ₁ fuel hchk.2 (Stmt.interp_preserves_typedStore hcompat hchk.1 hts hq)
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨hb, h1⟩, h2⟩ := hchk
    simp only [Stmt.intTyped]
    refine ⟨checkSBool_intTyped hcompat hb hts, ?_⟩
    cases b.eval σ <;> simp
    · exact ih2 σ fuel h2 hts
    · exact ih1 σ fuel h1 hts
  | loop b body ih =>
    induction fuel generalizing σ with
    | zero => simp [Stmt.intTyped]
    | succ fuel' ihf =>
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      simp only [Stmt.intTyped]
      refine ⟨checkSBool_intTyped hcompat hchk.1 hts, ?_⟩
      cases hcond : b.eval σ <;> simp [hcond]
      refine ⟨ih σ fuel' hchk.2 hts, ?_⟩
      cases hq : body.interp fuel' σ with
      | none => simp [hq]
      | some σ₁ =>
        simp [hq]
        exact ihf σ₁ (Stmt.interp_preserves_typedStore hcompat hchk.2 hts hq)

/-- **Bridge lemma**: A type-checked program with a well-typed store satisfies intTyped. -/
theorem Program.typeCheck_intTyped (prog : Program) (h : prog.typeCheck = true)
    (σ : Store) (hts : TypedStore prog.tyCtx σ) (fuel : Nat) :
    prog.body.intTyped fuel σ := by
  simp [Program.typeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨_, _⟩, hchk⟩ := h
  exact checkStmt_intTyped prog.lookupTy prog.tyCtx σ prog.body fuel
    (fun x ty hlook => by
      show (prog.lookupTy x).getD .int = ty
      rw [hlook]; rfl) hchk hts

-- ============================================================
-- § 5. Fragment execution
-- ============================================================

abbrev FragExec (p : Prog) (pc : Nat) (σ : Store) (pc' : Nat) (σ' : Store) (am am' : ArrayMem) : Prop :=
  p ⊩ Cfg.run pc σ am ⟶* Cfg.run pc' σ' am'

theorem FragExec.rfl' (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) :
    FragExec p pc σ pc σ am am := Steps.refl

theorem FragExec.trans' {p : Prog} {pc₁ pc₂ pc₃ : Nat} {σ₁ σ₂ σ₃ : Store} {am₁ am₂ am₃ : ArrayMem}
    (h₁ : FragExec p pc₁ σ₁ pc₂ σ₂ am₁ am₂) (h₂ : FragExec p pc₂ σ₂ pc₃ σ₃ am₂ am₃) :
    FragExec p pc₁ σ₁ pc₃ σ₃ am₁ am₃ := Steps.trans h₁ h₂

theorem FragExec.toHalt {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hfrag : FragExec p pc σ pc' σ' am am')
    (hhalt : p[pc']? = some .halt) :
    p ⊩ Cfg.run pc σ am ⟶* Cfg.halt σ' am' :=
  Steps.trans hfrag (Steps.single (.halt hhalt))
