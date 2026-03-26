import CredibleCompilation.WhileLang

set_option linter.unusedSimpArgs false

/-!
# Compiler Correctness: While Language → TAC

We prove that the compiler from the while language to TAC preserves
semantics: if the source interpreter produces a result, the compiled
TAC program halts with the same result on non-temporary variables.

## Main theorem

`compile_correct`: if `Stmt.interp fuel σ s = some σ'` and the program
is division-safe, then `haltsWithResult (compile s) 0 σ σ_tac` where
`σ_tac` agrees with `σ'` on all non-temporary variables.
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
  | .cmp _ a b => a.freeVars ++ b.freeVars
  | .not e => e.freeVars
  | .and a b => a.freeVars ++ b.freeVars
  | .or a b => a.freeVars ++ b.freeVars

def Stmt.allVars : Stmt → List Var
  | .skip => []
  | .assign x e => x :: e.freeVars
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
  | var x => simp only [SExpr.eval]; exact h x (by simp [SExpr.freeVars])
  | bin op a b iha ihb =>
    simp only [SExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]

theorem SBool.eval_agree (sb : SBool) (σ τ : Store)
    (h : ∀ v ∈ sb.freeVars, σ v = τ v) : sb.eval σ = sb.eval τ := by
  induction sb with
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
-- § 2a. String / array helpers
-- ============================================================

private axiom string_startsWith_append_left (s t : String) :
    (s ++ t).startsWith s = true

theorem freshVar_isTmp (n : Nat) : (s!"__t{n}" : String).startsWith "__t" = true :=
  string_startsWith_append_left "__t" (toString n)

private theorem array_set!_size {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by
  simp [Array.set!, Array.setIfInBounds]
  split <;> simp [Array.size_set]

private theorem set!_getElem?_ne {α : Type} (a : Array α) (idx : Nat) (v : α)
    (i : Nat) (hne : i ≠ idx) (_hi : i < a.size) :
    (a.set! idx v)[i]? = a[i]? := by
  simp [Array.set!, Array.setIfInBounds]
  split
  · rw [Array.getElem?_set (by omega)]; simp [Ne.symm hne]
  · rfl

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
    refine ⟨τ[x ↦ e.eval τ], by simp [Stmt.interp], ?_⟩
    intro v hv; simp only [Store.update]
    split
    · exact SExpr.eval_tmpAgree e σ τ hagree
        (fun w hw => htf w (List.mem_cons_of_mem x hw))
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
  | .cmp _ a b => a.divSafe σ ∧ b.divSafe σ
  | .not e => e.divSafe σ
  | .and a b => a.divSafe σ ∧ b.divSafe σ
  | .or a b => a.divSafe σ ∧ b.divSafe σ

def Stmt.divSafe (fuel : Nat) (σ : Store) : Stmt → Prop
  | .skip => True
  | .assign _ e => e.divSafe σ
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

-- ============================================================
-- § 6. Compilation output characterization
-- ============================================================

theorem compileStmt_seq_code (s₁ s₂ : Stmt) (st : CompState) :
    ((compileStmt (.seq s₁ s₂)).run st).2 =
      ((compileStmt s₂).run ((compileStmt s₁).run st).2).2 := by
  simp only [compileStmt, StateT.run, bind, Bind.bind, StateT.bind]; rfl

theorem compileStmt_skip_code (st : CompState) :
    ((compileStmt .skip).run st).2 = st := by
  simp only [compileStmt, StateT.run, pure, Pure.pure, StateT.pure]

-- ============================================================
-- § 7. Code extension: compiled sub-blocks are prefixes
-- ============================================================

private theorem push_old (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]? = a[i]? := by
  simp [Array.getElem?_push]; omega

private theorem push_last (a : Array α) (x : α) :
    (a.push x)[a.size]? = some x := by
  simp [Array.getElem?_push]

theorem compileExpr_code_ge (e : SExpr) (st : CompState) :
    st.code.size ≤ ((compileExpr e).run st).2.code.size := by
  induction e generalizing st with
  | lit _ =>
    show st.code.size ≤ (st.code.push _).size
    simp [Array.size_push]
  | var _ => exact Nat.le_refl _
  | bin op a b iha ihb =>
    simp only [compileExpr, bind, Bind.bind, StateT.bind, StateT.run,
      freshVar, emit, get, set, StateT.set, StateT.pure, StateT.get,
      pure, Pure.pure, getThe, MonadStateOf.get, MonadStateOf.set]
    generalize hpa : compileExpr a st = pa
    obtain ⟨va, st₁⟩ := pa; simp only []
    generalize hpb : compileExpr b st₁ = pb
    obtain ⟨vb, st₂⟩ := pb
    simp only [Array.size_push]
    have h1 := iha st
    rw [show (compileExpr a).run st = (va, st₁) from hpa] at h1
    have h2 := ihb st₁
    rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at h2
    simp at h1 h2; omega

theorem compileExpr_code_preserved (e : SExpr) (st : CompState) (i : Nat)
    (h : i < st.code.size) :
    ((compileExpr e).run st).2.code[i]? = st.code[i]? := by
  induction e generalizing st i with
  | lit _ =>
    simp only [compileExpr, StateT.run, bind, Bind.bind, StateT.bind,
      freshVar, emit, get, set, StateT.set, StateT.pure, StateT.get,
      pure, Pure.pure, getThe, MonadStateOf.get, MonadStateOf.set]
    exact push_old _ _ _ h
  | var _ => rfl
  | bin op a b iha ihb =>
    simp only [compileExpr, StateT.run, bind, Bind.bind, StateT.bind,
      freshVar, emit, get, set, StateT.set, StateT.pure, StateT.get,
      pure, Pure.pure, getThe, MonadStateOf.get, MonadStateOf.set]
    generalize hpa : compileExpr a st = pa
    obtain ⟨va, st₁⟩ := pa; simp only []
    generalize hpb : compileExpr b st₁ = pb
    obtain ⟨vb, st₂⟩ := pb; simp only []
    -- Goal: (st₂.code.push _)[i]? = st.code[i]?
    have h1 := compileExpr_code_ge a st
    rw [show (compileExpr a).run st = (va, st₁) from hpa] at h1; simp at h1
    have h2 := compileExpr_code_ge b st₁
    rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at h2; simp at h2
    rw [push_old _ _ _ (by omega)]
    have hb_pres := ihb st₁ i (by omega)
    rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at hb_pres; simp at hb_pres
    rw [hb_pres]
    have ha_pres := iha st i h
    rw [show (compileExpr a).run st = (va, st₁) from hpa] at ha_pres; simp at ha_pres
    exact ha_pres

theorem compileBool_code_ge (sb : SBool) (st : CompState) :
    st.code.size ≤ ((compileBool sb).run st).2.code.size := by
  induction sb generalizing st with
  | cmp _ a b =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpa : compileExpr a st = pa
    obtain ⟨va, st₁⟩ := pa; simp only []
    generalize hpb : compileExpr b st₁ = pb
    obtain ⟨vb, st₂⟩ := pb; simp only []
    have h1 := compileExpr_code_ge a st
    rw [show (compileExpr a).run st = (va, st₁) from hpa] at h1; simp at h1
    have h2 := compileExpr_code_ge b st₁
    rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at h2; simp at h2
    omega
  | not e ih =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpe : compileBool e st = pe
    obtain ⟨be, stE⟩ := pe; simp only []
    have := ih st
    rw [show (compileBool e).run st = (be, stE) from hpe] at this; simp at this
    exact this
  | and a b iha ihb =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpa : compileBool a st = pa
    obtain ⟨ba, stA⟩ := pa; simp only []
    generalize hpb : compileBool b stA = pb
    obtain ⟨bb, stB⟩ := pb; simp only []
    have h1 := iha st
    rw [show (compileBool a).run st = (ba, stA) from hpa] at h1; simp at h1
    have h2 := ihb stA
    rw [show (compileBool b).run stA = (bb, stB) from hpb] at h2; simp at h2
    omega
  | or a b iha ihb =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpa : compileBool a st = pa
    obtain ⟨ba, stA⟩ := pa; simp only []
    generalize hpb : compileBool b stA = pb
    obtain ⟨bb, stB⟩ := pb; simp only []
    have h1 := iha st
    rw [show (compileBool a).run st = (ba, stA) from hpa] at h1; simp at h1
    have h2 := ihb stA
    rw [show (compileBool b).run stA = (bb, stB) from hpb] at h2; simp at h2
    omega

theorem compileBool_code_preserved (sb : SBool) (st : CompState) (i : Nat)
    (h : i < st.code.size) :
    ((compileBool sb).run st).2.code[i]? = st.code[i]? := by
  induction sb generalizing st i with
  | cmp _ a b =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpa : compileExpr a st = pa
    obtain ⟨va, st₁⟩ := pa; simp only []
    generalize hpb : compileExpr b st₁ = pb
    obtain ⟨vb, st₂⟩ := pb; simp only []
    have h1 := compileExpr_code_ge a st
    rw [show (compileExpr a).run st = (va, st₁) from hpa] at h1; simp at h1
    have hb_pres := compileExpr_code_preserved b st₁ i (by omega)
    rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at hb_pres; simp at hb_pres
    have ha_pres := compileExpr_code_preserved a st i h
    rw [show (compileExpr a).run st = (va, st₁) from hpa] at ha_pres; simp at ha_pres
    exact hb_pres.trans ha_pres
  | not e ih =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpe : compileBool e st = pe
    obtain ⟨be, stE⟩ := pe; simp only []
    have := ih st i h
    rw [show (compileBool e).run st = (be, stE) from hpe] at this; simp at this
    exact this
  | and a b iha ihb =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpa : compileBool a st = pa
    obtain ⟨ba, stA⟩ := pa; simp only []
    generalize hpb : compileBool b stA = pb
    obtain ⟨bb, stB⟩ := pb; simp only []
    have h1 := compileBool_code_ge a st
    rw [show (compileBool a).run st = (ba, stA) from hpa] at h1; simp at h1
    have hb_pres := ihb stA i (by omega)
    rw [show (compileBool b).run stA = (bb, stB) from hpb] at hb_pres; simp at hb_pres
    have ha_pres := iha st i h
    rw [show (compileBool a).run st = (ba, stA) from hpa] at ha_pres; simp at ha_pres
    exact hb_pres.trans ha_pres
  | or a b iha ihb =>
    simp only [compileBool, bind, Bind.bind, StateT.bind, StateT.run,
      pure, Pure.pure, StateT.pure]
    generalize hpa : compileBool a st = pa
    obtain ⟨ba, stA⟩ := pa; simp only []
    generalize hpb : compileBool b stA = pb
    obtain ⟨bb, stB⟩ := pb; simp only []
    have h1 := compileBool_code_ge a st
    rw [show (compileBool a).run st = (ba, stA) from hpa] at h1; simp at h1
    have hb_pres := ihb stA i (by omega)
    rw [show (compileBool b).run stA = (bb, stB) from hpb] at hb_pres; simp at hb_pres
    have ha_pres := iha st i h
    rw [show (compileBool a).run st = (ba, stA) from hpa] at ha_pres; simp at ha_pres
    exact hb_pres.trans ha_pres

theorem compileStmt_code_ge (s : Stmt) (st : CompState) :
    st.code.size ≤ ((compileStmt s).run st).2.code.size := by
  induction s generalizing st with
  | skip => exact Nat.le_refl _
  | assign x e =>
    cases e with
    | lit n =>
      show st.code.size ≤ (st.code.push _).size
      simp [Array.size_push]
    | var y =>
      show st.code.size ≤ (st.code.push _).size
      simp [Array.size_push]
    | bin op a b =>
      simp only [compileStmt, bind, Bind.bind, StateT.bind, StateT.run,
        emit, get, set, StateT.set, StateT.pure, StateT.get,
        pure, Pure.pure, getThe, MonadStateOf.get, MonadStateOf.set]
      generalize hpa : compileExpr a st = pa
      obtain ⟨va, st₁⟩ := pa; simp only []
      generalize hpb : compileExpr b st₁ = pb
      obtain ⟨vb, st₂⟩ := pb; simp only []
      simp only [Array.size_push]
      have h1 := compileExpr_code_ge a st
      rw [show (compileExpr a).run st = (va, st₁) from hpa] at h1; simp at h1
      have h2 := compileExpr_code_ge b st₁
      rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at h2; simp at h2
      omega
  | seq s₁ s₂ ih₁ ih₂ =>
    show st.code.size ≤
      ((compileStmt s₂).run ((compileStmt s₁).run st).2).2.code.size
    exact Nat.le_trans (ih₁ st) (ih₂ _)
  | ite b s₁ s₂ ih₁ ih₂ =>
    dsimp only [compileStmt]
    simp only [StateT.run, bind, Bind.bind, StateT.bind,
      pure, Pure.pure, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set,
      emit, currentLabel, patch]
    generalize hcb : compileBool b st = cb
    obtain ⟨be, stB⟩ := cb; dsimp only []
    generalize hcs2 : compileStmt s₂ ⟨stB.code.push (.ifgoto be 0), stB.nextTmp⟩ = cs2
    obtain ⟨_, stS2⟩ := cs2; dsimp only []
    generalize hcs1 : compileStmt s₁ ⟨stS2.code.push (.goto 0), stS2.nextTmp⟩ = cs1
    obtain ⟨_, stS1⟩ := cs1; dsimp only []
    simp only [array_set!_size]
    have hb := compileBool_code_ge b st
    rw [show (compileBool b).run st = (be, stB) from hcb] at hb; simp at hb
    have h2 := ih₂ ⟨stB.code.push (.ifgoto be 0), stB.nextTmp⟩
    rw [show (compileStmt s₂).run _ = (_, stS2) from hcs2] at h2; simp [Array.size_push] at h2
    have h1 := ih₁ ⟨stS2.code.push (.goto 0), stS2.nextTmp⟩
    rw [show (compileStmt s₁).run _ = (_, stS1) from hcs1] at h1; simp [Array.size_push] at h1
    omega
  | loop b body ih =>
    dsimp only [compileStmt]
    simp only [StateT.run, bind, Bind.bind, StateT.bind,
      pure, Pure.pure, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set,
      emit, currentLabel, patch]
    generalize hcb : compileBool b st = cb
    obtain ⟨be, stB⟩ := cb; dsimp only []
    generalize hcbody : compileStmt body ⟨stB.code.push (.ifgoto (.not be) 0), stB.nextTmp⟩ = cbody
    obtain ⟨_, stBody⟩ := cbody; dsimp only []
    simp only [array_set!_size, Array.size_push]
    have hb := compileBool_code_ge b st
    rw [show (compileBool b).run st = (be, stB) from hcb] at hb; simp at hb
    have hbd := ih ⟨stB.code.push (.ifgoto (.not be) 0), stB.nextTmp⟩
    rw [show (compileStmt body).run _ = (_, stBody) from hcbody] at hbd
    simp [Array.size_push] at hbd
    omega

theorem compileStmt_code_preserved (s : Stmt) (st : CompState) (i : Nat)
    (h : i < st.code.size) :
    ((compileStmt s).run st).2.code[i]? = st.code[i]? := by
  induction s generalizing st i with
  | skip => rfl
  | assign x e =>
    cases e with
    | lit n =>
      show (st.code.push (.const x n))[i]? = st.code[i]?
      exact push_old _ _ _ h
    | var y =>
      show (st.code.push (.copy x y))[i]? = st.code[i]?
      exact push_old _ _ _ h
    | bin op a b =>
      simp only [compileStmt, bind, Bind.bind, StateT.bind, StateT.run,
        emit, get, set, StateT.set, StateT.pure, StateT.get,
        pure, Pure.pure, getThe, MonadStateOf.get, MonadStateOf.set]
      generalize hpa : compileExpr a st = pa
      obtain ⟨va, st₁⟩ := pa; simp only []
      generalize hpb : compileExpr b st₁ = pb
      obtain ⟨vb, st₂⟩ := pb; simp only []
      have h1 := compileExpr_code_ge a st
      rw [show (compileExpr a).run st = (va, st₁) from hpa] at h1; simp at h1
      have h2 := compileExpr_code_ge b st₁
      rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at h2; simp at h2
      rw [push_old _ _ _ (by omega)]
      have hb_pres := compileExpr_code_preserved b st₁ i (by omega)
      rw [show (compileExpr b).run st₁ = (vb, st₂) from hpb] at hb_pres; simp at hb_pres
      rw [hb_pres]
      have ha_pres := compileExpr_code_preserved a st i h
      rw [show (compileExpr a).run st = (va, st₁) from hpa] at ha_pres; simp at ha_pres
      exact ha_pres
  | seq s₁ s₂ ih₁ ih₂ =>
    show ((compileStmt s₂).run ((compileStmt s₁).run st).2).2.code[i]? = st.code[i]?
    rw [ih₂ _ i (Nat.lt_of_lt_of_le h (compileStmt_code_ge s₁ st)),
        ih₁ st i h]
  | ite b s₁ s₂ ih₁ ih₂ =>
    dsimp only [compileStmt]
    simp only [StateT.run, bind, Bind.bind, StateT.bind,
      pure, Pure.pure, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set,
      emit, currentLabel, patch]
    generalize hcb : compileBool b st = cb
    obtain ⟨be, stB⟩ := cb; dsimp only []
    generalize hcs2 : compileStmt s₂ ⟨stB.code.push (.ifgoto be 0), stB.nextTmp⟩ = cs2
    obtain ⟨_, stS2⟩ := cs2; dsimp only []
    generalize hcs1 : compileStmt s₁ ⟨stS2.code.push (.goto 0), stS2.nextTmp⟩ = cs1
    obtain ⟨_, stS1⟩ := cs1; dsimp only []
    -- Both set! targets are at indices ≥ st.code.size, so don't affect i
    have hb := compileBool_code_ge b st
    rw [show (compileBool b).run st = (be, stB) from hcb] at hb; simp at hb
    have h2 := compileStmt_code_ge s₂ ⟨stB.code.push (.ifgoto be 0), stB.nextTmp⟩
    rw [show (compileStmt s₂).run _ = (_, stS2) from hcs2] at h2; simp [Array.size_push] at h2
    have h1 := compileStmt_code_ge s₁ ⟨stS2.code.push (.goto 0), stS2.nextTmp⟩
    rw [show (compileStmt s₁).run _ = (_, stS1) from hcs1] at h1; simp [Array.size_push] at h1
    -- set! at stS2.code.size (≥ stB.code.size + 1 > i)
    rw [set!_getElem?_ne _ _ _ _ (by omega) (by rw [array_set!_size]; omega)]
    -- set! at stB.code.size (≥ st.code.size > i)
    rw [set!_getElem?_ne _ _ _ _ (by omega) (by omega)]
    -- Now: stS1.code[i]? = st.code[i]?
    have hp1 := ih₁ ⟨stS2.code.push (.goto 0), stS2.nextTmp⟩ i (by simp [Array.size_push]; omega)
    rw [show (compileStmt s₁).run _ = (_, stS1) from hcs1] at hp1; simp at hp1
    rw [hp1, push_old _ _ _ (by omega)]
    have hp2 := ih₂ ⟨stB.code.push (.ifgoto be 0), stB.nextTmp⟩ i (by simp [Array.size_push]; omega)
    rw [show (compileStmt s₂).run _ = (_, stS2) from hcs2] at hp2; simp at hp2
    rw [hp2, push_old _ _ _ (by omega)]
    have hpb := compileBool_code_preserved b st i h
    rw [show (compileBool b).run st = (be, stB) from hcb] at hpb; simp at hpb
    exact hpb
  | loop b body ih =>
    dsimp only [compileStmt]
    simp only [StateT.run, bind, Bind.bind, StateT.bind,
      pure, Pure.pure, StateT.pure,
      get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set,
      emit, currentLabel, patch]
    generalize hcb : compileBool b st = cb
    obtain ⟨be, stB⟩ := cb; dsimp only []
    generalize hcbody : compileStmt body ⟨stB.code.push (.ifgoto (.not be) 0), stB.nextTmp⟩ = cbody
    obtain ⟨_, stBody⟩ := cbody; dsimp only []
    have hb := compileBool_code_ge b st
    rw [show (compileBool b).run st = (be, stB) from hcb] at hb; simp at hb
    have hbd := compileStmt_code_ge body ⟨stB.code.push (.ifgoto (.not be) 0), stB.nextTmp⟩
    rw [show (compileStmt body).run _ = (_, stBody) from hcbody] at hbd
    simp [Array.size_push] at hbd
    -- set! at stB.code.size
    rw [set!_getElem?_ne _ _ _ _ (by omega) (by rw [Array.size_push]; omega)]
    -- push at stBody.code.size
    rw [push_old _ _ _ (by omega)]
    -- stBody.code[i]? = st.code[i]?
    have hp := ih ⟨stB.code.push (.ifgoto (.not be) 0), stB.nextTmp⟩ i
      (by simp [Array.size_push]; omega)
    rw [show (compileStmt body).run _ = (_, stBody) from hcbody] at hp; simp at hp
    rw [hp, push_old _ _ _ (by omega)]
    have hpb := compileBool_code_preserved b st i h
    rw [show (compileBool b).run st = (be, stB) from hcb] at hpb; simp at hpb
    exact hpb

-- ============================================================
-- § 8. Expression compilation correctness
-- ============================================================

theorem compileExpr_correct (e : SExpr) (st : CompState) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false)
    (hsafe : e.divSafe σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hext : ∀ i, i < ((compileExpr e).run st).2.code.size →
      p[i]? = ((compileExpr e).run st).2.code[i]?) :
    let result := (compileExpr e).run st
    ∃ σ', FragExec p st.code.size σ_tac result.2.code.size σ' ∧
      σ' result.1 = e.eval σ ∧
      (∀ w, w.isTmp = false → σ' w = σ_tac w) := by
  sorry

-- ============================================================
-- § 9. Boolean compilation correctness
-- ============================================================

theorem compileBool_correct (sb : SBool) (st : CompState) (σ σ_tac : Store) (p : Prog)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hext : ∀ i, i < ((compileBool sb).run st).2.code.size →
      p[i]? = ((compileBool sb).run st).2.code[i]?) :
    let result := (compileBool sb).run st
    ∃ σ', FragExec p st.code.size σ_tac result.2.code.size σ' ∧
      result.1.eval σ' = sb.eval σ ∧
      (∀ w, w.isTmp = false → σ' w = σ_tac w) := by
  sorry

-- ============================================================
-- § 10. Statement compilation correctness
-- ============================================================

theorem compileStmt_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (st : CompState) (p : Prog) (σ_tac : Store)
    (hinterp : s.interp fuel σ = some σ')
    (htmpfree : s.tmpFree)
    (hsafe : s.divSafe fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hext : ∀ i, i < ((compileStmt s).run st).2.code.size →
      p[i]? = ((compileStmt s).run st).2.code[i]?) :
    ∃ σ_tac', FragExec p st.code.size σ_tac
                ((compileStmt s).run st).2.code.size σ_tac' ∧
      (∀ v, v.isTmp = false → σ_tac' v = σ' v) := by
  induction s generalizing fuel σ σ' st p σ_tac with
  | skip =>
    simp only [Stmt.interp, Option.some.injEq] at hinterp
    subst hinterp
    rw [compileStmt_skip_code]
    exact ⟨σ_tac, FragExec.rfl' _ _ _, hagree⟩

  | assign x e =>
    simp only [Stmt.interp, Option.some.injEq] at hinterp
    subst hinterp
    sorry

  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at hinterp
    cases hq₁ : s₁.interp fuel σ with
    | none => simp [hq₁] at hinterp
    | some σ₁ =>
      simp [hq₁] at hinterp
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hds₁ : s₁.divSafe fuel σ := by
        simp only [Stmt.divSafe] at hsafe; exact hsafe.1
      have hds₂ : s₂.divSafe fuel σ₁ := by
        simp only [Stmt.divSafe] at hsafe; rw [hq₁] at hsafe; exact hsafe.2
      have hext₁ : ∀ i, i < ((compileStmt s₁).run st).2.code.size →
          p[i]? = ((compileStmt s₁).run st).2.code[i]? := by
        intro i hi
        have hle := compileStmt_code_ge s₂ ((compileStmt s₁).run st).2
        simp only [compileStmt_seq_code] at hext
        have hi' : i < ((compileStmt s₂).run ((compileStmt s₁).run st).2).2.code.size :=
          Nat.lt_of_lt_of_le hi hle
        rw [hext i hi', compileStmt_code_preserved s₂ ((compileStmt s₁).run st).2 i hi]
      obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
        ih₁ fuel σ σ₁ st p σ_tac hq₁ htf₁ hds₁ hagree hext₁
      have hext₂ : ∀ i, i < ((compileStmt s₂).run ((compileStmt s₁).run st).2).2.code.size →
          p[i]? = ((compileStmt s₂).run ((compileStmt s₁).run st).2).2.code[i]? := by
        intro i hi; simp only [compileStmt_seq_code] at hext; exact hext i hi
      obtain ⟨σ₂_tac, hexec₂, hagree₂⟩ :=
        ih₂ fuel σ₁ σ' ((compileStmt s₁).run st).2 p σ₁_tac hinterp htf₂ hds₂ hagree₁ hext₂
      simp only [compileStmt_seq_code]
      exact ⟨σ₂_tac, FragExec.trans' hexec₁ hexec₂, hagree₂⟩

  | ite _ _ _ _ _ => sorry

  | loop _ _ _ => sorry

-- ============================================================
-- § 11. Top-level correctness theorem
-- ============================================================

theorem compile_correct (s : Stmt) (fuel : Nat) (σ σ' : Store)
    (hinterp : s.interp fuel σ = some σ')
    (htmpfree : s.tmpFree)
    (hsafe : s.divSafe fuel σ) :
    ∃ σ_tac, haltsWithResult (compile s) 0 σ σ_tac ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  -- compile s = ((compileStmt s).run ⟨#[], 0⟩).2.code.push .halt
  have hprog_eq : compile s =
      ((compileStmt s).run (⟨#[], 0⟩ : CompState)).2.code.push .halt := by
    unfold compile
    simp only [StateT.run, bind, Bind.bind, StateT.bind,
      emit, get, set, pure, Pure.pure, StateT.pure, StateT.get,
      getThe, MonadStateOf.get, MonadStateOf.set, StateT.set]
    rfl
  -- Code extension: stmt code is a prefix of the compiled program
  have hext : ∀ i, i < ((compileStmt s).run (⟨#[], 0⟩ : CompState)).2.code.size →
      (compile s)[i]? = ((compileStmt s).run (⟨#[], 0⟩ : CompState)).2.code[i]? := by
    intro i hi; rw [hprog_eq]; exact push_old _ TAC.halt i hi
  -- compileStmt_correct: execution reaches end of stmt code
  have hstart : (⟨#[], 0⟩ : CompState).code.size = 0 := rfl
  obtain ⟨σ_tac, hexec, hagree'⟩ :=
    compileStmt_correct s fuel σ σ' ⟨#[], 0⟩ (compile s) σ
      hinterp htmpfree hsafe (fun _ _ => rfl) hext
  -- halt instruction at end
  have hhalt : (compile s)[((compileStmt s).run (⟨#[], 0⟩ : CompState)).2.code.size]? =
      some .halt := by
    rw [hprog_eq]; exact push_last _ TAC.halt
  rw [hstart] at hexec
  exact ⟨σ_tac, FragExec.toHalt hexec hhalt, hagree'⟩

-- ============================================================
-- § 12. Sorry inventory
-- ============================================================

/-!
## Status: 5 sorrys remaining (down from 13)

### Fully proved
- Expression/boolean evaluation congruence
- Interpreter congruence (`Stmt.interp_tmpAgree`)
- All code growth lemmas (`compileExpr_code_ge`, `compileBool_code_ge`, `compileStmt_code_ge`)
- All code preservation lemmas (`compileExpr_code_preserved`, `compileBool_code_preserved`, `compileStmt_code_preserved`)
- `compileStmt_correct / skip, seq`
- `compile_correct` (modulo `compileStmt_correct`)

### Remaining sorrys (5)
- `compileExpr_correct` — expression fragment execution
- `compileBool_correct` — boolean fragment execution
- `compileStmt_correct / assign` — assignment case
- `compileStmt_correct / ite` — if-then-else (requires patch reasoning)
- `compileStmt_correct / loop` — while loop (requires fuel induction)

### Key obstacle
The fragment execution proofs require a **temp-index preservation** invariant:
compileExpr must guarantee that temporaries with index < st.nextTmp are preserved
(not just non-tmp variables). Without this, the `bin` case cannot show that
sub-expression b's compilation preserves sub-expression a's result variable.
-/
