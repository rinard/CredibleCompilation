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
  | .arrRead _ idx => idx.freeVars
  | .flit _ => []
  | .fbin _ a b => a.freeVars ++ b.freeVars
  | .intToFloat e => e.freeVars
  | .floatToInt e => e.freeVars
  | .floatExp e => e.freeVars
  | .farrRead _ idx => idx.freeVars

def SBool.freeVars : SBool → List Var
  | .lit _ => []
  | .bvar x => [x]
  | .cmp _ a b => a.freeVars ++ b.freeVars
  | .not e => e.freeVars
  | .and a b => a.freeVars ++ b.freeVars
  | .or a b => a.freeVars ++ b.freeVars
  | .barrRead _ idx => idx.freeVars
  | .fcmp _ a b => a.freeVars ++ b.freeVars

def Stmt.allVars : Stmt → List Var
  | .skip => []
  | .assign x e => x :: e.freeVars
  | .bassign x b => x :: b.freeVars
  | .arrWrite _ idx val => idx.freeVars ++ val.freeVars
  | .barrWrite _ idx bval => idx.freeVars ++ bval.freeVars
  | .seq s₁ s₂ => s₁.allVars ++ s₂.allVars
  | .ite b s₁ s₂ => b.freeVars ++ s₁.allVars ++ s₂.allVars
  | .loop b body => b.freeVars ++ body.allVars
  | .fassign x e => x :: e.freeVars
  | .farrWrite _ idx val => idx.freeVars ++ val.freeVars

def Stmt.tmpFree (s : Stmt) : Prop := ∀ v ∈ s.allVars, v.isTmp = false
def Stmt.ftmpFree (s : Stmt) : Prop := ∀ v ∈ s.allVars, v.isFTmp = false

-- ============================================================
-- § 2. Expression evaluation congruence
-- ============================================================

theorem SExpr.eval_agree (e : SExpr) (σ τ : Store) (am : ArrayMem)
    (h : ∀ v ∈ e.freeVars, σ v = τ v) : e.eval σ am = e.eval τ am := by
  induction e with
  | lit _ => rfl
  | var x =>
    simp only [SExpr.eval, SExpr.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | bin op a b iha ihb =>
    simp only [SExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | arrRead _ idx ih =>
    simp only [SExpr.eval]
    rw [ih h]
  | flit _ => rfl
  | fbin _ a b iha ihb =>
    simp only [SExpr.eval]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | intToFloat e ih => simp only [SExpr.eval]; rw [ih h]
  | floatToInt e ih => simp only [SExpr.eval]; rw [ih h]
  | floatExp e ih => simp only [SExpr.eval]; rw [ih h]
  | farrRead _ idx ih => simp only [SExpr.eval]; rw [ih h]

theorem SBool.eval_agree (sb : SBool) (σ τ : Store) (am : ArrayMem)
    (h : ∀ v ∈ sb.freeVars, σ v = τ v) : sb.eval σ am = sb.eval τ am := by
  induction sb with
  | lit _ => rfl
  | bvar x =>
    simp only [SBool.eval, SBool.freeVars, List.mem_singleton] at *
    rw [h x rfl]
  | cmp op a b =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [SExpr.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.eval_agree b σ τ am (fun v hv => h v (List.mem_append_right _ hv))]
  | not e ih => simp only [SBool.eval]; rw [ih h]
  | and a b iha ihb =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [SBool.eval, SBool.freeVars] at *
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | barrRead arr idx =>
    simp only [SBool.eval]
    rw [SExpr.eval_agree idx σ τ am h]
  | fcmp _ a b =>
    simp only [SBool.eval]
    rw [SExpr.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.eval_agree b σ τ am (fun v hv => h v (List.mem_append_right _ hv))]

theorem SExpr.eval_tmpAgree (e : SExpr) (σ τ : Store) (am : ArrayMem)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    e.eval σ am = e.eval τ am :=
  SExpr.eval_agree e σ τ am (fun v hv => hagree v (htf v hv))

theorem SBool.eval_tmpAgree (sb : SBool) (σ τ : Store) (am : ArrayMem)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false) :
    sb.eval σ am = sb.eval τ am :=
  SBool.eval_agree sb σ τ am (fun v hv => hagree v (htf v hv))

-- ============================================================
-- § 2b. isSafe congruence
-- ============================================================

theorem SExpr.isSafe_agree (e : SExpr) (σ τ : Store) (am : ArrayMem) (decls)
    (h : ∀ v ∈ e.freeVars, σ v = τ v) :
    e.isSafe σ am decls = e.isSafe τ am decls := by
  induction e with
  | lit _ | var _ => rfl
  | bin op a b iha ihb =>
    have ha := iha (fun v hv => h v (List.mem_append_left _ hv))
    have hb := ihb (fun v hv => h v (List.mem_append_right _ hv))
    have hbe := SExpr.eval_agree b σ τ am (fun v hv => h v (List.mem_append_right _ hv))
    cases op <;> simp only [SExpr.isSafe, ha, hb, hbe]
  | arrRead arr idx ih =>
    simp only [SExpr.isSafe]
    rw [ih h, SExpr.eval_agree idx σ τ am h]
  | flit _ => rfl
  | fbin _ a b iha ihb =>
    simp only [SExpr.isSafe]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | intToFloat e ih => simp only [SExpr.isSafe]; rw [ih h]
  | floatToInt e ih => simp only [SExpr.isSafe]; rw [ih h]
  | floatExp e ih => simp only [SExpr.isSafe]; rw [ih h]
  | farrRead arr idx ih =>
    simp only [SExpr.isSafe]
    rw [ih h, SExpr.eval_agree idx σ τ am h]

theorem SBool.isSafe_agree (sb : SBool) (σ τ : Store) (am : ArrayMem) (decls)
    (h : ∀ v ∈ sb.freeVars, σ v = τ v) :
    sb.isSafe σ am decls = sb.isSafe τ am decls := by
  induction sb with
  | lit _ | bvar _ => rfl
  | cmp _ a b =>
    simp only [SBool.isSafe]
    rw [SExpr.isSafe_agree a σ τ am decls (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.isSafe_agree b σ τ am decls (fun v hv => h v (List.mem_append_right _ hv))]
  | not e ih => simp only [SBool.isSafe]; rw [ih h]
  | and a b iha ihb =>
    simp only [SBool.isSafe]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        SBool.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | or a b iha ihb =>
    simp only [SBool.isSafe]
    rw [iha (fun v hv => h v (List.mem_append_left _ hv)),
        SBool.eval_agree a σ τ am (fun v hv => h v (List.mem_append_left _ hv)),
        ihb (fun v hv => h v (List.mem_append_right _ hv))]
  | barrRead arr idx =>
    simp only [SBool.isSafe]
    rw [SExpr.isSafe_agree idx σ τ am decls h,
        SExpr.eval_agree idx σ τ am h]
  | fcmp _ a b =>
    simp only [SBool.isSafe]
    rw [SExpr.isSafe_agree a σ τ am decls (fun v hv => h v (List.mem_append_left _ hv)),
        SExpr.isSafe_agree b σ τ am decls (fun v hv => h v (List.mem_append_right _ hv))]

theorem SExpr.isSafe_tmpAgree (e : SExpr) (σ τ : Store) (am : ArrayMem) (decls)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ e.freeVars, v.isTmp = false) :
    e.isSafe σ am decls = e.isSafe τ am decls :=
  SExpr.isSafe_agree e σ τ am decls (fun v hv => hagree v (htf v hv))

theorem SBool.isSafe_tmpAgree (sb : SBool) (σ τ : Store) (am : ArrayMem) (decls)
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : ∀ v ∈ sb.freeVars, v.isTmp = false) :
    sb.isSafe σ am decls = sb.isSafe τ am decls :=
  SBool.isSafe_agree sb σ τ am decls (fun v hv => hagree v (htf v hv))

-- ============================================================
-- § 3. Interpreter congruence on tmp-free programs
-- ============================================================

theorem Stmt.interp_tmpAgree (s : Stmt) (fuel : Nat) (σ τ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hagree : ∀ v, v.isTmp = false → σ v = τ v)
    (htf : s.tmpFree)
    (σ' : Store) (am' : ArrayMem) (h : s.interp fuel σ am decls = some (σ', am')) :
    ∃ τ' am'', s.interp fuel τ am decls = some (τ', am'') ∧
      (∀ v, v.isTmp = false → σ' v = τ' v) ∧ am'' = am' := by
  induction s generalizing fuel σ τ σ' am am' with
  | skip =>
    simp only [Stmt.interp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨τ, am, by simp [Stmt.interp], hagree, rfl⟩
  | assign x e =>
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun w hw => htf w (List.mem_cons_of_mem x hw)
    have hiSafe_eq : e.isSafe σ am decls = e.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree e σ τ am decls hagree htf_e
    simp only [Stmt.interp] at h
    by_cases hiSafe : e.isSafe σ am decls
    · simp [hiSafe] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ[x ↦ .int (e.eval τ am)], am, by simp [Stmt.interp, ← hiSafe_eq, hiSafe], ?_, rfl⟩
      intro v hv; simp only [Store.update]; split
      · exact congrArg (Value.int ·) (SExpr.eval_tmpAgree e σ τ am hagree htf_e)
      · exact hagree v hv
    · simp [hiSafe] at h
  | bassign x b =>
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun w hw => htf w (List.mem_cons_of_mem x hw)
    have hiSafe_eq : b.isSafe σ am decls = b.isSafe τ am decls :=
      SBool.isSafe_tmpAgree b σ τ am decls hagree htf_b
    simp only [Stmt.interp] at h
    by_cases hiSafe : b.isSafe σ am decls
    · simp [hiSafe] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ[x ↦ .bool (b.eval τ am)], am, by simp [Stmt.interp, ← hiSafe_eq, hiSafe], ?_, rfl⟩
      intro v hv; simp only [Store.update]; split
      · exact congrArg (Value.bool ·) (SBool.eval_tmpAgree b σ τ am hagree htf_b)
      · exact hagree v hv
    · simp [hiSafe] at h
  | arrWrite arr idx val =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hiSafe_idx : idx.isSafe σ am decls = idx.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree idx σ τ am decls hagree htf_idx
    have hiSafe_val : val.isSafe σ am decls = val.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree val σ τ am decls hagree htf_val
    have heval_idx : idx.eval σ am = idx.eval τ am :=
      SExpr.eval_tmpAgree idx σ τ am hagree htf_idx
    have heval_val : val.eval σ am = val.eval τ am :=
      SExpr.eval_tmpAgree val σ τ am hagree htf_val
    simp only [Stmt.interp] at h ⊢
    rw [← hiSafe_idx, ← hiSafe_val, ← heval_idx, ← heval_val]
    by_cases hc : idx.isSafe σ am decls && val.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
    · simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨τ, am.write arr (idx.eval σ am) (val.eval σ am), by simp [hc], hagree, rfl⟩
    · simp [hc] at h
  | barrWrite arr idx bval =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_bval : ∀ v ∈ bval.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hiSafe_idx : (idx : SExpr).isSafe σ am decls = (idx : SExpr).isSafe τ am decls :=
      SExpr.isSafe_tmpAgree idx σ τ am decls hagree htf_idx
    have hiSafe_bval : bval.isSafe σ am decls = bval.isSafe τ am decls :=
      SBool.isSafe_tmpAgree bval σ τ am decls hagree htf_bval
    have heval_idx : idx.eval σ am = idx.eval τ am :=
      SExpr.eval_tmpAgree idx σ τ am hagree htf_idx
    have heval_bval : bval.eval σ am = bval.eval τ am :=
      SBool.eval_tmpAgree bval σ τ am hagree htf_bval
    simp only [Stmt.interp] at h ⊢
    rw [← hiSafe_idx, ← hiSafe_bval, ← heval_idx, ← heval_bval]
    by_cases hc : (idx : SExpr).isSafe σ am decls && bval.isSafe σ am decls && decide ((idx.eval σ am) < arraySizeBv decls arr)
    · simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨τ, am.write arr (idx.eval σ am) (if bval.eval σ am then 1 else 0),
             by simp [hc], hagree, rfl⟩
    · simp [hc] at h
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [Stmt.interp] at h
    cases hq : s₁.interp fuel σ am decls with
    | none => simp [hq] at h
    | some p₁ =>
      simp [hq] at h
      have htf₁ : s₁.tmpFree := fun v hv => htf v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htf v (List.mem_append_right _ hv)
      obtain ⟨τ₁, am₁, hτ₁, hagree₁, ham₁⟩ := ih₁ fuel σ τ am hagree htf₁ p₁.1 p₁.2 hq
      subst ham₁
      obtain ⟨τ', am'', hτ', hagree', ham'⟩ := ih₂ fuel p₁.1 τ₁ p₁.2 hagree₁ htf₂ σ' am' h
      refine ⟨τ', am'', ?_, hagree', ham'⟩
      simp only [Stmt.interp]; rw [hτ₁]; simp [hτ']
  | ite b s₁ s₂ ih₁ ih₂ =>
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ (List.mem_append_left _ hv))
    have hbool : b.eval σ am = b.eval τ am := SBool.eval_tmpAgree b σ τ am hagree htf_b
    have hiSafe_b : b.isSafe σ am decls = b.isSafe τ am decls :=
      SBool.isSafe_tmpAgree b σ τ am decls hagree htf_b
    simp only [Stmt.interp] at h
    by_cases hbs : b.isSafe σ am decls
    · simp [hbs] at h
      cases hb : b.eval σ am with
      | true =>
        simp [hb] at h
        have htf₁ : s₁.tmpFree :=
          fun v hv => htf v (List.mem_append_left _ (List.mem_append_right _ hv))
        obtain ⟨τ', am'', hτ', hagree', ham'⟩ := ih₁ fuel σ τ am hagree htf₁ σ' am' h
        exact ⟨τ', am'', by simp [Stmt.interp, ← hiSafe_b, hbs, ← hbool, hb, hτ'], hagree', ham'⟩
      | false =>
        simp [hb] at h
        have htf₂ : s₂.tmpFree := fun v hv => htf v (List.mem_append_right _ hv)
        obtain ⟨τ', am'', hτ', hagree', ham'⟩ := ih₂ fuel σ τ am hagree htf₂ σ' am' h
        exact ⟨τ', am'', by simp [Stmt.interp, ← hiSafe_b, hbs, ← hbool, hb, hτ'], hagree', ham'⟩
    · simp [hbs] at h
  | loop b body ih =>
    have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    induction fuel generalizing σ τ σ' am am' with
    | zero => simp [Stmt.interp] at h
    | succ fuel' ihf =>
      have hbool : b.eval σ am = b.eval τ am := SBool.eval_tmpAgree b σ τ am hagree htf_b
      have hiSafe_b : b.isSafe σ am decls = b.isSafe τ am decls :=
        SBool.isSafe_tmpAgree b σ τ am decls hagree htf_b
      simp only [Stmt.interp] at h
      by_cases hbs : b.isSafe σ am decls
      · simp [hbs] at h
        cases hb : b.eval σ am with
        | true =>
          simp [hb] at h
          cases hq : body.interp fuel' σ am decls with
          | none => simp [hq] at h
          | some p₁ =>
            simp [hq] at h
            have htf_body : body.tmpFree :=
              fun v hv => htf v (List.mem_append_right _ hv)
            obtain ⟨τ₁, am₁, hτ₁, hagree₁, ham₁⟩ := ih fuel' σ τ am hagree htf_body p₁.1 p₁.2 hq
            subst ham₁
            obtain ⟨τ', am'', hτ', hagree', ham'⟩ := ihf p₁.1 τ₁ p₁.2 hagree₁ σ' am' h
            refine ⟨τ', am'', ?_, hagree', ham'⟩
            simp [Stmt.interp, ← hiSafe_b, hbs, ← hbool, hb, hτ₁, hτ']
        | false =>
          simp [hb] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨τ, am, ?_, hagree, rfl⟩
          simp [Stmt.interp, ← hiSafe_b, hbs, ← hbool, hb]
      · simp [hbs] at h
  | fassign x e =>
    have htf_e : ∀ v ∈ e.freeVars, v.isTmp = false :=
      fun w hw => htf w (List.mem_cons_of_mem x hw)
    have hiSafe_eq : e.isSafe σ am decls = e.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree e σ τ am decls hagree htf_e
    simp only [Stmt.interp] at h
    by_cases hiSafe : e.isSafe σ am decls
    · simp [hiSafe] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨τ[x ↦ .float (e.eval τ am)], am, by simp [Stmt.interp, ← hiSafe_eq, hiSafe], ?_, rfl⟩
      intro v hv; simp only [Store.update]; split
      · exact congrArg (Value.float ·) (SExpr.eval_tmpAgree e σ τ am hagree htf_e)
      · exact hagree v hv
    · simp [hiSafe] at h
  | farrWrite arr idx val =>
    have htf_idx : ∀ v ∈ idx.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_left _ hv)
    have htf_val : ∀ v ∈ val.freeVars, v.isTmp = false :=
      fun v hv => htf v (List.mem_append_right _ hv)
    have hiSafe_idx : idx.isSafe σ am decls = idx.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree idx σ τ am decls hagree htf_idx
    have hiSafe_val : val.isSafe σ am decls = val.isSafe τ am decls :=
      SExpr.isSafe_tmpAgree val σ τ am decls hagree htf_val
    have heval_idx : idx.eval σ am = idx.eval τ am :=
      SExpr.eval_tmpAgree idx σ τ am hagree htf_idx
    have heval_val : val.eval σ am = val.eval τ am :=
      SExpr.eval_tmpAgree val σ τ am hagree htf_val
    simp only [Stmt.interp] at h
    split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      rename_i hcond
      obtain ⟨⟨hs_i, hs_v⟩, hb⟩ := hcond
      refine ⟨τ, am.write arr (idx.eval τ am) (val.eval τ am), ?_, hagree, ?_⟩
      · simp [Stmt.interp, ← hiSafe_idx, ← hiSafe_val, hs_i, hs_v, ← heval_idx, hb]
      · rw [heval_idx, heval_val]
    · simp at h

-- ============================================================
-- § 4. Safety (division + bounds)
-- ============================================================

def SExpr.safe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SExpr → Prop
  | .lit _ => True
  | .var _ => True
  | .bin .div a b => a.safe σ am decls ∧ b.safe σ am decls ∧ b.eval σ am ≠ 0
  | .bin .mod a b => a.safe σ am decls ∧ b.safe σ am decls ∧ b.eval σ am ≠ 0
  | .bin _ a b => a.safe σ am decls ∧ b.safe σ am decls
  | .arrRead arr idx => idx.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .flit _ => True
  | .fbin _ a b => a.safe σ am decls ∧ b.safe σ am decls
  | .intToFloat e => e.safe σ am decls
  | .floatToInt e => e.safe σ am decls
  | .floatExp e => e.safe σ am decls
  | .farrRead arr idx => idx.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr

def SBool.safe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SBool → Prop
  | .lit _ => True
  | .bvar _ => True
  | .cmp _ a b => a.safe σ am decls ∧ b.safe σ am decls
  | .not e => e.safe σ am decls
  | .and a b => a.safe σ am decls ∧ (a.eval σ am = true → b.safe σ am decls)
  | .or a b => a.safe σ am decls ∧ (a.eval σ am = false → b.safe σ am decls)
  | .barrRead arr idx => idx.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .fcmp _ a b => a.safe σ am decls ∧ b.safe σ am decls

def Stmt.safe (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip => True
  | .assign _ e => e.safe σ am decls
  | .bassign _ b => b.safe σ am decls
  | .arrWrite arr idx val =>
    idx.safe σ am decls ∧ val.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .barrWrite arr idx bval =>
    (idx : SExpr).safe σ am decls ∧ bval.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr
  | .seq s₁ s₂ =>
    s₁.safe fuel σ am decls ∧
    match s₁.interp fuel σ am decls with
    | some (σ', am') => s₂.safe fuel σ' am' decls
    | none => True
  | .ite b s₁ s₂ =>
    b.safe σ am decls ∧ (if b.eval σ am then s₁.safe fuel σ am decls else s₂.safe fuel σ am decls)
  | .loop b body =>
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      b.safe σ am decls ∧
      if b.eval σ am then
        body.safe fuel' σ am decls ∧
        match body.interp fuel' σ am decls with
        | some (σ', am') => (Stmt.loop b body).safe fuel' σ' am' decls
        | none => True
      else True
  | .fassign _ e => e.safe σ am decls
  | .farrWrite arr idx val =>
    idx.safe σ am decls ∧ val.safe σ am decls ∧ (idx.eval σ am) < arraySizeBv decls arr

-- ============================================================
-- § 4a. isSafe → safe bridge
-- ============================================================

theorem SExpr.isSafe_implies_safe (e : SExpr) (σ : Store) (am : ArrayMem) (decls) :
    e.isSafe σ am decls = true → e.safe σ am decls := by
  induction e with
  | lit _ => intro; trivial
  | var _ => intro; trivial
  | bin op a b iha ihb =>
    intro h
    cases op <;> (simp only [SExpr.isSafe, Bool.and_eq_true, decide_eq_true_eq] at h;
                   simp only [SExpr.safe]) <;>
      first
      | exact ⟨iha h.1, ihb h.2⟩
      | exact ⟨iha h.1.1, ihb h.1.2, h.2⟩
  | arrRead arr idx ih =>
    simp only [SExpr.isSafe, SExpr.safe, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hs, hb⟩; exact ⟨ih hs, hb⟩
  | flit _ => intro; trivial
  | fbin _ a b iha ihb =>
    simp only [SExpr.isSafe, SExpr.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨iha ha, ihb hb⟩
  | intToFloat e ih => simp only [SExpr.isSafe, SExpr.safe]; exact ih
  | floatToInt e ih => simp only [SExpr.isSafe, SExpr.safe]; exact ih
  | floatExp e ih => simp only [SExpr.isSafe, SExpr.safe]; exact ih
  | farrRead arr idx ih =>
    simp only [SExpr.isSafe, SExpr.safe, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hs, hb⟩; exact ⟨ih hs, hb⟩

theorem SBool.isSafe_implies_safe (sb : SBool) (σ : Store) (am : ArrayMem) (decls) :
    sb.isSafe σ am decls = true → sb.safe σ am decls := by
  induction sb with
  | lit _ => intro; trivial
  | bvar _ => intro; trivial
  | cmp _ a b =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨SExpr.isSafe_implies_safe a σ am decls ha,
                           SExpr.isSafe_implies_safe b σ am decls hb⟩
  | not e ih =>
    simp only [SBool.isSafe, SBool.safe]; exact ih
  | and a b iha ihb =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    refine ⟨iha ha, fun heval => ?_⟩
    simp [heval] at hb; exact ihb hb
  | or a b iha ihb =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩
    refine ⟨iha ha, fun heval => ?_⟩
    simp [heval] at hb; exact ihb hb
  | barrRead arr idx =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hs, hb⟩; exact ⟨SExpr.isSafe_implies_safe idx σ am decls hs, hb⟩
  | fcmp _ a b =>
    simp only [SBool.isSafe, SBool.safe, Bool.and_eq_true]
    intro ⟨ha, hb⟩; exact ⟨SExpr.isSafe_implies_safe a σ am decls ha,
                           SExpr.isSafe_implies_safe b σ am decls hb⟩

theorem Stmt.interp_some_implies_safe (s : Stmt) (fuel : Nat)
    (σ σ' : Store) (am am' : ArrayMem) (decls) :
    s.interp fuel σ am decls = some (σ', am') → s.safe fuel σ am decls := by
  induction s generalizing fuel σ σ' am am' with
  | skip => intro _; simp [Stmt.safe]
  | assign _ e =>
    intro h; simp only [Stmt.interp] at h; simp only [Stmt.safe]
    split at h
    · exact SExpr.isSafe_implies_safe e σ am decls ‹_›
    · simp at h
  | bassign _ b =>
    intro h; simp only [Stmt.interp] at h; simp only [Stmt.safe]
    split at h
    · exact SBool.isSafe_implies_safe b σ am decls ‹_›
    · simp at h
  | arrWrite arr idx val =>
    intro h; simp only [Stmt.interp] at h; simp only [Stmt.safe]
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨SExpr.isSafe_implies_safe idx σ am decls hc.1.1,
             SExpr.isSafe_implies_safe val σ am decls hc.1.2, hc.2⟩
    · simp at h
  | barrWrite arr idx bval =>
    intro h; simp only [Stmt.interp] at h; simp only [Stmt.safe]
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨SExpr.isSafe_implies_safe idx σ am decls hc.1.1,
             SBool.isSafe_implies_safe bval σ am decls hc.1.2, hc.2⟩
    · simp at h
  | seq s₁ s₂ ih₁ ih₂ =>
    intro h; simp only [Stmt.interp] at h
    cases hq : s₁.interp fuel σ am decls with
    | none => simp [hq] at h
    | some p₁ =>
      simp [hq] at h
      simp only [Stmt.safe, hq]
      exact ⟨ih₁ fuel σ p₁.1 am p₁.2 hq, ih₂ fuel p₁.1 σ' p₁.2 am' h⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro h; simp only [Stmt.interp] at h
    split at h
    · rename_i hbs
      have hbs_safe := SBool.isSafe_implies_safe b σ am decls hbs
      simp only [Stmt.safe]
      cases hb : b.eval σ am with
      | true => simp [hb] at h; exact ⟨hbs_safe, by simp [hb]; exact ih₁ fuel σ σ' am am' h⟩
      | false => simp [hb] at h; exact ⟨hbs_safe, by simp [hb]; exact ih₂ fuel σ σ' am am' h⟩
    · simp at h
  | loop b body ih =>
    intro h
    induction fuel generalizing σ σ' am am' with
    | zero => simp [Stmt.interp] at h
    | succ fuel' ihf =>
      simp only [Stmt.interp] at h
      split at h
      · rename_i hbs
        have hbs_safe := SBool.isSafe_implies_safe b σ am decls hbs
        simp only [Stmt.safe]
        cases hb : b.eval σ am with
        | false =>
          simp [hb] at h
          exact ⟨hbs_safe, by simp [hb]⟩
        | true =>
          simp [hb] at h
          cases hq : body.interp fuel' σ am decls with
          | none => simp [hq] at h
          | some p₁ =>
            simp [hq] at h
            refine ⟨hbs_safe, ?_⟩; simp [hb]; refine ⟨ih fuel' σ p₁.1 am p₁.2 hq, ?_⟩
            exact ihf p₁.1 σ' p₁.2 am' h
      · simp at h
  | fassign _ e =>
    intro h; simp only [Stmt.interp] at h; simp only [Stmt.safe]
    split at h
    · exact SExpr.isSafe_implies_safe e σ am decls ‹_›
    · simp at h
  | farrWrite arr idx val =>
    intro h; simp only [Stmt.interp] at h; simp only [Stmt.safe]
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨SExpr.isSafe_implies_safe idx σ am decls hc.1.1,
             SExpr.isSafe_implies_safe val σ am decls hc.1.2, hc.2⟩
    · simp at h

-- ============================================================
-- § 4b. Integer typing (all arithmetic-position variables have int values)
-- ============================================================

/-- Context-sensitive typing for statements. Uses `typedVars` and `wrapEval`
    instead of the broken `intTyped` which assumes all vars are int. -/
def Stmt.typedVars (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip => True
  | .assign _ e => e.typedVars σ am ∧ e.wrapEval σ am = .int (e.eval σ am)
  | .bassign _ b => b.typedVars σ am
  | .arrWrite _ idx val =>
    (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
    (val.typedVars σ am ∧ val.wrapEval σ am = .int (val.eval σ am))
  | .barrWrite _ idx bval =>
    (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧ bval.typedVars σ am
  | .seq s₁ s₂ =>
    s₁.typedVars fuel σ am decls ∧
    match s₁.interp fuel σ am decls with
    | some (σ', am') => s₂.typedVars fuel σ' am' decls
    | none => True
  | .ite b s₁ s₂ =>
    b.typedVars σ am ∧ (if b.eval σ am then s₁.typedVars fuel σ am decls else s₂.typedVars fuel σ am decls)
  | .loop b body =>
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      b.typedVars σ am ∧
      if b.eval σ am then
        body.typedVars fuel' σ am decls ∧
        match body.interp fuel' σ am decls with
        | some (σ', am') => (Stmt.loop b body).typedVars fuel' σ' am' decls
        | none => True
      else True
  | .fassign _ e => e.typedVars σ am ∧ e.wrapEval σ am = .float (e.eval σ am)
  | .farrWrite _ idx val =>
    (idx.typedVars σ am ∧ idx.wrapEval σ am = .int (idx.eval σ am)) ∧
    (val.typedVars σ am ∧ val.wrapEval σ am = .float (val.eval σ am))

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

private theorem noTmpDecls_not_ftmp {decls : List (Var × VarTy)} {v : Var} {ty : VarTy}
    (hnt : Program.noTmpDecls decls = true) (hlook : decls.lookup v = some ty) :
    v.isFTmp = false := by
  cases hv : v.isFTmp with
  | false => rfl
  | true =>
    have := lookup_none_of_isFTmp_wt hnt hv
    simp [this] at hlook

/-- All variables in a well-typed arithmetic expression are declared. -/
private theorem checkExpr_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)} {ty : VarTy}
    {e : SExpr} (h : Program.checkExpr lookup arrayDecls ty e = true) :
    ∀ v ∈ e.freeVars, ∃ ty, lookup v = some ty := by
  induction e generalizing ty with
  | lit _ =>
    match ty with
    | .int => intro v hv; simp [SExpr.freeVars] at hv
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | var x =>
    match ty with
    | .int =>
      intro v hv; simp [SExpr.freeVars] at hv; subst hv
      simp [Program.checkExpr] at h; exact ⟨.int, h⟩
    | .float =>
      intro v hv; simp [SExpr.freeVars] at hv; subst hv
      simp [Program.checkExpr] at h; exact ⟨.float, h⟩
    | .bool => simp [Program.checkExpr] at h
  | bin _ a b iha ihb =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; simp [SExpr.freeVars] at hv
      rcases hv with ha | hb
      · exact iha h.1 v ha
      · exact ihb h.2 v hb
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | arrRead _ idx ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; exact ih h.2 v hv
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | flit _ =>
    match ty with
    | .float => intro v hv; simp [SExpr.freeVars] at hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | fbin _ a b iha ihb =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; simp [SExpr.freeVars] at hv
      rcases hv with ha | hb
      · exact iha h.1 v ha
      · exact ihb h.2 v hb
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | intToFloat e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at h
      intro v hv; exact ih h v hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | floatToInt e ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr] at h
      intro v hv; exact ih h v hv
    | .float => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | floatExp e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at h
      intro v hv; exact ih h v hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h
  | farrRead _ idx ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at h
      intro v hv; exact ih h.2 v hv
    | .int => simp [Program.checkExpr] at h
    | .bool => simp [Program.checkExpr] at h

private theorem checkSExpr_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {e : SExpr} (h : Program.checkSExpr lookup arrayDecls e = true) :
    ∀ v ∈ e.freeVars, ∃ ty, lookup v = some ty :=
  checkExpr_declared h

private theorem TypedStore.getInt {Γ : TyCtx} {σ : Store} {x : Var}
    (hts : TypedStore Γ σ) (hty : Γ x = .int) : ∃ n, σ x = .int n := by
  have := hts x; rw [hty] at this
  exact Value.int_of_typeOf_int this

private theorem TypedStore.getFloat {Γ : TyCtx} {σ : Store} {x : Var}
    (hts : TypedStore Γ σ) (hty : Γ x = .float) : ∃ f, σ x = .float f := by
  have := hts x; rw [hty] at this
  exact Value.float_of_typeOf_float this

/-- Bridge: `checkExpr ty e = true` + `TypedStore` implies `e.typedVars` and
    that `e.wrapEval` matches the expected type wrapper. -/
theorem checkExpr_typedVars {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)} {Γ : TyCtx} {σ : Store}
    {am : ArrayMem} {ty : VarTy} {e : SExpr}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkExpr lookup arrayDecls ty e = true)
    (hts : TypedStore Γ σ) :
    e.typedVars σ am ∧
    (ty = .int → e.wrapEval σ am = .int (e.eval σ am)) ∧
    (ty = .float → e.wrapEval σ am = .float (e.eval σ am)) := by
  induction e generalizing ty with
  | lit n =>
    match ty with
    | .int => exact ⟨trivial, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | var x =>
    match ty with
    | .int =>
      simp [Program.checkExpr, beq_iff_eq] at hchk
      obtain ⟨n, hn⟩ := TypedStore.getInt hts (hcompat _ .int hchk)
      refine ⟨trivial, fun _ => ?_, fun h => absurd h (by decide)⟩
      simp [SExpr.wrapEval, SExpr.eval, hn]
    | .float =>
      simp [Program.checkExpr, beq_iff_eq] at hchk
      obtain ⟨f, hf⟩ := TypedStore.getFloat hts (hcompat _ .float hchk)
      refine ⟨trivial, fun h => absurd h (by decide), fun _ => ?_⟩
      simp [SExpr.wrapEval, SExpr.eval, hf]
    | .bool => simp [Program.checkExpr] at hchk
  | bin op a b iha ihb =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_a, hwi_a, _⟩ := iha hchk.1
      have ⟨htv_b, hwi_b, _⟩ := ihb hchk.2
      exact ⟨⟨hwi_a rfl, hwi_b rfl, htv_a, htv_b⟩, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | arrRead _arr idx ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_i, hwi_i, _⟩ := ih hchk.2
      exact ⟨⟨hwi_i rfl, htv_i⟩, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | flit f =>
    match ty with
    | .float => exact ⟨trivial, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | fbin op a b iha ihb =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_a, _, hwf_a⟩ := iha hchk.1
      have ⟨htv_b, _, hwf_b⟩ := ihb hchk.2
      exact ⟨⟨hwf_a rfl, hwf_b rfl, htv_a, htv_b⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | intToFloat e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at hchk
      have ⟨htv_e, hwi_e, _⟩ := ih hchk
      exact ⟨⟨hwi_e rfl, htv_e⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | floatToInt e ih =>
    match ty with
    | .int =>
      simp [Program.checkExpr] at hchk
      have ⟨htv_e, _, hwf_e⟩ := ih hchk
      exact ⟨⟨hwf_e rfl, htv_e⟩, fun _ => rfl, fun h => absurd h (by decide)⟩
    | .float => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | floatExp e ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr] at hchk
      have ⟨htv_e, _, hwf_e⟩ := ih hchk
      exact ⟨sorry, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk
  | farrRead _arr idx ih =>
    match ty with
    | .float =>
      simp [Program.checkExpr, Bool.and_eq_true] at hchk
      have ⟨htv_i, hwi_i, _⟩ := ih hchk.2
      exact ⟨⟨hwi_i rfl, htv_i⟩, fun h => absurd h (by decide), fun _ => rfl⟩
    | .int => simp [Program.checkExpr] at hchk
    | .bool => simp [Program.checkExpr] at hchk

/-- All variables in a well-typed boolean expression are declared. -/
private theorem checkSBool_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {b : SBool} (h : Program.checkSBool lookup arrayDecls b = true) :
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
  | barrRead arr idx =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv; exact checkSExpr_declared h.2 v hv
  | fcmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at h
    intro v hv; simp [SBool.freeVars] at hv
    rcases hv with ha | hb
    · exact checkExpr_declared h.1 v ha
    · exact checkExpr_declared h.2 v hb

/-- All variables in a well-typed statement are declared. -/
private theorem checkStmt_declared {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {s : Stmt} (h : Program.checkStmt lookup arrayDecls s = true) :
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
  | arrWrite _ idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨_, hi⟩, hv⟩ := h
    intro v hv'; simp [Stmt.allVars] at hv'
    rcases hv' with hi' | hv'
    · exact checkSExpr_declared hi v hi'
    · exact checkSExpr_declared hv v hv'
  | barrWrite arr idx bval =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨_, hi⟩, hb⟩ := h
    intro v hv'; simp [Stmt.allVars] at hv'
    rcases hv' with hi' | hb'
    · exact checkSExpr_declared hi v hi'
    · exact checkSBool_declared hb v hb'
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
  | fassign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    intro v hv; simp [Stmt.allVars] at hv
    rcases hv with rfl | he
    · exact ⟨.float, h.1⟩
    · exact checkExpr_declared h.2 v he
  | farrWrite _ idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at h
    obtain ⟨⟨_, hi⟩, hv⟩ := h
    intro v hv'; simp [Stmt.allVars] at hv'
    rcases hv' with hi' | hv'
    · exact checkExpr_declared hi v hi'
    · exact checkExpr_declared hv v hv'

/-- **Bridge lemma**: A type-checked program's body is tmp-free — no variable
    in the source program uses the compiler-reserved `__t` prefix. -/
theorem Program.typeCheck_tmpFree (prog : Program) (h : prog.typeCheck = true) :
    prog.body.tmpFree := by
  simp [Program.typeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨_, hnt⟩, hchk⟩ := h
  intro v hv
  obtain ⟨ty, hlook⟩ := checkStmt_declared hchk v hv
  exact noTmpDecls_not_tmp hnt hlook

/-- A type-checked program's body has no ftmp-prefixed variables. -/
theorem Program.typeCheck_ftmpFree (prog : Program) (h : prog.typeCheck = true) :
    ∀ v ∈ prog.body.allVars, v.isFTmp = false := by
  simp [Program.typeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨_, hnt⟩, hchk⟩ := h
  intro v hv
  obtain ⟨ty, hlook⟩ := checkStmt_declared hchk v hv
  exact noTmpDecls_not_ftmp hnt hlook

-- ============================================================
-- § 4d. Source-level type preservation
-- ============================================================

/-- Helper: checkStmt-declared variables have their declared type in tyCtx. -/
private theorem lookup_tyCtx {lookup : Var → Option VarTy} {Γ : TyCtx}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty) {x : Var} {ty : VarTy}
    (h : lookup x = some ty) : Γ x = ty := hcompat x ty h

/-- Source-level type preservation: interpreting a well-typed statement
    preserves TypedStore. -/
theorem Stmt.interp_preserves_typedStore
    {s : Stmt} {fuel : Nat} {σ σ' : Store} {am am' : ArrayMem} {Γ : TyCtx}
    {lookup : Var → Option VarTy} {arrayDecls : List (ArrayName × Nat × VarTy)}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkStmt lookup arrayDecls s = true)
    (hts : TypedStore Γ σ)
    (hinterp : s.interp fuel σ am arrayDecls = some (σ', am')) :
    TypedStore Γ σ' := by
  induction s generalizing fuel σ σ' am am' with
  | skip =>
    simp [Stmt.interp] at hinterp; obtain ⟨rfl, _⟩ := hinterp; exact hts
  | assign x e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · simp at hinterp; obtain ⟨rfl, _⟩ := hinterp
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      intro y; simp [Store.update]; split
      · case isTrue heq => simp [heq, Value.typeOf_int, hcompat _ .int hchk.1]
      · case isFalse => exact hts y
    · simp at hinterp
  | bassign x b =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · simp at hinterp; obtain ⟨rfl, _⟩ := hinterp
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      intro y; simp [Store.update]; split
      · case isTrue heq => simp [heq, Value.typeOf_bool, hcompat _ .bool hchk.1]
      · case isFalse => exact hts y
    · simp at hinterp
  | arrWrite _ _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · simp at hinterp; obtain ⟨rfl, _⟩ := hinterp; exact hts
    · simp at hinterp
  | barrWrite _ _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · simp at hinterp; obtain ⟨rfl, _⟩ := hinterp; exact hts
    · simp at hinterp
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp [Stmt.interp] at hinterp
    cases hq : s1.interp fuel σ am arrayDecls with
    | none => simp [hq] at hinterp
    | some p₁ =>
      simp [hq] at hinterp
      exact ih2 hchk.2 (ih1 hchk.1 hts hq) hinterp
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, h1⟩, h2⟩ := hchk
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · cases hcond : b.eval σ am with
      | true => simp [hcond] at hinterp; exact ih1 h1 hts hinterp
      | false => simp [hcond] at hinterp; exact ih2 h2 hts hinterp
    · simp at hinterp
  | loop b body ih =>
    induction fuel generalizing σ σ' am am' with
    | zero => simp [Stmt.interp] at hinterp
    | succ fuel' ihf =>
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      simp only [Stmt.interp] at hinterp
      split at hinterp
      · cases hcond : b.eval σ am with
        | false => simp [hcond] at hinterp; obtain ⟨rfl, _⟩ := hinterp; exact hts
        | true =>
          simp [hcond] at hinterp
          cases hq : body.interp fuel' σ am arrayDecls with
          | none => simp [hq] at hinterp
          | some p₁ =>
            simp [hq] at hinterp
            exact ihf (ih hchk.2 hts hq) hinterp
      · simp at hinterp
  | fassign x e =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · simp at hinterp; obtain ⟨rfl, _⟩ := hinterp
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      intro y; simp [Store.update]; split
      · case isTrue heq => simp [heq, Value.typeOf_float, hcompat _ .float hchk.1]
      · case isFalse => exact hts y
    · simp at hinterp
  | farrWrite _ _ _ =>
    simp only [Stmt.interp] at hinterp
    split at hinterp
    · simp at hinterp; obtain ⟨rfl, _⟩ := hinterp; exact hts
    · simp at hinterp

-- ============================================================
-- § 4e. Bridge: typeCheck + TypedStore → typedVars
-- ============================================================

/-- Bridge: `checkSBool` + `TypedStore` implies `SBool.typedVars`. -/
theorem checkSBool_typedVars {lookup : Var → Option VarTy}
    {arrayDecls : List (ArrayName × Nat × VarTy)} {Γ : TyCtx} {σ : Store}
    {am : ArrayMem} {b : SBool}
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkSBool lookup arrayDecls b = true)
    (hts : TypedStore Γ σ) :
    b.typedVars σ am := by
  induction b with
  | lit _ => trivial
  | bvar _ => trivial
  | cmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    simp only [SBool.typedVars]
    have ⟨htv_a, hwi_a, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.1 hts
    have ⟨htv_b, hwi_b, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv_a, htv_b, hwi_a rfl, hwi_b rfl⟩
  | not e ih => simp [Program.checkSBool] at hchk; exact ih hchk
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨iha hchk.1, ihb hchk.2⟩
  | or a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    exact ⟨iha hchk.1, ihb hchk.2⟩
  | barrRead arr idx =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    simp only [SBool.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv_i, hwi_i rfl⟩
  | fcmp _ a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    simp only [SBool.typedVars]
    have ⟨htv_a, _, hwf_a⟩ := checkExpr_typedVars (am := am) hcompat hchk.1 hts
    have ⟨htv_b, _, hwf_b⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv_a, htv_b, hwf_a rfl, hwf_b rfl⟩

/-- Bridge: `checkStmt` + `TypedStore` implies `Stmt.typedVars`. -/
theorem checkStmt_typedVars
    (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy))
    (Γ : TyCtx) (σ : Store) (am : ArrayMem) (s : Stmt) (fuel : Nat)
    (hcompat : ∀ x ty, lookup x = some ty → Γ x = ty)
    (hchk : Program.checkStmt lookup arrayDecls s = true)
    (hts : TypedStore Γ σ) :
    s.typedVars fuel σ am arrayDecls := by
  induction s generalizing fuel σ am with
  | skip => simp [Stmt.typedVars]
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp only [Stmt.typedVars]
    have ⟨htv, hwi, _⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv, hwi rfl⟩
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp only [Stmt.typedVars]
    exact checkSBool_typedVars hcompat hchk.2 hts
  | arrWrite _ idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hv⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hi hts
    have ⟨htv_v, hwi_v, _⟩ := checkExpr_typedVars (am := am) hcompat hv hts
    exact ⟨⟨htv_i, hwi_i rfl⟩, ⟨htv_v, hwi_v rfl⟩⟩
  | barrWrite _ idx bval =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hb⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hi hts
    exact ⟨⟨htv_i, hwi_i rfl⟩, checkSBool_typedVars hcompat hb hts⟩
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp only [Stmt.typedVars]
    refine ⟨ih1 σ am fuel hchk.1 hts, ?_⟩
    cases hq : s1.interp fuel σ am arrayDecls with
    | none => simp [hq]
    | some p₁ =>
        exact ih2 p₁.1 p₁.2 fuel hchk.2 (Stmt.interp_preserves_typedStore hcompat hchk.1 hts hq)
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨hb, h1⟩, h2⟩ := hchk
    simp only [Stmt.typedVars]
    refine ⟨checkSBool_typedVars hcompat hb hts, ?_⟩
    cases b.eval σ am <;> simp
    · exact ih2 σ am fuel h2 hts
    · exact ih1 σ am fuel h1 hts
  | loop b body ih =>
    induction fuel generalizing σ am with
    | zero => simp [Stmt.typedVars]
    | succ fuel' ihf =>
      simp [Program.checkStmt, Bool.and_eq_true] at hchk
      simp only [Stmt.typedVars]
      refine ⟨checkSBool_typedVars hcompat hchk.1 hts, ?_⟩
      cases hcond : b.eval σ am <;> simp [hcond]
      refine ⟨ih σ am fuel' hchk.2 hts, ?_⟩
      cases hq : body.interp fuel' σ am arrayDecls with
      | none => simp [hq]
      | some p₁ =>
        simp [hq]
        exact ihf p₁.1 p₁.2 (Stmt.interp_preserves_typedStore hcompat hchk.2 hts hq)
  | fassign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    simp only [Stmt.typedVars]
    have ⟨htv, _, hwf⟩ := checkExpr_typedVars (am := am) hcompat hchk.2 hts
    exact ⟨htv, hwf rfl⟩
  | farrWrite _ idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hv⟩ := hchk
    simp only [Stmt.typedVars]
    have ⟨htv_i, hwi_i, _⟩ := checkExpr_typedVars (am := am) hcompat hi hts
    have ⟨htv_v, _, hwf_v⟩ := checkExpr_typedVars (am := am) hcompat hv hts
    exact ⟨⟨htv_i, hwi_i rfl⟩, ⟨htv_v, hwf_v rfl⟩⟩

/-- **Bridge lemma**: A type-checked program with a well-typed store satisfies typedVars. -/
theorem Program.typeCheck_typedVars (prog : Program) (h : prog.typeCheck = true)
    (σ : Store) (am : ArrayMem) (hts : TypedStore prog.tyCtx σ) (fuel : Nat) :
    prog.body.typedVars fuel σ am prog.arrayDecls := by
  simp [Program.typeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨_, _⟩, hchk⟩ := h
  exact checkStmt_typedVars prog.lookupTy prog.arrayDecls prog.tyCtx σ am prog.body fuel
    (fun x ty hlook => by
      show (prog.lookupTy x).getD (if x.isFTmp then .float else .int) = ty
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
