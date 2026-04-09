import CredibleCompilation.RefCompiler.ErrorHandling

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

-- Helper: Prop-level safe implies Bool-level isSafe
theorem SExpr.isSafe_of_safe (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : e.safe σ am decls) : e.isSafe σ am decls = true := by
  induction e with
  | lit _ => simp [SExpr.isSafe]
  | var _ => simp [SExpr.isSafe]
  | bin op a b iha ihb =>
    cases op <;> simp_all [SExpr.safe, SExpr.isSafe, decide_eq_true_eq]
  | arrRead arr idx ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h.1, decide_eq_true_eq, h.2]
  | flit _ | fbin _ _ _ _ _ | intToFloat _ _ | floatToInt _ _ | farrRead _ _ _ => sorry

theorem SBool.isSafe_of_safe (sb : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : sb.safe σ am decls) : sb.isSafe σ am decls = true := by
  induction sb with
  | lit _ => simp [SBool.isSafe]
  | bvar _ => simp [SBool.isSafe]
  | cmp _ a b =>
    simp [SBool.safe] at h; simp [SBool.isSafe, SExpr.isSafe_of_safe a σ am decls h.1, SExpr.isSafe_of_safe b σ am decls h.2]
  | not e ih =>
    simp [SBool.safe] at h; simp [SBool.isSafe, ih h]
  | and a b iha ihb =>
    simp [SBool.safe] at h
    simp only [SBool.isSafe, iha h.1, Bool.true_and]
    split <;> simp_all
  | or a b iha ihb =>
    simp [SBool.safe] at h
    simp only [SBool.isSafe, iha h.1, Bool.true_and]
    split <;> simp_all
  | barrRead arr idx =>
    simp [SBool.safe] at h
    have hih := SExpr.isSafe_of_safe idx σ am decls h.1
    simp [SBool.isSafe, hih, decide_eq_true_eq, h.2]
  | fcmp _ _ _ => sorry

private theorem Stmt.interp_ne_none_of_safe_assign (x : Var) (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.assign x e).safe 0 σ am decls) :
    (Stmt.assign x e).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe e σ am decls hsafe]

private theorem Stmt.interp_ne_none_of_safe_bassign (x : Var) (b : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.bassign x b).safe 0 σ am decls) :
    (Stmt.bassign x b).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SBool.isSafe_of_safe b σ am decls hsafe]

private theorem Stmt.interp_ne_none_of_safe_arrWrite (arr : ArrayName) (idx val : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.arrWrite arr idx val).safe 0 σ am decls) :
    (Stmt.arrWrite arr idx val).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe idx σ am decls hsafe.1,
        SExpr.isSafe_of_safe val σ am decls hsafe.2.1, decide_eq_true_eq, hsafe.2.2]

private theorem Stmt.interp_ne_none_of_safe_barrWrite (arr : ArrayName) (idx : SExpr) (bval : SBool) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.barrWrite arr idx bval).safe 0 σ am decls) :
    (Stmt.barrWrite arr idx bval).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe idx σ am decls hsafe.1,
        SBool.isSafe_of_safe bval σ am decls hsafe.2.1, decide_eq_true_eq, hsafe.2.2]

/-!
# Reference Compiler: Metatheory

Step-indexed execution (RefStepsN), fuel monotonicity,
safe/typedVars anti-monotonicity, and divergence theorems.
-/

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
  | refl => exact Steps.refl
  | step s _ ih => exact Steps.step s ih
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
  induction h₁ with
  | refl => simpa using h₂
  | step s _ ih => exact refStepsN_cast (.step s (ih h₂)) (by omega)
theorem RefStepsN.det_prefix {p : Prog} {n m : Nat} {c c₁ c₂ : Cfg}
    (h₁ : RefStepsN p n c c₁) (h₂ : RefStepsN p m c c₂) (hle : n ≤ m) :
    RefStepsN p (m - n) c₁ c₂ := by
  induction h₁ generalizing m c₂ with
  | refl => simpa using h₂
  | step s _ ih =>
    cases h₂ with
    | refl => omega
    | step s' rest =>
      have := Step.deterministic s s'; subst this
      exact refStepsN_cast (ih rest (by omega)) (by omega)
/-- A halted config cannot take a step in RefStepsN. -/
theorem RefStepsN.no_step_halt {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.halt σ _xam) c) : False := by
  cases h with
  | step s _ => exact Step.no_step_from_halt s
/-- If execution takes unbounded steps through `run` configs, it cannot halt. -/
theorem no_halt_of_unbounded {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ am) (Cfg.run pc' σ' am)) :
    ∀ σ' am', ¬ haltsWithResult p pc σ σ' am am' := by
  intro σ' am' hhalt
  obtain ⟨n, hn⟩ := hhalt.to_RefStepsN
  obtain ⟨m, hm, pc', σ'', hrun⟩ := hunbounded (n + 1)
  have hsuffix := RefStepsN.det_prefix hn hrun (by omega : n ≤ m)
  exact RefStepsN.no_step_halt (refStepsN_cast hsuffix (by omega : m - n = (m - n - 1) + 1))
/-- Variant of `no_halt_of_unbounded` where the array memory can change at each step. -/
theorem no_halt_of_unbounded_am {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
      RefStepsN p n (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∀ σ' am', ¬ haltsWithResult p pc σ σ' am am' := by
  intro σ' am' hhalt
  obtain ⟨n, hn⟩ := hhalt.to_RefStepsN
  obtain ⟨m, hm, pc', σ'', am'', hrun⟩ := hunbounded (n + 1)
  have hsuffix := RefStepsN.det_prefix hn hrun (by omega : n ≤ m)
  exact RefStepsN.no_step_halt (refStepsN_cast hsuffix (by omega : m - n = (m - n - 1) + 1))
-- ============================================================
-- § 18. Fuel monotonicity
-- ============================================================

/-- If the interpreter terminates at some fuel, it terminates with the same
    result at one more fuel. -/
theorem Stmt.interp_fuel_succ (s : Stmt) :
    ∀ fuel σ am decls r, s.interp fuel σ am decls = some r → s.interp (fuel + 1) σ am decls = some r := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ =>
    intro _ _ _ _ _ h; simp_all [Stmt.interp]
  | barrWrite arr idx bval =>
    intro _ _ _ _ _ h; simp_all [Stmt.interp]
  | fassign _ _ => sorry
  | farrWrite _ _ _ => sorry
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am decls r h
    simp only [Stmt.interp.eq_6] at h ⊢
    cases h₁ : s₁.interp fuel σ am decls with
    | none => simp [h₁] at h
    | some val =>
      obtain ⟨σ₁, am₁⟩ := val
      simp [h₁] at h
      simp [ih₁ fuel σ am decls ⟨σ₁, am₁⟩ h₁]
      exact ih₂ fuel σ₁ am₁ decls r h
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am decls r h
    simp only [Stmt.interp.eq_7] at h ⊢
    split at h <;> [skip; simp at h]
    rename_i hisSafe
    rw [if_pos hisSafe]
    split at h
    · rename_i hb; rw [if_pos hb]; exact ih₁ fuel σ am decls r h
    · rename_i hb; rw [if_neg hb]; exact ih₂ fuel σ am decls r h
  | loop b body ih_body =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls r h; simp [Stmt.interp.eq_8] at h
    | succ fuel' ih_fuel =>
      intro σ am decls r h
      rw [Stmt.interp.eq_9] at h; rw [Stmt.interp.eq_9]
      split at h <;> [skip; simp at h]
      rename_i hisSafe
      rw [if_pos hisSafe]
      by_cases hb : b.eval σ am = true
      · rw [if_pos hb] at h ⊢
        simp only [bind, Option.bind] at h ⊢
        cases hbody : body.interp fuel' σ am decls with
        | none => simp [hbody] at h
        | some val =>
          obtain ⟨σ₁, am₁⟩ := val
          simp only [hbody, Option.bind_some] at h
          simp only [ih_body fuel' σ am decls ⟨σ₁, am₁⟩ hbody, Option.bind_some]
          exact ih_fuel σ₁ am₁ decls r h
      · rw [if_neg hb] at h ⊢; exact h
/-- Fuel monotonicity: success at `fuel` implies success at `fuel + k`. -/
theorem Stmt.interp_fuel_mono (s : Stmt) (fuel k : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) (r : Store × ArrayMem)
    (h : s.interp fuel σ am decls = some r) : s.interp (fuel + k) σ am decls = some r := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [show fuel + (k + 1) = (fuel + k) + 1 from by omega]; exact s.interp_fuel_succ _ _ _ _ _ ih
/-- Contrapositive of fuel monotonicity: `none` at higher fuel implies `none`
    at lower fuel. -/
theorem Stmt.interp_none_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : s.interp fuel' σ am decls = none) (hle : fuel ≤ fuel') : s.interp fuel σ am decls = none := by
  by_contra hc; push_neg at hc
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hc
  have := s.interp_fuel_mono fuel (fuel' - fuel) σ am decls r hr
  rw [show fuel + (fuel' - fuel) = fuel' from by omega] at this
  simp [this] at h
-- ============================================================
-- § 19. safe anti-monotonicity
-- ============================================================

/-- `safe` at higher fuel implies `safe` at lower fuel. -/
theorem Stmt.safe_fuel_succ (s : Stmt) :
    ∀ fuel σ am decls, s.safe (fuel + 1) σ am decls → s.safe fuel σ am decls := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ =>
    intro _ _ _ _ h; simp_all [Stmt.safe]
  | barrWrite arr idx bval =>
    intro _ _ _ _ h; simp_all [Stmt.safe]
  | fassign _ _ => sorry
  | farrWrite _ _ _ => sorry
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am decls h
    rw [Stmt.safe.eq_6] at h ⊢
    obtain ⟨hds₁, hds₂⟩ := h
    refine ⟨ih₁ fuel σ am decls hds₁, ?_⟩
    cases h₁ : s₁.interp fuel σ am decls with
    | none => trivial
    | some val =>
      obtain ⟨σ₁, am₁⟩ := val
      have h₁' := s₁.interp_fuel_succ fuel σ am decls ⟨σ₁, am₁⟩ h₁
      rw [h₁'] at hds₂; exact ih₂ fuel σ₁ am₁ decls hds₂
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am decls h
    rw [Stmt.safe.eq_7] at h ⊢
    obtain ⟨hb, hbranch⟩ := h
    refine ⟨hb, ?_⟩
    split at hbranch
    · rename_i hb; rw [if_pos hb]; exact ih₁ fuel σ am decls hbranch
    · rename_i hb; rw [if_neg hb]; exact ih₂ fuel σ am decls hbranch
  | loop b body ih_body =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls _; simp [Stmt.safe.eq_8]
    | succ fuel' ih_fuel =>
      intro σ am decls h
      rw [Stmt.safe.eq_9] at h ⊢
      obtain ⟨hb, hbranch⟩ := h
      refine ⟨hb, ?_⟩
      by_cases hcond : b.eval σ am = true
      · rw [if_pos hcond] at hbranch ⊢
        obtain ⟨hds_body, hds_loop⟩ := hbranch
        refine ⟨ih_body fuel' σ am decls hds_body, ?_⟩
        cases hbody : body.interp fuel' σ am decls with
        | none => trivial
        | some val =>
          obtain ⟨σ₁, am₁⟩ := val
          have hbody' := body.interp_fuel_succ fuel' σ am decls ⟨σ₁, am₁⟩ hbody
          rw [hbody'] at hds_loop; exact ih_fuel σ₁ am₁ decls hds_loop
      · rw [if_neg hcond] at hbranch ⊢; exact hbranch
theorem Stmt.safe_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : s.safe fuel' σ am decls) (hle : fuel ≤ fuel') : s.safe fuel σ am decls := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    · exact s.safe_fuel_succ (fuel + k) σ am decls (by rwa [show fuel + (k + 1) = (fuel + k) + 1 from by omega] at h)
    · omega
-- ============================================================
-- § 19c. typedVars anti-monotonicity
-- ============================================================

/-- `typedVars` at higher fuel implies `typedVars` at lower fuel. -/
theorem Stmt.typedVars_fuel_succ (s : Stmt) :
    ∀ fuel σ am decls, s.typedVars (fuel + 1) σ am decls → s.typedVars fuel σ am decls := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ =>
    intro _ _ _ _ h; simp_all [Stmt.typedVars]
  | barrWrite arr idx bval =>
    intro _ _ _ _ h; simp_all [Stmt.typedVars]
  | fassign _ _ => intro _ _ _ _ h; simp_all [Stmt.typedVars]
  | farrWrite _ _ _ => intro _ _ _ _ h; simp_all [Stmt.typedVars]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am decls h
    simp only [Stmt.typedVars] at h ⊢
    obtain ⟨hit₁, hit₂⟩ := h
    refine ⟨ih₁ fuel σ am decls hit₁, ?_⟩
    cases h₁ : s₁.interp fuel σ am decls with
    | none => trivial
    | some val =>
      obtain ⟨σ₁, am₁⟩ := val
      have h₁' := s₁.interp_fuel_succ fuel σ am decls ⟨σ₁, am₁⟩ h₁
      rw [h₁'] at hit₂; exact ih₂ fuel σ₁ am₁ decls hit₂
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am decls h
    simp only [Stmt.typedVars] at h ⊢
    obtain ⟨hb, hbranch⟩ := h
    refine ⟨hb, ?_⟩
    split at hbranch
    · rename_i hcond; rw [if_pos hcond]; exact ih₁ fuel σ am decls hbranch
    · rename_i hcond; rw [if_neg hcond]; exact ih₂ fuel σ am decls hbranch
  | loop b body ih_body =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls _; simp [Stmt.typedVars]
    | succ fuel' ih_fuel =>
      intro σ am decls h
      simp only [Stmt.typedVars] at h ⊢
      obtain ⟨hb, hbranch⟩ := h
      refine ⟨hb, ?_⟩
      by_cases hcond : b.eval σ am = true
      · rw [if_pos hcond] at hbranch ⊢
        obtain ⟨hit_body, hit_loop⟩ := hbranch
        refine ⟨ih_body fuel' σ am decls hit_body, ?_⟩
        cases hbody : body.interp fuel' σ am decls with
        | none => trivial
        | some val =>
          obtain ⟨σ₁, am₁⟩ := val
          have hbody' := body.interp_fuel_succ fuel' σ am decls ⟨σ₁, am₁⟩ hbody
          rw [hbody'] at hit_loop
          have : (Stmt.loop b body).typedVars (fuel' + 1) σ₁ am₁ decls := by
            simp only [Stmt.typedVars]; exact hit_loop
          exact ih_fuel σ₁ am₁ decls this
      · rw [if_neg hcond] at hbranch ⊢; exact hbranch

theorem Stmt.typedVars_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (h : s.typedVars fuel' σ am decls) (hle : fuel ≤ fuel') : s.typedVars fuel σ am decls := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    · exact s.typedVars_fuel_succ (fuel + k) σ am decls (by rwa [show fuel + (k + 1) = (fuel + k) + 1 from by omega] at h)
    · omega

-- ============================================================
-- § 20. Divergence theorems
-- ============================================================

set_option maxHeartbeats 1600000

/-- One iteration of a divergent loop: execute bool, ifgoto (fall through),
    body, goto back to condLabel. Returns RefStepsN and updated state. -/
private theorem loop_one_iter
    (b : SBool) (body : Stmt) (fuel₀ : Nat) (σ σ₁ : Store) (am am₁ : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : (Stmt.loop b body).tmpFree)
    (hftmpfree : (Stmt.loop b body).ftmpFree)
    (hb : b.eval σ am = true)
    (hbds : SBool.safe σ am p.arrayDecls b)
    (htypedv_b : b.typedVars σ am)
    (hbody_res : body.interp fuel₀ σ am p.arrayDecls = some (σ₁, am₁))
    (hds_body : body.safe fuel₀ σ am p.arrayDecls)
    (htypedv_body : body.typedVars fuel₀ σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt (.loop b body) offset nextTmp).1 p offset) :
    ∃ σ₁_tac k,
      RefStepsN p k (Cfg.run offset σ_tac am) (Cfg.run offset σ₁_tac am₁) ∧
      (∀ v, v.isTmp = false → v.isFTmp = false → σ₁_tac v = σ₁ v) ∧ 1 ≤ k := by
  -- Destructure the compiled code for the loop
  dsimp only [refCompileStmt] at hcode
  generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode
  obtain ⟨codeBool, be, tmpB⟩ := rcb
  generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody at hcode
  obtain ⟨codeBody, tmpBody⟩ := rcbody
  simp only [] at hcode
  -- Extract sub-proofs
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
  -- Step 1: Execute bool
  obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
    refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
  rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
  have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
    intro v hv hfv; rw [hntmp_bool v hv hfv]; exact hagree v hv hfv
  -- Step 2: ifgoto (.not be) falls through (condition is true)
  have hifg : p[offset + codeBool.length]? =
      some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
    have := hcode.left.left.right.head
    simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
  have hnotbe : (BoolExpr.not be).eval σ_bool = false := by
    simp [BoolExpr.eval, heval_bool, hb]
  have hexec_if := FragExec.single_iffalse (am := am) hifg hnotbe
  -- Step 3: Execute body
  have hcbody : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
      (offset + codeBool.length + 1) := by
    rw [hrcbody]; have := hcode.left.right
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rwa [show offset + (codeBool.length + 1) = offset + codeBool.length + 1 from by omega] at this
  obtain ⟨σ_body, hexec_body, hagree_body⟩ :=
    refCompileStmt_correct body fuel₀ σ σ₁ am am₁ (offset + codeBool.length + 1) tmpB p
      σ_bool hbody_res htf_body hftf_body hds_body htypedv_body hagree_bool hcbody
  rw [hrcbody] at hexec_body; simp at hexec_body
  -- Step 4: goto back to condLabel
  have hgoto_back : p[offset + codeBool.length + 1 + codeBody.length]? =
      some (.goto offset) := by
    have := hcode.right.head
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rwa [show offset + (codeBool.length + 1 + codeBody.length) =
        offset + codeBool.length + 1 + codeBody.length from by omega] at this
  have hexec_goto := FragExec.single_goto (am := am₁) hgoto_back (σ := σ_body)
  -- Compose all steps: use the goto step explicitly to guarantee k ≥ 1
  have hexec_pre := FragExec.trans'
    (FragExec.trans' hexec_bool hexec_if) hexec_body
  obtain ⟨k_pre, hk_pre⟩ := hexec_pre.to_RefStepsN
  -- The goto is exactly 1 step
  have hgoto_step : Step p (Cfg.run (offset + codeBool.length + 1 + codeBody.length) σ_body am₁)
      (Cfg.run offset σ_body am₁) := Step.goto hgoto_back
  have hk : RefStepsN p (k_pre + 1) (Cfg.run offset σ_tac am) (Cfg.run offset σ_body am₁) :=
    RefStepsN.trans hk_pre (.step hgoto_step .refl)
  exact ⟨σ_body, k_pre + 1, hk, hagree_body, by omega⟩
/-- Main divergence: a divergent, safe statement produces unbounded steps. -/
theorem refCompileStmt_diverges (s : Stmt) (σ : Store) (am : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ am p.arrayDecls = none)
    (hsafe : ∀ fuel, s.safe fuel σ am p.arrayDecls)
    (htypedv : ∀ fuel, s.typedVars fuel σ am p.arrayDecls)
    (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') := by
  induction s generalizing σ am offset nextTmp p σ_tac with
  | skip => intro _; exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | assign x e => intro _; exfalso; exact Stmt.interp_ne_none_of_safe_assign x e σ am p.arrayDecls (hsafe 0) (hdiv 0)
  | bassign x b => intro _; exfalso; exact Stmt.interp_ne_none_of_safe_bassign x b σ am p.arrayDecls (hsafe 0) (hdiv 0)
  | arrWrite arr idx val => intro _; exfalso; exact Stmt.interp_ne_none_of_safe_arrWrite arr idx val σ am p.arrayDecls (hsafe 0) (hdiv 0)
  | barrWrite arr idx bval => intro _; exfalso; exact Stmt.interp_ne_none_of_safe_barrWrite arr idx bval σ am p.arrayDecls (hsafe 0) (hdiv 0)
  | fassign _ _ => sorry
  | farrWrite _ _ _ => sorry
  | seq s₁ s₂ ih₁ ih₂ =>
    intro N
    -- Either s₁ diverges, or s₁ terminates and s₂ diverges
    by_cases hdiv₁ : ∀ fuel, s₁.interp fuel σ am p.arrayDecls = none
    · -- s₁ diverges: use ih₁ to get unbounded steps from s₁'s compiled code
      have hds₁ : ∀ fuel, s₁.safe fuel σ am p.arrayDecls := by intro f; have := hsafe f; simp [Stmt.safe] at this; exact this.1
      have htypedv₁ : ∀ fuel, s₁.typedVars fuel σ am p.arrayDecls := by intro f; have := htypedv f; simp [Stmt.typedVars] at this; exact this.1
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have hftf₁ : s₁.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      have := ih₁ σ am offset nextTmp p σ_tac htf₁ hftf₁ hdiv₁ hds₁ htypedv₁ hagree hcode1 N
      obtain ⟨n, hn, pc', σ', am', hsteps⟩ := this
      exact ⟨n, hn, pc', σ', am', hsteps⟩
    · -- s₁ terminates at some fuel → s₂ diverges
      push_neg at hdiv₁
      obtain ⟨fuel₁, hf₁⟩ := hdiv₁
      obtain ⟨r₁, hr₁⟩ := Option.ne_none_iff_exists'.mp hf₁
      obtain ⟨σ₁, am₁⟩ := r₁
      -- s₂ must diverge from σ₁, am₁
      have hdiv₂ : ∀ fuel, s₂.interp fuel σ₁ am₁ p.arrayDecls = none := by
        intro f
        have hseq := hdiv (max fuel₁ f)
        simp only [Stmt.interp.eq_6] at hseq
        have hterm := s₁.interp_fuel_mono fuel₁ (max fuel₁ f - fuel₁) σ am p.arrayDecls ⟨σ₁, am₁⟩ hr₁
        rw [show fuel₁ + (max fuel₁ f - fuel₁) = max fuel₁ f from by omega] at hterm
        simp only [hterm] at hseq
        exact s₂.interp_none_of_le f (max fuel₁ f) σ₁ am₁ p.arrayDecls hseq (by omega)
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf₁ : s₁.ftmpFree := fun v hv => hftmpfree v (List.mem_append_left _ hv)
      have hftf₂ : s₂.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      have hds₁ : s₁.safe fuel₁ σ am p.arrayDecls := by have := hsafe fuel₁; simp [Stmt.safe] at this; exact this.1
      have htypedv₁ : s₁.typedVars fuel₁ σ am p.arrayDecls := by have := htypedv fuel₁; simp [Stmt.typedVars] at this; exact this.1
      have hds₂ : ∀ f, s₂.safe f σ₁ am₁ p.arrayDecls := by
        intro f
        have hsf := hsafe (max fuel₁ f)
        simp only [Stmt.safe.eq_6] at hsf
        have hterm := s₁.interp_fuel_mono fuel₁ (max fuel₁ f - fuel₁) σ am p.arrayDecls ⟨σ₁, am₁⟩ hr₁
        rw [show fuel₁ + (max fuel₁ f - fuel₁) = max fuel₁ f from by omega] at hterm
        rw [hterm] at hsf
        exact Stmt.safe_of_le _ f _ σ₁ am₁ p.arrayDecls hsf.2 (by omega)
      have htypedv₂ : ∀ f, s₂.typedVars f σ₁ am₁ p.arrayDecls := by
        intro f
        have hif := htypedv (max fuel₁ f)
        simp only [Stmt.typedVars] at hif
        have hterm := s₁.interp_fuel_mono fuel₁ (max fuel₁ f - fuel₁) σ am p.arrayDecls ⟨σ₁, am₁⟩ hr₁
        rw [show fuel₁ + (max fuel₁ f - fuel₁) = max fuel₁ f from by omega] at hterm
        rw [hterm] at hif
        exact Stmt.typedVars_of_le _ f _ σ₁ am₁ p.arrayDecls hif.2 (by omega)
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
      obtain ⟨σ₁_tac, hexec₁, hagree₁⟩ :=
        refCompileStmt_correct s₁ fuel₁ σ σ₁ am am₁ offset nextTmp p σ_tac hr₁ htf₁ hftf₁ hds₁ htypedv₁ hagree hcode1
      rw [hrc1] at hexec₁; simp at hexec₁
      obtain ⟨k₁, hk₁⟩ := hexec₁.to_RefStepsN
      have := ih₂ σ₁ am₁ (offset + code1.length) tmp1 p σ₁_tac htf₂ hftf₂ hdiv₂ hds₂ htypedv₂ hagree₁ hcode2 N
      obtain ⟨n₂, hn₂, pc', σ', am', hsteps₂⟩ := this
      exact ⟨k₁ + n₂, by omega, pc', σ', am', RefStepsN.trans hk₁ hsteps₂⟩
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro N
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
    cases hb : b.eval σ am with
    | true =>
      -- s₁ diverges
      have hbds : SBool.safe σ am p.arrayDecls b := by
        have := hsafe 1; simp only [Stmt.safe, hb] at this; exact this.1
      have hisSafe_b : SBool.isSafe σ am p.arrayDecls b = true :=
        SBool.isSafe_of_safe b σ am p.arrayDecls hbds
      have hdiv₁ : ∀ fuel, s₁.interp fuel σ am p.arrayDecls = none := by
        intro f; have := hdiv f; simp only [Stmt.interp, hisSafe_b, hb, ite_true] at this; exact this
      have htypedv_b : b.typedVars σ am := by
        have := htypedv 1; simp only [Stmt.typedVars, hb] at this; exact this.1
      have hds₁ : ∀ f, s₁.safe f σ am p.arrayDecls := by
        intro f; have := hsafe f; simp only [Stmt.safe, hb] at this; exact this.2
      have htypedv₁ : ∀ f, s₁.typedVars f σ am p.arrayDecls := by
        intro f; have := htypedv f; simp only [Stmt.typedVars, hb] at this; exact this.2
      have htf₁ : s₁.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      have hftf₁ : s₁.ftmpFree :=
        fun v hv => hftmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
        intro v hv hfv; rw [hntmp_bool v hv hfv]; exact hagree v hv hfv
      have hbe_true : be.eval σ_bool = true := by rw [heval_bool, hb]
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      have hexec_if := FragExec.single_iftrue (am := am) hifg hbe_true
      have hct : CodeAt (refCompileStmt s₁
          (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse).1 p
          (offset + codeBool.length + 1 + codeElse.length + 1) := by
        rw [hrct]
        have := hcode.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1 + codeElse.length + 1) =
            offset + codeBool.length + 1 + codeElse.length + 1 from by omega] at this
      have := ih₁ σ am (offset + codeBool.length + 1 + codeElse.length + 1) tmpElse p σ_bool
        htf₁ hftf₁ hdiv₁ hds₁ htypedv₁ hagree_bool hct N
      obtain ⟨n₁, hn₁, pc', σ', am', hsteps₁⟩ := this
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      exact ⟨k_pre + n₁, by omega, pc', σ', am', RefStepsN.trans hk_pre hsteps₁⟩
    | false =>
      -- s₂ diverges
      have hbds : SBool.safe σ am p.arrayDecls b := by
        have := hsafe 1; simp only [Stmt.safe, hb] at this; exact this.1
      have hisSafe_b : SBool.isSafe σ am p.arrayDecls b = true :=
        SBool.isSafe_of_safe b σ am p.arrayDecls hbds
      have hdiv₂ : ∀ fuel, s₂.interp fuel σ am p.arrayDecls = none := by
        intro f; have := hdiv f; simp only [Stmt.interp, hisSafe_b, hb, Bool.false_eq_true, ite_false] at this; exact this
      have htypedv_b : b.typedVars σ am := by
        have := htypedv 1; simp only [Stmt.typedVars, hb] at this; exact this.1
      have hds₂ : ∀ f, s₂.safe f σ am p.arrayDecls := by
        intro f; have := hsafe f; simp only [Stmt.safe, hb, Bool.false_eq_true, ite_false] at this; exact this.2
      have htypedv₂ : ∀ f, s₂.typedVars f σ am p.arrayDecls := by
        intro f; have := htypedv f; simp only [Stmt.typedVars, hb, Bool.false_eq_true, ite_false] at this; exact this.2
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hftf₂ : s₂.ftmpFree := fun v hv => hftmpfree v (List.mem_append_right _ hv)
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hftf_b htypedv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ v := by
        intro v hv hfv; rw [hntmp_bool v hv hfv]; exact hagree v hv hfv
      have hbe_false : be.eval σ_bool = false := by rw [heval_bool, hb]
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto be (offset + codeBool.length + 1 + codeElse.length + 1)) := by
        have := hcode.left.left.left.right.head
        simp only [List.length_append] at this; exact this
      have hexec_if := FragExec.single_iffalse (am := am) hifg hbe_false
      have hce : CodeAt (refCompileStmt s₂ (offset + codeBool.length + 1) tmpB).1 p
          (offset + codeBool.length + 1) := by
        rw [hrce]
        have := hcode.left.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) =
            offset + codeBool.length + 1 from by omega] at this
      have := ih₂ σ am (offset + codeBool.length + 1) tmpB p σ_bool
        htf₂ hftf₂ hdiv₂ hds₂ htypedv₂ hagree_bool hce N
      obtain ⟨n₂, hn₂, pc', σ', am', hsteps₂⟩ := this
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      exact ⟨k_pre + n₂, by omega, pc', σ', am', RefStepsN.trans hk_pre hsteps₂⟩
  | loop b body ih =>
    intro N
    -- Helper: extract body divergence proof to get unbounded steps
    have body_div_case : ∀ (σ_cur : Store) (am_cur : ArrayMem) (σ_tac_cur : Store) (n₀ : Nat),
        (∀ f, (Stmt.loop b body).interp f σ_cur am_cur p.arrayDecls = none) →
        (∀ f, (Stmt.loop b body).safe f σ_cur am_cur p.arrayDecls) →
        (∀ f, (Stmt.loop b body).typedVars f σ_cur am_cur p.arrayDecls) →
        (Stmt.loop b body).tmpFree →
        (Stmt.loop b body).ftmpFree →
        (∀ v, v.isTmp = false → v.isFTmp = false → σ_tac_cur v = σ_cur v) →
        b.eval σ_cur am_cur = true →
        (∀ f, body.interp f σ_cur am_cur p.arrayDecls = none) →
        RefStepsN p n₀ (Cfg.run offset σ_tac am) (Cfg.run offset σ_tac_cur am_cur) →
        ∀ M, ∃ n, n ≥ M ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') := by
      intro σ_cur am_cur σ_tac_cur n₀ hdiv_cur hsafe_cur htypedv_cur htf_cur hftf_cur hagree_cur hb hbody_div hsteps_cur M
      have hds_body : ∀ f, body.safe f σ_cur am_cur p.arrayDecls := by
        intro f; have := hsafe_cur (f + 1); unfold Stmt.safe at this; simp [hb] at this; exact this.2.1
      have htypedv_body : ∀ f, body.typedVars f σ_cur am_cur p.arrayDecls := by
        intro f; have := htypedv_cur (f + 1); unfold Stmt.typedVars at this; simp [hb] at this; exact this.2.1
      have htf_body : body.tmpFree := fun v hv => htf_cur v (List.mem_append_right _ hv)
      have hftf_body : body.ftmpFree := fun v hv => hftf_cur v (List.mem_append_right _ hv)
      dsimp only [refCompileStmt] at hcode
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody at hcode
      obtain ⟨codeBody, tmpBody⟩ := rcbody
      simp only [] at hcode
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf_cur v (List.mem_append_left _ hv)
      have hftf_b : ∀ v ∈ b.freeVars, v.isFTmp = false :=
        fun v hv => hftf_cur v (List.mem_append_left _ hv)
      have hbds_b : SBool.safe σ_cur am_cur p.arrayDecls b := by
        have := hsafe_cur 1; unfold Stmt.safe at this; simp [hb] at this; exact this.1
      have htypedv_b : b.typedVars σ_cur am_cur := by
        have := htypedv_cur 1; unfold Stmt.typedVars at this; simp [hb] at this; exact this.1
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ_cur σ_tac_cur am_cur p htf_b hftf_b htypedv_b hbds_b hagree_cur hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → v.isFTmp = false → σ_bool v = σ_cur v := by
        intro v hv hfv; rw [hntmp_bool v hv hfv]; exact hagree_cur v hv hfv
      have hifg : p[offset + codeBool.length]? =
          some (.ifgoto (.not be) (offset + codeBool.length + 1 + codeBody.length + 1)) := by
        have := hcode.left.left.right.head
        simp only [List.length_append, List.length_cons, List.length_nil] at this; exact this
      have hnotbe : (BoolExpr.not be).eval σ_bool = false := by
        simp [BoolExpr.eval, heval_bool, hb]
      have hexec_if := FragExec.single_iffalse (am := am_cur) hifg hnotbe
      have hcbody : CodeAt (refCompileStmt body (offset + codeBool.length + 1) tmpB).1 p
          (offset + codeBool.length + 1) := by
        rw [hrcbody]; have := hcode.left.right
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        rwa [show offset + (codeBool.length + 1) = offset + codeBool.length + 1 from by omega] at this
      have := ih σ_cur am_cur (offset + codeBool.length + 1) tmpB p σ_bool
        htf_body hftf_body hbody_div hds_body htypedv_body hagree_bool hcbody M
      obtain ⟨n_body, hn_body, pc', σ', am', hsteps_body⟩ := this
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      have hsteps_total := RefStepsN.trans hsteps_cur (RefStepsN.trans hk_pre hsteps_body)
      exact ⟨n₀ + (k_pre + n_body), by omega, pc', σ', am',
        hsteps_total⟩
    -- Main proof: strong induction on (N - n₀). Each iteration adds ≥ 1 step.
    -- Either body diverges (handled by body_div_case) or we iterate via loop_one_iter.
    suffices h : ∀ (gap : Nat) (σ_cur : Store) (am_cur : ArrayMem) (σ_tac_cur : Store) (n₀ : Nat),
        N - n₀ ≤ gap →
        (∀ f, (Stmt.loop b body).interp f σ_cur am_cur p.arrayDecls = none) →
        (∀ f, (Stmt.loop b body).safe f σ_cur am_cur p.arrayDecls) →
        (∀ f, (Stmt.loop b body).typedVars f σ_cur am_cur p.arrayDecls) →
        (Stmt.loop b body).tmpFree →
        (Stmt.loop b body).ftmpFree →
        (∀ v, v.isTmp = false → v.isFTmp = false → σ_tac_cur v = σ_cur v) →
        RefStepsN p n₀ (Cfg.run offset σ_tac am) (Cfg.run offset σ_tac_cur am_cur) →
        ∃ n, n ≥ N ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') by
      exact h N σ am σ_tac 0 (by omega) hdiv hsafe htypedv htmpfree hftmpfree hagree .refl
    intro gap; induction gap with
    | zero =>
      intro σ_cur am_cur σ_tac_cur n₀ hgap _ _ _ _ _ _ hsteps_cur
      exact ⟨n₀, by omega, offset, σ_tac_cur, am_cur, hsteps_cur⟩
    | succ gap' ihgap =>
      intro σ_cur am_cur σ_tac_cur n₀ hgap hdiv_cur hsafe_cur htypedv_cur htf_cur hftf_cur hagree_cur hsteps_cur
      by_cases hn : n₀ ≥ N
      · exact ⟨n₀, hn, offset, σ_tac_cur, am_cur, hsteps_cur⟩
      · have hbds_cur : SBool.safe σ_cur am_cur p.arrayDecls b := by
          have := hsafe_cur 1; simp only [Stmt.safe] at this; exact this.1
        have hisSafe_cur : SBool.isSafe σ_cur am_cur p.arrayDecls b = true :=
          SBool.isSafe_of_safe b σ_cur am_cur p.arrayDecls hbds_cur
        have hb : b.eval σ_cur am_cur = true := by
          by_contra hc; push_neg at hc
          have := hdiv_cur 1; simp [Stmt.interp, hisSafe_cur, Bool.eq_false_iff.mpr hc] at this
        by_cases hbody_div : ∀ f, body.interp f σ_cur am_cur p.arrayDecls = none
        · exact body_div_case σ_cur am_cur σ_tac_cur n₀ hdiv_cur hsafe_cur htypedv_cur htf_cur hftf_cur
            hagree_cur hb hbody_div hsteps_cur N
        · push_neg at hbody_div
          obtain ⟨f₀, hf₀⟩ := hbody_div
          obtain ⟨r₁, hr₁⟩ := Option.ne_none_iff_exists'.mp hf₀
          obtain ⟨σ₁, am₁⟩ := r₁
          have hbds : SBool.safe σ_cur am_cur p.arrayDecls b := by
            have := hsafe_cur (f₀ + 1); simp only [Stmt.safe, hb] at this; exact this.1
          have hds_body : body.safe f₀ σ_cur am_cur p.arrayDecls := by
            have := hsafe_cur (f₀ + 1); simp only [Stmt.safe, hb] at this; exact this.2.1
          have htypedv_b : b.typedVars σ_cur am_cur := by
            have := htypedv_cur (f₀ + 1); simp only [Stmt.typedVars, hb] at this; exact this.1
          have htypedv_body : body.typedVars f₀ σ_cur am_cur p.arrayDecls := by
            have := htypedv_cur (f₀ + 1); simp only [Stmt.typedVars, hb] at this; exact this.2.1
          obtain ⟨σ₁_tac, k, hsteps_iter, hagree₁, hk1⟩ :=
            loop_one_iter b body f₀ σ_cur σ₁ am_cur am₁ offset nextTmp p σ_tac_cur
              htf_cur hftf_cur hb hbds htypedv_b hr₁ hds_body htypedv_body hagree_cur hcode
          have hdiv₁ : ∀ f, (Stmt.loop b body).interp f σ₁ am₁ p.arrayDecls = none := by
            intro f
            by_contra hc; push_neg at hc
            obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.mp hc
            have hsome := (Stmt.loop b body).interp_fuel_mono f f₀ σ₁ am₁ p.arrayDecls r' hr'
            have hloop := hdiv_cur (f + f₀ + 1)
            have hisSafe_b : SBool.isSafe σ_cur am_cur p.arrayDecls b = true :=
              SBool.isSafe_of_safe b σ_cur am_cur p.arrayDecls hbds
            simp only [Stmt.interp, hisSafe_b, hb, ite_true] at hloop
            have hbm : body.interp (f + f₀) σ_cur am_cur p.arrayDecls = some (σ₁, am₁) := by
              have := body.interp_fuel_mono f₀ f σ_cur am_cur p.arrayDecls ⟨σ₁, am₁⟩ hr₁; rwa [Nat.add_comm] at this
            simp only [hbm, bind, Option.bind] at hloop
            simp [hloop] at hsome
          have hsafe₁ : ∀ f, (Stmt.loop b body).safe f σ₁ am₁ p.arrayDecls := by
            intro f; have hsf := hsafe_cur (f + f₀ + 1)
            unfold Stmt.safe at hsf; simp only [hb, ite_true] at hsf
            have hbm := body.interp_fuel_mono f₀ (f + f₀ + 1 - (f₀ + 1)) σ_cur am_cur p.arrayDecls ⟨σ₁, am₁⟩ hr₁
            rw [show f₀ + (f + f₀ + 1 - (f₀ + 1)) = f + f₀ from by omega] at hbm
            rw [hbm] at hsf; exact Stmt.safe_of_le _ f _ σ₁ am₁ p.arrayDecls hsf.2.2 (by omega)
          have htypedv₁ : ∀ f, (Stmt.loop b body).typedVars f σ₁ am₁ p.arrayDecls := by
            intro f; have hif := htypedv_cur (f + f₀ + 1)
            unfold Stmt.typedVars at hif; simp only [hb, ite_true] at hif
            have hbm := body.interp_fuel_mono f₀ (f + f₀ + 1 - (f₀ + 1)) σ_cur am_cur p.arrayDecls ⟨σ₁, am₁⟩ hr₁
            rw [show f₀ + (f + f₀ + 1 - (f₀ + 1)) = f + f₀ from by omega] at hbm
            rw [hbm] at hif; exact Stmt.typedVars_of_le _ f _ σ₁ am₁ p.arrayDecls hif.2.2 (by omega)
          have hsteps_total := RefStepsN.trans hsteps_cur hsteps_iter
          exact ihgap σ₁ am₁ σ₁_tac (n₀ + k) (by omega) hdiv₁ hsafe₁ htypedv₁ htf_cur hftf_cur hagree₁ hsteps_total
/-- Top-level divergence: if the source diverges with safety,
    the compiled program does not halt. -/
theorem refCompile_diverge (s : Stmt) (σ : Store)
    (htmpfree : s.tmpFree)
    (hftmpfree : s.ftmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ ArrayMem.init (refCompile s).arrayDecls = none)
    (hsafe : ∀ fuel, s.safe fuel σ ArrayMem.init (refCompile s).arrayDecls)
    (htypedv : ∀ fuel, s.typedVars fuel σ ArrayMem.init (refCompile s).arrayDecls) :
    ∀ σ_tac am', ¬ haltsWithResult (refCompile s) 0 σ σ_tac ArrayMem.init am' := by
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  have hunbounded := refCompileStmt_diverges s σ ArrayMem.init 0 0 (refCompile s) σ
    htmpfree hftmpfree hdiv hsafe htypedv (fun _ _ _ => rfl) hcode
  exact no_halt_of_unbounded_am hunbounded
