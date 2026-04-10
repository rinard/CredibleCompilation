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
  | flit _ => simp [SExpr.isSafe]
  | fbin _ a b iha ihb =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, iha h.1, ihb h.2]
  | intToFloat e ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | floatToInt e ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | floatExp e ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h]
  | farrRead arr idx ih =>
    simp [SExpr.safe] at h; simp [SExpr.isSafe, ih h.1, decide_eq_true_eq, h.2]

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
  | fcmp _ a b =>
    simp [SBool.safe] at h
    simp [SBool.isSafe, SExpr.isSafe_of_safe a σ am decls h.1, SExpr.isSafe_of_safe b σ am decls h.2]

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

private theorem Stmt.interp_ne_none_of_safe_fassign (x : Var) (e : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.fassign x e).safe 0 σ am decls) :
    (Stmt.fassign x e).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe e σ am decls hsafe]

private theorem Stmt.interp_ne_none_of_safe_farrWrite (arr : ArrayName) (idx val : SExpr) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy))
    (hsafe : (Stmt.farrWrite arr idx val).safe 0 σ am decls) :
    (Stmt.farrWrite arr idx val).interp 0 σ am decls ≠ none := by
  simp only [Stmt.safe] at hsafe
  simp [Stmt.interp, SExpr.isSafe_of_safe idx σ am decls hsafe.1,
        SExpr.isSafe_of_safe val σ am decls hsafe.2.1, decide_eq_true_eq, hsafe.2.2]

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
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _ | fassign _ _ | farrWrite _ _ _ | label _ | goto _ | ifgoto _ _ =>
    intro fuel σ am decls r h; simp only [Stmt.interp] at h ⊢; exact h
  | seq s1 s2 ih1 ih2 =>
    intro fuel σ am decls r h
    simp only [Stmt.interp] at h ⊢
    cases h1 : s1.interp fuel σ am decls with
    | none => simp [h1] at h
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      simp [h1] at h
      simp [ih1 fuel σ am decls _ h1]
      exact ih2 fuel σ₁ am₁ decls r h
  | ite b s1 s2 ih1 ih2 =>
    intro fuel σ am decls r h
    simp only [Stmt.interp] at h ⊢
    cases hs : b.isSafe σ am decls <;> simp [hs] at h ⊢
    cases heval : b.eval σ am <;> simp [heval] at h ⊢
    · exact ih2 fuel σ am decls r h
    · exact ih1 fuel σ am decls r h
  | loop b body ihb =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls r h; simp [Stmt.interp.eq_8] at h
    | succ fuel' ih_fuel =>
      intro σ am decls r h
      rw [Stmt.interp.eq_9] at h
      rw [Stmt.interp.eq_9]
      cases hs : b.isSafe σ am decls <;> simp [hs] at h ⊢
      cases heval : b.eval σ am <;> simp [heval] at h ⊢
      · exact h
      · cases hb : body.interp fuel' σ am decls with
        | none => simp [hb] at h
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          simp [hb] at h
          simp [ihb fuel' σ am decls _ hb]
          exact ih_fuel σ₁ am₁ decls r h
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
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _ | fassign _ _ | farrWrite _ _ _ | label _ | goto _ | ifgoto _ _ =>
    intro fuel σ am decls h; simp only [Stmt.safe] at h ⊢; try exact h
  | seq s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.safe] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨ih1 fuel σ am decls h1, ?_⟩
    cases h_interp : s1.interp fuel σ am decls with
    | none => trivial
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      have h_interp' := s1.interp_fuel_succ fuel σ am decls _ h_interp
      simp [h_interp'] at h2
      exact ih2 fuel σ₁ am₁ decls h2
  | ite b s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.safe] at h ⊢
    obtain ⟨hb, h_branch⟩ := h
    refine ⟨hb, ?_⟩
    cases heval : b.eval σ am <;> simp [heval] at h_branch ⊢
    · exact ih2 fuel σ am decls h_branch
    · exact ih1 fuel σ am decls h_branch
  | loop b body ihb =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls _; simp [Stmt.safe.eq_8]
    | succ fuel' ih_fuel =>
      intro σ am decls h
      rw [Stmt.safe.eq_9] at h
      rw [Stmt.safe.eq_9]
      obtain ⟨hbs, h_cond⟩ := h
      refine ⟨hbs, ?_⟩
      cases heval : b.eval σ am
      · simp [heval] at h_cond ⊢
      · simp [heval] at h_cond ⊢
        obtain ⟨h_body_safe, h_rest⟩ := h_cond
        refine ⟨ihb fuel' σ am decls h_body_safe, ?_⟩
        cases h_interp : body.interp fuel' σ am decls with
        | none => trivial
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          have h_interp' := body.interp_fuel_succ fuel' σ am decls _ h_interp
          simp [h_interp'] at h_rest
          exact ih_fuel σ₁ am₁ decls h_rest
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
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ | barrWrite _ _ _ | fassign _ _ | farrWrite _ _ _ | label _ | goto _ | ifgoto _ _ =>
    intro fuel σ am decls h; simp only [Stmt.typedVars] at h ⊢; try exact h
  | seq s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.typedVars] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨ih1 fuel σ am decls h1, ?_⟩
    cases h_interp : s1.interp fuel σ am decls with
    | none => trivial
    | some p =>
      obtain ⟨σ₁, am₁⟩ := p
      have h_interp' := s1.interp_fuel_succ fuel σ am decls _ h_interp
      simp [h_interp'] at h2
      exact ih2 fuel σ₁ am₁ decls h2
  | ite b s1 s2 ih1 ih2 =>
    intro fuel σ am decls h
    simp only [Stmt.typedVars] at h ⊢
    obtain ⟨hb, h_branch⟩ := h
    refine ⟨hb, ?_⟩
    cases heval : b.eval σ am <;> simp [heval] at h_branch ⊢
    · exact ih2 fuel σ am decls h_branch
    · exact ih1 fuel σ am decls h_branch
  | loop b body ihb =>
    intro fuel
    induction fuel with
    | zero => intro σ am decls _; simp [Stmt.typedVars.eq_8]
    | succ fuel' ih_fuel =>
      intro σ am decls h
      rw [Stmt.typedVars.eq_9] at h
      rw [Stmt.typedVars.eq_9]
      obtain ⟨hbs, h_cond⟩ := h
      refine ⟨hbs, ?_⟩
      cases heval : b.eval σ am
      · simp [heval] at h_cond ⊢
      · simp [heval] at h_cond ⊢
        obtain ⟨h_body_tv, h_rest⟩ := h_cond
        refine ⟨ihb fuel' σ am decls h_body_tv, ?_⟩
        cases h_interp : body.interp fuel' σ am decls with
        | none => trivial
        | some p =>
          obtain ⟨σ₁, am₁⟩ := p
          have h_interp' := body.interp_fuel_succ fuel' σ am decls _ h_interp
          simp [h_interp'] at h_rest
          exact ih_fuel σ₁ am₁ decls h_rest

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
  sorry
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
