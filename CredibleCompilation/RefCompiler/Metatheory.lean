import CredibleCompilation.RefCompiler.ErrorHandling

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
# Reference Compiler: Metatheory

Step-indexed execution (RefStepsN), fuel monotonicity,
divSafe/intTyped anti-monotonicity, and divergence theorems.
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
  | bassign _ _ => intro fuel σ σ' h; simp only [Stmt.interp] at h ⊢; exact h
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
  | bassign _ _ => intro fuel σ h; simp only [Stmt.divSafe] at h ⊢; exact h
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
-- § 19b. intTyped anti-monotonicity
-- ============================================================

/-- `intTyped` at higher fuel implies `intTyped` at lower fuel. -/
theorem Stmt.intTyped_fuel_succ (s : Stmt) :
    ∀ fuel σ, s.intTyped (fuel + 1) σ → s.intTyped fuel σ := by
  induction s with
  | skip => intro _ _ _; simp only [Stmt.intTyped]
  | assign _ _ => intro fuel σ h; simp only [Stmt.intTyped] at h ⊢; exact h
  | bassign _ _ => intro fuel σ h; simp only [Stmt.intTyped] at h ⊢; exact h
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ h
    simp only [Stmt.intTyped] at h ⊢
    refine ⟨ih₁ fuel σ h.1, ?_⟩
    cases hq : s₁.interp fuel σ with
    | none => trivial
    | some σ₁ =>
      rw [s₁.interp_fuel_succ fuel σ σ₁ hq] at h
      exact ih₂ fuel σ₁ h.2
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ h
    simp only [Stmt.intTyped] at h ⊢
    refine ⟨h.1, ?_⟩
    cases hb : b.eval σ <;> simp [hb] at h ⊢
    · exact ih₂ fuel σ h.2
    · exact ih₁ fuel σ h.2
  | loop b body ih =>
    intro fuel
    induction fuel with
    | zero => intro _ _; simp only [Stmt.intTyped]
    | succ fuel' ihf =>
      intro σ h
      unfold Stmt.intTyped at h ⊢
      refine ⟨h.1, ?_⟩
      cases hb : b.eval σ <;> simp [hb] at h ⊢
      · refine ⟨ih fuel' σ h.2.1, ?_⟩
        cases hq : body.interp fuel' σ with
        | none => exact trivial
        | some σ₁ =>
          have hq' := body.interp_fuel_succ fuel' σ σ₁ hq
          rw [hq'] at h; exact ihf σ₁ h.2.2

theorem Stmt.intTyped_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store)
    (h : s.intTyped fuel' σ) (hle : fuel ≤ fuel') : s.intTyped fuel σ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simp at h; exact h
  | succ k ihk => exact ihk (s.intTyped_fuel_succ _ _ h) (by omega)

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
    (hintv_b : b.intTyped σ)
    (hbody_res : body.interp fuel₀ σ = some σ₁)
    (hds_body : body.divSafe fuel₀ σ)
    (hintv_body : body.intTyped fuel₀ σ)
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
    refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
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
      hbody_res htf_body hds_body hintv_body hagree_bool hcbody
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
    (hintv : ∀ fuel, s.intTyped fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ', RefStepsN p n (Cfg.run offset σ_tac) (Cfg.run pc' σ') := by
  induction s generalizing σ offset nextTmp σ_tac with
  | skip => exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | assign _ _ => exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | bassign _ _ => exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | seq s₁ s₂ ih₁ ih₂ =>
    -- Either s₁ diverges or s₁ terminates and s₂ diverges
    by_cases hs₁ : ∀ fuel, s₁.interp fuel σ = none
    · -- s₁ diverges
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have hs₁_safe : ∀ fuel, s₁.divSafe fuel σ := by
        intro fuel; have h := hsafe fuel; simp only [Stmt.divSafe] at h; exact h.1
      have hs₁_intv : ∀ fuel, s₁.intTyped fuel σ := by
        intro fuel; have h := hintv fuel; simp only [Stmt.intTyped] at h; exact h.1
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      intro N
      obtain ⟨n, hn_ge, pc', σ', hn⟩ := ih₁ σ offset nextTmp σ_tac htf₁ hs₁ hs₁_safe hs₁_intv hagree hcode1 N
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
        exact s₂.divSafe_of_le fuel g σ₁ h.2 (by omega)
      have hs₁_intv : s₁.intTyped fuel₀ σ := by
        have h := hintv fuel₀; simp only [Stmt.intTyped] at h; exact h.1
      have hs₂_intv : ∀ fuel, s₂.intTyped fuel σ₁ := by
        intro fuel
        let g := max fuel fuel₀
        have hq : s₁.interp g σ = some σ₁ := by
          have := s₁.interp_fuel_mono fuel₀ (g - fuel₀) σ σ₁ hσ₁
          rwa [show fuel₀ + (g - fuel₀) = g from by omega] at this
        have h := hintv g; simp only [Stmt.intTyped] at h
        rw [hq] at h
        exact s₂.intTyped_of_le fuel g σ₁ h.2 (by omega)
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
        refCompileStmt_correct s₁ fuel₀ σ σ₁ offset nextTmp p σ_tac hσ₁ htf₁ hs₁_safe' hs₁_intv hagree hcode1
      rw [hrc1] at hexec₁; simp at hexec₁
      obtain ⟨n₁, hn₁⟩ := hexec₁.to_RefStepsN
      have hcode2 : CodeAt (refCompileStmt s₂ (offset + code1.length) tmp1).1 p
          (offset + code1.length) := by rw [hrc2]; exact hcode.right
      intro N
      obtain ⟨n₂, hn₂_ge, pc', σ', hn₂⟩ :=
        ih₂ σ₁ (offset + code1.length) tmp1 σ₁_tac htf₂ hs₂_div hs₂_safe hs₂_intv hagree₁ hcode2 N
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
      have hintv_b : b.intTyped σ := by
        have := hintv 0; simp [Stmt.intTyped, hb] at this; exact this.1
      have hs₁_intv : ∀ fuel, s₁.intTyped fuel σ := by
        intro fuel; have := hintv fuel; simp [Stmt.intTyped, hb] at this; exact this.2
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
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
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
          htf₁ hs₁_div hs₁_safe hs₁_intv hagree_bool hct N
      exact ⟨n_bool + 1 + n₁, by omega, pc', σ', hn_prefix.trans hn₁⟩
    | false =>
      -- s₂ diverges (symmetric)
      have hs₂_div : ∀ fuel, s₂.interp fuel σ = none := by
        intro fuel; have := hdiv fuel; simp [Stmt.interp, hb] at this; exact this
      have hbds : SBool.divSafe σ b := by
        have := hsafe 0; simp [Stmt.divSafe, hb] at this; exact this.1
      have hs₂_safe : ∀ fuel, s₂.divSafe fuel σ := by
        intro fuel; have := hsafe fuel; simp [Stmt.divSafe, hb] at this; exact this.2
      have hintv_b : b.intTyped σ := by
        have := hintv 0; simp [Stmt.intTyped, hb] at this; exact this.1
      have hs₂_intv : ∀ fuel, s₂.intTyped fuel σ := by
        intro fuel; have := hintv fuel; simp [Stmt.intTyped, hb] at this; exact this.2
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
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
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
          htf₂ hs₂_div hs₂_safe hs₂_intv hagree_bool hce N
      exact ⟨n_bool + 1 + n₂, by omega, pc', σ', hn_prefix.trans hn₂⟩
  | loop b body ih_body =>
    -- b.eval σ = true (otherwise loop terminates at fuel 1)
    have hb : b.eval σ = true := by
      cases hb : b.eval σ with
      | true => rfl
      | false => have h := hdiv 1; unfold Stmt.interp at h; simp [hb] at h
    have hbds : SBool.divSafe σ b := by
      have h := hsafe 1; unfold Stmt.divSafe at h; simp [hb] at h; exact h.1
    have hintv_b : b.intTyped σ := by
      have h := hintv 1; unfold Stmt.intTyped at h; simp [hb] at h; exact h.1
    have htf_body : body.tmpFree :=
      fun v hv => htmpfree v (List.mem_append_right _ hv)
    -- Case split: body diverges or terminates
    by_cases hbody_div : ∀ fuel, body.interp fuel σ = none
    · -- Body diverges: use structural IH on body
      have hbody_safe : ∀ fuel, body.divSafe fuel σ := by
        intro fuel; have h := hsafe (fuel + 1)
        unfold Stmt.divSafe at h; simp [hb] at h; exact h.2.1
      have hbody_intv : ∀ fuel, body.intTyped fuel σ := by
        intro fuel; have h := hintv (fuel + 1)
        unfold Stmt.intTyped at h; simp [hb] at h; exact h.2.1
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
        refCompileBool_correct b offset nextTmp σ σ_tac p htf_b hintv_b hbds hagree hcb
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
          htf_body hbody_div hbody_safe hbody_intv hagree_bool hcbody N
      exact ⟨n_bool + 1 + n_body, by omega, pc', σ_r, hn_prefix.trans hn_body⟩
    · -- Body terminates: iterate loop via N-induction
      obtain ⟨fuel₀, hne⟩ := Classical.not_forall.mp hbody_div
      obtain ⟨σ₁, hσ₁⟩ := Option.ne_none_iff_exists.mp hne
      have hσ₁ := hσ₁.symm
      -- Inner induction on N, universally quantifying σ and σ_tac
      suffices h_inner : ∀ N (σ' : Store) (σ_tac' : Store),
          (∀ fuel, (Stmt.loop b body).interp fuel σ' = none) →
          (∀ fuel, (Stmt.loop b body).divSafe fuel σ') →
          (∀ fuel, (Stmt.loop b body).intTyped fuel σ') →
          (∀ v, v.isTmp = false → σ_tac' v = σ' v) →
          ∃ n, n ≥ N ∧ ∃ pc' σ_r,
            RefStepsN p n (Cfg.run offset σ_tac') (Cfg.run pc' σ_r) from
        fun N => h_inner N σ σ_tac hdiv hsafe hintv hagree
      intro N
      induction N with
      | zero => intro σ' σ_tac' _ _ _ _; exact ⟨0, Nat.le.refl, offset, σ_tac', .refl⟩
      | succ N ihN =>
        intro σ' σ_tac' hdiv' hsafe' hintv' hagree'
        -- b.eval σ' = true
        have hb' : b.eval σ' = true := by
          cases hb' : b.eval σ' with
          | true => rfl
          | false => have h := hdiv' 1; unfold Stmt.interp at h; simp [hb'] at h
        have hbds' : SBool.divSafe σ' b := by
          have h := hsafe' 1; unfold Stmt.divSafe at h; simp [hb'] at h; exact h.1
        have hintv_b' : b.intTyped σ' := by
          have h := hintv' 1; unfold Stmt.intTyped at h; simp [hb'] at h; exact h.1
        -- Find a fuel where body terminates from σ'
        by_cases hbody_div' : ∀ fuel, body.interp fuel σ' = none
        · -- Body diverges from σ': use structural IH on body
          have hbody_safe' : ∀ fuel, body.divSafe fuel σ' := by
            intro fuel; have h := hsafe' (fuel + 1)
            unfold Stmt.divSafe at h; simp [hb'] at h; exact h.2.1
          have hbody_intv' : ∀ fuel, body.intTyped fuel σ' := by
            intro fuel; have h := hintv' (fuel + 1)
            unfold Stmt.intTyped at h; simp [hb'] at h; exact h.2.1
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
            refCompileBool_correct b offset nextTmp σ' σ_tac' p htf_b' hintv_b' hbds' hagree' hcb
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
              htf_body hbody_div' hbody_safe' hbody_intv' hagree_bool' hcbody' N
          exact ⟨n_bool' + 1 + n_body', by omega, pc', σ_r', hn_prefix'.trans hn_body'⟩
        · -- Body terminates from σ': one iteration + IH on N
          obtain ⟨fuel₁, hne'⟩ := Classical.not_forall.mp hbody_div'
          obtain ⟨σ₂, hσ₂⟩ := Option.ne_none_iff_exists.mp hne'
          have hσ₂ := hσ₂.symm
          have hds_body' : body.divSafe fuel₁ σ' := by
            have h := hsafe' (fuel₁ + 1); unfold Stmt.divSafe at h
            simp [hb'] at h; exact h.2.1
          have hintv_body' : body.intTyped fuel₁ σ' := by
            have h := hintv' (fuel₁ + 1); unfold Stmt.intTyped at h
            simp [hb'] at h; exact h.2.1
          obtain ⟨σ₂_tac, k_iter, hk_ge, hk_steps, hagree₂⟩ :=
            loop_one_iter b body fuel₁ σ' σ₂ offset nextTmp p σ_tac'
              htmpfree hb' hbds' hintv_b' hσ₂ hds_body' hintv_body' hagree' hcode
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
          have hintv₂ : ∀ fuel, (Stmt.loop b body).intTyped fuel σ₂ := by
            intro fuel
            have hbody_up := body.interp_fuel_mono fuel₁ (max fuel fuel₁ - fuel₁) σ' σ₂ hσ₂
            rw [show fuel₁ + (max fuel fuel₁ - fuel₁) = max fuel fuel₁ from by omega] at hbody_up
            have h := hintv' (max fuel fuel₁ + 1)
            have : (Stmt.loop b body).intTyped (max fuel fuel₁) σ₂ := by
              unfold Stmt.intTyped at h; simp [hb'] at h
              have := h.2.2; rw [hbody_up] at this; exact this
            exact (Stmt.loop b body).intTyped_of_le fuel (max fuel fuel₁) σ₂ this (by omega)
          obtain ⟨n', hn'_ge, pc', σ_r, hn'⟩ := ihN σ₂ σ₂_tac hdiv₂ hsafe₂ hintv₂ hagree₂
          exact ⟨k_iter + n', by omega, pc', σ_r, hk_steps.trans hn'⟩

/-- Top-level divergence: if the source diverges with division safety,
    the compiled program does not halt. -/
theorem refCompile_diverge (s : Stmt) (σ : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ)
    (hintv : ∀ fuel, s.intTyped fuel σ) :
    ¬ ∃ σ_tac, haltsWithResult (refCompile s) 0 σ σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  have hunbounded := refCompileStmt_diverges s σ 0 0 (refCompile s) σ
    htmpfree hdiv hsafe hintv (fun _ _ => rfl) hcode
  exact no_halt_of_unbounded hunbounded σ_tac hhalt

