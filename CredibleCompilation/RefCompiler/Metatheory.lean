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
    ∀ fuel σ am r, s.interp fuel σ am = some r → s.interp (fuel + 1) σ am = some r := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ =>
    intro _ _ _ _ h; simp_all [Stmt.interp]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am r h
    simp only [Stmt.interp.eq_5] at h ⊢
    cases h₁ : s₁.interp fuel σ am with
    | none => simp [h₁] at h
    | some val =>
      obtain ⟨σ₁, am₁⟩ := val
      simp [h₁] at h
      simp [ih₁ fuel σ am ⟨σ₁, am₁⟩ h₁]
      exact ih₂ fuel σ₁ am₁ r h
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am r h
    simp only [Stmt.interp.eq_6] at h ⊢
    split at h
    · rename_i hb; rw [if_pos hb]; exact ih₁ fuel σ am r h
    · rename_i hb; rw [if_neg hb]; exact ih₂ fuel σ am r h
  | loop b body ih_body =>
    intro fuel
    induction fuel with
    | zero => intro σ am r h; simp [Stmt.interp.eq_7] at h
    | succ fuel' ih_fuel =>
      intro σ am r h
      rw [Stmt.interp.eq_8] at h; rw [Stmt.interp.eq_8]
      by_cases hb : b.eval σ am = true
      · rw [if_pos hb] at h ⊢
        simp only [bind, Option.bind] at h ⊢
        cases hbody : body.interp fuel' σ am with
        | none => simp [hbody] at h
        | some val =>
          obtain ⟨σ₁, am₁⟩ := val
          simp only [hbody, Option.bind_some] at h
          simp only [ih_body fuel' σ am ⟨σ₁, am₁⟩ hbody, Option.bind_some]
          exact ih_fuel σ₁ am₁ r h
      · rw [if_neg hb] at h ⊢; exact h
/-- Fuel monotonicity: success at `fuel` implies success at `fuel + k`. -/
theorem Stmt.interp_fuel_mono (s : Stmt) (fuel k : Nat) (σ : Store) (am : ArrayMem)
    (r : Store × ArrayMem)
    (h : s.interp fuel σ am = some r) : s.interp (fuel + k) σ am = some r := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [show fuel + (k + 1) = (fuel + k) + 1 from by omega]; exact s.interp_fuel_succ _ _ _ _ ih
/-- Contrapositive of fuel monotonicity: `none` at higher fuel implies `none`
    at lower fuel. -/
theorem Stmt.interp_none_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (h : s.interp fuel' σ am = none) (hle : fuel ≤ fuel') : s.interp fuel σ am = none := by
  by_contra hc; push_neg at hc
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hc
  have := s.interp_fuel_mono fuel (fuel' - fuel) σ am r hr
  rw [show fuel + (fuel' - fuel) = fuel' from by omega] at this
  simp [this] at h
-- ============================================================
-- § 19. divSafe anti-monotonicity
-- ============================================================

/-- `divSafe` at higher fuel implies `divSafe` at lower fuel. -/
theorem Stmt.divSafe_fuel_succ (s : Stmt) :
    ∀ fuel σ am, s.divSafe (fuel + 1) σ am → s.divSafe fuel σ am := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ =>
    intro _ _ _ h; simp_all [Stmt.divSafe]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am h
    rw [Stmt.divSafe.eq_5] at h ⊢
    obtain ⟨hds₁, hds₂⟩ := h
    refine ⟨ih₁ fuel σ am hds₁, ?_⟩
    cases h₁ : s₁.interp fuel σ am with
    | none => trivial
    | some val =>
      obtain ⟨σ₁, am₁⟩ := val
      have h₁' := s₁.interp_fuel_succ fuel σ am ⟨σ₁, am₁⟩ h₁
      rw [h₁'] at hds₂; exact ih₂ fuel σ₁ am₁ hds₂
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am h
    rw [Stmt.divSafe.eq_6] at h ⊢
    obtain ⟨hb, hbranch⟩ := h
    refine ⟨hb, ?_⟩
    split at hbranch
    · rename_i hb; rw [if_pos hb]; exact ih₁ fuel σ am hbranch
    · rename_i hb; rw [if_neg hb]; exact ih₂ fuel σ am hbranch
  | loop b body ih_body =>
    intro fuel
    induction fuel with
    | zero => intro σ am _; simp [Stmt.divSafe.eq_7]
    | succ fuel' ih_fuel =>
      intro σ am h
      rw [Stmt.divSafe.eq_8] at h ⊢
      obtain ⟨hb, hbranch⟩ := h
      refine ⟨hb, ?_⟩
      by_cases hcond : b.eval σ am = true
      · rw [if_pos hcond] at hbranch ⊢
        obtain ⟨hds_body, hds_loop⟩ := hbranch
        refine ⟨ih_body fuel' σ am hds_body, ?_⟩
        cases hbody : body.interp fuel' σ am with
        | none => trivial
        | some val =>
          obtain ⟨σ₁, am₁⟩ := val
          have hbody' := body.interp_fuel_succ fuel' σ am ⟨σ₁, am₁⟩ hbody
          rw [hbody'] at hds_loop; exact ih_fuel σ₁ am₁ hds_loop
      · rw [if_neg hcond] at hbranch ⊢; exact hbranch
theorem Stmt.divSafe_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (h : s.divSafe fuel' σ am) (hle : fuel ≤ fuel') : s.divSafe fuel σ am := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    · exact s.divSafe_fuel_succ (fuel + k) σ am (by rwa [show fuel + (k + 1) = (fuel + k) + 1 from by omega] at h)
    · omega
-- ============================================================
-- § 19b. intTyped anti-monotonicity
-- ============================================================

/-- `intTyped` at higher fuel implies `intTyped` at lower fuel. -/
theorem Stmt.intTyped_fuel_succ (s : Stmt) :
    ∀ fuel σ am, s.intTyped (fuel + 1) σ am → s.intTyped fuel σ am := by
  induction s with
  | skip | assign _ _ | bassign _ _ | arrWrite _ _ _ =>
    intro _ _ _ h; simp_all [Stmt.intTyped]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am h
    rw [Stmt.intTyped.eq_5] at h ⊢
    obtain ⟨hit₁, hit₂⟩ := h
    refine ⟨ih₁ fuel σ am hit₁, ?_⟩
    cases h₁ : s₁.interp fuel σ am with
    | none => trivial
    | some val =>
      obtain ⟨σ₁, am₁⟩ := val
      have h₁' := s₁.interp_fuel_succ fuel σ am ⟨σ₁, am₁⟩ h₁
      rw [h₁'] at hit₂; exact ih₂ fuel σ₁ am₁ hit₂
  | ite b s₁ s₂ ih₁ ih₂ =>
    intro fuel σ am h
    rw [Stmt.intTyped.eq_6] at h ⊢
    obtain ⟨hb, hbranch⟩ := h
    refine ⟨hb, ?_⟩
    split at hbranch
    · rename_i hcond; rw [if_pos hcond]; exact ih₁ fuel σ am hbranch
    · rename_i hcond; rw [if_neg hcond]; exact ih₂ fuel σ am hbranch
  | loop b body ih_body =>
    intro fuel
    induction fuel with
    | zero => intro σ am _; simp [Stmt.intTyped.eq_7]
    | succ fuel' ih_fuel =>
      intro σ am h
      rw [Stmt.intTyped.eq_8] at h ⊢
      obtain ⟨hb, hbranch⟩ := h
      refine ⟨hb, ?_⟩
      by_cases hcond : b.eval σ am = true
      · rw [if_pos hcond] at hbranch ⊢
        obtain ⟨hit_body, hit_loop⟩ := hbranch
        refine ⟨ih_body fuel' σ am hit_body, ?_⟩
        cases hbody : body.interp fuel' σ am with
        | none => trivial
        | some val =>
          obtain ⟨σ₁, am₁⟩ := val
          have hbody' := body.interp_fuel_succ fuel' σ am ⟨σ₁, am₁⟩ hbody
          rw [hbody'] at hit_loop; exact ih_fuel σ₁ am₁ hit_loop
      · rw [if_neg hcond] at hbranch ⊢; exact hbranch
theorem Stmt.intTyped_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store) (am : ArrayMem)
    (h : s.intTyped fuel' σ am) (hle : fuel ≤ fuel') : s.intTyped fuel σ am := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih =>
    apply ih
    · exact s.intTyped_fuel_succ (fuel + k) σ am (by rwa [show fuel + (k + 1) = (fuel + k) + 1 from by omega] at h)
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
    (hb : b.eval σ am = true)
    (hbds : SBool.divSafe σ am b)
    (hintv_b : b.intTyped σ)
    (hbody_res : body.interp fuel₀ σ am = some (σ₁, am₁))
    (hds_body : body.divSafe fuel₀ σ am)
    (hintv_body : body.intTyped fuel₀ σ am)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt (.loop b body) offset nextTmp).1 p offset) :
    ∃ σ₁_tac k,
      RefStepsN p k (Cfg.run offset σ_tac am) (Cfg.run offset σ₁_tac am₁) ∧
      (∀ v, v.isTmp = false → σ₁_tac v = σ₁ v) ∧ 1 ≤ k := by
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
  have htf_body : body.tmpFree :=
    fun v hv => htmpfree v (List.mem_append_right _ hv)
  have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
    rw [hrcb]; exact hcode.left.left.left
  -- Step 1: Execute bool
  obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
    refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
  rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
  have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
    intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
      σ_bool hbody_res htf_body hds_body hintv_body hagree_bool hcbody
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
/-- Main divergence: a divergent, div-safe statement produces unbounded steps. -/
theorem refCompileStmt_diverges (s : Stmt) (σ : Store) (am : ArrayMem)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ am = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ am)
    (hintv : ∀ fuel, s.intTyped fuel σ am)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') := by
  induction s generalizing σ am offset nextTmp p σ_tac with
  | skip => intro _; exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | assign _ _ => intro _; exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | bassign _ _ => intro _; exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | arrWrite _ _ _ => intro _; exfalso; have := hdiv 0; simp [Stmt.interp] at this
  | seq s₁ s₂ ih₁ ih₂ =>
    intro N
    -- Either s₁ diverges, or s₁ terminates and s₂ diverges
    by_cases hdiv₁ : ∀ fuel, s₁.interp fuel σ am = none
    · -- s₁ diverges: use ih₁ to get unbounded steps from s₁'s compiled code
      have hds₁ : ∀ fuel, s₁.divSafe fuel σ am := by intro f; have := hsafe f; simp [Stmt.divSafe] at this; exact this.1
      have hintv₁ : ∀ fuel, s₁.intTyped fuel σ am := by intro f; have := hintv f; simp [Stmt.intTyped] at this; exact this.1
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      dsimp only [refCompileStmt] at hcode ⊢
      generalize hrc1 : refCompileStmt s₁ offset nextTmp = rc1 at hcode ⊢
      obtain ⟨code1, tmp1⟩ := rc1
      generalize hrc2 : refCompileStmt s₂ (offset + code1.length) tmp1 = rc2 at hcode ⊢
      obtain ⟨code2, tmp2⟩ := rc2
      simp only [] at hcode ⊢
      have hcode1 : CodeAt (refCompileStmt s₁ offset nextTmp).1 p offset := by
        rw [hrc1]; exact hcode.left
      have := ih₁ σ am offset nextTmp p σ_tac htf₁ hdiv₁ hds₁ hintv₁ hagree hcode1 N
      obtain ⟨n, hn, pc', σ', am', hsteps⟩ := this
      exact ⟨n, hn, pc', σ', am', hsteps⟩
    · -- s₁ terminates at some fuel → s₂ diverges
      push_neg at hdiv₁
      obtain ⟨fuel₁, hf₁⟩ := hdiv₁
      obtain ⟨r₁, hr₁⟩ := Option.ne_none_iff_exists'.mp hf₁
      obtain ⟨σ₁, am₁⟩ := r₁
      -- s₂ must diverge from σ₁, am₁
      have hdiv₂ : ∀ fuel, s₂.interp fuel σ₁ am₁ = none := by
        intro f
        have hseq := hdiv (max fuel₁ f)
        simp only [Stmt.interp.eq_5] at hseq
        have hterm := s₁.interp_fuel_mono fuel₁ (max fuel₁ f - fuel₁) σ am ⟨σ₁, am₁⟩ hr₁
        rw [show fuel₁ + (max fuel₁ f - fuel₁) = max fuel₁ f from by omega] at hterm
        simp only [hterm] at hseq
        exact s₂.interp_none_of_le f (max fuel₁ f) σ₁ am₁ hseq (by omega)
      have htf₁ : s₁.tmpFree := fun v hv => htmpfree v (List.mem_append_left _ hv)
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      have hds₁ : s₁.divSafe fuel₁ σ am := by have := hsafe fuel₁; simp [Stmt.divSafe] at this; exact this.1
      have hintv₁ : s₁.intTyped fuel₁ σ am := by have := hintv fuel₁; simp [Stmt.intTyped] at this; exact this.1
      have hds₂ : ∀ f, s₂.divSafe f σ₁ am₁ := by
        intro f
        have hsf := hsafe (max fuel₁ f)
        simp only [Stmt.divSafe.eq_5] at hsf
        have hterm := s₁.interp_fuel_mono fuel₁ (max fuel₁ f - fuel₁) σ am ⟨σ₁, am₁⟩ hr₁
        rw [show fuel₁ + (max fuel₁ f - fuel₁) = max fuel₁ f from by omega] at hterm
        rw [hterm] at hsf
        exact Stmt.divSafe_of_le _ f _ σ₁ am₁ hsf.2 (by omega)
      have hintv₂ : ∀ f, s₂.intTyped f σ₁ am₁ := by
        intro f
        have hif := hintv (max fuel₁ f)
        simp only [Stmt.intTyped.eq_5] at hif
        have hterm := s₁.interp_fuel_mono fuel₁ (max fuel₁ f - fuel₁) σ am ⟨σ₁, am₁⟩ hr₁
        rw [show fuel₁ + (max fuel₁ f - fuel₁) = max fuel₁ f from by omega] at hterm
        rw [hterm] at hif
        exact Stmt.intTyped_of_le _ f _ σ₁ am₁ hif.2 (by omega)
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
        refCompileStmt_correct s₁ fuel₁ σ σ₁ am am₁ offset nextTmp p σ_tac hr₁ htf₁ hds₁ hintv₁ hagree hcode1
      rw [hrc1] at hexec₁; simp at hexec₁
      obtain ⟨k₁, hk₁⟩ := hexec₁.to_RefStepsN
      have := ih₂ σ₁ am₁ (offset + code1.length) tmp1 p σ₁_tac htf₂ hdiv₂ hds₂ hintv₂ hagree₁ hcode2 N
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
    have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
      rw [hrcb]; exact hcode.left.left.left.left
    cases hb : b.eval σ am with
    | true =>
      -- s₁ diverges
      have hdiv₁ : ∀ fuel, s₁.interp fuel σ am = none := by
        intro f; have := hdiv f; simp only [Stmt.interp, hb] at this; exact this
      have hbds : SBool.divSafe σ am b := by
        have := hsafe 1; simp only [Stmt.divSafe, hb] at this; exact this.1
      have hintv_b : b.intTyped σ := by
        have := hintv 1; simp only [Stmt.intTyped, hb] at this; exact this.1
      have hds₁ : ∀ f, s₁.divSafe f σ am := by
        intro f; have := hsafe f; simp only [Stmt.divSafe, hb] at this; exact this.2
      have hintv₁ : ∀ f, s₁.intTyped f σ am := by
        intro f; have := hintv f; simp only [Stmt.intTyped, hb] at this; exact this.2
      have htf₁ : s₁.tmpFree :=
        fun v hv => htmpfree v (List.mem_append_left _ (List.mem_append_right _ hv))
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
        htf₁ hdiv₁ hds₁ hintv₁ hagree_bool hct N
      obtain ⟨n₁, hn₁, pc', σ', am', hsteps₁⟩ := this
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      exact ⟨k_pre + n₁, by omega, pc', σ', am', RefStepsN.trans hk_pre hsteps₁⟩
    | false =>
      -- s₂ diverges
      have hdiv₂ : ∀ fuel, s₂.interp fuel σ am = none := by
        intro f; have := hdiv f; simp only [Stmt.interp, hb, Bool.false_eq_true, ite_false] at this; exact this
      have hbds : SBool.divSafe σ am b := by
        have := hsafe 1; simp only [Stmt.divSafe, hb] at this; exact this.1
      have hintv_b : b.intTyped σ := by
        have := hintv 1; simp only [Stmt.intTyped, hb] at this; exact this.1
      have hds₂ : ∀ f, s₂.divSafe f σ am := by
        intro f; have := hsafe f; simp only [Stmt.divSafe, hb, Bool.false_eq_true, ite_false] at this; exact this.2
      have hintv₂ : ∀ f, s₂.intTyped f σ am := by
        intro f; have := hintv f; simp only [Stmt.intTyped, hb, Bool.false_eq_true, ite_false] at this; exact this.2
      have htf₂ : s₂.tmpFree := fun v hv => htmpfree v (List.mem_append_right _ hv)
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ σ_tac am p htf_b hintv_b hbds hagree hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree v hv
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
        htf₂ hdiv₂ hds₂ hintv₂ hagree_bool hce N
      obtain ⟨n₂, hn₂, pc', σ', am', hsteps₂⟩ := this
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      exact ⟨k_pre + n₂, by omega, pc', σ', am', RefStepsN.trans hk_pre hsteps₂⟩
  | loop b body ih =>
    intro N
    -- Helper: extract body divergence proof to get unbounded steps
    have body_div_case : ∀ (σ_cur : Store) (am_cur : ArrayMem) (σ_tac_cur : Store) (n₀ : Nat),
        (∀ f, (Stmt.loop b body).interp f σ_cur am_cur = none) →
        (∀ f, (Stmt.loop b body).divSafe f σ_cur am_cur) →
        (∀ f, (Stmt.loop b body).intTyped f σ_cur am_cur) →
        (Stmt.loop b body).tmpFree →
        (∀ v, v.isTmp = false → σ_tac_cur v = σ_cur v) →
        b.eval σ_cur am_cur = true →
        (∀ f, body.interp f σ_cur am_cur = none) →
        RefStepsN p n₀ (Cfg.run offset σ_tac am) (Cfg.run offset σ_tac_cur am_cur) →
        ∀ M, ∃ n, n ≥ M ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') := by
      intro σ_cur am_cur σ_tac_cur n₀ hdiv_cur hsafe_cur hintv_cur htf_cur hagree_cur hb hbody_div hsteps_cur M
      have hds_body : ∀ f, body.divSafe f σ_cur am_cur := by
        intro f; have := hsafe_cur (f + 1); unfold Stmt.divSafe at this; simp [hb] at this; exact this.2.1
      have hintv_body : ∀ f, body.intTyped f σ_cur am_cur := by
        intro f; have := hintv_cur (f + 1); unfold Stmt.intTyped at this; simp [hb] at this; exact this.2.1
      have htf_body : body.tmpFree := fun v hv => htf_cur v (List.mem_append_right _ hv)
      dsimp only [refCompileStmt] at hcode
      generalize hrcb : refCompileBool b offset nextTmp = rcb at hcode
      obtain ⟨codeBool, be, tmpB⟩ := rcb
      generalize hrcbody : refCompileStmt body (offset + codeBool.length + 1) tmpB = rcbody at hcode
      obtain ⟨codeBody, tmpBody⟩ := rcbody
      simp only [] at hcode
      have htf_b : ∀ v ∈ b.freeVars, v.isTmp = false :=
        fun v hv => htf_cur v (List.mem_append_left _ hv)
      have hbds_b : SBool.divSafe σ_cur am_cur b := by
        have := hsafe_cur 1; unfold Stmt.divSafe at this; simp [hb] at this; exact this.1
      have hintv_b : b.intTyped σ_cur := by
        have := hintv_cur 1; unfold Stmt.intTyped at this; simp [hb] at this; exact this.1
      have hcb : CodeAt (refCompileBool b offset nextTmp).1 p offset := by
        rw [hrcb]; exact hcode.left.left.left
      obtain ⟨σ_bool, hexec_bool, heval_bool, hntmp_bool, _⟩ :=
        refCompileBool_correct b offset nextTmp σ_cur σ_tac_cur am_cur p htf_b hintv_b hbds_b hagree_cur hcb
      rw [hrcb] at hexec_bool heval_bool; simp at hexec_bool heval_bool
      have hagree_bool : ∀ v, v.isTmp = false → σ_bool v = σ_cur v := by
        intro v hv; rw [hntmp_bool v hv]; exact hagree_cur v hv
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
        htf_body hbody_div hds_body hintv_body hagree_bool hcbody M
      obtain ⟨n_body, hn_body, pc', σ', am', hsteps_body⟩ := this
      obtain ⟨k_pre, hk_pre⟩ := (FragExec.trans' hexec_bool hexec_if).to_RefStepsN
      have hsteps_total := RefStepsN.trans hsteps_cur (RefStepsN.trans hk_pre hsteps_body)
      exact ⟨n₀ + (k_pre + n_body), by omega, pc', σ', am',
        hsteps_total⟩
    -- Main proof: strong induction on (N - n₀). Each iteration adds ≥ 1 step.
    -- Either body diverges (handled by body_div_case) or we iterate via loop_one_iter.
    suffices h : ∀ (gap : Nat) (σ_cur : Store) (am_cur : ArrayMem) (σ_tac_cur : Store) (n₀ : Nat),
        N - n₀ ≤ gap →
        (∀ f, (Stmt.loop b body).interp f σ_cur am_cur = none) →
        (∀ f, (Stmt.loop b body).divSafe f σ_cur am_cur) →
        (∀ f, (Stmt.loop b body).intTyped f σ_cur am_cur) →
        (Stmt.loop b body).tmpFree →
        (∀ v, v.isTmp = false → σ_tac_cur v = σ_cur v) →
        RefStepsN p n₀ (Cfg.run offset σ_tac am) (Cfg.run offset σ_tac_cur am_cur) →
        ∃ n, n ≥ N ∧ ∃ pc' σ' am', RefStepsN p n (Cfg.run offset σ_tac am) (Cfg.run pc' σ' am') by
      exact h N σ am σ_tac 0 (by omega) hdiv hsafe hintv htmpfree hagree .refl
    intro gap; induction gap with
    | zero =>
      intro σ_cur am_cur σ_tac_cur n₀ hgap _ _ _ _ _ hsteps_cur
      exact ⟨n₀, by omega, offset, σ_tac_cur, am_cur, hsteps_cur⟩
    | succ gap' ihgap =>
      intro σ_cur am_cur σ_tac_cur n₀ hgap hdiv_cur hsafe_cur hintv_cur htf_cur hagree_cur hsteps_cur
      by_cases hn : n₀ ≥ N
      · exact ⟨n₀, hn, offset, σ_tac_cur, am_cur, hsteps_cur⟩
      · have hb : b.eval σ_cur am_cur = true := by
          by_contra hc; push_neg at hc
          have := hdiv_cur 1; simp [Stmt.interp, Bool.eq_false_iff.mpr hc] at this
        by_cases hbody_div : ∀ f, body.interp f σ_cur am_cur = none
        · exact body_div_case σ_cur am_cur σ_tac_cur n₀ hdiv_cur hsafe_cur hintv_cur htf_cur
            hagree_cur hb hbody_div hsteps_cur N
        · push_neg at hbody_div
          obtain ⟨f₀, hf₀⟩ := hbody_div
          obtain ⟨r₁, hr₁⟩ := Option.ne_none_iff_exists'.mp hf₀
          obtain ⟨σ₁, am₁⟩ := r₁
          have hbds : SBool.divSafe σ_cur am_cur b := by
            have := hsafe_cur (f₀ + 1); simp only [Stmt.divSafe, hb] at this; exact this.1
          have hds_body : body.divSafe f₀ σ_cur am_cur := by
            have := hsafe_cur (f₀ + 1); simp only [Stmt.divSafe, hb] at this; exact this.2.1
          have hintv_b : b.intTyped σ_cur := by
            have := hintv_cur (f₀ + 1); simp only [Stmt.intTyped, hb] at this; exact this.1
          have hintv_body : body.intTyped f₀ σ_cur am_cur := by
            have := hintv_cur (f₀ + 1); simp only [Stmt.intTyped, hb] at this; exact this.2.1
          obtain ⟨σ₁_tac, k, hsteps_iter, hagree₁, hk1⟩ :=
            loop_one_iter b body f₀ σ_cur σ₁ am_cur am₁ offset nextTmp p σ_tac_cur
              htf_cur hb hbds hintv_b hr₁ hds_body hintv_body hagree_cur hcode
          have hdiv₁ : ∀ f, (Stmt.loop b body).interp f σ₁ am₁ = none := by
            intro f
            by_contra hc; push_neg at hc
            obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.mp hc
            have hsome := (Stmt.loop b body).interp_fuel_mono f f₀ σ₁ am₁ r' hr'
            have hloop := hdiv_cur (f + f₀ + 1)
            simp only [Stmt.interp, hb, ite_true] at hloop
            have hbm : body.interp (f + f₀) σ_cur am_cur = some (σ₁, am₁) := by
              have := body.interp_fuel_mono f₀ f σ_cur am_cur ⟨σ₁, am₁⟩ hr₁; rwa [Nat.add_comm] at this
            simp only [hbm] at hloop
            change Stmt.interp (f + f₀) σ₁ am₁ (Stmt.loop b body) = none at hloop
            simp [hloop] at hsome
          have hsafe₁ : ∀ f, (Stmt.loop b body).divSafe f σ₁ am₁ := by
            intro f; have hsf := hsafe_cur (f + f₀ + 1)
            unfold Stmt.divSafe at hsf; simp only [hb, ite_true] at hsf
            have hbm := body.interp_fuel_mono f₀ (f + f₀ + 1 - (f₀ + 1)) σ_cur am_cur ⟨σ₁, am₁⟩ hr₁
            rw [show f₀ + (f + f₀ + 1 - (f₀ + 1)) = f + f₀ from by omega] at hbm
            rw [hbm] at hsf; exact Stmt.divSafe_of_le _ f _ σ₁ am₁ hsf.2.2 (by omega)
          have hintv₁ : ∀ f, (Stmt.loop b body).intTyped f σ₁ am₁ := by
            intro f; have hif := hintv_cur (f + f₀ + 1)
            unfold Stmt.intTyped at hif; simp only [hb, ite_true] at hif
            have hbm := body.interp_fuel_mono f₀ (f + f₀ + 1 - (f₀ + 1)) σ_cur am_cur ⟨σ₁, am₁⟩ hr₁
            rw [show f₀ + (f + f₀ + 1 - (f₀ + 1)) = f + f₀ from by omega] at hbm
            rw [hbm] at hif; exact Stmt.intTyped_of_le _ f _ σ₁ am₁ hif.2.2 (by omega)
          have hsteps_total := RefStepsN.trans hsteps_cur hsteps_iter
          exact ihgap σ₁ am₁ σ₁_tac (n₀ + k) (by omega) hdiv₁ hsafe₁ hintv₁ htf_cur hagree₁ hsteps_total
/-- Top-level divergence: if the source diverges with division safety,
    the compiled program does not halt. -/
theorem refCompile_diverge (s : Stmt) (σ : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ ArrayMem.init = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ ArrayMem.init)
    (hintv : ∀ fuel, s.intTyped fuel σ ArrayMem.init) :
    ∀ σ_tac am', ¬ haltsWithResult (refCompile s) 0 σ σ_tac ArrayMem.init am' := by
  have hcode : CodeAt (refCompileStmt s 0 0).1 (refCompile s) 0 := by
    intro i hi; unfold refCompile; simp only [Prog.ofCode, Prog.getElem?_code, List.getElem?_toArray, Nat.zero_add]
    exact List.getElem?_append_left hi
  have hunbounded := refCompileStmt_diverges s σ ArrayMem.init 0 0 (refCompile s) σ
    htmpfree hdiv hsafe hintv (fun _ _ => rfl) hcode
  exact no_halt_of_unbounded_am hunbounded
