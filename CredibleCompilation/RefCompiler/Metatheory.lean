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
  sorry
theorem Steps.to_RefStepsN {p : Prog} {c c' : Cfg}
    (h : p ⊩ c ⟶* c') : ∃ n, RefStepsN p n c c' := by
  sorry
private theorem refStepsN_cast {p : Prog} {n n' : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') (heq : n = n') : RefStepsN p n' c c' := heq ▸ h

theorem RefStepsN.trans {p : Prog} {n m : Nat} {c c' c'' : Cfg}
    (h₁ : RefStepsN p n c c') (h₂ : RefStepsN p m c' c'') :
    RefStepsN p (n + m) c c'' := by
  sorry
theorem RefStepsN.det_prefix {p : Prog} {n m : Nat} {c c₁ c₂ : Cfg}
    (h₁ : RefStepsN p n c c₁) (h₂ : RefStepsN p m c c₂) (hle : n ≤ m) :
    RefStepsN p (m - n) c₁ c₂ := by
  sorry
/-- A halted config cannot take a step in RefStepsN. -/
theorem RefStepsN.no_step_halt {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.halt σ _xam) c) : False := by
  sorry
/-- If execution takes unbounded steps through `run` configs, it cannot halt. -/
theorem no_halt_of_unbounded {p : Prog} {pc : Nat} {σ : Store}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ _xam) (Cfg.run pc' σ' _xam)) :
    ∀ σ' am am', ¬ haltsWithResult p pc σ σ' am am' := by
  sorry
-- ============================================================
-- § 18. Fuel monotonicity
-- ============================================================

/-- If the interpreter terminates at some fuel, it terminates with the same
    result at one more fuel. -/
theorem Stmt.interp_fuel_succ (s : Stmt) :
    ∀ fuel σ σ', s.interp fuel σ = some σ' → s.interp (fuel + 1) σ = some σ' := by
  sorry
/-- Fuel monotonicity: success at `fuel` implies success at `fuel + k`. -/
theorem Stmt.interp_fuel_mono (s : Stmt) (fuel k : Nat) (σ σ' : Store)
    (h : s.interp fuel σ = some σ') : s.interp (fuel + k) σ = some σ' := by
  sorry
/-- Contrapositive of fuel monotonicity: `none` at higher fuel implies `none`
    at lower fuel. -/
theorem Stmt.interp_none_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store)
    (h : s.interp fuel' σ = none) (hle : fuel ≤ fuel') : s.interp fuel σ = none := by
  sorry
-- ============================================================
-- § 19. divSafe anti-monotonicity
-- ============================================================

/-- `divSafe` at higher fuel implies `divSafe` at lower fuel. -/
theorem Stmt.divSafe_fuel_succ (s : Stmt) :
    ∀ fuel σ, s.divSafe (fuel + 1) σ → s.divSafe fuel σ := by
  sorry
theorem Stmt.divSafe_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store)
    (h : s.divSafe fuel' σ) (hle : fuel ≤ fuel') : s.divSafe fuel σ := by
  sorry
-- ============================================================
-- § 19b. intTyped anti-monotonicity
-- ============================================================

/-- `intTyped` at higher fuel implies `intTyped` at lower fuel. -/
theorem Stmt.intTyped_fuel_succ (s : Stmt) :
    ∀ fuel σ, s.intTyped (fuel + 1) σ → s.intTyped fuel σ := by
  sorry
theorem Stmt.intTyped_of_le (s : Stmt) (fuel fuel' : Nat) (σ : Store)
    (h : s.intTyped fuel' σ) (hle : fuel ≤ fuel') : s.intTyped fuel σ := by
  sorry
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
      RefStepsN p k (Cfg.run offset σ_tac _xam) (Cfg.run offset σ₁_tac _xam) ∧
      (∀ v, v.isTmp = false → σ₁_tac v = σ₁ v) := by
  sorry
/-- Main divergence: a divergent, div-safe statement produces unbounded steps. -/
theorem refCompileStmt_diverges (s : Stmt) (σ : Store)
    (offset nextTmp : Nat) (p : Prog) (σ_tac : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ)
    (hintv : ∀ fuel, s.intTyped fuel σ)
    (hagree : ∀ v, v.isTmp = false → σ_tac v = σ v)
    (hcode : CodeAt (refCompileStmt s offset nextTmp).1 p offset) :
    ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ', RefStepsN p n (Cfg.run offset σ_tac _xam) (Cfg.run pc' σ' _xam) := by
  sorry
/-- Top-level divergence: if the source diverges with division safety,
    the compiled program does not halt. -/
theorem refCompile_diverge (s : Stmt) (σ : Store)
    (htmpfree : s.tmpFree)
    (hdiv : ∀ fuel, s.interp fuel σ = none)
    (hsafe : ∀ fuel, s.divSafe fuel σ)
    (hintv : ∀ fuel, s.intTyped fuel σ) :
    ¬ ∃ σ_tac am am', haltsWithResult (refCompile s) 0 σ σ_tac am am' := by
  sorry
