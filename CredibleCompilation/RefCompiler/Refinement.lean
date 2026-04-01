import CredibleCompilation.RefCompiler.Metatheory

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

/-!
# Reference Compiler: Refinement

Bridge between compileStmt and refCompileStmt, and full program-level
backward refinement theorem.
-/

-- ============================================================
-- § 12. Bridge: compileStmt = refCompileStmt
-- ============================================================

theorem compileExpr_eq_refCompileExpr (e : SExpr) (o t : Nat) :
    compileExpr e o t = refCompileExpr e o t := by
  induction e generalizing o t with
  | lit _ => rfl
  | var _ => rfl
  | bin _ a b iha ihb => simp only [compileExpr, refCompileExpr, iha, ihb]

theorem compileBool_eq_refCompileBool (b : SBool) (o t : Nat) :
    compileBool b o t = refCompileBool b o t := by
  induction b generalizing o t with
  | lit _ => rfl
  | bvar _ => rfl
  | cmp _ a b => simp only [compileBool, refCompileBool, compileExpr_eq_refCompileExpr]
  | not _ ih => simp only [compileBool, refCompileBool, ih]
  | and a b iha ihb =>
    simp only [compileBool, refCompileBool, iha, ihb]
  | or a b iha ihb =>
    simp only [compileBool, refCompileBool, iha, ihb]

theorem compileStmt_eq_refCompileStmt (s : Stmt) (o t : Nat) :
    compileStmt s o t = refCompileStmt s o t := by
  induction s generalizing o t with
  | skip => rfl
  | assign x e =>
    cases e with
    | lit _ => rfl
    | var _ => rfl
    | bin _ a b => simp only [compileStmt, refCompileStmt, compileExpr_eq_refCompileExpr]
  | bassign _ b => simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool]
  | seq _ _ ih1 ih2 => simp only [compileStmt, refCompileStmt, ih1, ih2]
  | ite _ _ _ ih1 ih2 =>
    simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool, ih1, ih2]
  | loop _ _ ih =>
    simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool, ih]

-- ============================================================
-- § 16. Refinement for Program.compile (with init code)
-- ============================================================

-- ============================================================
-- § 13. Helpers for backward refinement
-- ============================================================

/-- Source interpreter returns `none` iff it doesn't return `some`. -/
private theorem interp_none_iff (s : Stmt) (fuel : Nat) (σ : Store) :
    s.interp fuel σ = none ↔ ¬ ∃ σ', s.interp fuel σ = some σ' := by
  constructor
  · intro h ⟨σ', hσ'⟩; simp [h] at hσ'
  · intro h; cases hq : s.interp fuel σ with
    | none => rfl
    | some σ' => exact absurd ⟨σ', hq⟩ h

/-- No steps from error: error is a terminal configuration. -/
private theorem RefStepsN.no_step_error {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.error σ) c) : False := by
  cases h with | step s _ => exact Step.no_step_from_error s

/-- If execution takes unbounded steps through `run` configs, it cannot error. -/
theorem no_error_of_unbounded {p : Prog} {pc : Nat} {σ : Store}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ) (Cfg.run pc' σ')) :
    ∀ σ', ¬ (p ⊩ Cfg.run pc σ ⟶* Cfg.error σ') := by
  intro σ' herr
  obtain ⟨k, hk⟩ := herr.to_RefStepsN
  obtain ⟨n, hn_ge, pc', σ_r, hn⟩ := hunbounded (k + 1)
  have hpref := RefStepsN.det_prefix hk hn (by omega)
  have : ∃ d, n - k = d + 1 := ⟨n - k - 1, by omega⟩
  obtain ⟨d, hd⟩ := this
  rw [hd] at hpref
  exact RefStepsN.no_step_error hpref

/-- Extract `StepsN` from an `IsInfiniteExec`: the first `n` steps of an
    infinite execution give a deterministic `n`-step path. -/
private theorem inf_exec_to_StepsN {p : Prog} {f : Nat → Cfg}
    (hinf : IsInfiniteExec p f) :
    ∀ n, StepsN p (f 0) (f n) n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => exact StepsN_trans ih ⟨f (n + 1), hinf.2 n, rfl⟩

-- ============================================================
-- § 14. Refinement for Program.compile (with init code)
-- ============================================================

/-- The body code from `compileStmt` (= `refCompileStmt`) is embedded in `prog.compile`
    starting at offset `prog.decls.length`. -/
private theorem progCompile_body_codeAt (prog : Program) :
    CodeAt (refCompileStmt prog.body prog.decls.length 0).1
      prog.compile prog.decls.length := by
  rw [← compileStmt_eq_refCompileStmt]
  intro i hi
  open Program in exact compile_body_getElem prog i hi

/-- **Forward halt** for `prog.compile`: if the source terminates safely,
    `prog.compile` halts with a matching store. -/
theorem progCompile_halt (prog : Program) (fuel : Nat) (σ' : Store)
    (htc : prog.typeCheck = true)
    (hinterp : prog.body.interp fuel prog.initStore = some σ')
    (hsafe : prog.body.divSafe fuel prog.initStore) :
    ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  have hnd := prog.typeCheck_noDups htc
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore hts fuel
  have hcode := progCompile_body_codeAt prog
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    refCompileStmt_correct prog.body fuel prog.initStore σ' prog.decls.length 0
      prog.compile prog.initStore hinterp htmpfree hsafe hintv (fun _ _ => rfl) hcode
  have hinit := open Program in compile_initExec prog hnd
  have hhalt_instr := open Program in compile_halt_getElem prog
  rw [compileStmt_eq_refCompileStmt] at hhalt_instr
  have hfull : FragExec prog.compile 0 prog.initStore
      (prog.decls.length + (refCompileStmt prog.body prog.decls.length 0).1.length)
      σ_tac :=
    FragExec.trans' hinit hexec
  exact ⟨σ_tac, FragExec.toHalt hfull hhalt_instr, hagree⟩

/-- **Forward error** for `prog.compile`: if `¬divSafe`, the compiled program
    cannot halt (it reaches an error). -/
theorem progCompile_no_halt_unsafe (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hnd := prog.typeCheck_noDups htc
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore hts fuel
  have hcode := progCompile_body_codeAt prog
  obtain ⟨pc_s, σ_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe prog.body fuel prog.initStore prog.decls.length 0
      prog.compile prog.initStore htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  have hinit := open Program in compile_initExec prog hnd
  have hfull : prog.compile ⊩ Cfg.run 0 prog.initStore ⟶* Cfg.run pc_s σ_s :=
    FragExec.trans' hinit hfrag
  have herr_reach : prog.compile ⊩ Cfg.run 0 prog.initStore ⟶* Cfg.error σ_s :=
    Steps.trans hfull (Steps.step herror Steps.refl)
  have halt_terminal : ∀ d, ¬ Step prog.compile (Cfg.halt σ_tac) d :=
    fun _ h => Step.no_step_from_halt h
  have err_terminal : ∀ d, ¬ Step prog.compile (Cfg.error σ_s) d :=
    fun _ h => Step.no_step_from_error h
  exact Cfg.noConfusion (Steps.stuck_det hhalt herr_reach halt_terminal err_terminal)

/-- **Forward error reachability** for `prog.compile`: if `¬divSafe`, the
    compiled program reaches an error state. -/
theorem progCompile_reaches_error (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore) :
    ∃ σ_e, prog.compile ⊩ Cfg.run 0 prog.initStore ⟶* Cfg.error σ_e := by
  have hnd := prog.typeCheck_noDups htc
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore hts fuel
  have hcode := progCompile_body_codeAt prog
  obtain ⟨pc_s, σ_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe prog.body fuel prog.initStore prog.decls.length 0
      prog.compile prog.initStore htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  have hinit := open Program in compile_initExec prog hnd
  exact ⟨σ_s, Steps.trans (FragExec.trans' hinit hfrag) (Steps.step herror Steps.refl)⟩

/-- **Forward no-halt for safe divergence** in `prog.compile`: if the source
    diverges safely, the compiled program doesn't halt. -/
theorem progCompile_no_halt_diverge (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore = none)
    (hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac := by
  intro ⟨σ_tac, hhalt⟩
  have hnd := prog.typeCheck_noDups htc
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := fun fuel => Program.typeCheck_intTyped prog htc prog.initStore hts fuel
  have hcode := progCompile_body_codeAt prog
  have hunbounded := refCompileStmt_diverges prog.body prog.initStore prog.decls.length 0
    prog.compile prog.initStore htmpfree hdiv hsafe hintv (fun _ _ => rfl) hcode
  -- Shift unbounded to PC 0 using init exec
  have hinit := open Program in compile_initExec prog hnd
  have hunb0 : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN prog.compile n (Cfg.run 0 prog.initStore) (Cfg.run pc' σ') := by
    intro N
    obtain ⟨n, hn_ge, pc', σ', hn⟩ := hunbounded N
    obtain ⟨k, hk⟩ := hinit.to_RefStepsN
    exact ⟨k + n, by omega, pc', σ', RefStepsN.trans hk hn⟩
  exact no_halt_of_unbounded hunb0 σ_tac hhalt

/-- **Forward no-halt for unsafe divergence** in `prog.compile`. -/
private theorem progCompile_no_halt_diverge_unsafe (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore = none) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac := by
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hnd := prog.typeCheck_noDups htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := fun fuel => Program.typeCheck_intTyped prog htc prog.initStore hts fuel
  by_cases hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore
  · exact progCompile_no_halt_diverge prog htc hdiv hsafe
  · obtain ⟨fuel₀, hunsafe⟩ := Classical.not_forall.mp hsafe
    exact progCompile_no_halt_unsafe prog fuel₀ htc hunsafe

/-- **Full backward refinement for `Program.compile`**: For every behavior of
    the compiled program (with init code), the source program has a
    corresponding behavior.
    - TAC halts with σ_tac → source terminates with agreeing σ'
    - TAC errors → source has an unsafe division
    - TAC diverges → source diverges -/
theorem program_refinement (prog : Program) (htc : prog.typeCheck = true) (b : Behavior)
    (hbeh : program_behavior prog.compile prog.initStore b) :
    match b with
    | .halts σ_tac => ∃ fuel σ', prog.interp fuel = some σ' ∧
        ∀ v, v.isTmp = false → σ_tac v = σ' v
    | .errors _ => ∃ fuel, ¬ prog.body.divSafe fuel prog.initStore
    | .typeErrors _ => False
    | .diverges => ∀ fuel, prog.interp fuel = none := by
  have hnd := prog.typeCheck_noDups htc
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := fun fuel => Program.typeCheck_intTyped prog htc prog.initStore hts fuel
  cases b with
  | halts σ_tac =>
    -- hbeh : haltsWithResult prog.compile 0 prog.initStore σ_tac
    by_cases hterm : ∃ fuel σ', prog.body.interp fuel prog.initStore = some σ'
    · obtain ⟨fuel, σ', hinterp⟩ := hterm
      by_cases hsafe : prog.body.divSafe fuel prog.initStore
      · obtain ⟨σ_tac', hhalt', hagree⟩ := progCompile_halt prog fuel σ' htc hinterp hsafe
        have : σ_tac = σ_tac' := haltsWithResult_unique hbeh hhalt'
        subst this
        exact ⟨fuel, σ', hinterp, hagree⟩
      · exact absurd ⟨σ_tac, hbeh⟩ (progCompile_no_halt_unsafe prog fuel htc hsafe)
    · have hdiv : ∀ fuel, prog.body.interp fuel prog.initStore = none :=
        fun fuel => (interp_none_iff _ _ _).mpr (fun ⟨σ', h⟩ => hterm ⟨fuel, σ', h⟩)
      exact absurd ⟨σ_tac, hbeh⟩ (progCompile_no_halt_diverge_unsafe prog htc hdiv)
  | errors σ_e =>
    -- hbeh : prog.compile ⊩ Cfg.run 0 prog.initStore ⟶* Cfg.error σ_e
    by_cases h : ∀ fuel, prog.body.divSafe fuel prog.initStore
    · exfalso
      by_cases hterm : ∃ fuel σ', prog.body.interp fuel prog.initStore = some σ'
      · obtain ⟨fuel, σ', hinterp⟩ := hterm
        obtain ⟨σ_tac, hhalt, _⟩ := progCompile_halt prog fuel σ' htc hinterp (h fuel)
        have halt_terminal : ∀ d, ¬ Step prog.compile (Cfg.halt σ_tac) d :=
          fun _ h => Step.no_step_from_halt h
        have err_terminal : ∀ d, ¬ Step prog.compile (Cfg.error σ_e) d :=
          fun _ h => Step.no_step_from_error h
        exact Cfg.noConfusion (Steps.stuck_det hhalt hbeh halt_terminal err_terminal)
      · have hdiv : ∀ fuel, prog.body.interp fuel prog.initStore = none :=
          fun fuel => (interp_none_iff _ _ _).mpr (fun ⟨σ', hq⟩ => hterm ⟨fuel, σ', hq⟩)
        have hcode := progCompile_body_codeAt prog
        have hunbounded := refCompileStmt_diverges prog.body prog.initStore
          prog.decls.length 0 prog.compile prog.initStore htmpfree hdiv h hintv
          (fun _ _ => rfl) hcode
        have hinit := open Program in compile_initExec prog hnd
        have hunb0 : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
            RefStepsN prog.compile n (Cfg.run 0 prog.initStore) (Cfg.run pc' σ') := by
          intro N
          obtain ⟨n, hn_ge, pc', σ', hn⟩ := hunbounded N
          obtain ⟨k, hk⟩ := hinit.to_RefStepsN
          exact ⟨k + n, by omega, pc', σ', RefStepsN.trans hk hn⟩
        exact no_error_of_unbounded hunb0 σ_e hbeh
    · exact Classical.not_forall.mp h
  | typeErrors σ_e =>
    exact absurd hbeh (type_safety (prog.compile_wellTyped htc) hts
      (prog.compile_stepClosed htc))
  | diverges =>
    -- hbeh : ∃ f, IsInfiniteExec prog.compile f ∧ f 0 = Cfg.run 0 prog.initStore
    intro fuel
    rw [Program.interp]
    by_cases hq : prog.body.interp fuel prog.initStore = none
    · exact hq
    · exfalso
      obtain ⟨σ', hinterp⟩ := Option.ne_none_iff_exists'.mp hq
      by_cases hsafe : prog.body.divSafe fuel prog.initStore
      · obtain ⟨σ_tac, hhalt, _⟩ := progCompile_halt prog fuel σ' htc hinterp hsafe
        obtain ⟨f, hinf, hf0⟩ := hbeh
        have inf_steps : ∀ n, StepsN prog.compile (Cfg.run 0 prog.initStore) (f n) n :=
          fun n => hf0 ▸ inf_exec_to_StepsN hinf n
        obtain ⟨k, hk⟩ := Steps_to_StepsN hhalt
        obtain ⟨pc_k, σ_k, hfk_eq⟩ := inf_exec_is_run hinf k
        have := (StepsN_det hk (inf_steps k)).trans hfk_eq
        exact Cfg.noConfusion this
      · obtain ⟨σ_e, herr⟩ := progCompile_reaches_error prog fuel htc hsafe
        obtain ⟨f, hinf, hf0⟩ := hbeh
        have inf_steps : ∀ n, StepsN prog.compile (Cfg.run 0 prog.initStore) (f n) n :=
          fun n => hf0 ▸ inf_exec_to_StepsN hinf n
        obtain ⟨k, hk⟩ := Steps_to_StepsN herr
        obtain ⟨pc_k, σ_k, hfk_eq⟩ := inf_exec_is_run hinf k
        have := (StepsN_det hk (inf_steps k)).trans hfk_eq
        exact Cfg.noConfusion this
