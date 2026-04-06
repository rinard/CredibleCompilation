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
  | bin op a b iha ihb =>
    simp only [compileExpr, refCompileExpr, iha, ihb]
  | arrRead _ _ ih => simp only [compileExpr, refCompileExpr, ih]
theorem compileBool_eq_refCompileBool (b : SBool) (o t : Nat) :
    compileBool b o t = refCompileBool b o t := by
  induction b generalizing o t with
  | lit _ => rfl
  | bvar _ => rfl
  | cmp op a b => simp only [compileBool, refCompileBool, compileExpr_eq_refCompileExpr]
  | not e ih => simp only [compileBool, refCompileBool, ih]
  | and a b iha ihb => simp only [compileBool, refCompileBool, iha, ihb]
  | or a b iha ihb => simp only [compileBool, refCompileBool, iha, ihb]
  | barrRead arr idx => simp only [compileBool, refCompileBool, compileExpr_eq_refCompileExpr]
theorem compileStmt_eq_refCompileStmt (s : Stmt) (o t : Nat) :
    compileStmt s o t = refCompileStmt s o t := by
  induction s generalizing o t with
  | skip => rfl
  | assign x e =>
    cases e with
    | lit _ => rfl
    | var _ => rfl
    | bin op a b => simp only [compileStmt, refCompileStmt, compileExpr_eq_refCompileExpr]
    | arrRead _ _ => simp only [compileStmt, refCompileStmt, compileExpr_eq_refCompileExpr]
  | bassign x b => simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool]
  | arrWrite _ _ _ => simp only [compileStmt, refCompileStmt, compileExpr_eq_refCompileExpr]
  | barrWrite _ _ _ =>
    simp only [compileStmt, refCompileStmt, compileExpr_eq_refCompileExpr, compileBool_eq_refCompileBool]
  | seq s1 s2 ih1 ih2 => simp only [compileStmt, refCompileStmt, ih1, ih2]
  | ite b s1 s2 ih1 ih2 => simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool, ih1, ih2]
  | loop b body ih => simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool, ih]
-- ============================================================
-- § 16. Refinement for Program.compile (with init code)
-- ============================================================

-- ============================================================
-- § 13. Helpers for backward refinement
-- ============================================================

/-- Source interpreter returns `none` iff it doesn't return `some`. -/
private theorem interp_none_iff (s : Stmt) (fuel : Nat) (σ : Store) (am : ArrayMem) :
    s.interp fuel σ am = none ↔ ¬ ∃ r, s.interp fuel σ am = some r := by
  constructor
  · intro h ⟨r, hr⟩; simp [h] at hr
  · intro h; by_contra hc; push_neg at hc; exact h (Option.ne_none_iff_exists'.mp hc)
/-- No steps from error: error is a terminal configuration. -/
private theorem RefStepsN.no_step_error {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.error σ _xam) c) : False := by
  cases h with
  | step s _ => exact Step.no_step_from_error s
/-- No steps from typeError: typeError is a terminal configuration. -/
private theorem RefStepsN.no_step_typeError {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.typeError σ _xam) c) : False := by
  cases h with
  | step s _ => exact Step.no_step_from_typeError s
/-- If execution takes unbounded steps through `run` configs, it cannot error. -/
theorem no_error_of_unbounded {p : Prog} {pc : Nat} {σ : Store}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ _xam) (Cfg.run pc' σ' _xam)) :
    ∀ σ' am_e, ¬ (p ⊩ Cfg.run pc σ _xam ⟶* Cfg.error σ' am_e) := by
  intro σ' am_e herr
  obtain ⟨n, hn⟩ := herr.to_RefStepsN
  obtain ⟨m, hm, pc', σ'', hrun⟩ := hunbounded (n + 1)
  have hsuffix := RefStepsN.det_prefix hn hrun (by omega)
  have hmn : m - n = (m - n - 1) + 1 := by omega
  exact RefStepsN.no_step_error (hmn ▸ hsuffix)
/-- Extract `StepsN` from an `IsInfiniteExec`: the first `n` steps of an
    infinite execution give a deterministic `n`-step path. -/
private theorem inf_exec_to_StepsN {p : Prog} {f : Nat → Cfg}
    (hinf : IsInfiniteExec p f) :
    ∀ n, StepsN p (f 0) (f n) n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => exact StepsN_extend ih (hinf.2 n)
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
  exact Program.compile_body_getElem prog i hi
/-- **Forward halt** for `prog.compile`: if the source terminates safely,
    `prog.compile` halts with a matching store. -/
theorem progCompile_halt (prog : Program) (fuel : Nat) (σ' : Store) (am' : ArrayMem)
    (htc : prog.typeCheck = true)
    (hinterp : prog.body.interp fuel prog.initStore ArrayMem.init = some (σ', am'))
    (hsafe : prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ∃ σ_tac am_h, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init am_h ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    refCompileStmt_correct prog.body fuel prog.initStore σ' ArrayMem.init am' prog.decls.length 0
      prog.compile prog.initStore hinterp htmpfree hsafe hintv (fun _ _ => rfl) hcode
  have hhalt_instr : prog.compile[prog.decls.length +
      (refCompileStmt prog.body prog.decls.length 0).1.length]? = some .halt := by
    rw [← compileStmt_eq_refCompileStmt]; exact Program.compile_halt_getElem prog
  have hfull : FragExec prog.compile 0 prog.initStore
      (prog.decls.length + (refCompileStmt prog.body prog.decls.length 0).1.length)
      σ_tac ArrayMem.init am' :=
    FragExec.trans' hinit hexec
  exact ⟨σ_tac, am', FragExec.toHalt hfull hhalt_instr, hagree⟩
/-- **Forward error** for `prog.compile`: if `¬divSafe`, the compiled program
    cannot halt (it reaches an error). -/
theorem progCompile_no_halt_unsafe (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ¬ ∃ σ_tac am_h, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init am_h := by
  intro ⟨σ_tac, am_h, hhalt⟩
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe prog.body fuel prog.initStore ArrayMem.init prog.decls.length 0
      prog.compile prog.initStore htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  exact error_run_no_halt (FragExec.trans' hinit hfrag) herror hhalt
/-- **Forward error reachability** for `prog.compile`: if `¬divSafe`, the
    compiled program reaches an error state. -/
theorem progCompile_reaches_error (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ∃ σ_e am_e, prog.compile ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* Cfg.error σ_e am_e := by
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨pc_s, σ_s, am_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe prog.body fuel prog.initStore ArrayMem.init prog.decls.length 0
      prog.compile prog.initStore htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  exact ⟨σ_s, am_s, Steps.trans (FragExec.trans' hinit hfrag)
    (Steps.step herror Steps.refl)⟩
/-- **Forward no-halt for safe divergence** in `prog.compile`: if the source
    diverges safely, the compiled program doesn't halt. -/
theorem progCompile_no_halt_diverge (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none)
    (hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ¬ ∃ σ_tac am_h, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init am_h := by
  intro ⟨σ_tac, am_h, hhalt⟩
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv : ∀ fuel, prog.body.intTyped fuel prog.initStore ArrayMem.init :=
    fun fuel => Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  have hunbounded := refCompileStmt_diverges prog.body prog.initStore ArrayMem.init
    prog.decls.length 0 prog.compile prog.initStore
    htmpfree hdiv hsafe hintv (fun _ _ => rfl) hcode
  have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
      RefStepsN prog.compile n (Cfg.run 0 prog.initStore ArrayMem.init)
        (Cfg.run pc' σ' am') := by
    obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
    intro N
    obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
    exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
  exact no_halt_of_unbounded_am hunbounded' σ_tac am_h hhalt
/-- **Forward no-halt for unsafe divergence** in `prog.compile`. -/
private theorem progCompile_no_halt_diverge_unsafe (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none) :
    ¬ ∃ σ_tac am_h, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init am_h := by
  by_cases hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore ArrayMem.init
  · exact progCompile_no_halt_diverge prog htc hdiv hsafe
  · push_neg at hsafe
    obtain ⟨fuel, hunsafe⟩ := hsafe
    exact progCompile_no_halt_unsafe prog fuel htc hunsafe
-- ============================================================
-- § 15. Backward refinement
-- ============================================================

/-- Specialised `program_behavior` that fixes the initial array memory to
    `ArrayMem.init` (which is what `has_behavior` always produces). -/
def program_behavior_init (p : Prog) (σ₀ : Store) (b : Behavior) : Prop :=
  match b with
  | .halts σ'      => ∃ am', haltsWithResult p 0 σ₀ σ' ArrayMem.init am'
  | .errors σ'     => ∃ am', p ⊩ Cfg.run 0 σ₀ ArrayMem.init ⟶* Cfg.error σ' am'
  | .typeErrors σ' => ∃ am', p ⊩ Cfg.run 0 σ₀ ArrayMem.init ⟶* Cfg.typeError σ' am'
  | .diverges      => ∃ f : Nat → Cfg, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init

/-- `program_behavior_init` implies `program_behavior`. -/
theorem program_behavior_of_init {p : Prog} {σ₀ : Store} {b : Behavior}
    (h : program_behavior_init p σ₀ b) : program_behavior p σ₀ b := by
  cases b with
  | halts _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | errors _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | typeErrors _ => obtain ⟨am', hh⟩ := h; exact ⟨ArrayMem.init, am', hh⟩
  | diverges => exact h

/-- Convert `StepsN` to `RefStepsN`. -/
private theorem StepsN_to_RefStepsN {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' n) : RefStepsN p n c c' := by
  induction n generalizing c with
  | zero => exact h ▸ .refl
  | succ n ih => obtain ⟨c'', hs, hr⟩ := h; exact .step hs (ih hr)

/-- Cast `RefStepsN` along an equality of step counts. -/
private theorem refStepsN_cast' {p : Prog} {n n' : Nat} {c c' : Cfg}
    (h : RefStepsN p n c c') (heq : n = n') : RefStepsN p n' c c' := heq ▸ h

/-- Get `some` witness from non-`none` option. -/
private theorem Option.some_of_ne_none {o : Option α} (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-- Backward refinement: any observable behavior of `prog.compile` starting from
    `ArrayMem.init` corresponds to a behavior of the source program. -/
theorem program_refinement (prog : Program) (htc : prog.typeCheck = true) (b : Behavior)
    (hbeh : program_behavior_init prog.compile prog.initStore b) :
    match b with
    | .halts σ_tac => ∃ fuel σ' am', prog.interp fuel = some (σ', am') ∧
        ∀ v, v.isTmp = false → σ_tac v = σ' v
    | .errors _ => ∃ fuel, ¬ prog.body.divSafe fuel prog.initStore ArrayMem.init
    | .typeErrors _ => False
    | .diverges => ∀ fuel, prog.interp fuel = none := by
  cases b with
  | halts σ_tac =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_h, hhalt⟩ := hbeh
    -- Source either terminates at some fuel or diverges at all fuels
    by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none
    · -- Source diverges → compiled program cannot halt → contradiction
      exact absurd ⟨σ_tac, am_h, hhalt⟩ (progCompile_no_halt_diverge_unsafe prog htc hdiv)
    · -- Source terminates at some fuel
      push_neg at hdiv
      obtain ⟨fuel, hfuel⟩ := hdiv
      obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
      obtain ⟨σ', am'⟩ := r
      by_cases hsafe : prog.body.divSafe fuel prog.initStore ArrayMem.init
      · -- Source terminates safely → forward halt → determinism gives store match
        obtain ⟨σ_fwd, am_fwd, hhalt_fwd, hagree⟩ :=
          progCompile_halt prog fuel σ' am' htc hinterp hsafe
        have heq := haltsWithResult_unique hhalt hhalt_fwd
        subst heq
        exact ⟨fuel, σ', am', hinterp, hagree⟩
      · -- not divSafe → compiled cannot halt → contradiction
        exact absurd ⟨σ_tac, am_h, hhalt⟩ (progCompile_no_halt_unsafe prog fuel htc hsafe)
  | errors σ_e =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_e, herr⟩ := hbeh
    by_contra hall
    push_neg at hall
    -- hall : ∀ fuel, prog.body.divSafe fuel prog.initStore ArrayMem.init
    by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none
    · -- Source diverges safely → unbounded execution → error contradicts unbounded
      have htmpfree := Program.typeCheck_tmpFree prog htc
      have hts := Program.typeCheck_initStore_typedStore prog htc
      have hintv : ∀ fuel, prog.body.intTyped fuel prog.initStore ArrayMem.init :=
        fun fuel => Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
      have hcode := progCompile_body_codeAt prog
      have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
      have hunbounded := refCompileStmt_diverges prog.body prog.initStore ArrayMem.init
        prog.decls.length 0 prog.compile prog.initStore
        htmpfree hdiv hall hintv (fun _ _ => rfl) hcode
      have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
          RefStepsN prog.compile n (Cfg.run 0 prog.initStore ArrayMem.init)
            (Cfg.run pc' σ' am') := by
        obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
        intro N
        obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
        exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
      obtain ⟨k_err, hk_err⟩ := herr.to_RefStepsN
      obtain ⟨m, hm, _pc', _σ'', _am'', hrun⟩ := hunbounded' (k_err + 1)
      have hsuffix := RefStepsN.det_prefix hk_err hrun (by omega)
      have hmk : m - k_err = (m - k_err - 1) + 1 := by omega
      exact RefStepsN.no_step_error (hmk ▸ hsuffix)
    · -- Source terminates at some fuel
      push_neg at hdiv
      obtain ⟨fuel, hfuel⟩ := hdiv
      obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
      obtain ⟨σ', am'⟩ := r
      obtain ⟨σ_fwd, am_fwd, hhalt_fwd, _⟩ :=
        progCompile_halt prog fuel σ' am' htc hinterp (hall fuel)
      have halt_terminal : ∀ d, ¬ Step prog.compile (Cfg.halt σ_fwd am_fwd) d :=
        fun _ h => Step.no_step_from_halt h
      have err_terminal : ∀ d, ¬ Step prog.compile (Cfg.error σ_e am_e) d :=
        fun _ h => Step.no_step_from_error h
      exact Cfg.noConfusion (Steps.stuck_det hhalt_fwd herr halt_terminal err_terminal)
  | typeErrors σ_te =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨am_te, hte⟩ := hbeh
    by_cases hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none
    · by_cases hsafe_all : ∀ fuel, prog.body.divSafe fuel prog.initStore ArrayMem.init
      · -- Source diverges safely → unbounded → typeError contradicts unbounded
        have htmpfree := Program.typeCheck_tmpFree prog htc
        have hts := Program.typeCheck_initStore_typedStore prog htc
        have hintv : ∀ fuel, prog.body.intTyped fuel prog.initStore ArrayMem.init :=
          fun fuel => Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
        have hcode := progCompile_body_codeAt prog
        have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
        have hunbounded := refCompileStmt_diverges prog.body prog.initStore ArrayMem.init
          prog.decls.length 0 prog.compile prog.initStore
          htmpfree hdiv hsafe_all hintv (fun _ _ => rfl) hcode
        have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ' am',
            RefStepsN prog.compile n (Cfg.run 0 prog.initStore ArrayMem.init)
              (Cfg.run pc' σ' am') := by
          obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
          intro N
          obtain ⟨n, hn, pc', σ', am', hsteps⟩ := hunbounded (N)
          exact ⟨k_init + n, by omega, pc', σ', am', RefStepsN.trans hk_init hsteps⟩
        obtain ⟨k_te, hk_te⟩ := hte.to_RefStepsN
        obtain ⟨m, hm, _pc', _σ'', _am'', hrun⟩ := hunbounded' (k_te + 1)
        have hsuffix := RefStepsN.det_prefix hk_te hrun (by omega)
        have hmk : m - k_te = (m - k_te - 1) + 1 := by omega
        exact RefStepsN.no_step_typeError (hmk ▸ hsuffix)
      · -- not all safe → error reachable → typeError contradicts error
        push_neg at hsafe_all
        obtain ⟨fuel, hunsafe⟩ := hsafe_all
        obtain ⟨σ_e, am_e, herr⟩ := progCompile_reaches_error prog fuel htc hunsafe
        have err_terminal : ∀ d, ¬ Step prog.compile (Cfg.error σ_e am_e) d :=
          fun _ h => Step.no_step_from_error h
        have te_terminal : ∀ d, ¬ Step prog.compile (Cfg.typeError σ_te am_te) d :=
          fun _ h => Step.no_step_from_typeError h
        exact Cfg.noConfusion (Steps.stuck_det herr hte err_terminal te_terminal)
    · -- Source terminates at some fuel
      push_neg at hdiv
      obtain ⟨fuel, hfuel⟩ := hdiv
      obtain ⟨r, hinterp⟩ := Option.some_of_ne_none hfuel
      obtain ⟨σ', am'⟩ := r
      by_cases hsafe : prog.body.divSafe fuel prog.initStore ArrayMem.init
      · obtain ⟨σ_fwd, am_fwd, hhalt_fwd, _⟩ :=
          progCompile_halt prog fuel σ' am' htc hinterp hsafe
        have halt_terminal : ∀ d, ¬ Step prog.compile (Cfg.halt σ_fwd am_fwd) d :=
          fun _ h => Step.no_step_from_halt h
        have te_terminal : ∀ d, ¬ Step prog.compile (Cfg.typeError σ_te am_te) d :=
          fun _ h => Step.no_step_from_typeError h
        exact Cfg.noConfusion (Steps.stuck_det hhalt_fwd hte halt_terminal te_terminal)
      · obtain ⟨σ_e, am_e, herr⟩ := progCompile_reaches_error prog fuel htc hsafe
        have err_terminal : ∀ d, ¬ Step prog.compile (Cfg.error σ_e am_e) d :=
          fun _ h => Step.no_step_from_error h
        have te_terminal : ∀ d, ¬ Step prog.compile (Cfg.typeError σ_te am_te) d :=
          fun _ h => Step.no_step_from_typeError h
        exact Cfg.noConfusion (Steps.stuck_det herr hte err_terminal te_terminal)
  | diverges =>
    simp only [program_behavior_init] at hbeh
    obtain ⟨f, hinf, hf0⟩ := hbeh
    intro fuel
    show prog.body.interp fuel prog.initStore ArrayMem.init = none
    by_contra hfuel
    have ⟨r, hinterp⟩ : ∃ r, prog.body.interp fuel prog.initStore ArrayMem.init = some r := by
      by_contra h
      exact hfuel ((interp_none_iff _ _ _ _).mpr h)
    obtain ⟨σ', am'⟩ := r
    by_cases hsafe : prog.body.divSafe fuel prog.initStore ArrayMem.init
    · -- divSafe → forward halt → contradicts infinite exec
      obtain ⟨σ_fwd, am_fwd, hhalt_fwd, _⟩ :=
        progCompile_halt prog fuel σ' am' htc hinterp hsafe
      obtain ⟨k, hk⟩ := hhalt_fwd.to_RefStepsN
      have hstepsN := inf_exec_to_StepsN hinf (k + 1)
      rw [hf0] at hstepsN
      have hstepsR := StepsN_to_RefStepsN hstepsN
      have hsuffix := RefStepsN.det_prefix hk hstepsR (by omega)
      have hmk : (k + 1) - k = ((k + 1) - k - 1) + 1 := by omega
      exact RefStepsN.no_step_halt (hmk ▸ hsuffix)
    · -- not divSafe → forward error → contradicts infinite exec
      obtain ⟨σ_e, am_e, herr⟩ := progCompile_reaches_error prog fuel htc hsafe
      obtain ⟨k, hk⟩ := herr.to_RefStepsN
      have hstepsN := inf_exec_to_StepsN hinf (k + 1)
      rw [hf0] at hstepsN
      have hstepsR := StepsN_to_RefStepsN hstepsN
      have hsuffix := RefStepsN.det_prefix hk hstepsR (by omega)
      have hmk : (k + 1) - k = ((k + 1) - k - 1) + 1 := by omega
      exact RefStepsN.no_step_error (hmk ▸ hsuffix)
