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
  sorry
theorem compileBool_eq_refCompileBool (b : SBool) (o t : Nat) :
    compileBool b o t = refCompileBool b o t := by
  sorry
theorem compileStmt_eq_refCompileStmt (s : Stmt) (o t : Nat) :
    compileStmt s o t = refCompileStmt s o t := by
  sorry
-- ============================================================
-- § 16. Refinement for Program.compile (with init code)
-- ============================================================

-- ============================================================
-- § 13. Helpers for backward refinement
-- ============================================================

/-- Source interpreter returns `none` iff it doesn't return `some`. -/
private theorem interp_none_iff (s : Stmt) (fuel : Nat) (σ : Store) :
    s.interp fuel σ = none ↔ ¬ ∃ σ', s.interp fuel σ = some σ' := by
  sorry
/-- No steps from error: error is a terminal configuration. -/
private theorem RefStepsN.no_step_error {p : Prog} {n : Nat} {σ : Store} {c : Cfg}
    (h : RefStepsN p (n + 1) (Cfg.error σ _xam) c) : False := by
  sorry
/-- If execution takes unbounded steps through `run` configs, it cannot error. -/
theorem no_error_of_unbounded {p : Prog} {pc : Nat} {σ : Store}
    (hunbounded : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN p n (Cfg.run pc σ _xam) (Cfg.run pc' σ' _xam)) :
    ∀ σ' am_e, ¬ (p ⊩ Cfg.run pc σ _xam ⟶* Cfg.error σ' am_e) := by
  sorry
/-- Extract `StepsN` from an `IsInfiniteExec`: the first `n` steps of an
    infinite execution give a deterministic `n`-step path. -/
private theorem inf_exec_to_StepsN {p : Prog} {f : Nat → Cfg}
    (hinf : IsInfiniteExec p f) :
    ∀ n, StepsN p (f 0) (f n) n := by
  sorry
-- ============================================================
-- § 14. Refinement for Program.compile (with init code)
-- ============================================================

/-- The body code from `compileStmt` (= `refCompileStmt`) is embedded in `prog.compile`
    starting at offset `prog.decls.length`. -/
private theorem progCompile_body_codeAt (prog : Program) :
    CodeAt (refCompileStmt prog.body prog.decls.length 0).1
      prog.compile prog.decls.length := by
  sorry
/-- **Forward halt** for `prog.compile`: if the source terminates safely,
    `prog.compile` halts with a matching store. -/
theorem progCompile_halt (prog : Program) (fuel : Nat) (σ' : Store)
    (htc : prog.typeCheck = true)
    (hinterp : prog.body.interp fuel prog.initStore = some σ')
    (hsafe : prog.body.divSafe fuel prog.initStore) :
    ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac _xam _xam2 ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  sorry
/-- **Forward error** for `prog.compile`: if `¬divSafe`, the compiled program
    cannot halt (it reaches an error). -/
theorem progCompile_no_halt_unsafe (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac _xam _xam2 := by
  sorry
/-- **Forward error reachability** for `prog.compile`: if `¬divSafe`, the
    compiled program reaches an error state. -/
theorem progCompile_reaches_error (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore) :
    ∃ σ_e am_e, prog.compile ⊩ Cfg.run 0 prog.initStore _xam ⟶* Cfg.error σ_e am_e := by
  sorry
/-- **Forward no-halt for safe divergence** in `prog.compile`: if the source
    diverges safely, the compiled program doesn't halt. -/
theorem progCompile_no_halt_diverge (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore = none)
    (hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac _xam _xam2 := by
  sorry
/-- **Forward no-halt for unsafe divergence** in `prog.compile`. -/
private theorem progCompile_no_halt_diverge_unsafe (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore = none) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac _xam _xam2 := by
  sorry
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
  sorry
