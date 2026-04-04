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
  | arrRead _ _ ih => sorry
theorem compileBool_eq_refCompileBool (b : SBool) (o t : Nat) :
    compileBool b o t = refCompileBool b o t := by
  induction b generalizing o t with
  | lit _ => rfl
  | bvar _ => rfl
  | cmp op a b => simp only [compileBool, refCompileBool, compileExpr_eq_refCompileExpr]
  | not e ih => simp only [compileBool, refCompileBool, ih]
  | and a b iha ihb => simp only [compileBool, refCompileBool, iha, ihb]
  | or a b iha ihb => simp only [compileBool, refCompileBool, iha, ihb]
theorem compileStmt_eq_refCompileStmt (s : Stmt) (o t : Nat) :
    compileStmt s o t = refCompileStmt s o t := by
  induction s generalizing o t with
  | skip => rfl
  | assign x e =>
    cases e with
    | lit _ => rfl
    | var _ => rfl
    | bin op a b => simp only [compileStmt, refCompileStmt, compileExpr_eq_refCompileExpr]
    | arrRead _ _ => sorry
  | bassign x b => simp only [compileStmt, refCompileStmt, compileBool_eq_refCompileBool]
  | arrWrite _ _ _ => sorry
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
theorem progCompile_halt (prog : Program) (fuel : Nat) (σ' : Store)
    (htc : prog.typeCheck = true)
    (hinterp : prog.body.interp fuel prog.initStore ArrayMem.init = some (σ', ArrayMem.init))
    (hsafe : prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init ArrayMem.init ∧
      (∀ v, v.isTmp = false → σ_tac v = σ' v) := by
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨σ_tac, hexec, hagree⟩ :=
    refCompileStmt_correct prog.body fuel prog.initStore σ' prog.decls.length 0
      prog.compile prog.initStore hinterp htmpfree hsafe hintv (fun _ _ => rfl) hcode
  have hhalt_instr : prog.compile[prog.decls.length +
      (refCompileStmt prog.body prog.decls.length 0).1.length]? = some .halt := by
    rw [← compileStmt_eq_refCompileStmt]; exact Program.compile_halt_getElem prog
  have hfull : FragExec prog.compile 0 prog.initStore
      (prog.decls.length + (refCompileStmt prog.body prog.decls.length 0).1.length)
      σ_tac ArrayMem.init ArrayMem.init :=
    FragExec.trans' hinit hexec
  exact ⟨σ_tac, FragExec.toHalt hfull hhalt_instr, hagree⟩
/-- **Forward error** for `prog.compile`: if `¬divSafe`, the compiled program
    cannot halt (it reaches an error). -/
theorem progCompile_no_halt_unsafe (prog : Program) (fuel : Nat)
    (htc : prog.typeCheck = true)
    (hunsafe : ¬ prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init ArrayMem.init := by
  intro ⟨σ_tac, hhalt⟩
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv := Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  obtain ⟨pc_s, σ_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe prog.body fuel prog.initStore prog.decls.length 0
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
  obtain ⟨pc_s, σ_s, hfrag, herror, _⟩ :=
    refCompileStmt_unsafe prog.body fuel prog.initStore prog.decls.length 0
      prog.compile prog.initStore htmpfree hunsafe hintv (fun _ _ => rfl) hcode
  exact ⟨σ_s, ArrayMem.init, Steps.trans (FragExec.trans' hinit hfrag)
    (Steps.step herror Steps.refl)⟩
/-- **Forward no-halt for safe divergence** in `prog.compile`: if the source
    diverges safely, the compiled program doesn't halt. -/
theorem progCompile_no_halt_diverge (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none)
    (hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore ArrayMem.init) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init ArrayMem.init := by
  intro ⟨σ_tac, hhalt⟩
  have htmpfree := Program.typeCheck_tmpFree prog htc
  have hts := Program.typeCheck_initStore_typedStore prog htc
  have hintv : ∀ fuel, prog.body.intTyped fuel prog.initStore ArrayMem.init :=
    fun fuel => Program.typeCheck_intTyped prog htc prog.initStore ArrayMem.init hts fuel
  have hcode := progCompile_body_codeAt prog
  have hinit := Program.compile_initExec prog (Program.typeCheck_noDups prog htc)
  have hunbounded := refCompileStmt_diverges prog.body prog.initStore
    prog.decls.length 0 prog.compile prog.initStore
    htmpfree hdiv hsafe hintv (fun _ _ => rfl) hcode
  have hunbounded' : ∀ N, ∃ n, n ≥ N ∧ ∃ pc' σ',
      RefStepsN prog.compile n (Cfg.run 0 prog.initStore ArrayMem.init)
        (Cfg.run pc' σ' ArrayMem.init) := by
    obtain ⟨k_init, hk_init⟩ := hinit.to_RefStepsN
    intro N
    obtain ⟨n, hn, pc', σ', hsteps⟩ := hunbounded (N)
    exact ⟨k_init + n, by omega, pc', σ', RefStepsN.trans hk_init hsteps⟩
  exact no_halt_of_unbounded hunbounded' σ_tac ArrayMem.init hhalt
/-- **Forward no-halt for unsafe divergence** in `prog.compile`. -/
private theorem progCompile_no_halt_diverge_unsafe (prog : Program)
    (htc : prog.typeCheck = true)
    (hdiv : ∀ fuel, prog.body.interp fuel prog.initStore ArrayMem.init = none) :
    ¬ ∃ σ_tac, haltsWithResult prog.compile 0 prog.initStore σ_tac ArrayMem.init ArrayMem.init := by
  by_cases hsafe : ∀ fuel, prog.body.divSafe fuel prog.initStore ArrayMem.init
  · exact progCompile_no_halt_diverge prog htc hdiv hsafe
  · push_neg at hsafe
    obtain ⟨fuel, hunsafe⟩ := hsafe
    exact progCompile_no_halt_unsafe prog fuel htc hunsafe
-- § 15. ArrayMem-independence for compiled While programs

/-- All elements of a list satisfy `TAC.isScalar`. -/
private def AllScalar : List TAC → Prop
  | [] => True
  | x :: xs => x.isScalar = true ∧ AllScalar xs

private theorem AllScalar_append {l₁ l₂ : List TAC} :
    AllScalar (l₁ ++ l₂) ↔ AllScalar l₁ ∧ AllScalar l₂ := by
  induction l₁ with
  | nil => simp [AllScalar]
  | cons x xs ih => simp [AllScalar, ih, and_assoc]

private theorem AllScalar_getElem {l : List TAC} (h : AllScalar l)
    (i : Nat) (hi : i < l.length) : l[i].isScalar = true := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := h
    cases i with
    | zero => exact hx
    | succ j => exact ih hxs j (by simp [List.length_cons] at hi; omega)

private theorem allScalar_initCode_map (decls : List (Var × VarTy)) :
    AllScalar (decls.map fun (x, ty) => match ty with
      | .int  => TAC.const x (.int (0 : BitVec 64))
      | .bool => TAC.const x (.bool false)) := by
  induction decls with
  | nil => exact trivial
  | cons d ds ih =>
    simp only [List.map_cons, AllScalar]
    exact ⟨by cases d.2 <;> simp [TAC.isScalar], ih⟩

private theorem allScalar_compileExpr (e : SExpr) (o t : Nat) :
    AllScalar (compileExpr e o t).1 := by
  induction e generalizing o t with
  | lit _ => simp [compileExpr, AllScalar, TAC.isScalar]
  | var _ => exact trivial
  | bin op a b iha ihb =>
    simp only [compileExpr]
    rw [AllScalar_append, AllScalar_append]
    exact ⟨⟨iha o t, ihb _ _⟩, by simp [AllScalar, TAC.isScalar]⟩
  | arrRead _ _ ih => sorry

private theorem allScalar_compileBool (b : SBool) (o t : Nat) :
    AllScalar (compileBool b o t).1 := by
  induction b generalizing o t with
  | lit _ => exact trivial
  | bvar _ => exact trivial
  | cmp _ a b =>
    simp only [compileBool]
    rw [AllScalar_append]; exact ⟨allScalar_compileExpr a _ _, allScalar_compileExpr b _ _⟩
  | not e ih => simp only [compileBool]; exact ih o t
  | and a b iha ihb =>
    simp only [compileBool]
    rw [AllScalar_append, AllScalar_append, AllScalar_append]
    refine ⟨⟨⟨iha o t, ?_⟩, ihb _ _⟩, ?_⟩ <;> simp [AllScalar, TAC.isScalar]
  | or a b iha ihb =>
    simp only [compileBool]
    rw [AllScalar_append, AllScalar_append, AllScalar_append]
    refine ⟨⟨⟨iha o t, ?_⟩, ihb _ _⟩, ?_⟩ <;> simp [AllScalar, TAC.isScalar]

private theorem allScalar_compileStmt (s : Stmt) (o t : Nat) :
    AllScalar (compileStmt s o t).1 := by
  induction s generalizing o t with
  | skip => exact trivial
  | assign v e =>
    cases e with
    | lit _ => simp [compileStmt, AllScalar, TAC.isScalar]
    | var _ => simp [compileStmt, AllScalar, TAC.isScalar]
    | bin op a b =>
      simp only [compileStmt]
      rw [AllScalar_append, AllScalar_append]
      exact ⟨⟨allScalar_compileExpr a _ _, allScalar_compileExpr b _ _⟩, by simp [AllScalar, TAC.isScalar]⟩
    | arrRead _ _ => sorry
  | bassign v b =>
    simp only [compileStmt]
    rw [AllScalar_append]; exact ⟨allScalar_compileBool b _ _, by simp [AllScalar, TAC.isScalar]⟩
  | arrWrite _ _ _ => sorry
  | seq s1 s2 ih1 ih2 =>
    simp only [compileStmt]
    rw [AllScalar_append]; exact ⟨ih1 _ _, ih2 _ _⟩
  | ite b s1 s2 ih1 ih2 =>
    simp only [compileStmt]
    rw [AllScalar_append, AllScalar_append, AllScalar_append, AllScalar_append]
    exact ⟨⟨⟨⟨allScalar_compileBool b _ _, by simp [AllScalar, TAC.isScalar]⟩, ih2 _ _⟩,
      by simp [AllScalar, TAC.isScalar]⟩, ih1 _ _⟩
  | loop b body ih =>
    simp only [compileStmt]
    rw [AllScalar_append, AllScalar_append, AllScalar_append]
    exact ⟨⟨⟨allScalar_compileBool b _ _, by simp [AllScalar, TAC.isScalar]⟩, ih _ _⟩,
      by simp [AllScalar, TAC.isScalar]⟩

/-- All instructions in a compiled While program are scalar (no array ops). -/
private theorem progCompile_allScalar (prog : Program) :
    ∀ (i : Nat) (hi : i < prog.compile.code.size), prog.compile.code[i].isScalar = true := by
  intro i hi
  suffices h : AllScalar prog.compile.code.toList by
    have hlen : i < prog.compile.code.toList.length := by
      rwa [Array.length_toList]
    have := AllScalar_getElem h i hlen
    rwa [Array.getElem_toList hi] at this
  show AllScalar (Program.compile prog).code.toList
  unfold Program.compile
  simp only [List.toList_toArray]
  rw [AllScalar_append, AllScalar_append]
  exact ⟨⟨allScalar_initCode_map prog.decls, allScalar_compileStmt _ _ _⟩, ⟨by simp [TAC.isScalar], trivial⟩⟩

/-- Replace ArrayMem in a Cfg. -/
private def Cfg.replaceAm (c : Cfg) (am₀ : ArrayMem) : Cfg :=
  match c with
  | .run pc σ _ => .run pc σ am₀
  | .halt σ _ => .halt σ am₀
  | .error σ _ => .error σ am₀
  | .typeError σ _ => .typeError σ am₀

@[simp] private theorem Cfg.replaceAm_run :
    (Cfg.run pc σ am).replaceAm am₀ = Cfg.run pc σ am₀ := rfl
@[simp] private theorem Cfg.replaceAm_halt :
    (Cfg.halt σ am).replaceAm am₀ = Cfg.halt σ am₀ := rfl
@[simp] private theorem Cfg.replaceAm_error :
    (Cfg.error σ am).replaceAm am₀ = Cfg.error σ am₀ := rfl

private theorem scalar_of_getElem?_eq_some {p : Prog} {pc : Nat} {instr : TAC}
    (h : p[pc]? = some instr)
    (hscalar : ∀ i (hi : i < p.code.size), p.code[i].isScalar = true) :
    instr.isScalar = true := by
  rw [Prog.getElem?_code] at h
  by_cases hpc : pc < p.code.size
  · rw [Array.getElem?_eq_getElem hpc] at h
    have := Option.some_injective _ h
    rw [← this]; exact hscalar pc hpc
  · simp [getElem?, hpc] at h

/-- For scalar programs, a single step transfers with replaced am. -/
private theorem Step.am_transfer_replaceAm {p : Prog} {c c' : Cfg}
    (hstep : p ⊩ c ⟶ c')
    (hscalar : ∀ i (hi : i < p.code.size), p.code[i].isScalar = true)
    (am₀ : ArrayMem) :
    p ⊩ c.replaceAm am₀ ⟶ c'.replaceAm am₀ := by
  cases hstep with
  | const h => exact Step.const h
  | copy h => exact Step.copy h
  | binop h hy hz hs => exact Step.binop h hy hz hs
  | boolop h => exact Step.boolop h
  | goto h => exact Step.goto h
  | iftrue h hb => exact Step.iftrue h hb
  | iffall h hb => exact Step.iffall h hb
  | halt h => exact Step.halt h
  | error h hy hz hu => exact Step.error h hy hz hu
  | binop_typeError h hne => exact Step.binop_typeError h hne
  | arrLoad h _ => exact absurd (scalar_of_getElem?_eq_some h hscalar) (by simp [TAC.isScalar])
  | arrStore h _ _ => exact absurd (scalar_of_getElem?_eq_some h hscalar) (by simp [TAC.isScalar])
  | arrLoad_typeError h _ => exact absurd (scalar_of_getElem?_eq_some h hscalar) (by simp [TAC.isScalar])
  | arrStore_typeError h _ => exact absurd (scalar_of_getElem?_eq_some h hscalar) (by simp [TAC.isScalar])

/-- Multi-step am-transfer for Steps. -/
private theorem Steps.am_transfer {p : Prog} {c c' : Cfg}
    (h : p ⊩ c ⟶* c')
    (hscalar : ∀ i (hi : i < p.code.size), p.code[i].isScalar = true)
    (am₀ : ArrayMem) :
    p ⊩ c.replaceAm am₀ ⟶* c'.replaceAm am₀ := by
  induction h with
  | refl => exact Steps.refl
  | step s _ ih => exact Steps.step (Step.am_transfer_replaceAm s hscalar am₀) ih

/-- Multi-step am-transfer for Steps to halt: for scalar programs, a halt from
    any ArrayMem can be replayed from any other ArrayMem. -/
private theorem Steps.am_transfer_halt {p : Prog} {pc : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (h : p ⊩ Cfg.run pc σ am ⟶* Cfg.halt σ' am')
    (hscalar : ∀ i (hi : i < p.code.size), p.code[i].isScalar = true)
    (am₀ : ArrayMem) :
    p ⊩ Cfg.run pc σ am₀ ⟶* Cfg.halt σ' am₀ :=
  Steps.am_transfer h hscalar am₀

/-- Multi-step am-transfer for Steps to error. -/
private theorem Steps.am_transfer_error {p : Prog} {pc : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (h : p ⊩ Cfg.run pc σ am ⟶* Cfg.error σ' am')
    (hscalar : ∀ i (hi : i < p.code.size), p.code[i].isScalar = true)
    (am₀ : ArrayMem) :
    p ⊩ Cfg.run pc σ am₀ ⟶* Cfg.error σ' am₀ :=
  Steps.am_transfer h hscalar am₀

/-- Multi-step am-transfer for infinite execution. -/
private theorem InfiniteExec.am_transfer {p : Prog} {f : Nat → Cfg}
    (hinf : IsInfiniteExec p f) {pc : Nat} {σ : Store} {am : ArrayMem}
    (hf0 : f 0 = Cfg.run pc σ am)
    (hscalar : ∀ i (hi : i < p.code.size), p.code[i].isScalar = true)
    (am₀ : ArrayMem) :
    ∃ g : Nat → Cfg, IsInfiniteExec p g ∧ g 0 = Cfg.run pc σ am₀ := by
  refine ⟨fun n => (f n).replaceAm am₀, ⟨⟨σ, am₀, ?_⟩, fun n => ?_⟩, ?_⟩
  · obtain ⟨σ₀, am₀', hf0'⟩ := hinf.1
    rw [hf0'] at hf0; cases hf0
    simp [Cfg.replaceAm, hf0']
  · exact Step.am_transfer_replaceAm (hinf.2 n) hscalar am₀
  · simp [Cfg.replaceAm, hf0]

theorem program_refinement (prog : Program) (htc : prog.typeCheck = true) (b : Behavior)
    (hbeh : program_behavior prog.compile prog.initStore b) :
    match b with
    | .halts σ_tac => ∃ fuel σ', prog.interp fuel = some (σ', ArrayMem.init) ∧
        ∀ v, v.isTmp = false → σ_tac v = σ' v
    | .errors _ => ∃ fuel, ¬ prog.body.divSafe fuel prog.initStore ArrayMem.init
    | .typeErrors _ => False
    | .diverges => ∀ fuel, prog.interp fuel = none := by
  sorry
