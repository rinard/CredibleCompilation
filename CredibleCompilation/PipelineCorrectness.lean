import CredibleCompilation.CodeGen
import CredibleCompilation.SoundnessBridge
import CredibleCompilation.RefCompiler.Refinement

/-!
# Pipeline Correctness

End-to-end correctness for the credible compilation pipeline:
While source → TAC → certified optimizations → ARM.

The theorems are parameterized over an arbitrary list of certificate-checked
optimization passes. Each pass either succeeds (certificate validates) and
transforms the program, or fails and leaves the program unchanged.

## Key theorems
- `applyPassesPure_preserves_halt_am`: pipeline preserves halting behavior with AM
- `applyPassesPure_preserves_error_am`: pipeline preserves error behavior with AM
- `while_to_arm_correctness`: full While→ARM for halting programs
- `while_to_arm_error_preservation`: full While→ARM for error programs
- `while_to_arm_divergence_preservation`: full While→ARM for diverging programs
-/

-- ============================================================
-- § 0. Code-equality implies behavioral equivalence
-- ============================================================

/-- `p[pc]?` depends only on `p.code`. -/
private theorem getElem?_of_code_eq {p q : Prog} (h : p.code = q.code) (pc : Nat) :
    p[pc]? = q[pc]? := by
  simp [Prog.getElem?_code, h]

/-- `arraySizeBv` depends only on `arrayDecls`. -/
private theorem arraySizeBv_of_decls_eq {p q : Prog}
    (h : p.arrayDecls = q.arrayDecls) (arr : ArrayName) :
    Prog.arraySizeBv p arr = Prog.arraySizeBv q arr := by
  unfold Prog.arraySizeBv; rw [h]

/-- A single step transfers across programs with the same code and arrayDecls. -/
theorem Step_of_code_arrayDecls_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {c c' : Cfg} (hs : Step p c c') : Step q c c' := by
  have hg : ∀ pc, p[pc]? = q[pc]? := getElem?_of_code_eq hc
  have has : ∀ arr, Prog.arraySizeBv p arr = Prog.arraySizeBv q arr :=
    arraySizeBv_of_decls_eq ha
  cases hs with
  | const h => exact .const (hg _ ▸ h)
  | copy h => exact .copy (hg _ ▸ h)
  | binop h hy hz hs => exact .binop (hg _ ▸ h) hy hz hs
  | boolop h => exact .boolop (hg _ ▸ h)
  | goto h => exact .goto (hg _ ▸ h)
  | iftrue h hb => exact .iftrue (hg _ ▸ h) hb
  | iffall h hb => exact .iffall (hg _ ▸ h) hb
  | halt h => exact .halt (hg _ ▸ h)
  | error h hy hz hn => exact .error (hg _ ▸ h) hy hz hn
  | binop_typeError h ht => exact .binop_typeError (hg _ ▸ h) ht
  | arrLoad h hi hb => exact .arrLoad (hg _ ▸ h) hi (has _ ▸ hb)
  | arrStore h hi ht hb => exact .arrStore (hg _ ▸ h) hi ht (has _ ▸ hb)
  | arrLoad_boundsError h hi hb => exact .arrLoad_boundsError (hg _ ▸ h) hi (has _ ▸ hb)
  | arrStore_boundsError h hi ht hb => exact .arrStore_boundsError (hg _ ▸ h) hi ht (has _ ▸ hb)
  | arrLoad_typeError h ht => exact .arrLoad_typeError (hg _ ▸ h) ht
  | arrStore_typeError h ht => exact .arrStore_typeError (hg _ ▸ h) ht
  | fbinop h hy hz => exact .fbinop (hg _ ▸ h) hy hz
  | fbinop_typeError h ht => exact .fbinop_typeError (hg _ ▸ h) ht
  | fternop h hy hz hw => exact .fternop (hg _ ▸ h) hy hz hw
  | fternop_typeError h ht => exact .fternop_typeError (hg _ ▸ h) ht
  | intToFloat h hy => exact .intToFloat (hg _ ▸ h) hy
  | intToFloat_typeError h ht => exact .intToFloat_typeError (hg _ ▸ h) ht
  | floatToInt h hy => exact .floatToInt (hg _ ▸ h) hy
  | floatToInt_typeError h ht => exact .floatToInt_typeError (hg _ ▸ h) ht
  | floatUnary h hy => exact .floatUnary (hg _ ▸ h) hy
  | floatUnary_typeError h ht => exact .floatUnary_typeError (hg _ ▸ h) ht
  | print h => exact .print (hg _ ▸ h)

/-- Multi-step transfers across programs with the same code and arrayDecls. -/
theorem Steps_of_code_arrayDecls_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {c c' : Cfg} (hs : Steps p c c') : Steps q c c' := by
  induction hs with
  | refl => exact .refl
  | step h _ ih => exact .step (Step_of_code_arrayDecls_eq hc ha h) ih

/-- `IsInfiniteExec` transfers across code-equal programs. -/
theorem IsInfiniteExec_of_code_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {f} (h : IsInfiniteExec p f) : IsInfiniteExec q f :=
  ⟨h.1, fun n => Step_of_code_arrayDecls_eq hc ha (h.2 n)⟩

-- ============================================================
-- § 1. applyPass soundness
-- ============================================================

/-- If `applyPass` returns `.ok p'`, then the checker accepted `pass p`,
    the output is `(pass p).trans`, and orig matches input on code/obs/arr. -/
theorem applyPass_sound {name : String} {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name pass p = .ok p') :
    checkCertificateExec (pass p) = true ∧
    (pass p).trans = p' ∧
    (pass p).orig.code = p.code ∧
    (pass p).orig.observable = p.observable ∧
    (pass p).orig.arrayDecls = p.arrayDecls := by
  simp only [applyPass] at h
  by_cases hOrig : (pass p).orig.code != p.code || (pass p).orig.observable != p.observable ||
      (pass p).orig.arrayDecls != p.arrayDecls
  · simp [hOrig] at h
  · simp [hOrig] at h
    by_cases hCheck : checkCertificateExec (pass p)
    · simp [hCheck] at h
      simp [not_or, bne_iff_ne, ne_eq] at hOrig
      obtain ⟨⟨hc, hobs⟩, harr⟩ := hOrig
      exact ⟨hCheck, h, hc, hobs, harr⟩
    · simp [hCheck] at h

-- ============================================================
-- § 2. Single-pass halt/error/diverge with AM preservation
-- ============================================================

/-- Extract same_observable from checkCertificateExec. -/
private theorem same_obs_of_check (cert : ECertificate)
    (h : checkCertificateExec cert = true) :
    cert.orig.observable = cert.trans.observable := by
  unfold checkCertificateExec at h
  simp only [Bool.and_eq_true] at h
  exact beq_iff_eq.mp h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- A single optimization pass preserves halting with fixed initial AM.
    The final AM is the same for orig and trans (via determinism). -/
private theorem applyPass_preserves_halt_am {name : String} {pass : Prog → ECertificate}
    {p p' : Prog}
    (h : applyPass name pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore (pass p).tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hh : haltsWithResult p' 0 σ₀ σ' am₀ am') :
    ∃ σ_orig, haltsWithResult p 0 σ₀ σ_orig am₀ am' ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  obtain ⟨hcheck, hTrans, hOrigCode, hOrigObs, hOrigArr⟩ := applyPass_sound h
  have hvalid := soundness_bridge (pass p) hcheck
  have hTransP : (toPCertificate (pass p)).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate (pass p)).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have hhalt_cert : ∃ am', haltsWithResult (toPCertificate (pass p)).trans 0 σ₀ σ' am₀ am' :=
    ⟨am', hTransP ▸ hh⟩
  obtain ⟨σ_o, am_f, hhalt_o, hhalt_t, hobs⟩ :=
    soundness_halt (toPCertificate (pass p)) hvalid σ₀ σ' hts' hhalt_cert
  -- am_f = am' by determinism (both are final AM of trans execution)
  have ham : am_f = am' :=
    (haltsWithResult_unique (hTransP ▸ hhalt_t : haltsWithResult p' 0 σ₀ σ' am₀ am_f) hh).2
  subst ham
  have hOC : (toPCertificate (pass p)).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate (pass p)).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  have hOO : (toPCertificate (pass p)).observable = p.observable := by
    simp [toPCertificate, PCertificate.observable]; exact hOrigObs
  exact ⟨σ_o, Steps_of_code_arrayDecls_eq hOC hOA hhalt_o,
    fun v hv => hobs v (hOO ▸ hv)⟩

/-- A single optimization pass preserves errors with fixed initial AM. -/
private theorem applyPass_preserves_error_am {name : String} {pass : Prog → ECertificate}
    {p p' : Prog}
    (h : applyPass name pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore (pass p).tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hbeh : p' ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ_o am_o' := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  have hvalid := soundness_bridge (pass p) hcheck
  have hTransP : (toPCertificate (pass p)).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate (pass p)).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have herr_cert : (toPCertificate (pass p)).trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ' am' :=
    hTransP ▸ hbeh
  obtain ⟨σ_o, ⟨am_f, herr_orig⟩⟩ := error_preservation _ hvalid σ₀ hts' herr_cert
  have hOC : (toPCertificate (pass p)).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate (pass p)).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨σ_o, am_f, Steps_of_code_arrayDecls_eq hOC hOA herr_orig⟩

/-- A single optimization pass preserves divergence. -/
private theorem applyPass_preserves_diverge {name : String} {pass : Prog → ECertificate}
    {p p' : Prog}
    (h : applyPass name pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore (pass p).tyCtx σ₀)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec p' f) (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g, IsInfiniteExec p g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  have hvalid := soundness_bridge (pass p) hcheck
  have hTransP : (toPCertificate (pass p)).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate (pass p)).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have hinf' : IsInfiniteExec (toPCertificate (pass p)).trans f := hTransP ▸ hinf
  have hf0' : f 0 = Cfg.run 0 σ₀ ArrayMem.init := hf0
  obtain ⟨g, hg, hg0⟩ := soundness_diverge _ hvalid f σ₀ hts' hinf' hf0'
  have hOC : (toPCertificate (pass p)).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate (pass p)).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨g, IsInfiniteExec_of_code_eq hOC hOA hg, hg0⟩

/-- Each pass preserves observable variable list. -/
private theorem obs_preserved_by_pass (n : String) (pass : Prog → ECertificate) (q q' : Prog)
    (hap : applyPass n pass q = .ok q') : q'.observable = q.observable := by
  obtain ⟨hcheck, hTrans, _, hOrigObs, _⟩ := applyPass_sound hap
  rw [← hTrans]
  have hSameObs := same_obs_of_check (pass q) hcheck
  rw [← hSameObs, hOrigObs]

-- ============================================================
-- § 3. applyPassesPure: inductive soundness
-- ============================================================

/-- `applyPassesPure` preserves observable variables across all passes. -/
theorem applyPassesPure_obs_eq
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog) :
    (applyPassesPure passes p).observable = p.observable := by
  induction passes generalizing p with
  | nil => rfl
  | cons np rest ih =>
    simp only [applyPassesPure]
    obtain ⟨name, pass⟩ := np
    split
    · rename_i p' hap; rw [ih _, obs_preserved_by_pass name pass p p' hap]
    · exact ih _

/-- `applyPassesPure` preserves halting behavior with fixed initial AM.
    Each pass's certificate carries the same tyCtx, so TypedStore is preserved. -/
theorem applyPassesPure_preserves_halt_am
    (passes : List (String × (Prog → ECertificate)))
    {tyCtx : TyCtx} (hTyCtx : ∀ np ∈ passes, ∀ q, (np.2 q).tyCtx = tyCtx)
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hHalt : haltsWithResult (applyPassesPure passes p) 0 σ₀ σ' am₀ am') :
    ∃ σ_orig, haltsWithResult p 0 σ₀ σ_orig am₀ am' ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPassesPure] at hHalt
    exact ⟨σ', hHalt, fun _ _ => rfl⟩
  | cons np rest ih =>
    simp only [applyPassesPure] at hHalt
    obtain ⟨name, pass⟩ := np
    have hRest : ∀ np ∈ rest, ∀ q, (np.2 q).tyCtx = tyCtx :=
      fun np' h => hTyCtx np' (List.mem_cons_of_mem _ h)
    split at hHalt
    · -- Pass succeeded
      rename_i p' hap
      obtain ⟨σ_mid, hHalt_mid, hobs_mid⟩ := ih hRest hHalt
      have hts_pass : TypedStore (pass p).tyCtx σ₀ :=
        hTyCtx (name, pass) (List.mem_cons_self ..) p ▸ hts
      obtain ⟨σ_orig, hHalt_orig, hobs_orig⟩ :=
        applyPass_preserves_halt_am hap σ₀ hts_pass hHalt_mid
      have hobs_p' := obs_preserved_by_pass name pass p p' hap
      exact ⟨σ_orig, hHalt_orig, fun v hv => by
        rw [hobs_mid v (hobs_p' ▸ hv), hobs_orig v hv]⟩
    · -- Pass failed: identity
      exact ih hRest hHalt

/-- `applyPassesPure` preserves error behavior with fixed initial AM. -/
theorem applyPassesPure_preserves_error_am
    (passes : List (String × (Prog → ECertificate)))
    {tyCtx : TyCtx} (hTyCtx : ∀ np ∈ passes, ∀ q, (np.2 q).tyCtx = tyCtx)
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hErr : (applyPassesPure passes p) ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ_o am_o' := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPassesPure] at hErr
    exact ⟨σ', am', hErr⟩
  | cons np rest ih =>
    simp only [applyPassesPure] at hErr
    obtain ⟨name, pass⟩ := np
    have hRest : ∀ np ∈ rest, ∀ q, (np.2 q).tyCtx = tyCtx :=
      fun np' h => hTyCtx np' (List.mem_cons_of_mem _ h)
    split at hErr
    · rename_i p' hap
      obtain ⟨σ_mid, am_mid, hErr_mid⟩ := ih hRest hErr
      have hts_pass : TypedStore (pass p).tyCtx σ₀ :=
        hTyCtx (name, pass) (List.mem_cons_self ..) p ▸ hts
      exact applyPass_preserves_error_am hap σ₀ hts_pass hErr_mid
    · exact ih hRest hErr

/-- `applyPassesPure` preserves divergence. -/
theorem applyPassesPure_preserves_diverge
    (passes : List (String × (Prog → ECertificate)))
    {tyCtx : TyCtx} (hTyCtx : ∀ np ∈ passes, ∀ q, (np.2 q).tyCtx = tyCtx)
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPassesPure passes p) f)
    (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g, IsInfiniteExec p g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  induction passes generalizing p f with
  | nil =>
    simp [applyPassesPure] at hinf
    exact ⟨f, hinf, hf0⟩
  | cons np rest ih =>
    simp only [applyPassesPure] at hinf
    obtain ⟨name, pass⟩ := np
    have hRest : ∀ np ∈ rest, ∀ q, (np.2 q).tyCtx = tyCtx :=
      fun np' h => hTyCtx np' (List.mem_cons_of_mem _ h)
    split at hinf
    · rename_i p' hap
      obtain ⟨g, hg, hg0⟩ := ih hRest hinf hf0
      have hts_pass : TypedStore (pass p).tyCtx σ₀ :=
        hTyCtx (name, pass) (List.mem_cons_self ..) p ▸ hts
      exact applyPass_preserves_diverge hap σ₀ hts_pass hg hg0
    · exact ih hRest hinf hf0

-- ============================================================
-- § 4. Full end-to-end: While source → ARM (halts)
-- ============================================================

/-- **Full end-to-end correctness (halts): While source → ARM.**

    If a well-typed While program is compiled to TAC, optimized through
    any list of certificate-checked passes, and code-generated to ARM,
    and the optimized TAC halts, then:
    1. The source program terminates with matching observable variables
       and identical final array memory
    2. The ARM program simulates the TAC halt -/
theorem while_to_arm_correctness
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    (hTyCtx : ∀ np ∈ passes, ∀ q, (np.2 q).tyCtx = prog.tyCtx)
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPassesPure passes prog.compileToTAC) = .ok r)
    {σ_opt : Store} {am_opt : ArrayMem}
    (hHalt : haltsWithResult (applyPassesPure passes prog.compileToTAC) 0
      (Store.typedInit prog.tyCtx) σ_opt ArrayMem.init am_opt) :
    (∃ fuel σ_src am_src,
      prog.interp fuel = some (σ_src, am_src) ∧
      am_src = am_opt ∧
      ∀ v ∈ prog.compileToTAC.observable, σ_opt v = σ_src v) ∧
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap (.halt σ_opt am_opt) s') := by
  have htc := Program.typeCheckStrict_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  -- Part 2: ARM simulation
  refine ⟨?_, tacToArm_correctness hGen hHalt⟩
  -- Part 1: Pipeline → original TAC halts with same final AM
  obtain ⟨σ_tac, hHalt_tac, hobs_tac⟩ :=
    applyPassesPure_preserves_halt_am passes hTyCtx _ hts hHalt
  -- Original TAC halts → source terminates
  have hHalt_init : haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_opt :=
    hInitEq ▸ hHalt_tac
  have hbeh_tac : program_behavior_init prog.compileToTAC prog.initStore (.halts σ_tac) :=
    ⟨am_opt, hHalt_init⟩
  have hsrc := whileToTAC_refinement prog htcs (.halts σ_tac) hbeh_tac
  simp only at hsrc
  obtain ⟨fuel, σ_src, am_h, am_src, hinterp, hHalt_tac2, ham_eq, hobs_src⟩ := hsrc
  -- am_h = am_opt by determinism, am_h = am_src from whileToTAC_refinement
  have ham_opt : am_h = am_opt := (haltsWithResult_unique hHalt_tac2 hHalt_init).2
  have hnt : Program.noTmpDecls prog.decls = true := by
    unfold Program.typeCheck at htc; simp only [Bool.and_eq_true] at htc; exact htc.1.2
  have hobs_eq := applyPassesPure_obs_eq passes prog.compileToTAC
  exact ⟨fuel, σ_src, am_src, hinterp, ham_opt ▸ ham_eq.symm, fun v hv => by
    rw [hobs_tac v (hobs_eq ▸ hv)]
    have hv' : v ∈ prog.decls.map Prod.fst := by
      have : prog.compileToTAC.observable = prog.decls.map Prod.fst := by
        simp [Program.compileToTAC]
      rw [this] at hv; exact hv
    obtain ⟨⟨w, ty⟩, hp, hw⟩ := List.exists_of_mem_map hv'
    simp only at hw; subst hw
    simp only [Program.noTmpDecls, List.all_eq_true] at hnt
    have hntw := hnt ⟨w, ty⟩ hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hntw
    exact hobs_src w hntw.1 hntw.2⟩

-- ============================================================
-- § 5. Full end-to-end: While source → ARM (errors)
-- ============================================================

/-- **Full end-to-end error preservation: While source → ARM.**

    If the optimized TAC reaches an error (division by zero or array
    out-of-bounds), then the source program is unsafe at some fuel,
    and the ARM program simulates the error execution. -/
theorem while_to_arm_error_preservation
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    (hTyCtx : ∀ np ∈ passes, ∀ q, (np.2 q).tyCtx = prog.tyCtx)
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPassesPure passes prog.compileToTAC) = .ok r)
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (applyPassesPure passes prog.compileToTAC) ⊩
      Cfg.run 0 (Store.typedInit prog.tyCtx)
        ArrayMem.init ⟶* Cfg.error σ_err am_err) :
    (∃ fuel, ¬ prog.body.safe fuel prog.initStore ArrayMem.init prog.arrayDecls) ∧
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap (.error σ_err am_err) s') := by
  have htc := Program.typeCheckStrict_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  -- ARM simulation
  refine ⟨?_, tacToArm_correctness hGen hErr⟩
  -- Pipeline → original TAC errors from ArrayMem.init
  obtain ⟨σ_o, am_o', hErr_tac⟩ :=
    applyPassesPure_preserves_error_am passes hTyCtx _ hts hErr
  -- Original TAC errors → source is unsafe
  have hErr_init : program_behavior_init prog.compileToTAC prog.initStore (.errors σ_o) :=
    ⟨am_o', hInitEq ▸ hErr_tac⟩
  exact whileToTAC_refinement prog htcs (.errors σ_o) hErr_init

-- ============================================================
-- § 6. Full end-to-end: While source → ARM (diverges)
-- ============================================================

/-- **Full end-to-end divergence preservation: While source → ARM.**

    If the optimized TAC diverges, then the source program diverges
    at all fuels. -/
theorem while_to_arm_divergence_preservation
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    (hTyCtx : ∀ np ∈ passes, ∀ q, (np.2 q).tyCtx = prog.tyCtx)
    {f : Nat → Cfg}
    (hDiv : IsInfiniteExec (applyPassesPure passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init) :
    ∀ fuel, prog.interp fuel = none := by
  have htc := Program.typeCheckStrict_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  -- Pipeline → original TAC diverges
  obtain ⟨g, hg, hg0⟩ :=
    applyPassesPure_preserves_diverge passes hTyCtx _ hts hDiv hf0
  -- Original TAC diverges → source diverges
  have hdiv_init : program_behavior_init prog.compileToTAC prog.initStore .diverges :=
    ⟨g, hg, hInitEq ▸ hg0⟩
  exact whileToTAC_refinement prog htcs .diverges hdiv_init
