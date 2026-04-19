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

/-- If `applyPass` returns `.ok p'`, then the checker accepted the certificate
    (with the enforced tyCtx), the output is `(pass p).trans`, and orig matches
    input on code/obs/arr. -/
theorem applyPass_sound {name : String} {tyCtx : TyCtx} {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p') :
    checkCertificateExec { pass p with tyCtx := tyCtx } = true ∧
    (pass p).trans = p' ∧
    (pass p).orig.code = p.code ∧
    (pass p).orig.observable = p.observable ∧
    (pass p).orig.arrayDecls = p.arrayDecls := by
  simp only [applyPass] at h
  by_cases hOrig : (pass p).orig.code != p.code || (pass p).orig.observable != p.observable ||
      (pass p).orig.arrayDecls != p.arrayDecls
  · simp [hOrig] at h
  · simp [hOrig] at h
    by_cases hCheck : checkCertificateExec { pass p with tyCtx := tyCtx }
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
  exact beq_iff_eq.mp h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- A single optimization pass preserves halting with fixed initial AM.
    The final AM is the same for orig and trans (via determinism). -/
private theorem applyPass_preserves_halt_am {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hh : haltsWithResult p' 0 σ₀ σ' am₀ am') :
    ∃ σ_orig, haltsWithResult p 0 σ₀ σ_orig am₀ am' ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  obtain ⟨hcheck, hTrans, hOrigCode, hOrigObs, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have hhalt_cert : ∃ am', haltsWithResult (toPCertificate cert).trans 0 σ₀ σ' am₀ am' :=
    ⟨am', hTransP ▸ hh⟩
  obtain ⟨σ_o, am_f, hhalt_o, hhalt_t, hobs⟩ :=
    soundness_halt (toPCertificate cert) hvalid σ₀ σ' hts' hhalt_cert
  have ham : am_f = am' :=
    (haltsWithResult_unique (hTransP ▸ hhalt_t : haltsWithResult p' 0 σ₀ σ' am₀ am_f) hh).2
  subst ham
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  have hOO : (toPCertificate cert).observable = p.observable := by
    simp [toPCertificate, PCertificate.observable]; exact hOrigObs
  exact ⟨σ_o, Steps_of_code_arrayDecls_eq hOC hOA hhalt_o,
    fun v hv => hobs v (hOO ▸ hv)⟩

/-- A single optimization pass preserves errors with fixed initial AM. -/
private theorem applyPass_preserves_error_am {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hbeh : p' ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ_o am_o' := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have herr_cert : (toPCertificate cert).trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ' am' :=
    hTransP ▸ hbeh
  obtain ⟨σ_o, ⟨am_f, herr_orig⟩⟩ := error_preservation _ hvalid σ₀ hts' herr_cert
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨σ_o, am_f, Steps_of_code_arrayDecls_eq hOC hOA herr_orig⟩

/-- A single optimization pass preserves divergence. -/
private theorem applyPass_preserves_diverge {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p')
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec p' f) (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g, IsInfiniteExec p g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  obtain ⟨hcheck, hTrans, hOrigCode, _, hOrigArr⟩ := applyPass_sound h
  let cert := { pass p with tyCtx := tyCtx }
  have hvalid := soundness_bridge cert hcheck
  have hTransP : (toPCertificate cert).trans = p' := by simp [toPCertificate]; exact hTrans
  have hts' : TypedStore (toPCertificate cert).tyCtx σ₀ := by
    simp [toPCertificate]; exact hts
  have hinf' : IsInfiniteExec (toPCertificate cert).trans f := hTransP ▸ hinf
  obtain ⟨g, hg, hg0⟩ := soundness_diverge _ hvalid f σ₀ hts' hinf' hf0
  have hOC : (toPCertificate cert).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate cert).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  exact ⟨g, IsInfiniteExec_of_code_eq hOC hOA hg, hg0⟩

/-- Each pass preserves observable variable list. -/
private theorem obs_preserved_by_pass (n : String) (tyCtx : TyCtx)
    (pass : Prog → ECertificate) (q q' : Prog)
    (hap : applyPass n tyCtx pass q = .ok q') : q'.observable = q.observable := by
  obtain ⟨hcheck, hTrans, _, hOrigObs, _⟩ := applyPass_sound hap
  rw [← hTrans]
  have hSameObs := same_obs_of_check { pass q with tyCtx := tyCtx } hcheck
  simp at hSameObs
  rw [← hSameObs, hOrigObs]

-- ============================================================
-- § 3. applyPassesPure: inductive soundness
-- ============================================================

/-- `applyPassesPure` preserves observable variables across all passes. -/
theorem applyPassesPure_obs_eq (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog) :
    (applyPassesPure tyCtx passes p).observable = p.observable := by
  induction passes generalizing p with
  | nil => rfl
  | cons np rest ih =>
    simp only [applyPassesPure]
    obtain ⟨name, pass⟩ := np
    split
    · rename_i p' hap; rw [ih _, obs_preserved_by_pass name tyCtx pass p p' hap]
    · exact ih _

/-- `applyPassesPure` preserves halting behavior with fixed initial AM.
    `applyPass` enforces tyCtx on each certificate, so TypedStore is preserved
    without requiring any assumption on the passes. -/
theorem applyPassesPure_preserves_halt_am (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hHalt : haltsWithResult (applyPassesPure tyCtx passes p) 0 σ₀ σ' am₀ am') :
    ∃ σ_orig, haltsWithResult p 0 σ₀ σ_orig am₀ am' ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPassesPure] at hHalt
    exact ⟨σ', hHalt, fun _ _ => rfl⟩
  | cons np rest ih =>
    simp only [applyPassesPure] at hHalt
    obtain ⟨name, pass⟩ := np
    split at hHalt
    · -- Pass succeeded
      rename_i p' hap
      obtain ⟨σ_mid, hHalt_mid, hobs_mid⟩ := ih hHalt
      obtain ⟨σ_orig, hHalt_orig, hobs_orig⟩ :=
        applyPass_preserves_halt_am hap σ₀ hts hHalt_mid
      have hobs_p' := obs_preserved_by_pass name tyCtx pass p p' hap
      exact ⟨σ_orig, hHalt_orig, fun v hv => by
        rw [hobs_mid v (hobs_p' ▸ hv), hobs_orig v hv]⟩
    · -- Pass failed: identity
      exact ih hHalt

/-- `applyPassesPure` preserves error behavior with fixed initial AM. -/
theorem applyPassesPure_preserves_error_am (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {σ' : Store} {am₀ am' : ArrayMem}
    (hErr : (applyPassesPure tyCtx passes p) ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ' am') :
    ∃ σ_o am_o', p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ_o am_o' := by
  induction passes generalizing p σ' am' with
  | nil =>
    simp [applyPassesPure] at hErr
    exact ⟨σ', am', hErr⟩
  | cons np rest ih =>
    simp only [applyPassesPure] at hErr
    obtain ⟨name, pass⟩ := np
    split at hErr
    · rename_i p' hap
      obtain ⟨σ_mid, am_mid, hErr_mid⟩ := ih hErr
      exact applyPass_preserves_error_am hap σ₀ hts hErr_mid
    · exact ih hErr

/-- `applyPassesPure` preserves divergence. -/
theorem applyPassesPure_preserves_diverge (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (σ₀ : Store) (hts : TypedStore tyCtx σ₀)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPassesPure tyCtx passes p) f)
    (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g, IsInfiniteExec p g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  induction passes generalizing p f with
  | nil =>
    simp [applyPassesPure] at hinf
    exact ⟨f, hinf, hf0⟩
  | cons np rest ih =>
    simp only [applyPassesPure] at hinf
    obtain ⟨name, pass⟩ := np
    split at hinf
    · rename_i p' hap
      obtain ⟨g, hg, hg0⟩ := ih hinf hf0
      exact applyPass_preserves_diverge hap σ₀ hts hg hg0
    · exact ih hinf hf0

-- ============================================================
-- § 4. ARM-to-While relation and full end-to-end (halts)
-- ============================================================

/-- The ARM program's observable output matches the While source output.
    For each observable variable with a layout entry, the ARM register or
    stack slot holds the encoded value from the source program's final store.
    Array memory also matches. -/
def ArmMatchesWhile (layout : VarLayout) (observables : List Var)
    (σ_src : Store) (am : ArrayMem) (s : ArmState) : Prop :=
  (∀ v ∈ observables, ∀ loc, layout v = some loc →
    match loc with
    | .stack off => s.stack off = (σ_src v).encode
    | .ireg r    => s.regs r = (σ_src v).encode
    | .freg r    => s.fregs r = (σ_src v).encode) ∧
  s.arrayMem = am

/-- **Full end-to-end correctness (halts): While source → ARM.**

    If a well-typed While program is compiled, optimized, and code-generated
    to ARM, and the optimized TAC halts, then:
    1. The source While program terminates safely
    2. The ARM program reaches a final state whose observable registers/stack
       slots hold the source program's output values -/
theorem while_to_arm_correctness
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok r)
    {σ_opt : Store} {am_opt : ArrayMem}
    (hHalt : haltsWithResult (applyPassesPure prog.tyCtx passes prog.compileToTAC) 0
      (Store.typedInit prog.tyCtx) σ_opt ArrayMem.init am_opt) :
    ∃ fuel σ_src am_src s',
      prog.interp fuel = some (σ_src, am_src) ∧
      ArmSteps r.bodyFlat
        { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
          pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ArmMatchesWhile r.layout prog.compileToTAC.observable σ_src am_src s' := by
  have htc := Program.typeCheckStrict_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  -- ARM simulation from TAC
  obtain ⟨s', hArm, hSimRel⟩ := tacToArm_correctness hGen hHalt
  have hStateRel : ExtStateRel r.layout σ_opt s' := hSimRel.1
  have hAmRel : s'.arrayMem = am_opt := hSimRel.2
  -- Pipeline → original TAC halts with same final AM
  obtain ⟨σ_tac, hHalt_tac, hobs_tac⟩ :=
    applyPassesPure_preserves_halt_am prog.tyCtx passes _ hts hHalt
  have hHalt_init : haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_opt :=
    hInitEq ▸ hHalt_tac
  have hbeh_tac : program_behavior_init prog.compileToTAC prog.initStore (.halts σ_tac) :=
    ⟨am_opt, hHalt_init⟩
  have hsrc := whileToTAC_refinement prog htcs (.halts σ_tac) hbeh_tac
  simp only at hsrc
  obtain ⟨fuel, σ_src, am_h, am_src, hinterp, hHalt_tac2, ham_eq, hobs_src⟩ := hsrc
  have ham_opt : am_h = am_opt := (haltsWithResult_unique hHalt_tac2 hHalt_init).2
  have hnt : Program.noTmpDecls prog.decls = true := by
    unfold Program.typeCheck at htc; simp only [Bool.and_eq_true] at htc; exact htc.1.2
  have hobs_eq := applyPassesPure_obs_eq prog.tyCtx passes prog.compileToTAC
  have hobs_match : ∀ v ∈ prog.compileToTAC.observable, σ_opt v = σ_src v := by
    intro v hv
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
    exact hobs_src w hntw.1 hntw.2
  exact ⟨fuel, σ_src, am_src, s', hinterp, hArm,
    ⟨fun v hv loc hloc => by
      have := hStateRel v loc hloc
      rw [hobs_match v hv] at this
      exact this,
    by rw [hAmRel, ← ham_opt, ham_eq]⟩⟩

-- ============================================================
-- § 5. Full end-to-end: While source → ARM (errors)
-- ============================================================

/-- **Full end-to-end error preservation: While source → ARM.**

    If the optimized TAC reaches an error (division by zero or array
    out-of-bounds), then the source While program is unsafe at some fuel.
    The ARM program also reaches the error (its execution does not get stuck). -/
theorem while_to_arm_error_preservation
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok r)
    {σ_err : Store} {am_err : ArrayMem}
    (hErr : (applyPassesPure prog.tyCtx passes prog.compileToTAC) ⊩
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
  refine ⟨?_, tacToArm_correctness hGen hErr⟩
  obtain ⟨σ_o, am_o', hErr_tac⟩ :=
    applyPassesPure_preserves_error_am prog.tyCtx passes _ hts hErr
  have hErr_init : program_behavior_init prog.compileToTAC prog.initStore (.errors σ_o) :=
    ⟨am_o', hInitEq ▸ hErr_tac⟩
  exact whileToTAC_refinement prog htcs (.errors σ_o) hErr_init

-- ============================================================
-- § 6. Full end-to-end: While source → ARM (diverges)
-- ============================================================

/-- **Full end-to-end divergence preservation: While source → ARM.**

    If the optimized TAC diverges, then the source While program diverges
    (does not terminate at any fuel). -/
theorem while_to_arm_divergence_preservation
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {f : Nat → Cfg}
    (hDiv : IsInfiniteExec (applyPassesPure prog.tyCtx passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init) :
    ∀ fuel, prog.interp fuel = none := by
  have htc := Program.typeCheckStrict_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.tyCtx = prog.initStore :=
    Program.typedInit_eq_initStore prog htc
  have hts : TypedStore prog.tyCtx (Store.typedInit prog.tyCtx) := TypedStore.typedInit _
  obtain ⟨g, hg, hg0⟩ :=
    applyPassesPure_preserves_diverge prog.tyCtx passes _ hts hDiv hf0
  have hdiv_init : program_behavior_init prog.compileToTAC prog.initStore .diverges :=
    ⟨g, hg, hInitEq ▸ hg0⟩
  exact whileToTAC_refinement prog htcs .diverges hdiv_init

-- ============================================================
-- § 7. Totality of generateAsm on the optimized pipeline
-- ============================================================

/-- Bridge: the exec-side `checkSuccessorsInBounds` (which checks every successor
    of every instruction) is strictly stronger than the codegen-facing
    `checkSuccessorsInBounds_prog` (which only looks at goto/ifgoto targets). -/
theorem checkSuccessorsInBounds_prog_of_exec {cert : ECertificate}
    (h : checkSuccessorsInBounds cert = true) :
    checkSuccessorsInBounds_prog cert.trans = true := by
  unfold checkSuccessorsInBounds at h
  unfold checkSuccessorsInBounds_prog
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  obtain ⟨hpos, hAll⟩ := h
  refine ⟨hpos, ?_⟩
  intro pc hpc
  have hext := hAll pc hpc
  cases hp : cert.trans[pc]? with
  | none => simp
  | some instr =>
    rw [hp] at hext
    simp only at hext
    cases instr with
    | goto l => simp [successors, decide_eq_true_eq] at hext ⊢; exact hext
    | ifgoto _ l =>
      simp [successors, decide_eq_true_eq] at hext ⊢
      exact hext.1
    | _ => simp

/-- Helper: decompose `(a && b) = true` into the two conjuncts. -/
private theorem and_true_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by simp [Bool.and_eq_true] at h; exact h

/-- Extract the four codegen prerequisites from `checkCertificateExec`: well-typed,
    codegen prereqs, branch targets, and simple bool ops — all on `cert.trans`.
    `checkCertificateExec` is a left-associative conjunction of 30 checks; we peel
    from the right, naming only the conjuncts we need. -/
private theorem invariants_of_checkCertificateExec {cert : ECertificate}
    (h : checkCertificateExec cert = true) :
    checkWellTypedProg cert.tyCtx cert.trans = true ∧
    checkCodegenPrereqs cert.tyCtx cert.trans = true ∧
    checkBranchTargets cert.trans.code = none ∧
    checkBoolExprSimpleOps cert.trans = true := by
  unfold checkCertificateExec at h
  have ⟨h29, hPrereqs_t⟩  := and_true_split h
  have ⟨h28, _⟩           := and_true_split h29
  have ⟨h27, _⟩           := and_true_split h28
  have ⟨h26, _⟩           := and_true_split h27
  have ⟨h25, _⟩           := and_true_split h26
  have ⟨h24, _⟩           := and_true_split h25
  have ⟨h23, _⟩           := and_true_split h24
  have ⟨h22, hSimple_t⟩   := and_true_split h23
  have ⟨h21, _⟩           := and_true_split h22
  have ⟨h20, _⟩           := and_true_split h21
  have ⟨h19, _⟩           := and_true_split h20
  have ⟨h18, hSIB⟩        := and_true_split h19
  have ⟨h17, _⟩           := and_true_split h18
  have ⟨h16, _⟩           := and_true_split h17
  have ⟨h15, _⟩           := and_true_split h16
  have ⟨h14, _⟩           := and_true_split h15
  have ⟨h13, _⟩           := and_true_split h14
  have ⟨h12, _⟩           := and_true_split h13
  have ⟨h11, _⟩           := and_true_split h12
  have ⟨h10, _⟩           := and_true_split h11
  have ⟨h9,  _⟩           := and_true_split h10
  have ⟨h8,  _⟩           := and_true_split h9
  have ⟨h7,  _⟩           := and_true_split h8
  have ⟨h6,  _⟩           := and_true_split h7
  have ⟨h5,  _⟩           := and_true_split h6
  have ⟨h4,  _⟩           := and_true_split h5
  have ⟨h3,  _⟩           := and_true_split h4
  have ⟨h2,  _⟩           := and_true_split h3
  have ⟨_,   hWT_t⟩       := and_true_split h2
  exact ⟨hWT_t, hPrereqs_t,
    checkBranchTargets_of_successorsInBounds _ (checkSuccessorsInBounds_prog_of_exec hSIB),
    hSimple_t⟩

/-- A single pass preserves the four codegen invariants: if the invariants hold
    at the input `p` and `applyPass` succeeds, they hold at the output `p'`. -/
theorem applyPass_preserves_invariants {name : String} {tyCtx : TyCtx}
    {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name tyCtx pass p = .ok p') :
    checkWellTypedProg tyCtx p' = true ∧
    checkCodegenPrereqs tyCtx p' = true ∧
    checkBranchTargets p'.code = none ∧
    checkBoolExprSimpleOps p' = true := by
  obtain ⟨hcheck, hTrans, _, _, _⟩ := applyPass_sound h
  have ⟨hWT, hPrereqs, hBranch, hSimple⟩ :=
    invariants_of_checkCertificateExec (cert := { pass p with tyCtx := tyCtx }) hcheck
  -- Record field projections reduce definitionally; rewrite .trans to p' via hTrans
  simp only [hTrans] at hWT hPrereqs hBranch hSimple
  exact ⟨hWT, hPrereqs, hBranch, hSimple⟩

/-- `applyPassesPure` preserves the four codegen invariants. Either a pass
    succeeds (and `applyPass_preserves_invariants` transfers them to the new
    program) or fails (and the program is unchanged). -/
theorem applyPassesPure_preserves_invariants (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog)
    (hWT : checkWellTypedProg tyCtx p = true)
    (hPrereqs : checkCodegenPrereqs tyCtx p = true)
    (hBranch : checkBranchTargets p.code = none)
    (hSimple : checkBoolExprSimpleOps p = true) :
    checkWellTypedProg tyCtx (applyPassesPure tyCtx passes p) = true ∧
    checkCodegenPrereqs tyCtx (applyPassesPure tyCtx passes p) = true ∧
    checkBranchTargets (applyPassesPure tyCtx passes p).code = none ∧
    checkBoolExprSimpleOps (applyPassesPure tyCtx passes p) = true := by
  induction passes generalizing p with
  | nil => simp [applyPassesPure]; exact ⟨hWT, hPrereqs, hBranch, hSimple⟩
  | cons np rest ih =>
    simp only [applyPassesPure]
    obtain ⟨name, pass⟩ := np
    split
    · rename_i p' hap
      obtain ⟨hWT', hPrereqs', hBranch', hSimple'⟩ :=
        applyPass_preserves_invariants hap
      exact ih p' hWT' hPrereqs' hBranch' hSimple'
    · exact ih p hWT hPrereqs hBranch hSimple

/-- End-to-end totality on the optimized pipeline: `verifiedGenerateAsm` succeeds
    for any well-typed source program after an arbitrary list of certificate-checked
    optimization passes. Each pass either validates (refining the program) or is
    skipped; the codegen invariants are preserved either way. -/
theorem generateAsm_total_with_passes (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate))) :
    ∃ asm, verifiedGenerateAsm prog.tyCtx
      (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok asm := by
  have htc := prog.typeCheckStrict_typeCheck htcs
  have hWT0 : checkWellTypedProg prog.tyCtx prog.compileToTAC = true :=
    checkWellTypedProg_complete (prog.compileToTAC_wellTyped htc)
  have hPrereqs0 := compileToTAC_codegenPrereqs prog htcs
  have hBranch0 := compileToTAC_checkBranchTargets prog
  have hSimple0 := compileToTAC_checkBoolExprSimpleOps prog
  obtain ⟨hWT, hPrereqs, hBranch, hSimple⟩ :=
    applyPassesPure_preserves_invariants prog.tyCtx passes prog.compileToTAC
      hWT0 hPrereqs0 hBranch0 hSimple0
  exact verifiedGenerateAsm_total prog.tyCtx _ hWT hPrereqs hBranch hSimple
