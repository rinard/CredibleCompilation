import CredibleCompilation.CodeGen
import CredibleCompilation.SoundnessBridge
import CredibleCompilation.RefCompiler.Refinement

/-!
# Pipeline Correctness

Proves that `applyPass` and `optimizePipeline` preserve program semantics.
Chains `soundness_bridge` (executable checker → prop validity) with
`credible_compilation_soundness` (prop validity → behavior preservation).

## Sorrys propagated
- 5 from SoundnessBridge (checkRelConsistency lemmas)
- 2 from ArmCorrectness (arrLoad, arrStore in verifiedGenInstr_correct)
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
  | printInt h => exact .printInt (hg _ ▸ h)
  | printFloat h => exact .printFloat (hg _ ▸ h)

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

/-- `program_behavior` transfers across programs with the same code and arrayDecls. -/
theorem program_behavior_of_code_eq {p q : Prog}
    (hc : p.code = q.code) (ha : p.arrayDecls = q.arrayDecls)
    {σ₀ b} (h : program_behavior p σ₀ b) : program_behavior q σ₀ b := by
  cases b with
  | halts σ' =>
    obtain ⟨am, am', hhalt⟩ := h
    exact ⟨am, am', Steps_of_code_arrayDecls_eq hc ha hhalt⟩
  | errors σ' =>
    obtain ⟨am, am', hsteps⟩ := h
    exact ⟨am, am', Steps_of_code_arrayDecls_eq hc ha hsteps⟩
  | typeErrors σ' =>
    obtain ⟨am, am', hsteps⟩ := h
    exact ⟨am, am', Steps_of_code_arrayDecls_eq hc ha hsteps⟩
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := h
    exact ⟨f, IsInfiniteExec_of_code_eq hc ha hinf, hf0⟩

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
-- § 2. Single-pass behavior preservation
-- ============================================================

/-- A single optimization pass preserves behavior. Uses code-equality transfer
    so no `hOrigId` needed — only `htyctx` (all passes preserve tyCtx).

    **Propagated sorrys:** depends on SoundnessBridge (5 sorrys). -/
theorem applyPass_preserves_behavior {name : String} {pass : Prog → ECertificate} {p p' : Prog}
    (h : applyPass name pass p = .ok p')
    (htyctx : (pass p).orig.tyCtx = (pass p).trans.tyCtx)
    (σ₀ : Store) (hts : TypedStore (pass p).orig.tyCtx σ₀)
    (b : Behavior) (hbeh : program_behavior p' σ₀ b) :
    match b with
    | .halts σ' => ∃ σ_orig am am_f,
        haltsWithResult p 0 σ₀ σ_orig am am_f ∧
        ∀ v ∈ p.observable, σ' v = σ_orig v
    | .errors _ => ∃ σ_o am_o am_o', p ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.error σ_o am_o'
    | .typeErrors _ => False
    | .diverges => ∃ f, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  obtain ⟨hcheck, hTrans, hOrigCode, hOrigObs, hOrigArr⟩ := applyPass_sound h
  have hvalid := soundness_bridge (pass p) hcheck htyctx
  have hTransP : (toPCertificate (pass p)).trans = p' := by simp [toPCertificate]; exact hTrans
  have hbeh' : program_behavior (toPCertificate (pass p)).trans σ₀ b := hTransP ▸ hbeh
  have hts' : TypedStore (toPCertificate (pass p)).tyCtx σ₀ := by
    simp [toPCertificate, PCertificate.tyCtx]; exact hts
  have hsound := credible_compilation_soundness (toPCertificate (pass p)) hvalid σ₀ hts' b hbeh'
  have hOC : (toPCertificate (pass p)).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate (pass p)).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  have hOO : (toPCertificate (pass p)).observable = p.observable := by
    simp [toPCertificate, PCertificate.observable]; exact hOrigObs
  cases b with
  | halts σ' =>
    simp only at hsound ⊢
    obtain ⟨σ_o, am, am_f, hhalt, hobs⟩ := hsound
    exact ⟨σ_o, am, am_f,
      Steps_of_code_arrayDecls_eq hOC hOA hhalt,
      fun v hv => hobs v (hOO ▸ hv)⟩
  | errors σ' =>
    simp only at hsound ⊢
    obtain ⟨σ_o, am_o, am_o', hsteps⟩ := hsound
    exact ⟨σ_o, am_o, am_o', Steps_of_code_arrayDecls_eq hOC hOA hsteps⟩
  | typeErrors σ' => exact hsound
  | diverges =>
    simp only at hsound ⊢
    obtain ⟨f, hinf, hf0⟩ := hsound
    exact ⟨f, IsInfiniteExec_of_code_eq hOC hOA hinf, hf0⟩

-- ============================================================
-- § 3. Pipeline behavior preservation
-- ============================================================

/-- Extract same_observable from checkCertificateExec. -/
private theorem same_obs_of_check (cert : ECertificate)
    (h : checkCertificateExec cert = true) :
    cert.orig.observable = cert.trans.observable := by
  unfold checkCertificateExec at h
  simp only [Bool.and_eq_true] at h
  exact beq_iff_eq.mp h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- Each optimization pass preserves the observable variable list. -/
private theorem obs_preserved_by_pass (n : String) (pass : Prog → ECertificate) (q q' : Prog)
    (hap : applyPass n pass q = .ok q') : q'.observable = q.observable := by
  obtain ⟨hcheck, hTrans, _, hOrigObs, _⟩ := applyPass_sound hap
  rw [← hTrans]
  have hSameObs := same_obs_of_check (pass q) hcheck
  rw [← hSameObs, hOrigObs]

/-- The full optimization pipeline preserves observable behavior.
    The tyCtx hypotheses hold for all passes (they set tyCtx := prog.tyCtx).

    **Propagated sorrys:** depends on SoundnessBridge (5 sorrys). -/
theorem optimizePipeline_preserves_behavior {p p' : Prog}
    (h : optimizePipeline p = .ok p')
    (hty_dce : ∀ q, (DCEOpt.optimize q).orig.tyCtx = (DCEOpt.optimize q).trans.tyCtx)
    (hty_licm : ∀ q, (LICMOpt.optimize q).orig.tyCtx = (LICMOpt.optimize q).trans.tyCtx)
    (hty_cp : ∀ q, (ConstPropOpt.optimize q).orig.tyCtx = (ConstPropOpt.optimize q).trans.tyCtx)
    (hty_dae : ∀ q, (DAEOpt.optimize q).orig.tyCtx = (DAEOpt.optimize q).trans.tyCtx)
    (hty_fma : ∀ q, (FMAFusionOpt.optimize q).orig.tyCtx = (FMAFusionOpt.optimize q).trans.tyCtx)
    (hty_cse : ∀ q, (CSEOpt.optimize q).orig.tyCtx = (CSEOpt.optimize q).trans.tyCtx)
    (hty_ch : ∀ q, (ConstHoistOpt.optimize q).orig.tyCtx = (ConstHoistOpt.optimize q).trans.tyCtx)
    (hty_ph : ∀ q, (PeepholeOpt.optimize q).orig.tyCtx = (PeepholeOpt.optimize q).trans.tyCtx)
    (hty_ra : ∀ q, (RegAllocOpt.optimize q).orig.tyCtx = (RegAllocOpt.optimize q).trans.tyCtx)
    (htyO_dce : ∀ q, (DCEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_licm : ∀ q, (LICMOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_cp : ∀ q, (ConstPropOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_dae : ∀ q, (DAEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_fma : ∀ q, (FMAFusionOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_cse : ∀ q, (CSEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ch : ∀ q, (ConstHoistOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ph : ∀ q, (PeepholeOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ra : ∀ q, (RegAllocOpt.optimize q).orig.tyCtx = q.tyCtx)
    (σ₀ : Store) (hts : TypedStore p.tyCtx σ₀)
    (b : Behavior) (hbeh : program_behavior p' σ₀ b) :
    match b with
    | .halts σ' => ∃ σ_orig am am_f,
        haltsWithResult p 0 σ₀ σ_orig am am_f ∧
        ∀ v ∈ p.observable, σ' v = σ_orig v
    | .errors _ => ∃ σ_o am_o am_o', p ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.error σ_o am_o'
    | .typeErrors _ => False
    | .diverges => ∃ f, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀ ArrayMem.init := by
  -- Decompose pipeline: extract each intermediate program from nested Except.bind
  have bind_ok : ∀ {α β : Type} {x : Except String α} {f : α → Except String β} {b : β},
      Except.bind x f = .ok b → ∃ a, x = .ok a ∧ f a = .ok b := by
    intro α β x f b h; cases x with | error e => simp [Except.bind] at h | ok a => exact ⟨a, rfl, h⟩
  unfold optimizePipeline at h; simp only [bind] at h
  obtain ⟨p1, h1, h⟩ := bind_ok h
  obtain ⟨p2, h2, h⟩ := bind_ok h
  obtain ⟨p3, h3, h⟩ := bind_ok h
  obtain ⟨p4, h4, h⟩ := bind_ok h
  obtain ⟨p5, h5, h⟩ := bind_ok h
  obtain ⟨p6, h6, h⟩ := bind_ok h
  obtain ⟨p7, h7, h⟩ := bind_ok h
  obtain ⟨p8, h8, h⟩ := bind_ok h
  obtain ⟨p9, h9, h⟩ := bind_ok h
  obtain ⟨p10, h10, h11⟩ := bind_ok h
  -- Derive tyCtx chain: all intermediate programs have same tyCtx as p
  have hT := fun {n pass q q'} (h : applyPass n pass q = .ok q') =>
    (applyPass_sound h).2.1
  have htyp1 : p1.tyCtx = p.tyCtx := by rw [← hT h1, ← hty_dce p, htyO_dce p]
  have htyp2 : p2.tyCtx = p.tyCtx := by rw [← hT h2, ← hty_licm p1, htyO_licm p1, htyp1]
  have htyp3 : p3.tyCtx = p.tyCtx := by rw [← hT h3, ← hty_cp p2, htyO_cp p2, htyp2]
  have htyp4 : p4.tyCtx = p.tyCtx := by rw [← hT h4, ← hty_dce p3, htyO_dce p3, htyp3]
  have htyp5 : p5.tyCtx = p.tyCtx := by rw [← hT h5, ← hty_dae p4, htyO_dae p4, htyp4]
  have htyp6 : p6.tyCtx = p.tyCtx := by rw [← hT h6, ← hty_fma p5, htyO_fma p5, htyp5]
  have htyp7 : p7.tyCtx = p.tyCtx := by rw [← hT h7, ← hty_cse p6, htyO_cse p6, htyp6]
  have htyp8 : p8.tyCtx = p.tyCtx := by rw [← hT h8, ← hty_ch p7, htyO_ch p7, htyp7]
  have htyp9 : p9.tyCtx = p.tyCtx := by rw [← hT h9, ← hty_ph p8, htyO_ph p8, htyp8]
  have htyp10 : p10.tyCtx = p.tyCtx := by rw [← hT h10, ← hty_dce p9, htyO_dce p9, htyp9]
  -- Observable chain: all intermediate programs have same observable as p
  have hobsp1 : p1.observable = p.observable := obs_preserved_by_pass _ _ _ _ h1
  have hobsp2 : p2.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h2, hobsp1]
  have hobsp3 : p3.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h3, hobsp2]
  have hobsp4 : p4.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h4, hobsp3]
  have hobsp5 : p5.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h5, hobsp4]
  have hobsp6 : p6.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h6, hobsp5]
  have hobsp7 : p7.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h7, hobsp6]
  have hobsp8 : p8.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h8, hobsp7]
  have hobsp9 : p9.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h9, hobsp8]
  have hobsp10 : p10.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h10, hobsp9]
  -- Helper: TypedStore transfer
  have tsAt : ∀ (pass : Prog → ECertificate) (q : Prog),
      (pass q).orig.tyCtx = q.tyCtx → q.tyCtx = p.tyCtx →
      TypedStore (pass q).orig.tyCtx σ₀ := fun _ q hO hq => hO ▸ hq ▸ hts
  -- Chain backward: apply applyPass_preserves_behavior for each pass
  -- For each behavior case, chain the results
  cases b with
  | halts σ' =>
    simp only at hbeh ⊢
    -- Step 11: p' halts → p10 halts with σ₁₀, obs eq on p10.observable
    have beh11 := applyPass_preserves_behavior h11 (hty_ra _) σ₀ (tsAt _ _ (htyO_ra _) htyp10) (.halts σ') hbeh
    simp only at beh11
    obtain ⟨σ₁₀, a₁₀, am₁₀, halt₁₀, obs₁₀⟩ := beh11
    -- Step 10-1: chain backward
    have mk_beh : ∀ {q σ am am'}, haltsWithResult q 0 σ₀ σ am am' →
        program_behavior q σ₀ (.halts σ) := fun h => ⟨_, _, h⟩
    have beh10 := applyPass_preserves_behavior h10 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) htyp9) (.halts σ₁₀) (mk_beh halt₁₀)
    simp only at beh10; obtain ⟨σ₉, a₉, am₉, halt₉, obs₉⟩ := beh10
    have beh9 := applyPass_preserves_behavior h9 (hty_ph _) σ₀ (tsAt _ _ (htyO_ph _) htyp8) (.halts σ₉) (mk_beh halt₉)
    simp only at beh9; obtain ⟨σ₈, a₈, am₈, halt₈, obs₈⟩ := beh9
    have beh8 := applyPass_preserves_behavior h8 (hty_ch _) σ₀ (tsAt _ _ (htyO_ch _) htyp7) (.halts σ₈) (mk_beh halt₈)
    simp only at beh8; obtain ⟨σ₇, a₇, am₇, halt₇, obs₇⟩ := beh8
    have beh7 := applyPass_preserves_behavior h7 (hty_cse _) σ₀ (tsAt _ _ (htyO_cse _) htyp6) (.halts σ₇) (mk_beh halt₇)
    simp only at beh7; obtain ⟨σ₆, a₆, am₆, halt₆, obs₆⟩ := beh7
    have beh6 := applyPass_preserves_behavior h6 (hty_fma _) σ₀ (tsAt _ _ (htyO_fma _) htyp5) (.halts σ₆) (mk_beh halt₆)
    simp only at beh6; obtain ⟨σ₅, a₅, am₅, halt₅, obs₅⟩ := beh6
    have beh5 := applyPass_preserves_behavior h5 (hty_dae _) σ₀ (tsAt _ _ (htyO_dae _) htyp4) (.halts σ₅) (mk_beh halt₅)
    simp only at beh5; obtain ⟨σ₄, a₄, am₄, halt₄, obs₄⟩ := beh5
    have beh4 := applyPass_preserves_behavior h4 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) htyp3) (.halts σ₄) (mk_beh halt₄)
    simp only at beh4; obtain ⟨σ₃, a₃, am₃, halt₃, obs₃⟩ := beh4
    have beh3 := applyPass_preserves_behavior h3 (hty_cp _) σ₀ (tsAt _ _ (htyO_cp _) htyp2) (.halts σ₃) (mk_beh halt₃)
    simp only at beh3; obtain ⟨σ₂, a₂, am₂, halt₂, obs₂⟩ := beh3
    have beh2 := applyPass_preserves_behavior h2 (hty_licm _) σ₀ (tsAt _ _ (htyO_licm _) htyp1) (.halts σ₂) (mk_beh halt₂)
    simp only at beh2; obtain ⟨σ₁, a₁, am₁, halt₁, obs₁⟩ := beh2
    have beh1 := applyPass_preserves_behavior h1 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) rfl) (.halts σ₁) (mk_beh halt₁)
    simp only at beh1; obtain ⟨σ₀', a₀, am₀, halt₀, obs₀⟩ := beh1
    -- Chain observables: σ' v = σ₁₀ v = σ₉ v = ... = σ₀' v for v ∈ p.observable
    exact ⟨σ₀', a₀, am₀, halt₀, fun v hv => by
      calc σ' v = σ₁₀ v := obs₁₀ v (hobsp10 ▸ hv)
        _ = σ₉ v := obs₉ v (hobsp9 ▸ hv)
        _ = σ₈ v := obs₈ v (hobsp8 ▸ hv)
        _ = σ₇ v := obs₇ v (hobsp7 ▸ hv)
        _ = σ₆ v := obs₆ v (hobsp6 ▸ hv)
        _ = σ₅ v := obs₅ v (hobsp5 ▸ hv)
        _ = σ₄ v := obs₄ v (hobsp4 ▸ hv)
        _ = σ₃ v := obs₃ v (hobsp3 ▸ hv)
        _ = σ₂ v := obs₂ v (hobsp2 ▸ hv)
        _ = σ₁ v := obs₁ v (hobsp1 ▸ hv)
        _ = σ₀' v := obs₀ v hv⟩
  | errors σ' =>
    simp only at hbeh ⊢
    -- Each step: p_{i+1} errors → p_i errors
    have mk_beh : ∀ {q σ am am'}, (q ⊩ Cfg.run 0 σ₀ am ⟶* Cfg.error σ am') →
        program_behavior q σ₀ (.errors σ) := fun h => ⟨_, _, h⟩
    obtain ⟨σ₁₀, a₁₀, a₁₀', s₁₀⟩ := applyPass_preserves_behavior h11 (hty_ra _) σ₀ (tsAt _ _ (htyO_ra _) htyp10) (.errors σ') hbeh
    obtain ⟨σ₉, a₉, a₉', s₉⟩ := applyPass_preserves_behavior h10 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) htyp9) (.errors σ₁₀) (mk_beh s₁₀)
    obtain ⟨σ₈, a₈, a₈', s₈⟩ := applyPass_preserves_behavior h9 (hty_ph _) σ₀ (tsAt _ _ (htyO_ph _) htyp8) (.errors σ₉) (mk_beh s₉)
    obtain ⟨σ₇, a₇, a₇', s₇⟩ := applyPass_preserves_behavior h8 (hty_ch _) σ₀ (tsAt _ _ (htyO_ch _) htyp7) (.errors σ₈) (mk_beh s₈)
    obtain ⟨σ₆, a₆, a₆', s₆⟩ := applyPass_preserves_behavior h7 (hty_cse _) σ₀ (tsAt _ _ (htyO_cse _) htyp6) (.errors σ₇) (mk_beh s₇)
    obtain ⟨σ₅, a₅, a₅', s₅⟩ := applyPass_preserves_behavior h6 (hty_fma _) σ₀ (tsAt _ _ (htyO_fma _) htyp5) (.errors σ₆) (mk_beh s₆)
    obtain ⟨σ₄, a₄, a₄', s₄⟩ := applyPass_preserves_behavior h5 (hty_dae _) σ₀ (tsAt _ _ (htyO_dae _) htyp4) (.errors σ₅) (mk_beh s₅)
    obtain ⟨σ₃, a₃, a₃', s₃⟩ := applyPass_preserves_behavior h4 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) htyp3) (.errors σ₄) (mk_beh s₄)
    obtain ⟨σ₂, a₂, a₂', s₂⟩ := applyPass_preserves_behavior h3 (hty_cp _) σ₀ (tsAt _ _ (htyO_cp _) htyp2) (.errors σ₃) (mk_beh s₃)
    obtain ⟨σ₁, a₁, a₁', s₁⟩ := applyPass_preserves_behavior h2 (hty_licm _) σ₀ (tsAt _ _ (htyO_licm _) htyp1) (.errors σ₂) (mk_beh s₂)
    obtain ⟨σ₀', a₀, a₀', s₀⟩ := applyPass_preserves_behavior h1 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) rfl) (.errors σ₁) (mk_beh s₁)
    exact ⟨σ₀', a₀, a₀', s₀⟩
  | typeErrors σ' =>
    exact applyPass_preserves_behavior h11 (hty_ra _) σ₀ (tsAt _ _ (htyO_ra _) htyp10) (.typeErrors σ') hbeh
  | diverges =>
    simp only at hbeh ⊢
    have mk_beh : ∀ {q f}, IsInfiniteExec q f → f 0 = Cfg.run 0 σ₀ ArrayMem.init →
        program_behavior q σ₀ .diverges := fun h hf => ⟨_, h, hf⟩
    obtain ⟨f₁₀, i₁₀, e₁₀⟩ := applyPass_preserves_behavior h11 (hty_ra _) σ₀ (tsAt _ _ (htyO_ra _) htyp10) .diverges hbeh
    obtain ⟨f₉, i₉, e₉⟩ := applyPass_preserves_behavior h10 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) htyp9) .diverges (mk_beh i₁₀ e₁₀)
    obtain ⟨f₈, i₈, e₈⟩ := applyPass_preserves_behavior h9 (hty_ph _) σ₀ (tsAt _ _ (htyO_ph _) htyp8) .diverges (mk_beh i₉ e₉)
    obtain ⟨f₇, i₇, e₇⟩ := applyPass_preserves_behavior h8 (hty_ch _) σ₀ (tsAt _ _ (htyO_ch _) htyp7) .diverges (mk_beh i₈ e₈)
    obtain ⟨f₆, i₆, e₆⟩ := applyPass_preserves_behavior h7 (hty_cse _) σ₀ (tsAt _ _ (htyO_cse _) htyp6) .diverges (mk_beh i₇ e₇)
    obtain ⟨f₅, i₅, e₅⟩ := applyPass_preserves_behavior h6 (hty_fma _) σ₀ (tsAt _ _ (htyO_fma _) htyp5) .diverges (mk_beh i₆ e₆)
    obtain ⟨f₄, i₄, e₄⟩ := applyPass_preserves_behavior h5 (hty_dae _) σ₀ (tsAt _ _ (htyO_dae _) htyp4) .diverges (mk_beh i₅ e₅)
    obtain ⟨f₃, i₃, e₃⟩ := applyPass_preserves_behavior h4 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) htyp3) .diverges (mk_beh i₄ e₄)
    obtain ⟨f₂, i₂, e₂⟩ := applyPass_preserves_behavior h3 (hty_cp _) σ₀ (tsAt _ _ (htyO_cp _) htyp2) .diverges (mk_beh i₃ e₃)
    obtain ⟨f₁, i₁, e₁⟩ := applyPass_preserves_behavior h2 (hty_licm _) σ₀ (tsAt _ _ (htyO_licm _) htyp1) .diverges (mk_beh i₂ e₂)
    obtain ⟨f₀, i₀, e₀⟩ := applyPass_preserves_behavior h1 (hty_dce _) σ₀ (tsAt _ _ (htyO_dce _) rfl) .diverges (mk_beh i₁ e₁)
    exact ⟨f₀, i₀, e₀⟩

/-- Specialization of `applyPass_preserves_behavior` for halts with a fixed
    initial ArrayMem. The initial AM is preserved through the soundness chain. -/
private theorem applyPass_preserves_halt_am {name : String} {pass : Prog → ECertificate}
    {p p' : Prog}
    (h : applyPass name pass p = .ok p')
    (htyctx : (pass p).orig.tyCtx = (pass p).trans.tyCtx)
    (σ₀ : Store) (hts : TypedStore (pass p).orig.tyCtx σ₀)
    {σ' : Store} {am₀ : ArrayMem}
    (hbeh : ∃ am', haltsWithResult p' 0 σ₀ σ' am₀ am') :
    ∃ σ_orig am_f, haltsWithResult p 0 σ₀ σ_orig am₀ am_f ∧
      ∀ v ∈ p.observable, σ' v = σ_orig v := by
  obtain ⟨am', hh⟩ := hbeh
  obtain ⟨hcheck, hTrans, hOrigCode, hOrigObs, hOrigArr⟩ := applyPass_sound h
  have hvalid := soundness_bridge (pass p) hcheck htyctx
  have hTransP : (toPCertificate (pass p)).trans = p' := by simp [toPCertificate]; exact hTrans
  -- Use soundness_halt directly with explicit am₀
  have hts' : TypedStore (toPCertificate (pass p)).tyCtx σ₀ := by
    simp [toPCertificate, PCertificate.tyCtx]; exact hts
  have hhalt_cert : ∃ am', haltsWithResult (toPCertificate (pass p)).trans 0 σ₀ σ' am₀ am' :=
    ⟨am', hTransP ▸ hh⟩
  obtain ⟨σ_o, am_f, hconj⟩ :=
    soundness_halt (toPCertificate (pass p)) hvalid σ₀ σ' hts' hhalt_cert
  have hhalt_o := hconj.1
  have hobs := hconj.2.2
  have hOC : (toPCertificate (pass p)).orig.code = p.code := by simp [toPCertificate]; exact hOrigCode
  have hOA : (toPCertificate (pass p)).orig.arrayDecls = p.arrayDecls := by simp [toPCertificate]; exact hOrigArr
  have hOO : (toPCertificate (pass p)).observable = p.observable := by
    simp [toPCertificate, PCertificate.observable]; exact hOrigObs
  exact ⟨σ_o, am_f, Steps_of_code_arrayDecls_eq hOC hOA hhalt_o,
    fun v hv => hobs v (hOO ▸ hv)⟩

-- ============================================================
-- § 4. End-to-end: TAC → optimized TAC → ARM
-- ============================================================

/-- ARM codegen correctness: optimized TAC steps are simulated by ARM steps.

    **Propagated sorrys:** 2 from ArmCorrectness (arrLoad, arrStore). -/
theorem pipeline_to_arm_correctness {p : Prog} {r : VerifiedAsmResult}
    (p_opt : Prog)
    (hOpt : optimizePipeline p = .ok p_opt)
    (hGen : verifiedGenerateAsm p_opt = .ok r)
    {cfg' : Cfg}
    (hSteps : p_opt ⊩ Cfg.run 0 (Store.typedInit p_opt.tyCtx) (fun _ _ => 0) ⟶* cfg') :
    ∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap cfg' s' :=
  tacToArm_correctness hGen hSteps

-- ============================================================
-- § 5. Top-level: original TAC → ARM preserves observables
-- ============================================================

/-- **Top-level correctness theorem.** If:
    1. The optimization pipeline succeeds: `optimizePipeline p = .ok p_opt`
    2. ARM code generation succeeds: `verifiedGenerateAsm p_opt = .ok r`
    3. The optimized TAC halts: `p_opt ⊩ run 0 σ₀ am₀ ⟶* halt σ_opt am_opt`

    Then the original TAC program also halts, and the observable variables
    have the same values in both the original and optimized executions.

    This composes `optimizePipeline_preserves_behavior` (TAC → optimized TAC)
    with `tacToArm_correctness` (optimized TAC → ARM simulation).

    **Hypotheses on passes:** all passes preserve tyCtx (hty_*, htyO_*).
    These hold by construction (every pass sets tyCtx := prog.tyCtx).

    **Propagated sorrys:** SoundnessBridge (5), ArmCorrectness (2). -/
theorem end_to_end_correctness {p p_opt : Prog} {r : VerifiedAsmResult}
    (hOpt : optimizePipeline p = .ok p_opt)
    (hGen : verifiedGenerateAsm p_opt = .ok r)
    -- tyCtx preservation (holds for all passes by construction)
    (hty_dce : ∀ q, (DCEOpt.optimize q).orig.tyCtx = (DCEOpt.optimize q).trans.tyCtx)
    (hty_licm : ∀ q, (LICMOpt.optimize q).orig.tyCtx = (LICMOpt.optimize q).trans.tyCtx)
    (hty_cp : ∀ q, (ConstPropOpt.optimize q).orig.tyCtx = (ConstPropOpt.optimize q).trans.tyCtx)
    (hty_dae : ∀ q, (DAEOpt.optimize q).orig.tyCtx = (DAEOpt.optimize q).trans.tyCtx)
    (hty_fma : ∀ q, (FMAFusionOpt.optimize q).orig.tyCtx = (FMAFusionOpt.optimize q).trans.tyCtx)
    (hty_cse : ∀ q, (CSEOpt.optimize q).orig.tyCtx = (CSEOpt.optimize q).trans.tyCtx)
    (hty_ch : ∀ q, (ConstHoistOpt.optimize q).orig.tyCtx = (ConstHoistOpt.optimize q).trans.tyCtx)
    (hty_ph : ∀ q, (PeepholeOpt.optimize q).orig.tyCtx = (PeepholeOpt.optimize q).trans.tyCtx)
    (hty_ra : ∀ q, (RegAllocOpt.optimize q).orig.tyCtx = (RegAllocOpt.optimize q).trans.tyCtx)
    (htyO_dce : ∀ q, (DCEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_licm : ∀ q, (LICMOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_cp : ∀ q, (ConstPropOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_dae : ∀ q, (DAEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_fma : ∀ q, (FMAFusionOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_cse : ∀ q, (CSEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ch : ∀ q, (ConstHoistOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ph : ∀ q, (PeepholeOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ra : ∀ q, (RegAllocOpt.optimize q).orig.tyCtx = q.tyCtx)
    -- Optimized program halts
    {σ_opt : Store} {am_opt : ArrayMem}
    (hHalt : haltsWithResult p_opt 0 (Store.typedInit p_opt.tyCtx) σ_opt ArrayMem.init am_opt) :
    -- Then: (1) original TAC halts from ArrayMem.init with same observables
    (∃ σ_orig am_f,
      haltsWithResult p 0 (Store.typedInit p.tyCtx) σ_orig ArrayMem.init am_f ∧
      ∀ v ∈ p.observable, σ_opt v = σ_orig v) ∧
    -- (2) ARM simulates the optimized TAC halt
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap (.halt σ_opt am_opt) s') := by
  constructor
  · -- (1) Pipeline preserves behavior: optimized halt → original halt with same observables
    -- Need: TypedStore p.tyCtx (Store.typedInit p.tyCtx)
    have hts : TypedStore p.tyCtx (Store.typedInit p.tyCtx) := TypedStore.typedInit p.tyCtx
    -- Need: TypedStore p.tyCtx (Store.typedInit p_opt.tyCtx) — but p_opt.tyCtx may differ
    -- Actually optimizePipeline preserves tyCtx, so p_opt.tyCtx = p.tyCtx
    -- Derive from the pipeline decomposition
    have hTyOpt : p_opt.tyCtx = p.tyCtx := by
      have bind_ok' : ∀ {α β : Type} {x : Except String α} {f : α → Except String β} {b : β},
          Except.bind x f = .ok b → ∃ a, x = .ok a ∧ f a = .ok b := by
        intro α β x f b h; cases x with | error e => simp [Except.bind] at h | ok a => exact ⟨a, rfl, h⟩
      unfold optimizePipeline at hOpt; simp only [bind] at hOpt
      obtain ⟨q1, hq1, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q2, hq2, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q3, hq3, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q4, hq4, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q5, hq5, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q6, hq6, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q7, hq7, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q8, hq8, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q9, hq9, hOpt⟩ := bind_ok' hOpt
      obtain ⟨q10, hq10, hq11⟩ := bind_ok' hOpt
      have hT := fun {n pass q q'} (h : applyPass n pass q = .ok q') => (applyPass_sound h).2.1
      calc p_opt.tyCtx
          = (RegAllocOpt.optimize q10).trans.tyCtx := by rw [← hT hq11]
        _ = q10.tyCtx := by rw [← htyO_ra q10, hty_ra q10]
        _ = q9.tyCtx := by rw [← hT hq10, ← hty_dce q9, htyO_dce q9]
        _ = q8.tyCtx := by rw [← hT hq9, ← hty_ph q8, htyO_ph q8]
        _ = q7.tyCtx := by rw [← hT hq8, ← hty_ch q7, htyO_ch q7]
        _ = q6.tyCtx := by rw [← hT hq7, ← hty_cse q6, htyO_cse q6]
        _ = q5.tyCtx := by rw [← hT hq6, ← hty_fma q5, htyO_fma q5]
        _ = q4.tyCtx := by rw [← hT hq5, ← hty_dae q4, htyO_dae q4]
        _ = q3.tyCtx := by rw [← hT hq4, ← hty_dce q3, htyO_dce q3]
        _ = q2.tyCtx := by rw [← hT hq3, ← hty_cp q2, htyO_cp q2]
        _ = q1.tyCtx := by rw [← hT hq2, ← hty_licm q1, htyO_licm q1]
        _ = p.tyCtx := by rw [← hT hq1, ← hty_dce p, htyO_dce p]
    -- Use applyPass_preserves_halt_am to thread ArrayMem.init through the pipeline
    have bind_ok' : ∀ {α β : Type} {x : Except String α} {f : α → Except String β} {b : β},
        Except.bind x f = .ok b → ∃ a, x = .ok a ∧ f a = .ok b := by
      intro α β x f b h; cases x with | error e => simp [Except.bind] at h | ok a => exact ⟨a, rfl, h⟩
    unfold optimizePipeline at hOpt; simp only [bind] at hOpt
    obtain ⟨q1, h1, hOpt'⟩ := bind_ok' hOpt
    obtain ⟨q2, h2, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q3, h3, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q4, h4, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q5, h5, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q6, h6, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q7, h7, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q8, h8, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q9, h9, hOpt'⟩ := bind_ok' hOpt'
    obtain ⟨q10, h10, h11⟩ := bind_ok' hOpt'
    have hT := fun {n pass q q'} (h : applyPass n pass q = .ok q') => (applyPass_sound h).2.1
    have htyp1 : q1.tyCtx = p.tyCtx := by rw [← hT h1, ← hty_dce p, htyO_dce p]
    have htyp2 : q2.tyCtx = p.tyCtx := by rw [← hT h2, ← hty_licm q1, htyO_licm q1, htyp1]
    have htyp3 : q3.tyCtx = p.tyCtx := by rw [← hT h3, ← hty_cp q2, htyO_cp q2, htyp2]
    have htyp4 : q4.tyCtx = p.tyCtx := by rw [← hT h4, ← hty_dce q3, htyO_dce q3, htyp3]
    have htyp5 : q5.tyCtx = p.tyCtx := by rw [← hT h5, ← hty_dae q4, htyO_dae q4, htyp4]
    have htyp6 : q6.tyCtx = p.tyCtx := by rw [← hT h6, ← hty_fma q5, htyO_fma q5, htyp5]
    have htyp7 : q7.tyCtx = p.tyCtx := by rw [← hT h7, ← hty_cse q6, htyO_cse q6, htyp6]
    have htyp8 : q8.tyCtx = p.tyCtx := by rw [← hT h8, ← hty_ch q7, htyO_ch q7, htyp7]
    have htyp9 : q9.tyCtx = p.tyCtx := by rw [← hT h9, ← hty_ph q8, htyO_ph q8, htyp8]
    have htyp10 : q10.tyCtx = p.tyCtx := by rw [← hT h10, ← hty_dce q9, htyO_dce q9, htyp9]
    have tsAt : ∀ (pass : Prog → ECertificate) (q : Prog),
        (pass q).orig.tyCtx = q.tyCtx → q.tyCtx = p.tyCtx →
        TypedStore (pass q).orig.tyCtx (Store.typedInit p.tyCtx) :=
      fun _ q hO hq => hO ▸ hq ▸ hts
    -- Chain: thread ArrayMem.init backward through each pass
    have hobsp1 : q1.observable = p.observable := obs_preserved_by_pass _ _ _ _ h1
    have hobsp2 : q2.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h2, hobsp1]
    have hobsp3 : q3.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h3, hobsp2]
    have hobsp4 : q4.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h4, hobsp3]
    have hobsp5 : q5.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h5, hobsp4]
    have hobsp6 : q6.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h6, hobsp5]
    have hobsp7 : q7.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h7, hobsp6]
    have hobsp8 : q8.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h8, hobsp7]
    have hobsp9 : q9.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h9, hobsp8]
    have hobsp10 : q10.observable = p.observable := by rw [obs_preserved_by_pass _ _ _ _ h10, hobsp9]
    have hHalt' : haltsWithResult p_opt 0 (Store.typedInit p.tyCtx) σ_opt ArrayMem.init am_opt :=
      hTyOpt ▸ hHalt
    obtain ⟨σ₁₀, am₁₀, h₁₀, obs₁₀⟩ := applyPass_preserves_halt_am h11 (hty_ra _) _ (tsAt _ _ (htyO_ra _) htyp10) ⟨am_opt, hHalt'⟩
    obtain ⟨σ₉, am₉, h₉, obs₉⟩ := applyPass_preserves_halt_am h10 (hty_dce _) _ (tsAt _ _ (htyO_dce _) htyp9) ⟨am₁₀, h₁₀⟩
    obtain ⟨σ₈, am₈, h₈, obs₈⟩ := applyPass_preserves_halt_am h9 (hty_ph _) _ (tsAt _ _ (htyO_ph _) htyp8) ⟨am₉, h₉⟩
    obtain ⟨σ₇, am₇, h₇, obs₇⟩ := applyPass_preserves_halt_am h8 (hty_ch _) _ (tsAt _ _ (htyO_ch _) htyp7) ⟨am₈, h₈⟩
    obtain ⟨σ₆, am₆, h₆, obs₆⟩ := applyPass_preserves_halt_am h7 (hty_cse _) _ (tsAt _ _ (htyO_cse _) htyp6) ⟨am₇, h₇⟩
    obtain ⟨σ₅, am₅, h₅, obs₅⟩ := applyPass_preserves_halt_am h6 (hty_fma _) _ (tsAt _ _ (htyO_fma _) htyp5) ⟨am₆, h₆⟩
    obtain ⟨σ₄, am₄, h₄, obs₄⟩ := applyPass_preserves_halt_am h5 (hty_dae _) _ (tsAt _ _ (htyO_dae _) htyp4) ⟨am₅, h₅⟩
    obtain ⟨σ₃, am₃, h₃, obs₃⟩ := applyPass_preserves_halt_am h4 (hty_dce _) _ (tsAt _ _ (htyO_dce _) htyp3) ⟨am₄, h₄⟩
    obtain ⟨σ₂, am₂, h₂, obs₂⟩ := applyPass_preserves_halt_am h3 (hty_cp _) _ (tsAt _ _ (htyO_cp _) htyp2) ⟨am₃, h₃⟩
    obtain ⟨σ₁, am₁, h₁, obs₁⟩ := applyPass_preserves_halt_am h2 (hty_licm _) _ (tsAt _ _ (htyO_licm _) htyp1) ⟨am₂, h₂⟩
    obtain ⟨σ₀', am₀, h₀, obs₀⟩ := applyPass_preserves_halt_am h1 (hty_dce _) _ (tsAt _ _ (htyO_dce _) rfl) ⟨am₁, h₁⟩
    exact ⟨σ₀', am₀, h₀, fun v hv => by
      calc σ_opt v = σ₁₀ v := obs₁₀ v (hobsp10 ▸ hv)
        _ = σ₉ v := obs₉ v (hobsp9 ▸ hv)
        _ = σ₈ v := obs₈ v (hobsp8 ▸ hv)
        _ = σ₇ v := obs₇ v (hobsp7 ▸ hv)
        _ = σ₆ v := obs₆ v (hobsp6 ▸ hv)
        _ = σ₅ v := obs₅ v (hobsp5 ▸ hv)
        _ = σ₄ v := obs₄ v (hobsp4 ▸ hv)
        _ = σ₃ v := obs₃ v (hobsp3 ▸ hv)
        _ = σ₂ v := obs₂ v (hobsp2 ▸ hv)
        _ = σ₁ v := obs₁ v (hobsp1 ▸ hv)
        _ = σ₀' v := obs₀ v hv⟩
  · -- (2) ARM simulation: direct from tacToArm_correctness
    exact tacToArm_correctness hGen hHalt

-- ============================================================
-- § 6. Full end-to-end: While source → ARM
-- ============================================================

/-- **Full end-to-end correctness: While source → optimized TAC → ARM.**

    If a well-typed While program is compiled to TAC, optimized, and
    code-generated to ARM, and the optimized TAC halts with store `σ_opt`,
    then:
    1. The source program terminates (at some fuel) with store `σ_src`
    2. Observable variables agree: `σ_opt v = σ_src v` for non-temp `v`
    3. The ARM program simulates the TAC halt

    This composes `whileToTAC_refinement` (source → TAC),
    `optimizePipeline_preserves_behavior` (TAC → optimized TAC), and
    `tacToArm_correctness` (optimized TAC → ARM).

    **Propagated sorrys:** SoundnessBridge (5), ArmCorrectness (2). -/
theorem while_to_arm_correctness
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    {p_opt : Prog} {r : VerifiedAsmResult}
    (hOpt : optimizePipeline prog.compileToTAC = .ok p_opt)
    (hGen : verifiedGenerateAsm p_opt = .ok r)
    -- tyCtx preservation hypotheses (hold by construction for all passes)
    (hty_dce : ∀ q, (DCEOpt.optimize q).orig.tyCtx = (DCEOpt.optimize q).trans.tyCtx)
    (hty_licm : ∀ q, (LICMOpt.optimize q).orig.tyCtx = (LICMOpt.optimize q).trans.tyCtx)
    (hty_cp : ∀ q, (ConstPropOpt.optimize q).orig.tyCtx = (ConstPropOpt.optimize q).trans.tyCtx)
    (hty_dae : ∀ q, (DAEOpt.optimize q).orig.tyCtx = (DAEOpt.optimize q).trans.tyCtx)
    (hty_fma : ∀ q, (FMAFusionOpt.optimize q).orig.tyCtx = (FMAFusionOpt.optimize q).trans.tyCtx)
    (hty_cse : ∀ q, (CSEOpt.optimize q).orig.tyCtx = (CSEOpt.optimize q).trans.tyCtx)
    (hty_ch : ∀ q, (ConstHoistOpt.optimize q).orig.tyCtx = (ConstHoistOpt.optimize q).trans.tyCtx)
    (hty_ph : ∀ q, (PeepholeOpt.optimize q).orig.tyCtx = (PeepholeOpt.optimize q).trans.tyCtx)
    (hty_ra : ∀ q, (RegAllocOpt.optimize q).orig.tyCtx = (RegAllocOpt.optimize q).trans.tyCtx)
    (htyO_dce : ∀ q, (DCEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_licm : ∀ q, (LICMOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_cp : ∀ q, (ConstPropOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_dae : ∀ q, (DAEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_fma : ∀ q, (FMAFusionOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_cse : ∀ q, (CSEOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ch : ∀ q, (ConstHoistOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ph : ∀ q, (PeepholeOpt.optimize q).orig.tyCtx = q.tyCtx)
    (htyO_ra : ∀ q, (RegAllocOpt.optimize q).orig.tyCtx = q.tyCtx)
    -- Optimized TAC halts
    {σ_opt : Store} {am_opt : ArrayMem}
    (hHalt : haltsWithResult p_opt 0 (Store.typedInit p_opt.tyCtx) σ_opt ArrayMem.init am_opt) :
    -- Then: source program terminates with matching observables
    (∃ fuel σ_src am_src,
      prog.interp fuel = some (σ_src, am_src) ∧
      ∀ v ∈ prog.compileToTAC.observable, σ_opt v = σ_src v) ∧
    -- And: ARM simulates the halt
    (∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap (.halt σ_opt am_opt) s') := by
  -- Part 2: ARM simulation (independent of source)
  refine ⟨?_, tacToArm_correctness hGen hHalt⟩
  -- Part 1: Source terminates with matching observables
  -- Step A: optimized TAC halts → original TAC halts with same observables
  -- Bridge: Store.typedInit (used by end_to_end_correctness) vs prog.initStore (used by whileToTAC)
  have htc := Program.typeCheckStrict_typeCheck prog htcs
  have hInitEq : Store.typedInit prog.compileToTAC.tyCtx = prog.initStore := by
    rw [Program.compileToTAC_tyCtx_eq prog htc]; exact Program.typedInit_eq_initStore prog htc
  -- end_to_end_correctness now gives ArrayMem.init as initial AM
  have ⟨σ_tac, am_f, hHalt_tac, hobs_tac⟩ :=
    (end_to_end_correctness hOpt hGen
      hty_dce hty_licm hty_cp hty_dae hty_fma hty_cse hty_ch hty_ph hty_ra
      htyO_dce htyO_licm htyO_cp htyO_dae htyO_fma htyO_cse htyO_ch htyO_ph htyO_ra
      hHalt).1
  -- Step B: TAC halts → source terminates (whileToTAC_refinement)
  -- Rewrite initial store; initial AM is already ArrayMem.init
  have hHalt_init : haltsWithResult prog.compileToTAC 0 prog.initStore σ_tac ArrayMem.init am_f :=
    hInitEq ▸ hHalt_tac
  have hbeh_tac : program_behavior_init prog.compileToTAC prog.initStore (.halts σ_tac) :=
    ⟨am_f, hHalt_init⟩
  have hsrc := whileToTAC_refinement prog htcs (.halts σ_tac) hbeh_tac
  simp only at hsrc
  obtain ⟨fuel, σ_src, am_h, am_src, hinterp, _, _, hobs_src⟩ := hsrc
  -- Chain: σ_opt v = σ_tac v (from pipeline) and σ_tac v = σ_src v (from whileToTAC)
  -- For v ∈ observable = prog.decls.map Prod.fst, v is not tmp/ftmp (from noTmpDecls)
  have hnt : Program.noTmpDecls prog.decls = true := by
    unfold Program.typeCheck at htc; simp only [Bool.and_eq_true] at htc; exact htc.1.2
  exact ⟨fuel, σ_src, am_src, hinterp, fun v hv => by
    rw [hobs_tac v hv]
    -- v ∈ observable = prog.decls.map Prod.fst, so ¬isTmp ∧ ¬isFTmp
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
