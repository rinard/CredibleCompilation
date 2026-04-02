import CredibleCompilation.Semantics

/-!
# Propositional PCertificate Checker for Credible Compilation

A Prop-based certificate checker that verifies: every behavior of a transformed
program has a corresponding behavior in the original program.

Based on the credible compilation framework (Rinard, MIT-LCS-TR-776).
-/

-- ============================================================
-- § 1. Invariants (Floyd-Hoare style properties)
-- ============================================================

/-- A predicate on stores, attached to a program point. -/
def PInvariant := Store → Prop

/-- An invariant map assigns an invariant to each label in a program. -/
def PInvariantMap := Label → PInvariant

def PInvariantMap.locally_preserved (inv : PInvariantMap) (p : Prog)
    (pc : Label) (σ : Store) : Prop :=
  inv pc σ →
  ∀ pc' σ' am am', (p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am') → inv pc' σ'

def PInvariantMap.preserved (inv : PInvariantMap) (p : Prog) : Prop :=
  ∀ pc σ, inv.locally_preserved p pc σ

def PStoreRel := Store → Store → Prop

structure PTransCorr where
  origLabels   : List Label
  storeRel     : PStoreRel
  storeRel_next : PStoreRel

structure PInstrCert where
  pc_orig    : Label
  storeRel   : PStoreRel
  transitions : List PTransCorr

structure PHaltCert where
  pc_orig  : Label
  storeRel : PStoreRel

def PTransMeasure := Label → Store → Nat

structure PCertificate where
  orig        : Prog
  trans       : Prog
  inv_orig    : PInvariantMap
  inv_trans   : PInvariantMap
  instrCerts  : Label → PInstrCert
  haltCerts   : Label → PHaltCert
  measure     : PTransMeasure

abbrev PCertificate.tyCtx (cert : PCertificate) : TyCtx := cert.orig.tyCtx
abbrev PCertificate.observable (cert : PCertificate) : List Var := cert.orig.observable

-- ============================================================
-- § 6. PCertificate checking conditions
-- ============================================================

def checkInvariantsPreservedProp (cert : PCertificate) : Prop :=
  cert.inv_orig.preserved cert.orig ∧ cert.inv_trans.preserved cert.trans

def checkTransitionRelProp (Γ : TyCtx) (p_orig p_trans : Prog)
    (inv_orig : PInvariantMap) (inv_trans : PInvariantMap)
    (pc_t pc_t' : Label) (pc_o pc_o' : Label) (tc : PTransCorr) : Prop :=
  ∀ σ_t σ_t' σ_o am_t am_t',
    inv_trans pc_t σ_t → inv_orig pc_o σ_o → tc.storeRel σ_o σ_t → TypedStore Γ σ_o →
    (p_trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t') →
    ∃ σ_o' am_o', (p_orig ⊩ Cfg.run pc_o σ_o ArrayMem.init ⟶* Cfg.run pc_o' σ_o' am_o') ∧
      tc.storeRel_next σ_o' σ_t'

def checkAllTransitionsProp (Γ : TyCtx) (cert : PCertificate) : Prop :=
  ∀ pc_t : Label, ∀ σ_t σ_t' : Store, ∀ pc_t' : Label, ∀ am_t am_t' : ArrayMem,
    (cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t') →
    let ic := cert.instrCerts pc_t; let ic' := cert.instrCerts pc_t'
    ∃ tc ∈ ic.transitions, tc.storeRel = ic.storeRel ∧ tc.storeRel_next = ic'.storeRel ∧
      checkTransitionRelProp Γ cert.orig cert.trans cert.inv_orig cert.inv_trans pc_t pc_t' ic.pc_orig ic'.pc_orig tc

def checkHaltCorrespondenceProp (cert : PCertificate) : Prop :=
  ∀ pc_t : Label, cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t; cert.orig[ic.pc_orig]? = some .halt

def checkHaltObservableProp (cert : PCertificate) : Prop :=
  ∀ pc_t : Label, ∀ σ_t σ_o : Store, cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t; ic.storeRel σ_o σ_t → ∀ v ∈ cert.observable, σ_t v = σ_o v

def checkErrorPreservationProp (cert : PCertificate) : Prop :=
  ∀ (pc_t : Label) (σ_t σ_o : Store) (am_t : ArrayMem),
    pc_t < cert.trans.size → (cert.instrCerts pc_t).storeRel σ_o σ_t →
    cert.inv_trans pc_t σ_t → cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o →
    (cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.error σ_t am_t) →
    ∃ σ_o' am_o', cert.orig ⊩ Cfg.run (cert.instrCerts pc_t).pc_orig σ_o ArrayMem.init ⟶* Cfg.error σ_o' am_o'

def checkStartCorrespondenceProp (cert : PCertificate) : Prop :=
  (cert.instrCerts 0).pc_orig = 0 ∧ ∀ σ : Store, (cert.instrCerts 0).storeRel σ σ

def checkInvariantsAtStartProp (cert : PCertificate) : Prop :=
  (∀ σ, cert.inv_trans 0 σ) ∧ (∀ σ, cert.inv_orig 0 σ)

def IsInfiniteExec (p : Prog) (f : Nat → Cfg) : Prop :=
  (∃ σ₀ am₀, f 0 = Cfg.run 0 σ₀ am₀) ∧ ∀ n, p ⊩ f n ⟶ f (n + 1)

def checkNonterminationProp (cert : PCertificate) : Prop :=
  ∀ (pc_t pc_t' : Label) (σ_t σ_t' σ_o : Store) (am_t : ArrayMem),
    cert.inv_trans pc_t σ_t →
    cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o →
    (cert.instrCerts pc_t).storeRel σ_o σ_t →
    (∃ c', (cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ c') ∧ ∃ am_t', c' = Cfg.run pc_t' σ_t' am_t') →
    (cert.instrCerts pc_t).pc_orig = (cert.instrCerts pc_t').pc_orig →
    cert.measure pc_t' σ_t' < cert.measure pc_t σ_t

structure PCertificateValid (cert : PCertificate) : Prop where
  well_typed_orig  : WellTypedProg cert.tyCtx cert.orig
  well_typed_trans : WellTypedProg cert.trans.tyCtx cert.trans
  same_tyCtx       : cert.orig.tyCtx = cert.trans.tyCtx
  same_observable  : cert.orig.observable = cert.trans.observable
  start_corr       : checkStartCorrespondenceProp cert
  start_inv        : checkInvariantsAtStartProp cert
  inv_preserved    : checkInvariantsPreservedProp cert
  transitions      : checkAllTransitionsProp cert.tyCtx cert
  halt_corr        : checkHaltCorrespondenceProp cert
  halt_obs         : checkHaltObservableProp cert
  nonterm          : checkNonterminationProp cert
  error_pres       : checkErrorPreservationProp cert
  step_closed      : StepClosedInBounds cert.trans

-- ============================================================
-- § 9. Soundness: simulation relation
-- ============================================================

def PSimRel (cert : PCertificate) (pc_t : Label) (σ_t : Store)
    (pc_o : Label) (σ_o : Store) : Prop :=
  let ic := cert.instrCerts pc_t
  ic.pc_orig = pc_o ∧ ic.storeRel σ_o σ_t ∧ cert.inv_trans pc_t σ_t ∧
  cert.inv_orig pc_o σ_o ∧ TypedStore cert.tyCtx σ_o

theorem inv_preserved_steps {inv : PInvariantMap} {p : Prog}
    (hpres : inv.preserved p) {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc σ am ⟶* Cfg.run pc' σ' am') (hinv : inv pc σ) :
    inv pc' σ' := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ am, c = Cfg.run pc σ am → inv pc σ →
      ∀ pc' σ' am', c' = Cfg.run pc' σ' am' → inv pc' σ' from
    this _ _ hsteps pc σ am rfl hinv pc' σ' am' rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc σ am hc hinv pc' σ' am' hc'; rw [hc] at hc'; cases hc'; exact hinv
  | step hstep rest ih =>
    intro pc σ am hc hinv pc' σ' am' hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | error h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.const h)) _ _ _ hc'
    | copy h => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.copy h)) _ _ _ hc'
    | binop h hy hz hs => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.binop h hy hz hs)) _ _ _ hc'
    | boolop h => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.boolop h)) _ _ _ hc'
    | goto h => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.goto h)) _ _ _ hc'
    | iftrue h hne => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.iftrue h hne)) _ _ _ hc'
    | iffall h heq => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.iffall h heq)) _ _ _ hc'
    | arrLoad h hidx => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am am (Step.arrLoad h hidx)) _ _ _ hc'
    | arrStore h hidx hv => exact ih _ _ _ rfl (hpres _ _ hinv _ _ am _ (Step.arrStore h hidx hv)) _ _ _ hc'

theorem bound_of_getElem? {a : Array α} {i : Nat} {v : α}
    (h : a[i]? = some v) : i < a.size := by
  rw [getElem?_eq_some_iff] at h; exact h.1

theorem type_preservation_steps {Γ : TyCtx} {p : Prog} (hwtp : WellTypedProg Γ p)
    {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc σ am ⟶* Cfg.run pc' σ' am') (hts : TypedStore Γ σ) :
    TypedStore Γ σ' := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ am, c = Cfg.run pc σ am → TypedStore Γ σ →
      ∀ pc' σ' am', c' = Cfg.run pc' σ' am' → TypedStore Γ σ' from
    this _ _ hsteps pc σ am rfl hts pc' σ' am' rfl
  intro c c' hsteps
  induction hsteps with
  | refl => intro pc σ am hc hts pc' σ' am' hc'; rw [hc] at hc'; cases hc'; exact hts
  | step hstep rest ih =>
    intro pc σ am hc hts pc' σ' am' hc'; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | error h _ _ _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | binop_typeError h _ | arrLoad_typeError h _ | arrStore_typeError h _ => cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_typeError
    | const h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.const (am := am) h)) _ _ _ hc'
    | copy h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.copy (am := am) h)) _ _ _ hc'
    | binop h hy hz hs => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.binop (am := am) h hy hz hs)) _ _ _ hc'
    | boolop h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.boolop (am := am) h)) _ _ _ hc'
    | goto h => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.goto (am := am) h)) _ _ _ hc'
    | iftrue h hne => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.iftrue (am := am) h hne)) _ _ _ hc'
    | iffall h heq => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.iffall (am := am) h heq)) _ _ _ hc'
    | arrLoad h hidx => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.arrLoad (am := am) h hidx)) _ _ _ hc'
    | arrStore h hidx hv => exact ih _ _ _ rfl (type_preservation hwtp hts (bound_of_getElem? h) (Step.arrStore (am := am) h hidx hv)) _ _ _ hc'

theorem step_sim {cert : PCertificate} (hvalid : PCertificateValid cert)
    {pc_t : Label} {σ_t σ_t' : Store} {am_t am_t' : ArrayMem}
    {pc_o : Label} {σ_o : Store} {pc_t' : Label}
    (hsim : PSimRel cert pc_t σ_t pc_o σ_o)
    (hstep : cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t') :
    ∃ pc_o' σ_o',
      (∃ am_o am_o', cert.orig ⊩ Cfg.run pc_o σ_o am_o ⟶* Cfg.run pc_o' σ_o' am_o') ∧
      PSimRel cert pc_t' σ_t' pc_o' σ_o' := by
  obtain ⟨hpc_orig, hrel_cons, hinv_t, hinv_o, hts_o⟩ := hsim
  have hall := hvalid.transitions pc_t σ_t σ_t' pc_t' am_t am_t' hstep
  simp only at hall
  obtain ⟨tc, _, hrel1, hrel2, htrans⟩ := hall
  have hrel_tc : tc.storeRel σ_o σ_t := hrel1 ▸ hrel_cons
  subst hpc_orig
  obtain ⟨σ_o', am_o', horig_steps, hrel_next⟩ :=
    htrans σ_t σ_t' σ_o am_t am_t' hinv_t hinv_o hrel_tc hts_o hstep
  refine ⟨(cert.instrCerts pc_t').pc_orig, σ_o', ⟨_, _, horig_steps⟩, ?_⟩
  exact ⟨rfl, hrel2 ▸ hrel_next,
         hvalid.inv_preserved.2 pc_t σ_t hinv_t pc_t' σ_t' _ _ hstep,
         inv_preserved_steps hvalid.inv_preserved.1 horig_steps hinv_o,
         type_preservation_steps hvalid.well_typed_orig horig_steps hts_o⟩

theorem soundness_halt (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ σ_t' : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (hexec : ∃ am am', haltsWithResult cert.trans 0 σ₀ σ_t' am am') :
    ∃ σ_o', (∃ am am', haltsWithResult cert.orig 0 σ₀ σ_o' am am') ∧
      ∀ v ∈ cert.observable, σ_t' v = σ_o' v := by
  sorry

-- ============================================================
-- § StepsN infrastructure
-- ============================================================

def StepsN (p : Prog) : Cfg → Cfg → Nat → Prop
  | c, c', 0 => c = c'
  | c, c', n + 1 => ∃ c'', Step p c c'' ∧ StepsN p c'' c' n

theorem StepsN_det {p : Prog} {c : Cfg} {n : Nat} :
    ∀ {c' c''}, StepsN p c c' n → StepsN p c c'' n → c' = c'' := by
  induction n generalizing c with
  | zero => intro _ _ h1 h2; exact h1.symm.trans h2
  | succ n ih =>
    intro _ _ h1 h2; obtain ⟨c1, hs1, hr1⟩ := h1; obtain ⟨c2, hs2, hr2⟩ := h2
    have := Step.deterministic hs1 hs2; subst this; exact ih hr1 hr2

theorem StepsN_extend {p : Prog} {c c' c'' : Cfg} {n : Nat}
    (h1 : StepsN p c c' n) (h2 : Step p c' c'') : StepsN p c c'' (n + 1) := by
  induction n generalizing c with
  | zero => change c = c' at h1; subst h1; exact ⟨c'', h2, rfl⟩
  | succ n ih => obtain ⟨cm, hs, hr⟩ := h1; exact ⟨cm, hs, ih hr⟩

theorem StepsN_split_last {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' (n + 1)) : ∃ c'', StepsN p c c'' n ∧ Step p c'' c' := by
  induction n generalizing c with
  | zero => obtain ⟨c'', hs, hr⟩ := h; exact ⟨c, rfl, hr ▸ hs⟩
  | succ n ih =>
    obtain ⟨c1, hs, hr⟩ := h; obtain ⟨c2, h2, hlast⟩ := ih hr
    exact ⟨c2, ⟨c1, hs, h2⟩, hlast⟩

theorem StepsN_trans {p : Prog} {c c' c'' : Cfg} {n m : Nat}
    (h1 : StepsN p c c' n) (h2 : StepsN p c' c'' m) : StepsN p c c'' (n + m) := by
  induction n generalizing c with
  | zero => change c = c' at h1; subst h1; rw [Nat.zero_add]; exact h2
  | succ n ih =>
    obtain ⟨cm, hs, hr⟩ := h1; rw [show n + 1 + m = (n + m) + 1 from by omega]
    exact ⟨cm, hs, ih hr⟩

theorem Steps_to_StepsN {p : Prog} {c c' : Cfg}
    (h : Steps p c c') : ∃ n, StepsN p c c' n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step s _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, ⟨_, s, hn⟩⟩

theorem StepsN_prefix {p : Prog} {c c' : Cfg} {n k : Nat}
    (h : StepsN p c c' (n + k)) : ∃ c'', StepsN p c c'' n := by
  induction k generalizing c' with
  | zero => exact ⟨c', h⟩
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 from by omega] at h
    obtain ⟨cmid, hmid, _⟩ := StepsN_split_last h; exact ih hmid

theorem step_from_run {p : Prog} {c c' : Cfg}
    (h : Step p c c') : ∃ pc σ am, c = Cfg.run pc σ am := by
  cases h <;> exact ⟨_, _, _, rfl⟩

theorem inf_exec_is_run {p : Prog} {f : Nat → Cfg} (hinf : IsInfiniteExec p f) :
    ∀ n, ∃ pc σ am, f n = Cfg.run pc σ am := by
  intro n; cases hfn : f n with
  | run pc σ am => exact ⟨pc, σ, am, rfl⟩
  | halt σ am => exfalso; exact Step.no_step_from_halt (hfn ▸ hinf.2 n)
  | error σ am => exfalso; exact Step.no_step_from_error (hfn ▸ hinf.2 n)
  | typeError σ am => exfalso; exact Step.no_step_from_typeError (hfn ▸ hinf.2 n)

theorem StepsN_run_predecessor {p : Prog} {c : Cfg} {pc : Label} {σ : Store} {am : ArrayMem} {n : Nat}
    (h : StepsN p c (Cfg.run pc σ am) (n + 1)) :
    ∃ pc' σ' am' c'', StepsN p c (Cfg.run pc' σ' am') n ∧ Step p (Cfg.run pc' σ' am') c'' := by
  obtain ⟨c'', h'', hlast⟩ := StepsN_split_last h
  obtain ⟨pc', σ', am', hc''⟩ := step_from_run hlast
  exact ⟨pc', σ', am', _, hc'' ▸ h'', hc'' ▸ hlast⟩

theorem StepsN_split {p : Prog} {c c' : Cfg} {n k : Nat}
    (h : StepsN p c c' (n + k)) : ∃ c'', StepsN p c c'' n ∧ StepsN p c'' c' k := by
  induction n generalizing c with
  | zero => exact ⟨c, rfl, (Nat.zero_add k) ▸ h⟩
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 from by omega] at h
    obtain ⟨cm, hs, hr⟩ := h; obtain ⟨c'', hp, hs'⟩ := ih hr
    exact ⟨c'', ⟨cm, hs, hp⟩, hs'⟩

theorem StepsN_intermediate_run {p : Prog} {pc₀ : Label} {σ₀ : Store} {am₀ : ArrayMem}
    {pc' : Label} {σ' : Store} {am' : ArrayMem} {total : Nat}
    (h : StepsN p (Cfg.run pc₀ σ₀ am₀) (Cfg.run pc' σ' am') total)
    {N : Nat} (hle : N ≤ total) :
    ∃ pc'' σ'' am'', StepsN p (Cfg.run pc₀ σ₀ am₀) (Cfg.run pc'' σ'' am'') N := by
  by_cases heq : N = total
  · subst heq; exact ⟨pc', σ', am', h⟩
  · obtain ⟨c'', h1, h2⟩ := StepsN_split (show StepsN p _ _ (N + (total - N)) by rwa [Nat.add_sub_cancel' (by omega : N ≤ total)])
    rw [show total - N = (total - N - 1) + 1 from by omega] at h2
    obtain ⟨c''', hs, _⟩ := h2
    obtain ⟨pc'', σ'', am'', hc⟩ := step_from_run hs; subst hc
    exact ⟨pc'', σ'', am'', h1⟩

-- ============================================================
-- § Soundness for divergence
-- ============================================================

theorem soundness_diverge (cert : PCertificate) (hvalid : PCertificateValid cert)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (hinf : IsInfiniteExec cert.trans f) (hf0 : ∃ am₀, f 0 = Cfg.run 0 σ₀ am₀) :
    ∃ g : Nat → Cfg, IsInfiniteExec cert.orig g ∧ ∃ am₀, g 0 = Cfg.run 0 σ₀ am₀ := by
  sorry
/-  obtain ⟨am₀_f, hf0⟩ := hf0
  suffices h_arb : ∀ N : Nat, ∃ pc σ am,
      StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc σ am) N by
    have g_spec : ∀ n, ∃ c, StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) c n ∧
        ∃ pc σ am, c = Cfg.run pc σ am := by
      intro n; obtain ⟨pc, σ, am, h⟩ := h_arb n; exact ⟨_, h, pc, σ, am, rfl⟩
    let g : Nat → Cfg := fun n => (g_spec n).choose
    have g_stepsN : ∀ n, StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (g n) n :=
      fun n => (g_spec n).choose_spec.1
    refine ⟨g, ⟨⟨σ₀, ArrayMem.init, ?_⟩, fun n => ?_⟩, ArrayMem.init, ?_⟩
    · exact (g_stepsN 0).symm
    · obtain ⟨c'', h_prefix, h_last⟩ := StepsN_split_last (g_stepsN (n + 1))
      exact StepsN_det (g_stepsN n) h_prefix ▸ h_last
    · exact (g_stepsN 0).symm
  have hf_run := inf_exec_is_run hinf
  have advance : ∀ (m n : Nat) (pc_o : Label) (σ_o : Store) (total : Nat),
      (∀ pc_t σ_t am_t, f n = Cfg.run pc_t σ_t am_t → cert.measure pc_t σ_t ≤ m) →
      (∀ pc_t σ_t am_t, f n = Cfg.run pc_t σ_t am_t → PSimRel cert pc_t σ_t pc_o σ_o) →
      (∃ am_o, StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc_o σ_o am_o) total) →
      ∃ (n' : Nat) (pc_o' : Label) (σ_o' : Store) (total' : Nat),
        (∀ pc_t σ_t am_t, f n' = Cfg.run pc_t σ_t am_t → PSimRel cert pc_t σ_t pc_o' σ_o') ∧
        (∃ am_o', StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc_o' σ_o' am_o') total') ∧
        total' ≥ total + 1 := by
    intro m; induction m with
    | zero =>
      intro n pc_o σ_o total hmu hsim_fn ⟨am_o, hsteps⟩
      obtain ⟨pc_t, σ_t, am_t, hfn⟩ := hf_run n
      obtain ⟨pc_t', σ_t', am_t', hfn1⟩ := hf_run (n + 1)
      have hsim := hsim_fn pc_t σ_t am_t hfn
      have hstep : cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t' := by
        have := hinf.2 n; rw [hfn, hfn1] at this; exact this
      obtain ⟨pc_o', σ_o', ⟨amo1, amo2, horig⟩, hsim'⟩ := step_sim hvalid hsim hstep
      obtain ⟨k, hk⟩ := Steps_to_StepsN horig
      cases k with
      | zero =>
        change Cfg.run pc_o σ_o amo1 = Cfg.run pc_o' σ_o' amo2 at hk; cases hk
        have hnt := hvalid.nonterm pc_t pc_t' σ_t σ_t' σ_o am_t
          hsim.2.2.1 (hsim.1 ▸ hsim.2.2.2.1) hsim.2.1 ⟨_, hstep, _, rfl⟩ (hsim.1.trans hsim'.1.symm)
        have := hmu pc_t σ_t am_t hfn; omega
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', total + (k' + 1),
          fun pc σ am hf => by rw [hfn1] at hf; cases hf; exact hsim',
          ⟨amo2, StepsN_trans hsteps hk⟩, by omega⟩
    | succ m ih =>
      intro n pc_o σ_o total hmu hsim_fn ⟨am_o, hsteps⟩
      obtain ⟨pc_t, σ_t, am_t, hfn⟩ := hf_run n
      obtain ⟨pc_t', σ_t', am_t', hfn1⟩ := hf_run (n + 1)
      have hsim := hsim_fn pc_t σ_t am_t hfn
      have hstep : cert.trans ⊩ Cfg.run pc_t σ_t am_t ⟶ Cfg.run pc_t' σ_t' am_t' := by
        have := hinf.2 n; rw [hfn, hfn1] at this; exact this
      obtain ⟨pc_o', σ_o', ⟨amo1, amo2, horig⟩, hsim'⟩ := step_sim hvalid hsim hstep
      obtain ⟨k, hk⟩ := Steps_to_StepsN horig
      cases k with
      | zero =>
        change Cfg.run pc_o σ_o amo1 = Cfg.run pc_o' σ_o' amo2 at hk; cases hk
        exact ih (n + 1) pc_o σ_o total
          (fun pc σ am hf => by rw [hfn1] at hf; cases hf
                               have := hvalid.nonterm pc_t pc_t' σ_t σ_t' σ_o am_t
                                 hsim.2.2.1 (hsim.1 ▸ hsim.2.2.2.1) hsim.2.1
                                 ⟨_, hstep, _, rfl⟩ (hsim.1.trans hsim'.1.symm)
                               have := hmu pc_t σ_t am_t hfn; omega)
          (fun pc σ am hf => by rw [hfn1] at hf; cases hf; exact hsim')
          ⟨am_o, hsteps⟩
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', total + (k' + 1),
          fun pc σ am hf => by rw [hfn1] at hf; cases hf; exact hsim',
          ⟨amo2, StepsN_trans hsteps hk⟩, by omega⟩
  suffices ∀ N, ∃ (n : Nat) (pc_o : Label) (σ_o : Store) (total : Nat),
      (∀ pc_t σ_t am_t, f n = Cfg.run pc_t σ_t am_t → PSimRel cert pc_t σ_t pc_o σ_o) ∧
      (∃ am_o, StepsN cert.orig (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc_o σ_o am_o) total) ∧ total ≥ N by
    intro N; obtain ⟨_, _, _, total, _, ⟨am_o, hsteps⟩, hge⟩ := this N
    exact StepsN_intermediate_run hsteps hge
  intro N; induction N with
  | zero =>
    refine ⟨0, 0, σ₀, 0, ?_, ⟨ArrayMem.init, rfl⟩, Nat.zero_le _⟩
    intro pc_t σ_t am_t hfn; rw [hf0] at hfn; cases hfn
    exact ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀,
           hvalid.start_inv.1 σ₀, hvalid.start_inv.2 σ₀, hts₀⟩
  | succ N ih =>
    obtain ⟨n, pc_o, σ_o, total, hsim_fn, hsteps, hge⟩ := ih
    obtain ⟨pc_t, σ_t, am_t, hfn⟩ := hf_run n
    obtain ⟨n', pc_o', σ_o', total', hsim', hsteps', hge'⟩ :=
      advance (cert.measure pc_t σ_t) n pc_o σ_o total
        (fun pc σ am hf => by rw [hfn] at hf; cases hf; omega)
        hsim_fn hsteps
    exact ⟨n', pc_o', σ_o', total', hsim', hsteps', by omega⟩
-/

-- ============================================================
-- § Behaviors
-- ============================================================

inductive Behavior where
  | halts      : Store → Behavior
  | errors     : Store → Behavior
  | typeErrors : Store → Behavior
  | diverges   : Behavior

def program_behavior (p : Prog) (σ₀ : Store) (b : Behavior) : Prop :=
  match b with
  | .halts σ'      => ∃ am am', haltsWithResult p 0 σ₀ σ' am am'
  | .errors σ'     => ∃ am am', p ⊩ Cfg.run 0 σ₀ am ⟶* Cfg.error σ' am'
  | .typeErrors σ' => ∃ am am', p ⊩ Cfg.run 0 σ₀ am ⟶* Cfg.typeError σ' am'
  | .diverges      => ∃ f : Nat → Cfg, IsInfiniteExec p f ∧ ∃ am₀, f 0 = Cfg.run 0 σ₀ am₀

private theorem StepsN_to_Steps' {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' n) : p ⊩ c ⟶* c' := by
  induction n generalizing c with
  | zero => exact h ▸ .refl
  | succ n ih => obtain ⟨c'', hs, hn⟩ := h; exact .step hs (ih hn)

theorem has_behavior (p : Prog) (σ₀ : Store) (hclosed : StepClosedInBounds p) :
    ∃ b, program_behavior p σ₀ b := by
  by_cases h : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.halt σ' am') n
  · obtain ⟨n, σ', am', hn⟩ := h
    exact ⟨.halts σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
  · by_cases he : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.error σ' am') n
    · obtain ⟨_, σ', am', hn⟩ := he
      exact ⟨.errors σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
    · by_cases hte : ∃ n σ' am', StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.typeError σ' am') n
      · obtain ⟨_, σ', am', hn⟩ := hte
        exact ⟨.typeErrors σ', ArrayMem.init, am', StepsN_to_Steps' hn⟩
      · have h_run : ∀ n, ∃ pc σ am, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (Cfg.run pc σ am) n ∧ pc < p.size := by
          intro n; induction n with
          | zero => exact ⟨0, σ₀, ArrayMem.init, rfl, hclosed.1⟩
          | succ n ih =>
            obtain ⟨pc, σ, am, hn, hpc⟩ := ih
            obtain ⟨c', hstep⟩ := Step.progress_untyped p pc σ am hpc
            match c', hstep with
            | .halt σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ h
            | .error σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ he
            | .typeError σ' am', s => exact absurd ⟨n+1, σ', am', StepsN_extend hn s⟩ hte
            | .run pc' σ' am', s => exact ⟨pc', σ', am', StepsN_extend hn s, hclosed.2 pc pc' σ σ' am am' hpc s⟩
        have g_spec : ∀ n, ∃ c, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) c n ∧ ∃ pc σ am, c = Cfg.run pc σ am := by
          intro n; obtain ⟨pc, σ, am, hn, _⟩ := h_run n; exact ⟨_, hn, pc, σ, am, rfl⟩
        let g := fun n => (g_spec n).choose
        have g_stepsN : ∀ n, StepsN p (Cfg.run 0 σ₀ ArrayMem.init) (g n) n :=
          fun n => (g_spec n).choose_spec.1
        refine ⟨.diverges, g, ⟨⟨σ₀, ArrayMem.init, ?_⟩, fun n => ?_⟩, ArrayMem.init, ?_⟩
        · exact (g_stepsN 0).symm
        · exact StepsN_det (g_stepsN n) (StepsN_split_last (g_stepsN (n+1))).choose_spec.1 ▸
            (StepsN_split_last (g_stepsN (n+1))).choose_spec.2
        · exact (g_stepsN 0).symm

-- ============================================================
-- § Simulation trace
-- ============================================================

theorem simulation_trace {cert : PCertificate} (hvalid : PCertificateValid cert)
    {σ₀ : Store} (hts₀ : TypedStore cert.tyCtx σ₀)
    {pc_t : Label} {σ_t : Store} {am₀ am_t : ArrayMem}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.run pc_t σ_t am_t) :
    ∃ pc_o σ_o, (∃ am_o am_o', cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.run pc_o σ_o am_o') ∧
      PSimRel cert pc_t σ_t pc_o σ_o := by
  sorry

-- ============================================================
-- § Observation helpers
-- ============================================================

private theorem obs_map_eq {obs : List Var} {σ_t σ_o : Store}
    (h : ∀ v ∈ obs, σ_t v = σ_o v) :
    obs.map (fun v => (v, σ_t v)) = obs.map (fun v => (v, σ_o v)) := by
  induction obs with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨congrArg (Prod.mk v) (h v (.head _)), ih (fun w hw => h w (.tail _ hw))⟩

private theorem steps_run_in_bounds {p : Prog} (hclosed : StepClosedInBounds p)
    {pc₀ : Label} {σ₀ : Store} {am₀ : ArrayMem} (hpc₀ : pc₀ < p.size)
    {pc : Label} {σ : Store} {am : ArrayMem}
    (hreach : p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) : pc < p.size := by
  sorry

-- ============================================================
-- § Halt preservation
-- ============================================================

theorem halt_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) (c_t : Cfg)
    (hreach : ∃ am₀, cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* c_t)
    (pairs : List (Var × Value))
    (hobs : observe cert.trans cert.observable c_t = Observation.halt pairs) :
    ∃ c_o, (∃ am₀, cert.orig ⊩ Cfg.run 0 σ₀ am₀ ⟶* c_o) ∧
      observe cert.orig cert.observable c_o = Observation.halt pairs := by
  obtain ⟨am₀, hreach⟩ := hreach
  cases c_t with
  | halt σ_t am_h =>
    obtain ⟨σ_o, horig, hobs_eq⟩ := soundness_halt cert hvalid σ₀ σ_t hts₀ ⟨am₀, am_h, hreach⟩
    obtain ⟨amo1, amo2, horig'⟩ := horig
    simp only [observe] at hobs; rw [Observation.halt.injEq] at hobs; subst hobs
    exact ⟨Cfg.halt σ_o amo2, ⟨amo1, horig'⟩,
      congrArg Observation.halt (obs_map_eq (fun v hv => (hobs_eq v hv).symm))⟩
  | run pc_t σ_t am_t =>
    have hpc := steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hreach
    obtain ⟨instr, hinstr⟩ : ∃ instr, cert.trans[pc_t]? = some instr :=
      ⟨cert.trans[pc_t], getElem?_eq_some_iff.mpr ⟨hpc, rfl⟩⟩
    cases instr with
    | halt =>
      obtain ⟨pc_o, σ_o, ⟨a1, a2, ho⟩, hpc_eq, hrel, _, _, _⟩ := simulation_trace hvalid hts₀ hreach
      have horig_halt : cert.orig[pc_o]? = some TAC.halt := by rw [← hpc_eq]; exact hvalid.halt_corr pc_t hinstr
      have htobs : observe cert.trans cert.observable (Cfg.run pc_t σ_t am_t) =
          Observation.halt (cert.observable.map fun v => (v, σ_t v)) := by simp only [observe, hinstr]
      have hoobs : observe cert.orig cert.observable (Cfg.run pc_o σ_o a2) =
          Observation.halt (cert.observable.map fun v => (v, σ_o v)) := by simp only [observe, horig_halt]
      rw [htobs] at hobs; rw [Observation.halt.injEq] at hobs; subst hobs
      exact ⟨Cfg.run pc_o σ_o a2, ⟨a1, ho⟩, hoobs ▸
        congrArg Observation.halt (obs_map_eq (fun v hv => (hvalid.halt_obs pc_t σ_t σ_o hinstr hrel v hv).symm))⟩
    | _ => simp only [observe, hinstr] at hobs; exact Observation.noConfusion hobs
  | error σ_t am_t => simp [observe] at hobs
  | typeError σ_t am_t => simp [observe] at hobs

-- ============================================================
-- § Error decomposition and preservation
-- ============================================================

private theorem steps_to_error_decompose {p : Prog} {pc₀ : Nat} {σ₀ σ_e : Store} {am₀ am_e : ArrayMem}
    (hsteps : p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.error σ_e am_e) :
    ∃ pc σ am, (p ⊩ Cfg.run pc₀ σ₀ am₀ ⟶* Cfg.run pc σ am) ∧
      (p ⊩ Cfg.run pc σ am ⟶ Cfg.error σ am) ∧ σ = σ_e := by
  sorry

theorem error_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) {σ_e : Store} {am₀ am_e : ArrayMem}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ_e am_e) :
    ∃ σ_o am_o am_o', cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.error σ_o am_o' := by
  obtain ⟨pc_t, σ_t, am_t, hrun, herr, rfl⟩ := steps_to_error_decompose hreach
  obtain ⟨pc_o, σ_o, ⟨_a1, _a2, _horig⟩, hpc_eq, hrel, hinv_t, hinv_o, _⟩ := simulation_trace hvalid hts₀ hrun
  have hpc := steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hrun
  obtain ⟨σ_o', am_o', horig_err⟩ := hvalid.error_pres pc_t σ_t σ_o am_t hpc hrel hinv_t (hpc_eq ▸ hinv_o) herr
  sorry

-- ============================================================
-- § Divergence preservation
-- ============================================================

theorem diverge_preservation (cert : PCertificate) (hvalid : PCertificateValid cert)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (hinf : IsInfiniteExec cert.trans f) (hf0 : ∃ am₀, f 0 = Cfg.run 0 σ₀ am₀) :
    ∃ g : Nat → Cfg, IsInfiniteExec cert.orig g ∧ ∃ am₀, g 0 = Cfg.run 0 σ₀ am₀ :=
  soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0

-- ============================================================
-- § Main soundness
-- ============================================================

theorem credible_compilation_soundness (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) (b : Behavior)
    (htrans : program_behavior cert.trans σ₀ b) :
    match b with
    | .halts σ_t => ∃ σ_o, (∃ am am', haltsWithResult cert.orig 0 σ₀ σ_o am am') ∧
        ∀ v ∈ cert.observable, σ_t v = σ_o v
    | .errors _ => ∃ σ_o am_o am_o', cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.error σ_o am_o'
    | .typeErrors _ => False
    | .diverges => ∃ f, IsInfiniteExec cert.orig f ∧ ∃ am₀, f 0 = Cfg.run 0 σ₀ am₀ := by
  cases b with
  | halts σ_t' => obtain ⟨am, am', h⟩ := htrans; exact soundness_halt cert hvalid σ₀ σ_t' hts₀ ⟨am, am', h⟩
  | errors σ_e => obtain ⟨am, am', h⟩ := htrans; exact error_preservation cert hvalid σ₀ hts₀ h
  | typeErrors σ_e =>
    obtain ⟨am, am', h⟩ := htrans
    have hwt : WellTypedProg cert.tyCtx cert.trans := by
      rw [PCertificate.tyCtx, hvalid.same_tyCtx]; exact hvalid.well_typed_trans
    exact absurd h (type_safety hwt hts₀ hvalid.step_closed)
  | diverges => obtain ⟨f, hinf, am₀, hf0⟩ := htrans; exact soundness_diverge cert hvalid f σ₀ hts₀ hinf ⟨am₀, hf0⟩

theorem credible_compilation_total (cert : PCertificate) (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) :
    ∃ b, program_behavior cert.trans σ₀ b ∧
      match b with
      | .halts σ_t => ∃ σ_o, (∃ am am', haltsWithResult cert.orig 0 σ₀ σ_o am am') ∧
          ∀ v ∈ cert.observable, σ_t v = σ_o v
      | .errors _ => ∃ σ_o am_o am_o', cert.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.error σ_o am_o'
      | .typeErrors _ => False
      | .diverges => ∃ f, IsInfiniteExec cert.orig f ∧ ∃ am₀, f 0 = Cfg.run 0 σ₀ am₀ := by
  obtain ⟨b, hb⟩ := has_behavior cert.trans σ₀ hvalid.step_closed
  refine ⟨b, hb, ?_⟩
  cases b with
  | halts σ_t =>
    obtain ⟨am, am', h⟩ := hb
    exact soundness_halt cert hvalid σ₀ σ_t hts₀ ⟨am, am', h⟩
  | errors σ_e =>
    obtain ⟨am, am', h⟩ := hb
    exact error_preservation cert hvalid σ₀ hts₀ h
  | typeErrors σ_e =>
    obtain ⟨am, am', h⟩ := hb
    have hwt : WellTypedProg cert.tyCtx cert.trans := by
      rw [PCertificate.tyCtx, hvalid.same_tyCtx]; exact hvalid.well_typed_trans
    exact absurd h (type_safety hwt hts₀ hvalid.step_closed)
  | diverges =>
    obtain ⟨f, hinf, am₀, hf0⟩ := hb
    exact soundness_diverge cert hvalid f σ₀ hts₀ hinf ⟨am₀, hf0⟩

-- ============================================================
-- § Observable output helper
-- ============================================================

def observeProp (cert : PCertificate) (c : Cfg) : Observation :=
  match c with
  | .halt σ _  => Observation.halt (cert.observable.map fun v => (v, σ v))
  | .error _ _ => Observation.error
  | .typeError _ _ => Observation.typeError
  | .run pc σ _ =>
    match cert.trans[pc]? with
    | some .halt => Observation.halt (cert.observable.map fun v => (v, σ v))
    | some _     => Observation.nothing
    | none       => Observation.error
