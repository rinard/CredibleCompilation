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

/-- An invariant map is valid for program `p` starting at `pc` with store `σ`
    if the invariant at `pc` holds for `σ`, and for every reachable
    configuration `(pc', σ')`, the invariant at `pc'` holds for `σ'`. -/
def PInvariantMap.locally_preserved (inv : PInvariantMap) (p : Prog)
    (pc : Label) (σ : Store) : Prop :=
  inv pc σ →
  ∀ pc' σ', (p ⊩ Cfg.run pc σ ⟶ Cfg.run pc' σ') → inv pc' σ'

def PInvariantMap.preserved (inv : PInvariantMap) (p : Prog) : Prop :=
  ∀ pc σ, inv.locally_preserved p pc σ

-- ============================================================
-- § 3. Store relation
-- ============================================================

/-- A relation between an original store and a transformed store.
    Generalizes variable maps: instead of mapping each transformed variable
    to an expression over original variables, we allow arbitrary pairs of
    expressions `(e_orig, e_trans)` asserting `e_orig.eval σ_o = e_trans.eval σ_t`. -/
def PStoreRel := Store → Store → Prop

-- ============================================================
-- § 4. Transition correspondence
-- ============================================================

/-- A single transition correspondence: when the transformed program
    steps from `pc_t` to `pc_t'`, the original program can step from
    `pc_o` through a sequence of labels to `pc_o'` (the corresponding
    original label of `pc_t'`). The labels are the successive PCs
    visited: the first is a successor of `pc_o`, each subsequent label
    is a successor of the previous, and the last equals `pc_o'`. -/
structure PTransCorr where
  /-- Labels of original PCs visited (successors of pc_orig, ending at pc_orig') -/
  origLabels   : List Label
  /-- Store relation at the source -/
  storeRel     : PStoreRel
  /-- Store relation at the target -/
  storeRel_next : PStoreRel

-- ============================================================
-- § 5. PCertificate
-- ============================================================

/-- Per-instruction certificate entry for a non-halt instruction
    in the transformed program. -/
structure PInstrCert where
  /-- Corresponding label in original program -/
  pc_orig    : Label
  /-- Store relation at this instruction -/
  storeRel   : PStoreRel
  /-- For each possible successor `pc_t'` in the transformed program,
      a proof obligation that the original program can match. -/
  transitions : List PTransCorr

/-- Per-instruction certificate entry for a halt instruction. -/
structure PHaltCert where
  /-- Corresponding label in original program -/
  pc_orig  : Label
  /-- Store relation at this instruction -/
  storeRel : PStoreRel

/-- A well-founded measure for proving non-termination correspondence.
    At each label in the transformed program, a measure on the original
    program's corresponding state. When the transformed program takes
    a step with 0 original transitions, the measure must decrease.
    This ensures we cannot have infinitely many transformed steps
    with 0 original steps — eventually the original must also progress. -/
def PTransMeasure := Label → Store → Nat

/-- The full compilation certificate. -/
structure PCertificate where
  /-- Original program -/
  orig        : Prog
  /-- Transformed program -/
  trans       : Prog
  /-- Type context for both programs -/
  tyCtx       : TyCtx
  /-- Invariants for the original program -/
  inv_orig    : PInvariantMap
  /-- Invariants for the transformed program -/
  inv_trans   : PInvariantMap
  /-- Observable variables (checked at halt for equivalence) -/
  observable  : List Var
  /-- PCertificate entry for each label in the transformed program -/
  instrCerts  : Label → PInstrCert
  /-- PCertificate entry for halt instructions in the transformed program -/
  haltCerts   : Label → PHaltCert
  /-- Well-founded measure for non-termination (per transformed label and store). -/
  measure     : PTransMeasure

-- ============================================================
-- § 6. PCertificate checking conditions
-- ============================================================

/-- Condition 2: Invariants are preserved in both programs. -/
def checkInvariantsPreservedProp (cert : PCertificate) : Prop :=
  cert.inv_orig.preserved cert.orig ∧
  cert.inv_trans.preserved cert.trans

/-- Condition 3b: Store relation is maintained across transitions.
    When the transformed program steps from `pc_t` to `pc_t'`,
    if the store relation holds before the step,
    it holds after (with the next relation).
    Requires the original store to be well-typed (`TypedStore Γ σ_o`)
    so that binop operand int-witnesses can be derived. -/
def checkTransitionRelProp
    (Γ : TyCtx)
    (p_orig p_trans : Prog)
    (inv_orig : PInvariantMap) (inv_trans : PInvariantMap)
    (pc_t pc_t' : Label) (pc_o pc_o' : Label) (tc : PTransCorr)
    : Prop :=
  ∀ σ_t σ_t' σ_o,
    inv_trans pc_t σ_t →
    inv_orig pc_o σ_o →
    tc.storeRel σ_o σ_t →
    TypedStore Γ σ_o →
    (p_trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t') →
    ∃ σ_o',
      (p_orig ⊩ Cfg.run pc_o σ_o ⟶* Cfg.run pc_o' σ_o') ∧
      tc.storeRel_next σ_o' σ_t'

/-- Condition 3: For each instruction in the transformed program,
    every transition has a corresponding sequence of transitions
    in the original program. -/
def checkAllTransitionsProp (Γ : TyCtx) (cert : PCertificate) : Prop :=
  ∀ pc_t : Label,
    ∀ σ_t σ_t' : Store,
    ∀ pc_t' : Label,
      (cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t') →
      let ic := cert.instrCerts pc_t
      let ic' := cert.instrCerts pc_t'
      ∃ tc ∈ ic.transitions,
        tc.storeRel = ic.storeRel ∧
        tc.storeRel_next = ic'.storeRel ∧
        checkTransitionRelProp Γ cert.orig cert.trans
          cert.inv_orig cert.inv_trans pc_t pc_t' ic.pc_orig ic'.pc_orig tc

/-- Condition 4a: Each halt in the transformed program corresponds to
    a halt in the original program. Uses `instrCerts` (not `haltCerts`)
    so that the simulation relation, which tracks `instrCerts`, can
    directly conclude the original also halts. -/
def checkHaltCorrespondenceProp (cert : PCertificate) : Prop :=
  ∀ pc_t : Label,
    cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t
    cert.orig[ic.pc_orig]? = some .halt

/-- Condition 4b: Observable variables have the same values at halt.
    Uses `instrCerts` for consistency with the simulation relation. -/
def checkHaltObservableProp (cert : PCertificate) : Prop :=
  ∀ pc_t : Label,
  ∀ σ_t σ_o : Store,
    cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t
    ic.storeRel σ_o σ_t →
    ∀ v ∈ cert.observable, σ_t v = σ_o v

/-- Condition 6 (error preservation): if the transformed program steps to
    `Cfg.error` from a run configuration, the original program can reach
    `Cfg.error` from the corresponding original configuration. -/
def checkErrorPreservationProp (cert : PCertificate) : Prop :=
  ∀ (pc_t : Label) (σ_t σ_o : Store),
    pc_t < cert.trans.size →
    (cert.instrCerts pc_t).storeRel σ_o σ_t →
    cert.inv_trans pc_t σ_t →
    cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o →
    (cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.error σ_t) →
    ∃ σ_o', cert.orig ⊩ Cfg.run (cert.instrCerts pc_t).pc_orig σ_o ⟶* Cfg.error σ_o'

/-- Condition 1 (start): The start instructions correspond. -/
def checkStartCorrespondenceProp (cert : PCertificate) : Prop :=
  (cert.instrCerts 0).pc_orig = 0 ∧
  -- Initial store relation is reflexive (programs start with same store)
  ∀ σ : Store, (cert.instrCerts 0).storeRel σ σ

/-- Condition for invariants to hold at start. -/
def checkInvariantsAtStartProp (cert : PCertificate) : Prop :=
  (∀ σ, cert.inv_trans 0 σ) ∧ (∀ σ, cert.inv_orig 0 σ)

-- ============================================================
-- § 7. Non-termination correspondence (Condition 5)
-- ============================================================

/-- An infinite execution is a function from Nat to configurations
    such that each step is valid. -/
def IsInfiniteExec (p : Prog) (f : Nat → Cfg) : Prop :=
  (∃ σ₀, f 0 = Cfg.run 0 σ₀) ∧
  ∀ n, p ⊩ f n ⟶ f (n + 1)


/-- Condition 5: Zero-step transitions decrease a well-founded measure.
    This ensures that if the transformed program diverges, the original
    also diverges: any infinite transformed execution forces infinitely
    many original steps. -/
def checkNonterminationProp (cert : PCertificate) : Prop :=
  ∀ (pc_t pc_t' : Label) (σ_t σ_t' σ_o : Store),
    cert.inv_trans pc_t σ_t →
    cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o →
    (cert.instrCerts pc_t).storeRel σ_o σ_t →
    (∃ c', (cert.trans ⊩ Cfg.run pc_t σ_t ⟶ c') ∧ c' = Cfg.run pc_t' σ_t') →
    -- If the original takes 0 steps (pc_orig doesn't change)
    (cert.instrCerts pc_t).pc_orig = (cert.instrCerts pc_t').pc_orig →
    -- Then the measure strictly decreases
    cert.measure pc_t' σ_t' < cert.measure pc_t σ_t

-- ============================================================
-- § 8. Complete certificate validity
-- ============================================================

/-- A certificate is valid if all checking conditions hold.
    Uses `cert.tyCtx` to require well-typedness of both programs. -/
structure PCertificateValid (cert : PCertificate) : Prop where
  well_typed_orig  : WellTypedProg cert.tyCtx cert.orig
  well_typed_trans : WellTypedProg cert.tyCtx cert.trans
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

/-- The simulation relation: transformed config at `(pc_t, σ_t)` is
    related to original config at `(pc_o, σ_o)` when the variable map
    is consistent, invariants hold, and the original store is well-typed. -/
def PSimRel (cert : PCertificate) (pc_t : Label) (σ_t : Store)
    (pc_o : Label) (σ_o : Store) : Prop :=
  let ic := cert.instrCerts pc_t
  ic.pc_orig = pc_o ∧
  ic.storeRel σ_o σ_t ∧
  cert.inv_trans pc_t σ_t ∧
  cert.inv_orig pc_o σ_o ∧
  TypedStore cert.tyCtx σ_o

/-- PInvariant preservation across multi-step execution. -/
theorem inv_preserved_steps {inv : PInvariantMap} {p : Prog}
    (hpres : inv.preserved p) {pc pc' : Label} {σ σ' : Store}
    (hsteps : p ⊩ Cfg.run pc σ ⟶* Cfg.run pc' σ')
    (hinv : inv pc σ) :
    inv pc' σ' := by
  -- Generalize to handle intermediate configs
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ, c = Cfg.run pc σ → inv pc σ →
      ∀ pc' σ', c' = Cfg.run pc' σ' → inv pc' σ' from
    this _ _ hsteps pc σ rfl hinv pc' σ' rfl
  intro c c' hsteps
  induction hsteps with
  | refl =>
    intro pc σ hc hinv pc' σ' hc'
    rw [hc] at hc'; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hc'; exact hinv
  | step hstep rest ih =>
    intro pc σ hc hinv pc' σ' hc'; subst hc
    -- Determine if step goes to Run or Halt
    cases hstep with
    | halt h =>
      -- Next is Cfg.halt, but rest reaches Cfg.run — impossible
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | error h _ _ _ =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | const h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.const h)) _ _ hc'
    | copy h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.copy h)) _ _ hc'
    | binop h hy hz hs => exact ih _ _ rfl (hpres _ _ hinv _ _ (.binop h hy hz hs)) _ _ hc'
    | boolop h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.boolop h)) _ _ hc'
    | goto h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.goto h)) _ _ hc'
    | iftrue h hne => exact ih _ _ rfl (hpres _ _ hinv _ _ (.iftrue h hne)) _ _ hc'
    | iffall h heq => exact ih _ _ rfl (hpres _ _ hinv _ _ (.iffall h heq)) _ _ hc'

/-- Bound from `getElem?` returning `some`. -/
private theorem bound_of_getElem? {a : Array α} {i : Nat} {v : α}
    (h : a[i]? = some v) : i < a.size := by
  rw [getElem?_eq_some_iff] at h; exact h.1

/-- Type preservation across multi-step execution. -/
theorem type_preservation_steps {Γ : TyCtx} {p : Prog}
    (hwtp : WellTypedProg Γ p)
    {pc pc' : Label} {σ σ' : Store}
    (hsteps : p ⊩ Cfg.run pc σ ⟶* Cfg.run pc' σ')
    (hts : TypedStore Γ σ) :
    TypedStore Γ σ' := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ, c = Cfg.run pc σ → TypedStore Γ σ →
      ∀ pc' σ', c' = Cfg.run pc' σ' → TypedStore Γ σ' from
    this _ _ hsteps pc σ rfl hts pc' σ' rfl
  intro c c' hsteps
  induction hsteps with
  | refl =>
    intro pc σ hc hts pc' σ' hc'
    rw [hc] at hc'; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hc'; exact hts
  | step hstep rest ih =>
    intro pc σ hc hts pc' σ' hc'; subst hc
    cases hstep with
    | halt h =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | error h _ _ _ =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | const h =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.const h)) _ _ hc'
    | copy h =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.copy h)) _ _ hc'
    | binop h hy hz hs =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.binop h hy hz hs)) _ _ hc'
    | boolop h =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.boolop h)) _ _ hc'
    | goto h =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.goto h)) _ _ hc'
    | iftrue h hne =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.iftrue h hne)) _ _ hc'
    | iffall h heq =>
      exact ih _ _ rfl
        (type_preservation hwtp hts (bound_of_getElem? h) (.iffall h heq)) _ _ hc'

/-- Single-step simulation: a transformed step is matched by original steps,
    preserving the simulation relation. -/
theorem step_sim {cert : PCertificate}
    (hvalid : PCertificateValid cert)
    {pc_t : Label} {σ_t σ_t' : Store} {pc_o : Label} {σ_o : Store} {pc_t' : Label}
    (hsim : PSimRel cert pc_t σ_t pc_o σ_o)
    (hstep : cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t') :
    ∃ pc_o' σ_o',
      (cert.orig ⊩ Cfg.run pc_o σ_o ⟶* Cfg.run pc_o' σ_o') ∧
      PSimRel cert pc_t' σ_t' pc_o' σ_o' := by
  obtain ⟨hpc_orig, hrel_cons, hinv_t, hinv_o, hts_o⟩ := hsim
  -- From checkAllTransitionsProp, get matching transition
  obtain ⟨tc, _, hrel1, hrel2, htrans⟩ :=
    hvalid.transitions pc_t σ_t σ_t' pc_t' hstep
  -- Store relation from hsim + tc agreement
  have hrel_tc : tc.storeRel σ_o σ_t := hrel1 ▸ hrel_cons
  -- Unify pc_o with ic.pc_orig
  subst hpc_orig
  -- Transition relation gives original steps
  obtain ⟨σ_o', horig_steps, hrel_next⟩ :=
    htrans σ_t σ_t' σ_o hinv_t hinv_o hrel_tc hts_o hstep
  -- Build the original steps from pc_o
  refine ⟨(cert.instrCerts pc_t').pc_orig, σ_o', horig_steps, ?_⟩
  -- Type preservation across original steps
  have hts_o' : TypedStore cert.tyCtx σ_o' :=
    type_preservation_steps hvalid.well_typed_orig horig_steps hts_o
  -- Establish PSimRel at new config
  exact ⟨rfl,
         hrel2 ▸ hrel_next,
         hvalid.inv_preserved.2 pc_t σ_t hinv_t pc_t' σ_t' hstep,
         inv_preserved_steps hvalid.inv_preserved.1 horig_steps hinv_o,
         hts_o'⟩

/-- Soundness for halting behaviors: if the certificate is valid and
    the transformed program halts, the original program also halts
    with the same observable values. -/
theorem soundness_halt
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (σ₀ σ_t' : Store)
    (hts₀ : TypedStore cert.tyCtx σ₀)
    (hexec : haltsWithResult cert.trans 0 σ₀ σ_t') :
    ∃ σ_o', haltsWithResult cert.orig 0 σ₀ σ_o' ∧
      ∀ v ∈ cert.observable, σ_t' v = σ_o' v := by
  -- Establish initial simulation relation
  have hsim₀ : PSimRel cert 0 σ₀ 0 σ₀ :=
    ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀,
     hvalid.start_inv.1 σ₀, hvalid.start_inv.2 σ₀, hts₀⟩
  -- Main simulation: induction on the transformed execution trace
  suffices ∀ c c', Steps cert.trans c c' → c' = Cfg.halt σ_t' →
      ∀ pc_t σ_t pc_o σ_o, c = Cfg.run pc_t σ_t →
        PSimRel cert pc_t σ_t pc_o σ_o →
        ∃ σ_o', (cert.orig ⊩ Cfg.run pc_o σ_o ⟶* Cfg.halt σ_o') ∧
          ∀ v ∈ cert.observable, σ_t' v = σ_o' v by
    obtain ⟨σ_o', hsteps, hobs⟩ :=
      this _ _ hexec rfl 0 σ₀ 0 σ₀ rfl hsim₀
    exact ⟨σ_o', hsteps, hobs⟩
  intro c c' hsteps hc'
  induction hsteps with
  | refl =>
    -- c = Cfg.halt σ_t', but c = Cfg.run pc_t σ_t → contradiction
    intro pc_t σ_t _ _ hc _; rw [hc] at hc'; exact absurd hc' Cfg.noConfusion
  | step hstep rest ih =>
    intro pc_t σ_t pc_o σ_o hc hsim; subst hc
    cases hstep with
    | halt h =>
      -- Transformed program halts at pc_t
      obtain ⟨hpc_orig, hrel_cons, _, _, _⟩ := hsim
      -- Unify pc_o with (instrCerts pc_t).pc_orig
      have h_pc_eq : pc_o = (cert.instrCerts pc_t).pc_orig := hpc_orig.symm
      subst h_pc_eq
      have horig_halt := hvalid.halt_corr pc_t h
      -- rest must be refl (no steps from halt)
      cases rest with
      | refl =>
        have := Cfg.halt.inj hc'
        subst this
        exact ⟨σ_o, Steps.single (Step.halt horig_halt),
               hvalid.halt_obs pc_t σ_t σ_o h hrel_cons⟩
      | step s _ => exact absurd s Step.no_step_from_halt
    | error h _ _ _ =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | const h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.const h)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | copy h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.copy h)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | binop h hy hz hs =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.binop h hy hz hs)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | boolop h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.boolop h)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | goto h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.goto h)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | iftrue h hne =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.iftrue h hne)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | iffall h heq =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.iffall h heq)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩

/-- n-step execution: there exist exactly n steps from c to c'. -/
def StepsN (p : Prog) : Cfg → Cfg → Nat → Prop
  | c, c', 0 => c = c'
  | c, c', n + 1 => ∃ c'', Step p c c'' ∧ StepsN p c'' c' n

/-- Determinism for StepsN. -/
theorem StepsN_det {p : Prog} {c : Cfg} {n : Nat} :
    ∀ {c' c''}, StepsN p c c' n → StepsN p c c'' n → c' = c'' := by
  induction n generalizing c with
  | zero => intro _ _ h1 h2; exact h1.symm.trans h2
  | succ n ih =>
    intro _ _ h1 h2
    obtain ⟨c1, hs1, hr1⟩ := h1
    obtain ⟨c2, hs2, hr2⟩ := h2
    have := Step.deterministic hs1 hs2; subst this
    exact ih hr1 hr2

/-- Extend a StepsN by one step at the end. -/
theorem StepsN_extend {p : Prog} {c c' c'' : Cfg} {n : Nat}
    (h1 : StepsN p c c' n) (h2 : Step p c' c'') :
    StepsN p c c'' (n + 1) := by
  induction n generalizing c with
  | zero =>
    change c = c' at h1; subst h1
    exact ⟨c'', h2, rfl⟩
  | succ n ih =>
    obtain ⟨cm, hs, hr⟩ := h1
    exact ⟨cm, hs, ih hr⟩

/-- Split last step from a (n+1)-step execution. -/
theorem StepsN_split_last {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' (n + 1)) : ∃ c'', StepsN p c c'' n ∧ Step p c'' c' := by
  induction n generalizing c with
  | zero =>
    obtain ⟨c'', hs, hr⟩ := h
    exact ⟨c, rfl, hr ▸ hs⟩
  | succ n ih =>
    obtain ⟨c1, hs, hr⟩ := h
    obtain ⟨c2, h2, hlast⟩ := ih hr
    exact ⟨c2, ⟨c1, hs, h2⟩, hlast⟩

/-- Compose two StepsN sequences. -/
theorem StepsN_trans {p : Prog} {c c' c'' : Cfg} {n m : Nat}
    (h1 : StepsN p c c' n) (h2 : StepsN p c' c'' m) :
    StepsN p c c'' (n + m) := by
  induction n generalizing c with
  | zero =>
    change c = c' at h1; subst h1
    show StepsN p c c'' (0 + m); rw [Nat.zero_add]; exact h2
  | succ n ih =>
    obtain ⟨cm, hs, hr⟩ := h1
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]; exact ⟨cm, hs, ih hr⟩

/-- Convert Steps to StepsN (existential on length). -/
theorem Steps_to_StepsN {p : Prog} {c c' : Cfg}
    (h : Steps p c c') : ∃ n, StepsN p c c' n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step s _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, ⟨_, s, hn⟩⟩

/-- Truncate: from StepsN of length n+k, extract prefix of length n. -/
theorem StepsN_prefix {p : Prog} {c c' : Cfg} {n k : Nat}
    (h : StepsN p c c' (n + k)) : ∃ c'', StepsN p c c'' n := by
  induction k generalizing c' with
  | zero => exact ⟨c', h⟩
  | succ k ih =>
    have : n + (k + 1) = (n + k) + 1 := by omega
    rw [this] at h
    obtain ⟨cmid, hmid, _⟩ := StepsN_split_last h
    exact ih hmid

/-- A Step must come from a Cfg.run. -/
theorem step_from_run {p : Prog} {c c' : Cfg}
    (h : Step p c c') : ∃ pc σ, c = Cfg.run pc σ := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- Transformed execution configs are always Cfg.run (never halt). -/
theorem inf_exec_is_run {p : Prog} {f : Nat → Cfg}
    (hinf : IsInfiniteExec p f) :
    ∀ n, ∃ pc σ, f n = Cfg.run pc σ := by
  intro n
  cases hfn : f n with
  | run pc σ => exact ⟨pc, σ, rfl⟩
  | halt σ =>
    exfalso; have := hinf.2 n; rw [hfn] at this
    exact Step.no_step_from_halt this
  | error σ =>
    exfalso; have := hinf.2 n; rw [hfn] at this
    exact Step.no_step_from_error this

/-- From an (n+1)-step execution that ends at Cfg.run, the n-th config
    is also Cfg.run and there's a step from it. -/
theorem StepsN_run_predecessor {p : Prog} {c : Cfg} {pc : Label} {σ : Store} {n : Nat}
    (h : StepsN p c (Cfg.run pc σ) (n + 1)) :
    ∃ pc' σ' c'', StepsN p c (Cfg.run pc' σ') n ∧
      Step p (Cfg.run pc' σ') c'' := by
  obtain ⟨c'', h'', hlast⟩ := StepsN_split_last h
  obtain ⟨pc', σ', hc''⟩ := step_from_run hlast
  exact ⟨pc', σ', _, hc'' ▸ h'', hc'' ▸ hlast⟩

/-- Split a StepsN into prefix and suffix. -/
theorem StepsN_split {p : Prog} {c c' : Cfg} {n k : Nat}
    (h : StepsN p c c' (n + k)) : ∃ c'', StepsN p c c'' n ∧ StepsN p c'' c' k := by
  induction n generalizing c with
  | zero =>
    have : 0 + k = k := Nat.zero_add k
    exact ⟨c, rfl, this ▸ h⟩
  | succ n ih =>
    have heq : n + 1 + k = (n + k) + 1 := by omega
    rw [heq] at h
    obtain ⟨cm, hs, hr⟩ := h
    obtain ⟨c'', hp, hs'⟩ := ih hr
    exact ⟨c'', ⟨cm, hs, hp⟩, hs'⟩

/-- If we can reach Cfg.run after total steps and N ≤ total, the N-th intermediate is also Cfg.run. -/
theorem StepsN_intermediate_run {p : Prog} {pc₀ : Label} {σ₀ : Store}
    {pc' : Label} {σ' : Store} {total : Nat}
    (h : StepsN p (Cfg.run pc₀ σ₀) (Cfg.run pc' σ') total)
    {N : Nat} (hle : N ≤ total) :
    ∃ pc'' σ'', StepsN p (Cfg.run pc₀ σ₀) (Cfg.run pc'' σ'') N := by
  by_cases heq : N = total
  · subst heq; exact ⟨pc', σ', h⟩
  · have hlt : N < total := by omega
    have h' : StepsN p (Cfg.run pc₀ σ₀) (Cfg.run pc' σ') (N + (total - N)) := by
      have : N + (total - N) = total := by omega
      rw [this]; exact h
    obtain ⟨c'', h1, h2⟩ := StepsN_split h'
    have hk : total - N = (total - N - 1) + 1 := by omega
    rw [hk] at h2
    obtain ⟨c''', hs, _⟩ := h2
    obtain ⟨pc'', σ'', hc⟩ := step_from_run hs; subst hc
    exact ⟨pc'', σ'', h1⟩

/-- Soundness for non-terminating behaviors: if the certificate is valid
    and the transformed program diverges, the original program also
    diverges. -/
theorem soundness_diverge
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (f : Nat → Cfg) (σ₀ : Store)
    (hts₀ : TypedStore cert.tyCtx σ₀)
    (hinf : IsInfiniteExec cert.trans f)
    (hf0 : f 0 = Cfg.run 0 σ₀) :
    ∃ g : Nat → Cfg, IsInfiniteExec cert.orig g ∧ g 0 = Cfg.run 0 σ₀ := by
  -- Key fact: for all N, the original can take exactly N steps and stay at Cfg.run
  suffices h_arb : ∀ N : Nat, ∃ pc σ,
      StepsN cert.orig (Cfg.run 0 σ₀) (Cfg.run pc σ) N by
    -- Define g(n) as the unique n-th config (via Classical.choice + determinism)
    have g_spec : ∀ n, ∃ c, StepsN cert.orig (Cfg.run 0 σ₀) c n ∧
        ∃ pc σ, c = Cfg.run pc σ := by
      intro n; obtain ⟨pc, σ, h⟩ := h_arb n; exact ⟨_, h, pc, σ, rfl⟩
    let g : Nat → Cfg := fun n => (g_spec n).choose
    have g_stepsN : ∀ n, StepsN cert.orig (Cfg.run 0 σ₀) (g n) n :=
      fun n => (g_spec n).choose_spec.1
    have g_run : ∀ n, ∃ pc σ, g n = Cfg.run pc σ :=
      fun n => (g_spec n).choose_spec.2
    refine ⟨g, ⟨⟨σ₀, ?_⟩, fun n => ?_⟩, ?_⟩
    · -- g 0 = Cfg.run 0 σ₀
      exact (g_stepsN 0).symm
    · -- Step cert.orig (g n) (g (n+1))
      obtain ⟨c'', h_prefix, h_last⟩ := StepsN_split_last (g_stepsN (n + 1))
      have heq := StepsN_det (g_stepsN n) h_prefix
      rw [← heq] at h_last
      exact h_last
    · -- g 0 = Cfg.run 0 σ₀
      have := g_stepsN 0
      exact this.symm
  -- Prove h_arb by building simulation trace + well-founded μ argument
  have hf_run := inf_exec_is_run hinf
  -- Progress: from any simulation state with μ-bound m, advance original ≥ 1 step
  have advance : ∀ (m n : Nat) (pc_o : Label) (σ_o : Store) (total : Nat),
      (∀ pc_t σ_t, f n = Cfg.run pc_t σ_t → cert.measure pc_t σ_t ≤ m) →
      (∀ pc_t σ_t, f n = Cfg.run pc_t σ_t → PSimRel cert pc_t σ_t pc_o σ_o) →
      StepsN cert.orig (Cfg.run 0 σ₀) (Cfg.run pc_o σ_o) total →
      ∃ (n' : Nat) (pc_o' : Label) (σ_o' : Store) (total' : Nat),
        (∀ pc_t σ_t, f n' = Cfg.run pc_t σ_t → PSimRel cert pc_t σ_t pc_o' σ_o') ∧
        StepsN cert.orig (Cfg.run 0 σ₀) (Cfg.run pc_o' σ_o') total' ∧
        total' ≥ total + 1 := by
    intro m; induction m with
    | zero =>
      intro n pc_o σ_o total hmu hsim_fn hsteps
      obtain ⟨pc_t, σ_t, hfn⟩ := hf_run n
      obtain ⟨pc_t', σ_t', hfn1⟩ := hf_run (n + 1)
      have hsim := hsim_fn pc_t σ_t hfn
      have hstep : cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t' := by
        have := hinf.2 n; rw [hfn, hfn1] at this; exact this
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim hstep
      obtain ⟨k, hk⟩ := Steps_to_StepsN horig
      cases k with
      | zero =>
        -- k = 0 original steps → μ < 0, contradiction
        change Cfg.run pc_o σ_o = Cfg.run pc_o' σ_o' at hk
        obtain ⟨rfl, rfl⟩ := Cfg.run.inj hk
        have hpc_eq := hsim.1.trans hsim'.1.symm
        have hnt := hvalid.nonterm pc_t pc_t' σ_t σ_t' σ_o
          hsim.2.2.1 (hsim.1 ▸ hsim.2.2.2.1) hsim.2.1 ⟨_, hstep, rfl⟩ hpc_eq
        have := hmu pc_t σ_t hfn; omega
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', total + (k' + 1),
          fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; exact hsim',
          StepsN_trans hsteps hk, by omega⟩
    | succ m ih =>
      intro n pc_o σ_o total hmu hsim_fn hsteps
      obtain ⟨pc_t, σ_t, hfn⟩ := hf_run n
      obtain ⟨pc_t', σ_t', hfn1⟩ := hf_run (n + 1)
      have hsim := hsim_fn pc_t σ_t hfn
      have hstep : cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t' := by
        have := hinf.2 n; rw [hfn, hfn1] at this; exact this
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim hstep
      obtain ⟨k, hk⟩ := Steps_to_StepsN horig
      cases k with
      | zero =>
        -- k = 0 → μ decreases, recurse with smaller bound
        change Cfg.run pc_o σ_o = Cfg.run pc_o' σ_o' at hk
        obtain ⟨rfl, rfl⟩ := Cfg.run.inj hk
        have hpc_eq := hsim.1.trans hsim'.1.symm
        have hmu_dec := hvalid.nonterm pc_t pc_t' σ_t σ_t' σ_o
          hsim.2.2.1 (hsim.1 ▸ hsim.2.2.2.1) hsim.2.1 ⟨_, hstep, rfl⟩ hpc_eq
        have hmu_n := hmu pc_t σ_t hfn
        exact ih (n + 1) pc_o σ_o total
          (fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; omega)
          (fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; exact hsim')
          hsteps
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', total + (k' + 1),
          fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; exact hsim',
          StepsN_trans hsteps hk, by omega⟩
  -- For any N, find enough original steps via stronger induction carrying PSimRel
  suffices ∀ N, ∃ (n : Nat) (pc_o : Label) (σ_o : Store) (total : Nat),
      (∀ pc_t σ_t, f n = Cfg.run pc_t σ_t → PSimRel cert pc_t σ_t pc_o σ_o) ∧
      StepsN cert.orig (Cfg.run 0 σ₀) (Cfg.run pc_o σ_o) total ∧ total ≥ N by
    intro N
    obtain ⟨_, _, _, total, _, hsteps, hge⟩ := this N
    exact StepsN_intermediate_run hsteps hge
  intro N; induction N with
  | zero =>
    refine ⟨0, 0, σ₀, 0, ?_, rfl, Nat.zero_le _⟩
    intro pc_t σ_t hfn; rw [hf0] at hfn; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hfn
    exact ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀,
           hvalid.start_inv.1 σ₀, hvalid.start_inv.2 σ₀, hts₀⟩
  | succ N ih =>
    obtain ⟨n, pc_o, σ_o, total, hsim_fn, hsteps, hge⟩ := ih
    obtain ⟨pc_t, σ_t, hfn⟩ := hf_run n
    obtain ⟨n', pc_o', σ_o', total', hsim', hsteps', hge'⟩ :=
      advance (cert.measure pc_t σ_t) n pc_o σ_o total
        (fun pc σ hf => by rw [hfn] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; omega)
        hsim_fn hsteps
    exact ⟨n', pc_o', σ_o', total', hsim', hsteps', by omega⟩

-- ============================================================
-- § 10. Main soundness theorem
-- ============================================================

/-- A behavior is halting (with a final store), erroring (e.g. div-by-zero),
    or diverging. -/
inductive Behavior where
  | halts    : Store → Behavior
  | errors   : Store → Behavior
  | diverges : Behavior

/-- Extract behavior of a program from label 0 with initial store σ₀. -/
def program_behavior (p : Prog) (σ₀ : Store) (b : Behavior) : Prop :=
  match b with
  | .halts σ'   => haltsWithResult p 0 σ₀ σ'
  | .errors σ'  => p ⊩ Cfg.run 0 σ₀ ⟶* Cfg.error σ'
  | .diverges   => ∃ f : Nat → Cfg, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀

-- ============================================================
-- § 10a. Totality: bounds-closed programs always have a behavior
-- ============================================================


/-- Convert StepsN to Steps. -/
private theorem StepsN_to_Steps' {p : Prog} {c c' : Cfg} {n : Nat}
    (h : StepsN p c c' n) : p ⊩ c ⟶* c' := by
  induction n generalizing c with
  | zero => exact h ▸ .refl
  | succ n ih =>
    obtain ⟨c'', hs, hn⟩ := h
    exact .step hs (ih hn)

/-- **Totality**: A well-typed, step-closed program always has a behavior
    (halts, errors, or diverges). -/
theorem has_behavior (p : Prog) (σ₀ : Store) (Γ : TyCtx)
    (hwtp : WellTypedProg Γ p) (hts₀ : TypedStore Γ σ₀)
    (hclosed : StepClosedInBounds p) :
    ∃ b, program_behavior p σ₀ b := by
  -- Either the program reaches halt at some finite step, or it never does.
  by_cases h : ∃ n σ', StepsN p (Cfg.run 0 σ₀) (Cfg.halt σ') n
  · -- Case: halts
    obtain ⟨n, σ', hn⟩ := h
    exact ⟨.halts σ', StepsN_to_Steps' hn⟩
  · by_cases he : ∃ n σ', StepsN p (Cfg.run 0 σ₀) (Cfg.error σ') n
    · -- Case: errors
      obtain ⟨_, σ', hn⟩ := he
      exact ⟨.errors σ', StepsN_to_Steps' hn⟩
    · -- Never halts and never errors. For well-typed, step-closed programs: diverges.
      have h_run : ∀ n, ∃ pc σ, StepsN p (Cfg.run 0 σ₀) (Cfg.run pc σ) n ∧
          pc < p.size ∧ TypedStore Γ σ := by
        intro n; induction n with
        | zero => exact ⟨0, σ₀, rfl, hclosed.1, hts₀⟩
        | succ n ih =>
          obtain ⟨pc, σ, hn, hpc, hts⟩ := ih
          obtain ⟨c', hstep⟩ := Step.progress p pc σ Γ hpc hwtp hts
          match c', hstep with
          | .halt σ', hstep =>
            exact absurd ⟨n + 1, σ', StepsN_extend hn hstep⟩ h
          | .error σ', hstep =>
            exact absurd ⟨n + 1, σ', StepsN_extend hn hstep⟩ he
          | .run pc' σ', hstep =>
            exact ⟨pc', σ', StepsN_extend hn hstep, hclosed.2 pc pc' σ σ' hpc hstep,
              type_preservation hwtp hts hpc hstep⟩
      -- Build the infinite execution using Classical.choice + determinism
      have g_spec : ∀ n, ∃ c, StepsN p (Cfg.run 0 σ₀) c n ∧ ∃ pc σ, c = Cfg.run pc σ := by
        intro n; obtain ⟨pc, σ, hn, _⟩ := h_run n; exact ⟨_, hn, pc, σ, rfl⟩
      let g : Nat → Cfg := fun n => (g_spec n).choose
      have g_stepsN : ∀ n, StepsN p (Cfg.run 0 σ₀) (g n) n :=
        fun n => (g_spec n).choose_spec.1
      refine ⟨.diverges, g, ⟨⟨σ₀, ?_⟩, fun n => ?_⟩, ?_⟩
      · exact (g_stepsN 0).symm
      · obtain ⟨c'', h_prefix, h_last⟩ := StepsN_split_last (g_stepsN (n + 1))
        exact StepsN_det (g_stepsN n) h_prefix ▸ h_last
      · exact (g_stepsN 0).symm

-- ============================================================
-- § 11. Simulation trace for reachable run-configs
-- ============================================================

/-- If the transformed program reaches `Cfg.run pc_t σ_t`, the original
    program reaches a corresponding `Cfg.run pc_o σ_o` with the simulation
    relation preserved. -/
theorem simulation_trace
    {cert : PCertificate}
    (hvalid : PCertificateValid cert)
    {σ₀ : Store} (hts₀ : TypedStore cert.tyCtx σ₀)
    {pc_t : Label} {σ_t : Store}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ ⟶* Cfg.run pc_t σ_t) :
    ∃ pc_o σ_o,
      (cert.orig ⊩ Cfg.run 0 σ₀ ⟶* Cfg.run pc_o σ_o) ∧
      PSimRel cert pc_t σ_t pc_o σ_o := by
  have hsim₀ : PSimRel cert 0 σ₀ 0 σ₀ :=
    ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀,
     hvalid.start_inv.1 σ₀, hvalid.start_inv.2 σ₀, hts₀⟩
  suffices ∀ c c', Steps cert.trans c c' →
      ∀ pc_t σ_t pc_o σ_o, c = Cfg.run pc_t σ_t →
        PSimRel cert pc_t σ_t pc_o σ_o →
        ∀ pc_t' σ_t', c' = Cfg.run pc_t' σ_t' →
        ∃ pc_o' σ_o',
          (cert.orig ⊩ Cfg.run pc_o σ_o ⟶* Cfg.run pc_o' σ_o') ∧
          PSimRel cert pc_t' σ_t' pc_o' σ_o' by
    exact this _ _ hreach 0 σ₀ 0 σ₀ rfl hsim₀ pc_t σ_t rfl
  intro c c' hsteps
  induction hsteps with
  | refl =>
    intro pc_t σ_t pc_o σ_o hc hsim pc_t' σ_t' hc'
    rw [hc] at hc'; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hc'
    exact ⟨pc_o, σ_o, Steps.refl, hsim⟩
  | step hstep rest ih =>
    intro pc_t σ_t pc_o σ_o hc hsim pc_t' σ_t' hc'; subst hc
    cases hstep with
    | halt h =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | error h _ _ _ =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | const h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.const h)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩
    | copy h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.copy h)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩
    | binop h hy hz hs =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.binop h hy hz hs)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩
    | boolop h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.boolop h)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩
    | goto h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.goto h)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩
    | iftrue h hne =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.iftrue h hne)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩
    | iffall h heq =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.iffall h heq)
      obtain ⟨pc_o'', σ_o'', hfinal, hsim''⟩ := ih _ _ pc_o' σ_o' rfl hsim' pc_t' σ_t' hc'
      exact ⟨pc_o'', σ_o'', Steps.trans horig hfinal, hsim''⟩

-- ============================================================
-- § 12. Observation preservation
-- ============================================================

/-- Helper: if two stores agree on a list of variables, their observable
    projections are equal. -/
private theorem obs_map_eq {obs : List Var} {σ_t σ_o : Store}
    (h : ∀ v ∈ obs, σ_t v = σ_o v) :
    obs.map (fun v => (v, σ_t v)) = obs.map (fun v => (v, σ_o v)) := by
  induction obs with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨congrArg (Prod.mk v) (h v (.head _)),
           ih (fun w hw => h w (.tail _ hw))⟩

/-- All reachable `Cfg.run` configurations have in-bounds PCs. -/
private theorem steps_run_in_bounds {p : Prog}
    (hclosed : StepClosedInBounds p)
    {pc₀ : Label} {σ₀ : Store} (hpc₀ : pc₀ < p.size)
    {pc : Label} {σ : Store}
    (hreach : p ⊩ Cfg.run pc₀ σ₀ ⟶* Cfg.run pc σ) :
    pc < p.size := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc₀ σ₀, c = Cfg.run pc₀ σ₀ → pc₀ < p.size →
      ∀ pc σ, c' = Cfg.run pc σ → pc < p.size from
    this _ _ hreach _ _ rfl hpc₀ _ _ rfl
  intro c c' hsteps
  induction hsteps with
  | refl =>
    intro _ _ hc hpc _ _ hc'
    rw [hc] at hc'; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hc'; exact hpc
  | step hstep rest ih =>
    intro pc₁ σ₁ hc hpc pc' σ' hc'; subst hc
    cases hstep with
    | halt _ =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | error _ _ _ _ =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_error
    | const h =>
      have s : Step p (.run pc₁ σ₁) _ := .const h
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'
    | copy h =>
      have s : Step p (.run pc₁ σ₁) _ := .copy h
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'
    | binop h hy hz hs =>
      have s : Step p (.run pc₁ σ₁) _ := .binop h hy hz hs
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'
    | boolop h =>
      have s : Step p (.run pc₁ σ₁) _ := .boolop h
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'
    | goto h =>
      have s : Step p (.run pc₁ σ₁) _ := .goto h
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'
    | iftrue h e =>
      have s : Step p (.run pc₁ σ₁) _ := .iftrue h e
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'
    | iffall h e =>
      have s : Step p (.run pc₁ σ₁) _ := .iffall h e
      exact ih _ _ rfl (hclosed.2 _ _ _ _ hpc s) _ _ hc'

/-- **Halt preservation**: If the certificate is valid and the transformed
    program has an execution that halts, then the original program has an
    execution that halts with the same values for observable variables. -/
theorem halt_preservation
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (c_t : Cfg)
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ ⟶* c_t)
    (pairs : List (Var × Value))
    (hobs : observe cert.trans cert.observable c_t = Observation.halt pairs) :
    ∃ c_o, (cert.orig ⊩ Cfg.run 0 σ₀ ⟶* c_o) ∧
      observe cert.orig cert.observable c_o = Observation.halt pairs := by
  cases c_t with
  | halt σ_t =>
    obtain ⟨σ_o, horig, hobs_eq⟩ := soundness_halt cert hvalid σ₀ σ_t hts₀ hreach
    have htobs : observe cert.trans cert.observable (Cfg.halt σ_t) =
        Observation.halt (cert.observable.map fun v => (v, σ_t v)) := rfl
    have hoobs : observe cert.orig cert.observable (Cfg.halt σ_o) =
        Observation.halt (cert.observable.map fun v => (v, σ_o v)) := rfl
    rw [htobs] at hobs; rw [Observation.halt.injEq] at hobs; subst hobs
    exact ⟨Cfg.halt σ_o, horig, hoobs ▸
      congrArg Observation.halt (obs_map_eq (fun v hv => (hobs_eq v hv).symm))⟩
  | run pc_t σ_t =>
    have hpc : pc_t < cert.trans.size :=
      steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hreach
    obtain ⟨instr, hinstr⟩ : ∃ instr, cert.trans[pc_t]? = some instr :=
      ⟨cert.trans[pc_t], getElem?_eq_some_iff.mpr ⟨hpc, rfl⟩⟩
    cases instr with
    | halt =>
      obtain ⟨pc_o, σ_o, horig, hpc_eq, hrel, _, _, _⟩ := simulation_trace hvalid hts₀ hreach
      have horig_halt : cert.orig[pc_o]? = some TAC.halt := by
        rw [← hpc_eq]; exact hvalid.halt_corr pc_t hinstr
      have hobs_eq := hvalid.halt_obs pc_t σ_t σ_o hinstr hrel
      have htobs : observe cert.trans cert.observable (Cfg.run pc_t σ_t) =
          Observation.halt (cert.observable.map fun v => (v, σ_t v)) := by
        simp only [observe, hinstr]
      have hoobs : observe cert.orig cert.observable (Cfg.run pc_o σ_o) =
          Observation.halt (cert.observable.map fun v => (v, σ_o v)) := by
        simp only [observe, horig_halt]
      rw [htobs] at hobs; rw [Observation.halt.injEq] at hobs; subst hobs
      exact ⟨Cfg.run pc_o σ_o, horig, hoobs ▸
        congrArg Observation.halt (obs_map_eq (fun v hv => (hobs_eq v hv).symm))⟩
    | _ =>
      have htobs : observe cert.trans cert.observable (Cfg.run pc_t σ_t) =
          Observation.nothing := by simp only [observe, hinstr]
      rw [htobs] at hobs; exact Observation.noConfusion hobs
  | error σ_t =>
    simp [observe] at hobs

/-- Helper: decompose steps to error into steps to a run config followed by one error step. -/
private theorem steps_to_error_decompose {p : Prog} {pc₀ : Nat} {σ₀ σ_e : Store}
    (hsteps : p ⊩ Cfg.run pc₀ σ₀ ⟶* Cfg.error σ_e) :
    ∃ pc σ, (p ⊩ Cfg.run pc₀ σ₀ ⟶* Cfg.run pc σ) ∧
      (p ⊩ Cfg.run pc σ ⟶ Cfg.error σ) ∧ σ = σ_e := by
  suffices ∀ c c', Steps p c c' →
      ∀ pc₀ σ₀, c = Cfg.run pc₀ σ₀ → c' = Cfg.error σ_e →
      ∃ pc σ, (p ⊩ Cfg.run pc₀ σ₀ ⟶* Cfg.run pc σ) ∧
        (p ⊩ Cfg.run pc σ ⟶ Cfg.error σ) ∧ σ = σ_e from
    this _ _ hsteps _ _ rfl rfl
  intro c c' hss
  induction hss with
  | refl => intro _ _ hc hc'; rw [hc] at hc'; exact Cfg.noConfusion hc'
  | step hstep rest ih =>
    intro pc₀ σ₀ hc hc'; subst hc
    cases hstep with
    | error hinstr hy hz hs =>
      cases rest with
      | refl =>
        have := Cfg.error.inj hc'; subst this
        exact ⟨pc₀, σ₀, Steps.refl, Step.error hinstr hy hz hs, rfl⟩
      | step s _ => exact absurd s Step.no_step_from_error
    | halt hinstr =>
      cases rest with
      | refl => exact absurd hc' Cfg.noConfusion
      | step s _ => exact absurd s Step.no_step_from_halt
    | const hinstr =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.const hinstr) hreach, herr, heq⟩
    | copy hinstr =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.copy hinstr) hreach, herr, heq⟩
    | binop hinstr hy hz hs =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.binop hinstr hy hz hs) hreach, herr, heq⟩
    | boolop hinstr =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.boolop hinstr) hreach, herr, heq⟩
    | goto hinstr =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.goto hinstr) hreach, herr, heq⟩
    | iftrue hinstr e =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.iftrue hinstr e) hreach, herr, heq⟩
    | iffall hinstr e =>
      obtain ⟨pc, σ, hreach, herr, heq⟩ := ih _ _ rfl hc'
      exact ⟨pc, σ, Steps.step (.iffall hinstr e) hreach, herr, heq⟩

/-- **Error preservation**: If the certificate is valid and the transformed
    program reaches `Cfg.error`, then the original program also reaches
    `Cfg.error`. -/
theorem error_preservation
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    {σ_e : Store}
    (hreach : cert.trans ⊩ Cfg.run 0 σ₀ ⟶* Cfg.error σ_e) :
    ∃ σ_o, cert.orig ⊩ Cfg.run 0 σ₀ ⟶* Cfg.error σ_o := by
  obtain ⟨pc_t, σ_t, hrun_reach, herr_step, rfl⟩ := steps_to_error_decompose hreach
  obtain ⟨pc_o, σ_o, horig_reach, hpc_eq, hrel, hinv_t, hinv_o, _⟩ :=
    simulation_trace hvalid hts₀ hrun_reach
  have hpc : pc_t < cert.trans.size :=
    steps_run_in_bounds hvalid.step_closed hvalid.step_closed.1 hrun_reach
  obtain ⟨σ_o', horig_err⟩ := hvalid.error_pres pc_t σ_t σ_o hpc hrel hinv_t
    (hpc_eq ▸ hinv_o) herr_step
  exact ⟨σ_o', Steps.trans horig_reach (hpc_eq ▸ horig_err)⟩

/-- **Divergence preservation**: If the certificate is valid and the
    transformed program has an execution that diverges (infinite trace),
    then the original program has an execution that diverges. -/
theorem diverge_preservation
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (hinf : IsInfiniteExec cert.trans f)
    (hf0 : f 0 = Cfg.run 0 σ₀) :
    ∃ g : Nat → Cfg, IsInfiniteExec cert.orig g ∧ g 0 = Cfg.run 0 σ₀ :=
  soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0

-- ============================================================
-- § 12b. Main soundness theorems
-- ============================================================

/-- **Main Theorem**: If the certificate is valid, then for every initial
    store, every behavior of the transformed program has a corresponding
    guarantee about the original program. -/
theorem credible_compilation_soundness
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀)
    (b : Behavior)
    (htrans : program_behavior cert.trans σ₀ b) :
    match b with
    | .halts σ_t => ∃ σ_o, haltsWithResult cert.orig 0 σ₀ σ_o ∧
        ∀ v ∈ cert.observable, σ_t v = σ_o v
    | .errors σ_e => ∃ σ_o, cert.orig ⊩ Cfg.run 0 σ₀ ⟶* Cfg.error σ_o
    | .diverges => ∃ f, IsInfiniteExec cert.orig f ∧ f 0 = Cfg.run 0 σ₀ := by
  cases b with
  | halts σ_t' => exact soundness_halt cert hvalid σ₀ σ_t' hts₀ htrans
  | errors σ_e => exact error_preservation cert hvalid σ₀ hts₀ htrans
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    exact soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0

/-- **Total soundness**: If the certificate is valid and the transformed
    program is step-closed, then for every initial store there exists a
    behavior of the transformed program with a corresponding guarantee
    about the original program. -/
theorem credible_compilation_total
    (cert : PCertificate)
    (hvalid : PCertificateValid cert)
    (σ₀ : Store) (hts₀ : TypedStore cert.tyCtx σ₀) :
    ∃ b, program_behavior cert.trans σ₀ b ∧
      match b with
      | .halts σ_t => ∃ σ_o, haltsWithResult cert.orig 0 σ₀ σ_o ∧
          ∀ v ∈ cert.observable, σ_t v = σ_o v
      | .errors σ_e => ∃ σ_o, cert.orig ⊩ Cfg.run 0 σ₀ ⟶* Cfg.error σ_o
      | .diverges => ∃ f, IsInfiniteExec cert.orig f ∧ f 0 = Cfg.run 0 σ₀ := by
  obtain ⟨b, hb⟩ := has_behavior cert.trans σ₀ cert.tyCtx hvalid.well_typed_trans hts₀ hvalid.step_closed
  refine ⟨b, hb, ?_⟩
  cases b with
  | halts σ_t => exact soundness_halt cert hvalid σ₀ σ_t hts₀ hb
  | errors σ_e => exact error_preservation cert hvalid σ₀ hts₀ hb
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := hb
    exact soundness_diverge cert hvalid f σ₀ hts₀ hinf hf0

-- ============================================================
-- § 13. Observable output at a configuration
-- ============================================================

/-- Observable output of a configuration with respect to a propositional certificate.
    - If the current instruction is `halt`, returns `halt` with observable variable–value pairs.
    - If the configuration is `error`, returns `error`.
    - If the PC is out of bounds, returns `error`.
    - Otherwise returns `nothing`. -/
def observeProp (cert : PCertificate) (c : Cfg) : Observation :=
  match c with
  | .halt σ  => Observation.halt (cert.observable.map fun v => (v, σ v))
  | .error _ => Observation.error
  | .run pc σ =>
    match cert.trans[pc]? with
    | some .halt => Observation.halt (cert.observable.map fun v => (v, σ v))
    | some _     => Observation.nothing
    | none       => Observation.error
