import CredibleCompilation.Semantics

/-!
# Certificate Checker for Credible Compilation

A certificate checker that verifies: every behavior of a transformed program
has a corresponding behavior in the original program.

Based on the credible compilation framework (Rinard, MIT-LCS-TR-776).
-/

-- ============================================================
-- § 1. Expressions over stores
-- ============================================================

/-- Expressions that can be evaluated in a store. Used to describe
    how transformed-program variables map to original-program values. -/
inductive Expr where
  | lit  : Val → Expr
  | var  : Var → Expr
  | bin  : BinOp → Expr → Expr → Expr
  deriving Repr, DecidableEq

def Expr.eval (σ : Store) : Expr → Val
  | .lit n       => n
  | .var x       => σ x
  | .bin op a b  => op.eval (a.eval σ) (b.eval σ)

-- ============================================================
-- § 2. Invariants (Floyd-Hoare style properties)
-- ============================================================

/-- A predicate on stores, attached to a program point. -/
def Invariant := Store → Prop

/-- An invariant map assigns an invariant to each label in a program. -/
def InvariantMap := Label → Invariant

/-- An invariant map is valid for program `p` starting at `pc` with store `σ`
    if the invariant at `pc` holds for `σ`, and for every reachable
    configuration `(pc', σ')`, the invariant at `pc'` holds for `σ'`. -/
def InvariantMap.locally_preserved (inv : InvariantMap) (p : Prog)
    (pc : Label) (σ : Store) : Prop :=
  inv pc σ →
  ∀ pc' σ', (p ⊩ Cfg.run pc σ ⟶ Cfg.run pc' σ') → inv pc' σ'

def InvariantMap.preserved (inv : InvariantMap) (p : Prog) : Prop :=
  ∀ pc σ, inv.locally_preserved p pc σ

-- ============================================================
-- § 3. Variable mapping
-- ============================================================

/-- Maps each variable in the transformed program to an expression over
    the original program's variables that should have the same value. -/
def VarMap := Var → Expr

/-- A variable mapping is consistent with two stores if for every variable,
    the transformed store's value equals the expression evaluated in the
    original store. -/
def VarMap.consistent (vm : VarMap) (σ_orig σ_trans : Store) : Prop :=
  ∀ x : Var, σ_trans x = (vm x).eval σ_orig

-- ============================================================
-- § 4. Transition correspondence
-- ============================================================

/-- A single transition correspondence: when the transformed program
    steps from `pc_t` to `pc_t'`, the original program can step from
    `pc_o` through a sequence of labels to `pc_o'` (the corresponding
    original label of `pc_t'`). The labels are the successive PCs
    visited: the first is a successor of `pc_o`, each subsequent label
    is a successor of the previous, and the last equals `pc_o'`. -/
structure TransCorr where
  /-- Labels of original PCs visited (successors of pc_orig, ending at pc_orig') -/
  origLabels   : List Label
  /-- Variable map at the source -/
  vm           : VarMap
  /-- Variable map at the target -/
  vm_next      : VarMap

-- ============================================================
-- § 5. Certificate
-- ============================================================

/-- Per-instruction certificate entry for a non-halt instruction
    in the transformed program. -/
structure InstrCert where
  /-- Corresponding label in original program -/
  pc_orig    : Label
  /-- Variable map at this instruction -/
  vm         : VarMap
  /-- For each possible successor `pc_t'` in the transformed program,
      a proof obligation that the original program can match. -/
  transitions : List TransCorr

/-- Per-instruction certificate entry for a halt instruction. -/
structure HaltCert where
  /-- Corresponding label in original program -/
  pc_orig  : Label
  /-- Variable map at this instruction -/
  vm       : VarMap

/-- The full compilation certificate. -/
structure Certificate where
  /-- Original program -/
  orig        : Prog
  /-- Transformed program -/
  trans       : Prog
  /-- Invariants for the original program -/
  inv_orig    : InvariantMap
  /-- Invariants for the transformed program -/
  inv_trans   : InvariantMap
  /-- Observable variables (checked at halt for equivalence) -/
  observable  : List Var
  /-- Certificate entry for each label in the transformed program -/
  instrCerts  : Label → InstrCert
  /-- Certificate entry for halt instructions in the transformed program -/
  haltCerts   : Label → HaltCert

-- ============================================================
-- § 6. Certificate checking conditions
-- ============================================================

/-- Condition 2: Invariants are preserved in both programs. -/
def check_invariants_preserved (cert : Certificate) : Prop :=
  cert.inv_orig.preserved cert.orig ∧
  cert.inv_trans.preserved cert.trans

/-- Condition 3b: Variable map consistency is maintained across transitions.
    When the transformed program steps from `pc_t` to `pc_t'`,
    if the variable maps are consistent before the step,
    they remain consistent after. -/
def check_transition_varmap
    (p_orig p_trans : Prog)
    (inv_orig : InvariantMap) (inv_trans : InvariantMap)
    (pc_t pc_t' : Label) (pc_o pc_o' : Label) (tc : TransCorr)
    : Prop :=
  ∀ σ_t σ_t' σ_o,
    inv_trans pc_t σ_t →
    inv_orig pc_o σ_o →
    tc.vm.consistent σ_o σ_t →
    (p_trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t') →
    ∃ σ_o',
      (p_orig ⊩ Cfg.run pc_o σ_o ⟶* Cfg.run pc_o' σ_o') ∧
      tc.vm_next.consistent σ_o' σ_t'

/-- Condition 3: For each instruction in the transformed program,
    every transition has a corresponding sequence of transitions
    in the original program. -/
def check_all_transitions (cert : Certificate) : Prop :=
  ∀ pc_t : Label,
    ∀ σ_t σ_t' : Store,
    ∀ pc_t' : Label,
      (cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t') →
      let ic := cert.instrCerts pc_t
      let ic' := cert.instrCerts pc_t'
      -- The successor's certificate must agree on the original label
      ∃ tc ∈ ic.transitions,
        tc.vm = ic.vm ∧
        tc.vm_next = ic'.vm ∧
        check_transition_varmap cert.orig cert.trans
          cert.inv_orig cert.inv_trans pc_t pc_t' ic.pc_orig ic'.pc_orig tc

/-- Condition 4a: Each halt in the transformed program corresponds to
    a halt in the original program. Uses `instrCerts` (not `haltCerts`)
    so that the simulation relation, which tracks `instrCerts`, can
    directly conclude the original also halts. -/
def check_halt_correspondence (cert : Certificate) : Prop :=
  ∀ pc_t : Label,
    cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t
    cert.orig[ic.pc_orig]? = some .halt

/-- Condition 4b: Observable variables have the same values at halt.
    Uses `instrCerts` for consistency with the simulation relation. -/
def check_halt_observable (cert : Certificate) : Prop :=
  ∀ pc_t : Label,
  ∀ σ_t σ_o : Store,
    cert.trans[pc_t]? = some .halt →
    let ic := cert.instrCerts pc_t
    ic.vm.consistent σ_o σ_t →
    ∀ v ∈ cert.observable, σ_t v = σ_o v

/-- Condition 1 (start): The start instructions correspond. -/
def check_start_correspondence (cert : Certificate) : Prop :=
  (cert.instrCerts 0).pc_orig = 0 ∧
  -- Initial variable map is identity (programs start with same store)
  ∀ σ : Store, (cert.instrCerts 0).vm.consistent σ σ

/-- Condition for invariants to hold at start. -/
def check_invariants_at_start (cert : Certificate) : Prop :=
  (∀ σ, cert.inv_trans 0 σ) ∧ (∀ σ, cert.inv_orig 0 σ)

-- ============================================================
-- § 7. Non-termination correspondence (Condition 5)
-- ============================================================

/-- An infinite execution is a function from Nat to configurations
    such that each step is valid. -/
def IsInfiniteExec (p : Prog) (f : Nat → Cfg) : Prop :=
  (∃ σ₀, f 0 = Cfg.run 0 σ₀) ∧
  ∀ n, p ⊩ f n ⟶ f (n + 1)

/-- A well-founded measure for proving non-termination correspondence.
    At each label in the transformed program, a measure on the original
    program's corresponding state. When the transformed program takes
    a step with 0 original transitions, the measure must decrease.
    This ensures we cannot have infinitely many transformed steps
    with 0 original steps — eventually the original must also progress. -/
def TransMeasure := Label → Store → Nat

/-- Condition 5: Zero-step transitions decrease a well-founded measure.
    This ensures that if the transformed program diverges, the original
    also diverges: any infinite transformed execution forces infinitely
    many original steps. -/
def check_nontermination (cert : Certificate) (μ : TransMeasure) : Prop :=
  ∀ (pc_t pc_t' : Label) (σ_t σ_t' σ_o : Store),
    cert.inv_trans pc_t σ_t →
    cert.inv_orig (cert.instrCerts pc_t).pc_orig σ_o →
    (cert.instrCerts pc_t).vm.consistent σ_o σ_t →
    (∃ c', (cert.trans ⊩ Cfg.run pc_t σ_t ⟶ c') ∧ c' = Cfg.run pc_t' σ_t') →
    -- If the original takes 0 steps (pc_orig doesn't change)
    (cert.instrCerts pc_t).pc_orig = (cert.instrCerts pc_t').pc_orig →
    -- Then the measure strictly decreases
    μ pc_t' σ_t' < μ pc_t σ_t

-- ============================================================
-- § 8. Complete certificate validity
-- ============================================================

/-- A certificate is valid if all checking conditions hold. -/
structure CertificateValid (cert : Certificate) (μ : TransMeasure) : Prop where
  start_corr      : check_start_correspondence cert
  start_inv       : check_invariants_at_start cert
  inv_preserved   : check_invariants_preserved cert
  transitions     : check_all_transitions cert
  halt_corr       : check_halt_correspondence cert
  halt_obs        : check_halt_observable cert
  nonterm         : check_nontermination cert μ

-- ============================================================
-- § 9. Soundness: simulation relation
-- ============================================================

/-- The simulation relation: transformed config at `(pc_t, σ_t)` is
    related to original config at `(pc_o, σ_o)` when the variable map
    is consistent and invariants hold. -/
def SimRel (cert : Certificate) (pc_t : Label) (σ_t : Store)
    (pc_o : Label) (σ_o : Store) : Prop :=
  let ic := cert.instrCerts pc_t
  ic.pc_orig = pc_o ∧
  ic.vm.consistent σ_o σ_t ∧
  cert.inv_trans pc_t σ_t ∧
  cert.inv_orig pc_o σ_o

/-- Invariant preservation across multi-step execution. -/
theorem inv_preserved_steps {inv : InvariantMap} {p : Prog}
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
    | const h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.const h)) _ _ hc'
    | copy h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.copy h)) _ _ hc'
    | binop h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.binop h)) _ _ hc'
    | goto h => exact ih _ _ rfl (hpres _ _ hinv _ _ (.goto h)) _ _ hc'
    | iftrue h hne => exact ih _ _ rfl (hpres _ _ hinv _ _ (.iftrue h hne)) _ _ hc'
    | iffall h heq => exact ih _ _ rfl (hpres _ _ hinv _ _ (.iffall h heq)) _ _ hc'

/-- Single-step simulation: a transformed step is matched by original steps,
    preserving the simulation relation. -/
theorem step_sim {cert : Certificate} {μ : TransMeasure}
    (hvalid : CertificateValid cert μ)
    {pc_t : Label} {σ_t σ_t' : Store} {pc_o : Label} {σ_o : Store} {pc_t' : Label}
    (hsim : SimRel cert pc_t σ_t pc_o σ_o)
    (hstep : cert.trans ⊩ Cfg.run pc_t σ_t ⟶ Cfg.run pc_t' σ_t') :
    ∃ pc_o' σ_o',
      (cert.orig ⊩ Cfg.run pc_o σ_o ⟶* Cfg.run pc_o' σ_o') ∧
      SimRel cert pc_t' σ_t' pc_o' σ_o' := by
  obtain ⟨hpc_orig, hvm_cons, hinv_t, hinv_o⟩ := hsim
  -- From check_all_transitions, get matching transition
  obtain ⟨tc, _, hvm1, hvm2, htrans⟩ :=
    hvalid.transitions pc_t σ_t σ_t' pc_t' hstep
  -- Variable map consistency from hsim + tc agreement
  have hvm_tc : tc.vm.consistent σ_o σ_t := hvm1 ▸ hvm_cons
  -- Unify pc_o with ic.pc_orig
  subst hpc_orig
  -- Transition varmap gives original steps
  obtain ⟨σ_o', horig_steps, hvm_next⟩ :=
    htrans σ_t σ_t' σ_o hinv_t hinv_o hvm_tc hstep
  -- Build the original steps from pc_o
  refine ⟨(cert.instrCerts pc_t').pc_orig, σ_o', horig_steps, ?_⟩
  -- Establish SimRel at new config
  exact ⟨rfl,
         hvm2 ▸ hvm_next,
         hvalid.inv_preserved.2 pc_t σ_t hinv_t pc_t' σ_t' hstep,
         inv_preserved_steps hvalid.inv_preserved.1 horig_steps hinv_o⟩

/-- Soundness for halting behaviors: if the certificate is valid and
    the transformed program halts, the original program also halts
    with the same observable values. -/
theorem soundness_halt
    (cert : Certificate) (μ : TransMeasure)
    (hvalid : CertificateValid cert μ)
    (σ₀ σ_t' : Store)
    (hexec : haltsWithResult cert.trans 0 σ₀ σ_t') :
    ∃ σ_o', haltsWithResult cert.orig 0 σ₀ σ_o' ∧
      ∀ v ∈ cert.observable, σ_t' v = σ_o' v := by
  -- Establish initial simulation relation
  have hsim₀ : SimRel cert 0 σ₀ 0 σ₀ :=
    ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀,
     hvalid.start_inv.1 σ₀, hvalid.start_inv.2 σ₀⟩
  -- Main simulation: induction on the transformed execution trace
  suffices ∀ c c', Steps cert.trans c c' → c' = Cfg.halt σ_t' →
      ∀ pc_t σ_t pc_o σ_o, c = Cfg.run pc_t σ_t →
        SimRel cert pc_t σ_t pc_o σ_o →
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
      obtain ⟨hpc_orig, hvm_cons, _, _⟩ := hsim
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
               hvalid.halt_obs pc_t σ_t σ_o h hvm_cons⟩
      | step s _ => exact absurd s Step.no_step_from_halt
    | const h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.const h)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | copy h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.copy h)
      obtain ⟨σ_o'', hfinal, hobs⟩ := ih hc' _ _ pc_o' σ_o' rfl hsim'
      exact ⟨σ_o'', Steps.trans horig hfinal, hobs⟩
    | binop h =>
      obtain ⟨pc_o', σ_o', horig, hsim'⟩ := step_sim hvalid hsim (.binop h)
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
    (cert : Certificate) (μ : TransMeasure)
    (hvalid : CertificateValid cert μ)
    (f : Nat → Cfg) (σ₀ : Store)
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
      (∀ pc_t σ_t, f n = Cfg.run pc_t σ_t → μ pc_t σ_t ≤ m) →
      (∀ pc_t σ_t, f n = Cfg.run pc_t σ_t → SimRel cert pc_t σ_t pc_o σ_o) →
      StepsN cert.orig (Cfg.run 0 σ₀) (Cfg.run pc_o σ_o) total →
      ∃ (n' : Nat) (pc_o' : Label) (σ_o' : Store) (total' : Nat),
        (∀ pc_t σ_t, f n' = Cfg.run pc_t σ_t → SimRel cert pc_t σ_t pc_o' σ_o') ∧
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
          hsim.2.2.1 (hsim.1 ▸ hsim.2.2.2) hsim.2.1 ⟨_, hstep, rfl⟩ hpc_eq
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
          hsim.2.2.1 (hsim.1 ▸ hsim.2.2.2) hsim.2.1 ⟨_, hstep, rfl⟩ hpc_eq
        have hmu_n := hmu pc_t σ_t hfn
        exact ih (n + 1) pc_o σ_o total
          (fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; omega)
          (fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; exact hsim')
          hsteps
      | succ k' =>
        exact ⟨n + 1, pc_o', σ_o', total + (k' + 1),
          fun pc σ hf => by rw [hfn1] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; exact hsim',
          StepsN_trans hsteps hk, by omega⟩
  -- For any N, find enough original steps via stronger induction carrying SimRel
  suffices ∀ N, ∃ (n : Nat) (pc_o : Label) (σ_o : Store) (total : Nat),
      (∀ pc_t σ_t, f n = Cfg.run pc_t σ_t → SimRel cert pc_t σ_t pc_o σ_o) ∧
      StepsN cert.orig (Cfg.run 0 σ₀) (Cfg.run pc_o σ_o) total ∧ total ≥ N by
    intro N
    obtain ⟨_, _, _, total, _, hsteps, hge⟩ := this N
    exact StepsN_intermediate_run hsteps hge
  intro N; induction N with
  | zero =>
    refine ⟨0, 0, σ₀, 0, ?_, rfl, Nat.zero_le _⟩
    intro pc_t σ_t hfn; rw [hf0] at hfn; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hfn
    exact ⟨hvalid.start_corr.1, hvalid.start_corr.2 σ₀,
           hvalid.start_inv.1 σ₀, hvalid.start_inv.2 σ₀⟩
  | succ N ih =>
    obtain ⟨n, pc_o, σ_o, total, hsim_fn, hsteps, hge⟩ := ih
    obtain ⟨pc_t, σ_t, hfn⟩ := hf_run n
    obtain ⟨n', pc_o', σ_o', total', hsim', hsteps', hge'⟩ :=
      advance (μ pc_t σ_t) n pc_o σ_o total
        (fun pc σ hf => by rw [hfn] at hf; obtain ⟨rfl, rfl⟩ := Cfg.run.inj hf; omega)
        hsim_fn hsteps
    exact ⟨n', pc_o', σ_o', total', hsim', hsteps', by omega⟩

-- ============================================================
-- § 10. Main soundness theorem
-- ============================================================

/-- A behavior is either halting (with a final store) or diverging. -/
inductive Behavior where
  | halts    : Store → Behavior
  | diverges : Behavior

/-- Extract behavior of a program from label 0 with initial store σ₀. -/
def program_behavior (p : Prog) (σ₀ : Store) (b : Behavior) : Prop :=
  match b with
  | .halts σ'  => haltsWithResult p 0 σ₀ σ'
  | .diverges  => ∃ f : Nat → Cfg, IsInfiniteExec p f ∧ f 0 = Cfg.run 0 σ₀

/-- **Main Theorem**: If the certificate is valid, then for every initial
    store, every behavior of the transformed program has a corresponding
    behavior in the original program (with observable equivalence at halt). -/
theorem credible_compilation_soundness
    (cert : Certificate) (μ : TransMeasure)
    (hvalid : CertificateValid cert μ)
    (σ₀ : Store) (b : Behavior)
    (htrans : program_behavior cert.trans σ₀ b) :
    ∃ b', program_behavior cert.orig σ₀ b' ∧
      match b, b' with
      | .halts σ_t, .halts σ_o =>
          ∀ v ∈ cert.observable, σ_t v = σ_o v
      | .diverges, .diverges => True
      | _, _ => True := by
  cases b with
  | halts σ_t' =>
    obtain ⟨σ_o', ho, hobs⟩ := soundness_halt cert μ hvalid σ₀ σ_t' htrans
    exact ⟨.halts σ_o', ho, hobs⟩
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    obtain ⟨g, hg, hg0⟩ := soundness_diverge cert μ hvalid f σ₀ hinf hf0
    exact ⟨.diverges, ⟨g, hg, hg0⟩, trivial⟩
