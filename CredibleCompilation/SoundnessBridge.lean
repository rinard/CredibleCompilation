import CredibleCompilation.DecidableChecker
import CredibleCompilation.CertExamples
import Mathlib.Tactic

/-!
# Soundness Bridge: Decidable Checker → Prop-based Checker

We prove that if the executable `checkCertificate` returns `true`,
then `CertificateValid` holds for the corresponding `Certificate`.

## Structure

1. **Translation**: `toCertificate` lifts a `DCertificate` to a `Certificate`
2. **Per-condition soundness**: each Bool check implies its Prop counterpart
3. **Main theorem**: `soundness_bridge`

## On the converse (completeness)

An iff is **not possible** in general:
- The Prop-based `Certificate` uses `InvariantMap := Label → Store → Prop`
  (arbitrary predicates on stores)
- The decidable `DCertificate` uses `DInv := List (Var × Val)`
  (only `var = constant` atoms)

Any `CertificateValid` proof using invariants beyond `var = val`
(e.g., relational invariants like `x < y`) cannot be captured by `checkCertificate`.
The decidable checker is **sound but incomplete**.
-/

set_option maxRecDepth 2048

/-- Helper: BEq on TAC derived instance implies equality.
    TAC derives both BEq and DecidableEq; they agree but are separate instances. -/
private theorem tac_beq_eq {a b : TAC} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> simp_all [BEq.beq, instBEqTAC.beq]

/-- Helper: extract orig[pc]? = some instr from the BEq check in checkOrigPath. -/
private theorem orig_eq_of_beq {orig : Prog} {pc : Label} {instr : TAC}
    (h : (orig[pc]? == some instr) = true) : orig[pc]? = some instr := by
  match horig : orig[pc]? with
  | none =>
    rw [horig] at h; exact nomatch h
  | some i =>
    rw [horig] at h
    exact congrArg some (tac_beq_eq h)

-- ============================================================
-- § 1. Lifting DInv to Prop
-- ============================================================

/-- A `DInv` as a proposition: every atom `(x, v)` asserts `σ x = v`. -/
def DInv.toProp (inv : DInv) : Invariant :=
  fun σ => ∀ p ∈ inv, σ p.1 = p.2

theorem DInv.toProp_nil : DInv.toProp [] = fun _ => True := by
  funext σ; simp [DInv.toProp]

theorem DInv.toProp_cons (x : Var) (v : Val) (rest : DInv) :
    DInv.toProp ((x, v) :: rest) = fun σ => σ x = v ∧ DInv.toProp rest σ := by
  funext σ; simp [DInv.toProp]

-- ============================================================
-- § 2. Translation: DCertificate → Certificate
-- ============================================================

/-- Lift a decidable certificate to a Prop-based certificate.
    Uses identity variable maps throughout. -/
def toCertificate (dc : DCertificate) : Certificate :=
  { orig       := dc.orig
    trans      := dc.trans
    inv_orig   := fun l => (dc.inv_orig.getD l ([] : DInv)).toProp
    inv_trans  := fun l => (dc.inv_trans.getD l ([] : DInv)).toProp
    observable := dc.observable
    instrCerts := fun l =>
      let dic := dc.instrCerts.getD l default
      { pc_orig    := dic.pc_orig
        vm         := idVarMap
        transitions := dic.transitions.map fun dtc =>
          { origLabels   := dtc.origLabels
            vm           := idVarMap
            vm_next      := idVarMap }
      }
    haltCerts := fun l =>
      let dhc := dc.haltCerts.getD l default
      { pc_orig := dhc.pc_orig
        vm      := idVarMap }
  }

/-- Lift the measure: ignores the store (depends only on label). -/
def toMeasure (dc : DCertificate) : TransMeasure :=
  fun l _ => dc.measure.getD l 0

-- ============================================================
-- § 3. lookupVar soundness
-- ============================================================

theorem lookupVar_sound (inv : DInv) (v : Var) (n : Val) (σ : Store)
    (hlook : lookupVar inv v = some n)
    (hinv : DInv.toProp inv σ) :
    σ v = n := by
  induction inv with
  | nil => simp [lookupVar] at hlook
  | cons p rest ih =>
    obtain ⟨x, val⟩ := p
    rw [DInv.toProp_cons] at hinv
    simp only [lookupVar, List.find?, Option.map] at hlook
    by_cases hxv : x == v
    · simp [hxv] at hlook
      rw [← hlook, ← beq_iff_eq.mp hxv]
      exact hinv.1
    · simp [hxv] at hlook
      exact ih hlook hinv.2

-- ============================================================
-- § 4. Expr.simplify soundness
-- ============================================================

/-- Simplification preserves semantics: evaluating `e.simplify inv` in `σ`
    gives the same result as evaluating `e` in `σ`, provided `σ` satisfies `inv`. -/
theorem Expr.simplify_sound (inv : DInv) (e : Expr) (σ : Store)
    (hinv : DInv.toProp inv σ) :
    (e.simplify inv).eval σ = e.eval σ := by
  induction e with
  | lit n => simp [Expr.simplify, Expr.eval]
  | var v =>
    simp [Expr.simplify]
    split
    · case h_1 n hlook =>
      simp [Expr.eval]
      exact (lookupVar_sound inv v n σ hlook hinv).symm
    · case h_2 =>
      simp [Expr.eval]
  | bin op a b iha ihb =>
    -- iha : (a.simplify inv).eval σ = a.eval σ
    -- ihb : (b.simplify inv).eval σ = b.eval σ
    simp only [Expr.simplify, Expr.eval]
    split
    · case h_1 na nb heqa heqb =>
      simp only [Expr.eval]
      rw [heqa] at iha; rw [heqb] at ihb
      simp only [Expr.eval] at iha ihb
      rw [iha, ihb]
    · case h_2 =>
      simp only [Expr.eval]
      rw [iha, ihb]

-- ============================================================
-- § 5. Easy soundness lemmas
-- ============================================================

/-- **Condition 1**: checkStart → check_start_correspondence -/
theorem checkStart_sound (dc : DCertificate)
    (h : checkStart dc = true) :
    check_start_correspondence (toCertificate dc) := by
  simp [checkStart] at h
  split at h
  · rename_i ic hic
    have hbound := bound_of_getElem? hic
    have hget : dc.instrCerts[0] = ic := (Array.getElem?_eq_some_iff.mp hic).2
    have hpc : ic.pc_orig = 0 := beq_iff_eq.mp h
    constructor
    · -- (instrCerts 0).pc_orig = 0
      simp only [toCertificate, Array.getD, dif_pos hbound]
      rw [show dc.instrCerts.getInternal 0 hbound = ic from hget]
      exact hpc
    · -- ∀ σ, vm.consistent σ σ
      intro σ
      simp only [toCertificate, Array.getD, dif_pos hbound]
      exact fun _ => rfl
  · contradiction

/-- **Condition 2a**: checkInvariantsAtStart → check_invariants_at_start -/
theorem checkInvariantsAtStart_sound (dc : DCertificate)
    (h : checkInvariantsAtStart dc = true) :
    check_invariants_at_start (toCertificate dc) := by
  unfold checkInvariantsAtStart at h
  have h1 : (dc.inv_orig.getD 0 ([] : DInv)).isEmpty = true := by
    revert h; cases (dc.inv_orig.getD 0 ([] : DInv)).isEmpty <;> simp
  have h2 : (dc.inv_trans.getD 0 ([] : DInv)).isEmpty = true := by
    revert h; cases (dc.inv_trans.getD 0 ([] : DInv)).isEmpty <;> simp
  have horig_nil : dc.inv_orig.getD 0 ([] : DInv) = [] := by
    revert h1; cases dc.inv_orig.getD 0 ([] : DInv) <;> simp [List.isEmpty]
  have htrans_nil : dc.inv_trans.getD 0 ([] : DInv) = [] := by
    revert h2; cases dc.inv_trans.getD 0 ([] : DInv) <;> simp [List.isEmpty]
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · change (dc.inv_trans.getD 0 ([] : DInv)).toProp σ
    rw [htrans_nil]; simp [DInv.toProp]
  · change (dc.inv_orig.getD 0 ([] : DInv)).toProp σ
    rw [horig_nil]; simp [DInv.toProp]

/-- **Condition 4a**: checkHaltCorrespondence → check_halt_correspondence -/
theorem checkHaltCorrespondence_sound (dc : DCertificate)
    (h : checkHaltCorrespondence dc = true) :
    check_halt_correspondence (toCertificate dc) := by
  intro pc_t
  dsimp only [toCertificate]
  intro hhalt
  have hbound : pc_t < dc.trans.size := bound_of_getElem? hhalt
  unfold checkHaltCorrespondence at h
  rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  simp only [hhalt] at hpc
  revert hpc
  generalize dc.orig[(dc.instrCerts.getD pc_t default).pc_orig]? = opt
  cases opt with
  | none => simp
  | some instr => cases instr <;> simp

/-- **Condition 4b**: checkHaltObservable → check_halt_observable -/
theorem checkHaltObservable_sound (dc : DCertificate)
    (_h : checkHaltObservable dc = true) :
    check_halt_observable (toCertificate dc) := by
  intro pc_t σ_t σ_o _hhalt
  -- The goal has a let binding; dsimp reduces it and unfolds idVarMap
  dsimp only [toCertificate, idVarMap, VarMap.consistent, Expr.eval]
  intro hcons v _hv
  exact hcons v

-- ============================================================
-- § 6. Invariant preservation soundness
-- ============================================================

/-- Key lemma: checkInvAtom soundness.
    If checkInvAtom succeeds, then for any store satisfying inv_pre,
    after executing `instr`, the atom holds in the post-store. -/
theorem checkInvAtom_sound (inv_pre : DInv) (instr : TAC) (atom : Var × Val)
    (σ σ' : Store) (pc pc' : Label) (prog : Prog)
    (hcheck : checkInvAtom inv_pre instr atom = true)
    (hinv : DInv.toProp inv_pre σ)
    (hstep : Step prog (Cfg.run pc σ) (Cfg.run pc' σ'))
    (hinstr : prog[pc]? = some instr) :
    σ' atom.1 = atom.2 := by
  obtain ⟨x, v⟩ := atom; simp only
  -- Helper: when the instruction doesn't modify x, σ' x = σ x
  -- and lookupVar gives us σ x = v
  have unmodified_case (heqσ : σ' x = σ x)
      (hfall : lookupVar inv_pre x = some v) : σ' x = v := by
    rw [heqσ]; exact lookupVar_sound inv_pre x v σ hfall hinv
  -- Helper: extract instruction identity from step + hinstr
  have instr_eq {i : TAC} (h : prog[pc]? = some i) : instr = i :=
    Option.some.inj (hinstr.symm.trans h)
  cases hstep with
  | const h =>
    rename_i y n
    have hi := instr_eq h; subst hi; simp only [checkInvAtom] at hcheck
    by_cases hyx : y == x
    · -- y = x: assigned
      simp [hyx] at hcheck; rw [beq_iff_eq.mp hyx, Store.update_self]; exact hcheck
    · -- y ≠ x: not assigned
      simp [hyx] at hcheck
      have hne : x ≠ y := fun h => hyx (beq_iff_eq.mpr h.symm)
      exact unmodified_case (Store.update_other σ y x n hne) hcheck
  | copy h =>
    rename_i y z
    have hi := instr_eq h; subst hi; simp only [checkInvAtom] at hcheck
    by_cases hyx : y == x
    · simp [hyx] at hcheck
      rw [beq_iff_eq.mp hyx, Store.update_self]
      revert hcheck
      cases hlook : lookupVar inv_pre z with
      | none => simp
      | some val =>
        simp; intro hcheck; subst hcheck
        exact lookupVar_sound _ _ _ _ hlook hinv
    · simp [hyx] at hcheck
      have hne : x ≠ y := fun h => hyx (beq_iff_eq.mpr h.symm)
      exact unmodified_case (Store.update_other σ y x _ hne) hcheck
  | binop h =>
    rename_i y op₁ a b
    have hi := instr_eq h; subst hi; simp only [checkInvAtom] at hcheck
    by_cases hyx : y == x
    · simp [hyx] at hcheck
      rw [beq_iff_eq.mp hyx, Store.update_self]
      revert hcheck
      cases hla : lookupVar inv_pre a with
      | none => simp
      | some va =>
        cases hlb : lookupVar inv_pre b with
        | none => simp
        | some vb =>
          simp; intro hcheck
          have ha := lookupVar_sound _ _ _ _ hla hinv
          have hb := lookupVar_sound _ _ _ _ hlb hinv
          rw [ha, hb]; exact hcheck
    · simp [hyx] at hcheck
      have hne : x ≠ y := fun h => hyx (beq_iff_eq.mpr h.symm)
      exact unmodified_case (Store.update_other σ y x _ hne) hcheck
  | goto h =>
    have hi := instr_eq h; subst hi; simp only [checkInvAtom] at hcheck
    simp at hcheck; exact lookupVar_sound inv_pre x v σ hcheck hinv
  | iftrue h _ =>
    have hi := instr_eq h; subst hi; simp only [checkInvAtom] at hcheck
    simp at hcheck; exact lookupVar_sound inv_pre x v σ hcheck hinv
  | iffall h _ =>
    have hi := instr_eq h; subst hi; simp only [checkInvAtom] at hcheck
    simp at hcheck; exact lookupVar_sound inv_pre x v σ hcheck hinv

/-- Extract instruction from a step to a run configuration. -/
theorem step_run_instr {p : Prog} {pc pc' : Label} {σ σ' : Store}
    (hstep : Step p (Cfg.run pc σ) (Cfg.run pc' σ')) :
    ∃ instr, p[pc]? = some instr := by
  cases hstep with
  | const h => exact ⟨_, h⟩
  | copy h => exact ⟨_, h⟩
  | binop h => exact ⟨_, h⟩
  | goto h => exact ⟨_, h⟩
  | iftrue h _ => exact ⟨_, h⟩
  | iffall h _ => exact ⟨_, h⟩

/-- A step target is always in the successors list. -/
theorem step_successor {p : Prog} {pc pc' : Label} {σ σ' : Store}
    (hstep : Step p (Cfg.run pc σ) (Cfg.run pc' σ'))
    {instr : TAC} (hinstr : p[pc]? = some instr) :
    pc' ∈ successors instr pc := by
  have instr_eq {i : TAC} (h : p[pc]? = some i) : instr = i :=
    Option.some.inj (hinstr.symm.trans h)
  cases hstep with
  | const h => have := instr_eq h; subst this; simp [successors]
  | copy h => have := instr_eq h; subst this; simp [successors]
  | binop h => have := instr_eq h; subst this; simp [successors]
  | goto h => have := instr_eq h; subst this; simp [successors]
  | iftrue h _ => have := instr_eq h; subst this; simp [successors]
  | iffall h _ => have := instr_eq h; subst this; simp [successors]

private theorem and_true_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simp [Bool.and_eq_true] at h; exact h

/-- Helper: checkProg soundness for one program/invariant pair. -/
private theorem checkProg_sound (prog : Prog) (inv : Array DInv)
    (h : (List.range prog.size).all (fun pc =>
      match prog[pc]? with
      | some instr =>
        (successors instr pc).all fun pc' =>
          (inv.getD pc' ([] : DInv)).all (checkInvAtom (inv.getD pc ([] : DInv)) instr)
      | none => true) = true) :
    InvariantMap.preserved (fun l => (inv.getD l ([] : DInv)).toProp) prog := by
  intro pc σ hinvpc pc' σ' hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hbound := bound_of_getElem? hinstr
  rw [List.all_eq_true] at h
  have hpc := h pc (List.mem_range.mpr hbound)
  simp only [hinstr] at hpc
  rw [List.all_eq_true] at hpc
  have hsucc := step_successor hstep hinstr
  have hpc' := hpc pc' hsucc
  rw [List.all_eq_true] at hpc'
  -- hpc' : ∀ atom ∈ (inv.getD pc' []), checkInvAtom (inv.getD pc []) instr atom = true
  intro atom hatom
  exact checkInvAtom_sound (inv.getD pc ([] : DInv)) instr atom σ σ' pc pc' prog
    (hpc' atom hatom) hinvpc hstep hinstr

/-- **Condition 2b**: checkInvariantsPreserved → check_invariants_preserved -/
theorem checkInvariantsPreserved_sound (dc : DCertificate)
    (h : checkInvariantsPreserved dc = true) :
    check_invariants_preserved (toCertificate dc) := by
  unfold checkInvariantsPreserved at h
  have ⟨h1, h2⟩ := and_true_split h
  exact ⟨checkProg_sound dc.orig dc.inv_orig h1,
         checkProg_sound dc.trans dc.inv_trans h2⟩

-- ============================================================
-- § 7. Transition correspondence soundness
-- ============================================================

/-- find? on filtered list equals find? on original when predicates are compatible. -/
private theorem find_filter_ne (ss : SymStore) (x y : Var) (hne : y ≠ x) :
    (ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) =
    ss.find? (fun p => p.1 == y) := by
  induction ss with
  | nil => rfl
  | cons p rest ih =>
    by_cases hpx : p.1 == x <;> by_cases hpy : p.1 == y
    · -- p.1 = x and p.1 = y, contradiction since y ≠ x
      exfalso; exact hne (beq_iff_eq.mp hpy ▸ beq_iff_eq.mp hpx)
    · simp [List.filter, List.find?, hpx, hpy, ih]
    · simp [List.filter, List.find?, hpx, hpy]
    · simp [List.filter, List.find?, hpx, hpy, ih]

theorem ssGet_ssSet_same (ss : SymStore) (x : Var) (e : Expr) :
    ssGet (ssSet ss x e) x = e := by
  simp [ssGet, ssSet]

theorem ssGet_ssSet_other (ss : SymStore) (x y : Var) (e : Expr) (hne : y ≠ x) :
    ssGet (ssSet ss x e) y = ssGet ss y := by
  unfold ssGet ssSet
  have hxy : (x == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  have step1 : ((x, e) :: ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) =
      (ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) := by
    simp [List.find?, hxy]
  rw [step1, find_filter_ne ss x y hne]

/-- Symbolic execution soundness: if the symbolic store `ss` correctly represents
    the relationship between an initial store `σ₀` and a current store `σ`,
    then after executing `instr`, the updated symbolic store correctly represents
    the relationship with the post-store `σ'`. -/
theorem execSymbolic_sound (ss : SymStore) (instr : TAC)
    (σ₀ σ σ' : Store) (pc pc' : Label) (prog : Prog)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ v)
    (hstep : Step prog (Cfg.run pc σ) (Cfg.run pc' σ'))
    (hinstr : prog[pc]? = some instr) :
    ∀ v, (ssGet (execSymbolic ss instr) v).eval σ₀ = σ' v := by
  -- Use determinism: any step from (pc, σ) must agree with hstep
  have step_det : ∀ c, Step prog (Cfg.run pc σ) c → c = Cfg.run pc' σ' :=
    fun c hc => Step.deterministic hc hstep
  intro v
  cases instr with
  | const dest val =>
    simp only [execSymbolic]
    have := step_det _ (Step.const hinstr)
    have hσ' : σ' = σ[dest ↦ val] := (Cfg.run.inj this).2.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v val hvd).symm
  | copy dest src =>
    simp only [execSymbolic]
    have := step_det _ (Step.copy hinstr)
    have hσ' : σ' = σ[dest ↦ σ src] := (Cfg.run.inj this).2.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same, hrepr]; exact (Store.update_self σ dest (σ src)).symm
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | binop dest op a b =>
    simp only [execSymbolic]
    have := step_det _ (Step.binop hinstr)
    have hσ' : σ' = σ[dest ↦ op.eval (σ a) (σ b)] := (Cfg.run.inj this).2.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, hrepr]
      exact (Store.update_self σ dest _).symm
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | goto l =>
    simp only [execSymbolic]
    have := step_det _ (Step.goto hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.symm
    rw [hσ']; exact hrepr v
  | ifgoto x l =>
    simp only [execSymbolic]
    by_cases hx : σ x ≠ 0
    · have := step_det _ (Step.iftrue hinstr hx)
      have hσ' : σ' = σ := (Cfg.run.inj this).2.symm
      rw [hσ']; exact hrepr v
    · push_neg at hx
      have := step_det _ (Step.iffall hinstr hx)
      have hσ' : σ' = σ := (Cfg.run.inj this).2.symm
      rw [hσ']; exact hrepr v
  | halt =>
    exfalso
    have := step_det _ (Step.halt hinstr)
    exact Cfg.noConfusion this

/-- Identity variable map consistency means stores are equal. -/
private theorem idVarMap_eq {σ₁ σ₂ : Store} (h : idVarMap.consistent σ₁ σ₂) :
    σ₁ = σ₂ := by
  funext x; exact (h x).symm

/-- Initial symbolic store represents identity: ssGet [] v evaluates to σ v. -/
private theorem ssGet_nil (σ : Store) (v : Var) :
    (ssGet ([] : SymStore) v).eval σ = σ v := by
  simp [ssGet, List.find?, Expr.eval]

/-- ssGet on empty store returns .var v. -/
private theorem ssGet_nil_var (v : Var) : ssGet ([] : SymStore) v = .var v := by
  simp [ssGet, List.find?]

/-- Variable names appearing in an instruction (matching collectAllVars.extract). -/
private def instrVars (instr : TAC) : List Var :=
  match instr with
  | .const x _     => [x]
  | .copy x y      => [x, y]
  | .binop x _ y z => [x, y, z]
  | .ifgoto x _    => [x]
  | _              => []

/-- Elements already in the accumulator survive foldl. -/
private theorem mem_foldl_init (xs : List TAC) (init : List Var)
    {v : Var} (hv : v ∈ init) :
    v ∈ xs.foldl (fun acc i => acc ++ instrVars i) init := by
  induction xs generalizing init with
  | nil => exact hv
  | cons _ tl ih => exact ih (init ++ instrVars _) (List.mem_append_left _ hv)

/-- Elements from any member's instrVars end up in the foldl result. -/
private theorem mem_foldl_elem (xs : List TAC) (init : List Var)
    {x : TAC} (hx : x ∈ xs) {v : Var} (hv : v ∈ instrVars x) :
    v ∈ xs.foldl (fun acc i => acc ++ instrVars i) init := by
  induction xs generalizing init with
  | nil => simp at hx
  | cons hd tl ih =>
    cases List.mem_cons.mp hx with
    | inl heq => subst heq; exact mem_foldl_init tl _ (List.mem_append_right init hv)
    | inr htl => exact ih _ htl

/-- If v ∈ instrVars of an instruction in p1, then v ∈ collectAllVars p1 p2. -/
private theorem instrVars_sub_collectAllVars_left (p1 p2 : Prog) (instr : TAC)
    (hmem : instr ∈ p1.toList) (v : Var) (hv : v ∈ instrVars instr) :
    v ∈ collectAllVars p1 p2 := by
  unfold collectAllVars
  apply List.mem_append_left
  exact mem_foldl_elem p1.toList ([] : List Var) hmem hv

/-- If v ∈ instrVars of an instruction in p2, then v ∈ collectAllVars p1 p2. -/
private theorem instrVars_sub_collectAllVars_right (p1 p2 : Prog) (instr : TAC)
    (hmem : instr ∈ p2.toList) (v : Var) (hv : v ∈ instrVars instr) :
    v ∈ collectAllVars p1 p2 := by
  unfold collectAllVars
  apply List.mem_append_right
  exact mem_foldl_elem p2.toList ([] : List Var) hmem hv

/-- Array getElem? to toList membership. -/
private theorem getElem?_mem_toList {arr : Prog} {i : Nat} {x : TAC}
    (h : arr[i]? = some x) : x ∈ arr.toList := by
  have hb := bound_of_getElem? h
  have heq := (Array.getElem?_eq_some_iff.mp h).2
  exact heq ▸ Array.getElem_mem_toList (h := hb)

/-- If v is not the dest of instr, execSymbolic preserves ssGet v. -/
private theorem execSymbolic_preserves_var (ss : SymStore) (instr : TAC) (v : Var)
    (hv : v ∉ instrVars instr) :
    ssGet (execSymbolic ss instr) v = ssGet ss v := by
  cases instr with
  | const x n =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
  | copy x y =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | binop x op y z =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | goto _ => rfl
  | ifgoto _ _ => rfl
  | halt => rfl

/-- If v is not the dest of any instruction in the program, execPath preserves ssGet v. -/
private theorem execPath_preserves_var (orig : Prog) (ss : SymStore) (pc : Label)
    (labels : List Label) (v : Var)
    (hv : ∀ (l : Label) (instr : TAC), orig[l]? = some instr → v ∉ instrVars instr) :
    ssGet (execPath orig ss pc labels) v = ssGet ss v := by
  induction labels generalizing ss pc with
  | nil => rfl
  | cons nextPC rest ih =>
    simp only [execPath]
    cases horig : orig[pc]? with
    | none => rfl
    | some instr =>
      have h1 := execSymbolic_preserves_var ss instr v (hv pc instr horig)
      have h2 := ih (execSymbolic ss instr) nextPC
      exact h2.trans h1

/-- If `isNonZeroLit e = true`, then `e = .lit n` for some `n ≠ 0`. -/
private theorem isNonZeroLit_sound {e : Expr} (h : e.isNonZeroLit = true) :
    ∃ n, e = .lit n ∧ n ≠ 0 := by
  cases e with
  | lit n =>
    refine ⟨n, rfl, ?_⟩
    intro heq; subst heq; simp [Expr.isNonZeroLit] at h
  | var => simp [Expr.isNonZeroLit] at h
  | bin => simp [Expr.isNonZeroLit] at h

/-- Generalized path execution soundness with arbitrary initial symbolic store.
    The path check includes symbolic branch-direction verification for ifgoto. -/
private theorem execPath_sound_gen (orig : Prog) (ss : SymStore) (inv : DInv)
    (σ₀ σ : Store) (pc : Label) (labels : List Label) (pc' : Label)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ v)
    (hinv : DInv.toProp inv σ₀)
    (hpath : checkOrigPath orig ss inv pc labels pc' = true) :
    ∃ σ', Steps orig (Cfg.run pc σ) (Cfg.run pc' σ') ∧
          ∀ v, (ssGet (execPath orig ss pc labels) v).eval σ₀ = σ' v := by
  induction labels generalizing pc σ ss with
  | nil =>
    simp only [checkOrigPath, beq_iff_eq] at hpath
    exact ⟨σ, hpath ▸ Steps.refl, hrepr⟩
  | cons nextPC rest ih =>
    simp only [checkOrigPath] at hpath
    -- Extract the instruction at pc
    generalize horig_opt : orig[pc]? = opt_instr at hpath
    cases opt_instr with
    | none => simp at hpath
    | some instr =>
      have ⟨hnext_eq, hpath_inner⟩ := and_true_split hpath
      -- Extract computeNextPC result
      generalize hnext_opt : computeNextPC instr pc ss inv = opt_next at hnext_eq
      cases opt_next with
      | none => simp at hnext_eq
      | some nextPC' =>
        have hpc_eq : nextPC = nextPC' := by
          have := beq_iff_eq.mp hnext_eq; exact Option.some.inj this.symm
        subst hpc_eq
        -- Construct the step + symbolic tracking
        have ⟨σ₁, hstep_orig, hrepr'⟩ : ∃ σ₁,
            Step orig (Cfg.run pc σ) (Cfg.run nextPC σ₁) ∧
            ∀ v, (ssGet (execSymbolic ss instr) v).eval σ₀ = σ₁ v := by
          cases instr with
          | const x n =>
            simp [computeNextPC] at hnext_opt
            have hpc_eq : nextPC = pc + 1 := hnext_opt.symm
            rw [hpc_eq]
            exact ⟨σ[x ↦ n], Step.const horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.const horig_opt) horig_opt⟩
          | copy x y =>
            simp [computeNextPC] at hnext_opt
            have hpc_eq : nextPC = pc + 1 := hnext_opt.symm
            rw [hpc_eq]
            exact ⟨σ[x ↦ σ y], Step.copy horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.copy horig_opt) horig_opt⟩
          | binop x op y z =>
            simp [computeNextPC] at hnext_opt
            have hpc_eq : nextPC = pc + 1 := hnext_opt.symm
            rw [hpc_eq]
            exact ⟨σ[x ↦ op.eval (σ y) (σ z)], Step.binop horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.binop horig_opt) horig_opt⟩
          | goto l =>
            simp [computeNextPC] at hnext_opt
            have hpc_eq : nextPC = l := hnext_opt.symm
            rw [hpc_eq]
            exact ⟨σ, Step.goto horig_opt,
              execSymbolic_sound ss _ σ₀ σ σ pc l orig hrepr (Step.goto horig_opt) horig_opt⟩
          | ifgoto x l =>
            have hexec_id : execSymbolic ss (.ifgoto x l) = ss := rfl
            simp only [computeNextPC] at hnext_opt
            have hsimpl := Expr.simplify_sound inv (ssGet ss x) σ₀ hinv
            by_cases hnonzero : (ssGet ss x).simplify inv |>.isNonZeroLit
            · -- True branch: nextPC = l
              simp only [hnonzero, ↓reduceIte] at hnext_opt
              have hpc_eq : nextPC = l := Option.some.inj hnext_opt.symm
              rw [hpc_eq]
              obtain ⟨n, hsv, hne⟩ := isNonZeroLit_sound hnonzero
              rw [hsv, Expr.eval] at hsimpl
              have : σ x ≠ 0 := by rw [← hrepr x, ← hsimpl]; exact hne
              exact ⟨σ, Step.iftrue horig_opt this, hexec_id ▸ hrepr⟩
            · -- Check if zero
              simp only [hnonzero, Bool.false_eq_true, ↓reduceIte] at hnext_opt
              by_cases hzero : (ssGet ss x).simplify inv == .lit 0
              · simp only [hzero, ↓reduceIte] at hnext_opt
                have hpc_eq : nextPC = pc + 1 := Option.some.inj hnext_opt.symm
                rw [hpc_eq]
                have hsv := beq_iff_eq.mp hzero
                rw [hsv, Expr.eval] at hsimpl
                have : σ x = 0 := by rw [← hrepr x, ← hsimpl]
                exact ⟨σ, Step.iffall horig_opt this, hexec_id ▸ hrepr⟩
              · simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hnext_opt
                exact absurd hnext_opt (by simp)
          | halt =>
            simp [computeNextPC] at hnext_opt
        -- Recursive step
        have hexec : execPath orig ss pc (nextPC :: rest) =
            execPath orig (execSymbolic ss instr) nextPC rest := by
          simp [execPath, horig_opt]
        obtain ⟨σ', hsteps_rest, hrepr_final⟩ :=
          ih (execSymbolic ss instr) σ₁ nextPC hrepr' hpath_inner
        exact ⟨σ', Steps.step hstep_orig hsteps_rest, hexec ▸ hrepr_final⟩

/-- Path execution soundness: specialization with empty initial symbolic store. -/
private theorem execPath_sound (orig : Prog) (inv : DInv) (σ : Store)
    (pc : Label) (labels : List Label) (pc' : Label)
    (hrepr : ∀ v, (ssGet ([] : SymStore) v).eval σ = σ v)
    (hinv : DInv.toProp inv σ)
    (hpath : checkOrigPath orig ([] : SymStore) inv pc labels pc' = true) :
    ∃ σ', Steps orig (Cfg.run pc σ) (Cfg.run pc' σ') ∧
          ∀ v, (ssGet (execPath orig ([] : SymStore) pc labels) v).eval σ = σ' v :=
  execPath_sound_gen orig ([] : SymStore) inv σ σ pc labels pc' hrepr hinv hpath

/-- BEq on Expr implies equality. -/
private theorem expr_beq_eq {e₁ e₂ : Expr} (h : (e₁ == e₂) = true) : e₁ = e₂ :=
  beq_iff_eq.mp h

/-- Soundness of check_transition_varmap from the Bool checks.
    Given: checkOrigPath and checkVarMapConsistency both pass, and stores
    satisfy invariants with identity variable maps. Then the original path
    produces steps reaching the target with the correct store. -/
private theorem transVarmap_sound (dc : DCertificate) (pc_t pc_t' : Label)
    (dic : DInstrCert) (dtc : DTransCorr) (instr : TAC)
    (pc_o' : Label)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hpath : checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : DInv))
      dic.pc_orig dtc.origLabels pc_o' = true)
    (hvm : checkVarMapConsistency (collectAllVars dc.orig dc.trans)
      dc.orig dic.pc_orig dtc.origLabels instr
      (dc.inv_orig.getD dic.pc_orig ([] : DInv))
      (dc.inv_trans.getD pc_t ([] : DInv)) = true) :
    check_transition_varmap dc.orig dc.trans
      (fun l => (dc.inv_orig.getD l ([] : DInv)).toProp)
      (fun l => (dc.inv_trans.getD l ([] : DInv)).toProp)
      pc_t pc_t' dic.pc_orig pc_o'
      { origLabels := dtc.origLabels
        vm := idVarMap
        vm_next := idVarMap } := by
  intro σ_t σ_t' σ_o hinv_t hinv_o hcons hstep
  -- Identity varmap: σ_o = σ_t
  have h_eq : σ_o = σ_t := idVarMap_eq hcons
  -- Rewrite σ_o to σ_t in the goal and invariant
  rw [h_eq] at hinv_o ⊢
  -- From checkOrigPath: the original path produces Steps with symbolic tracking
  obtain ⟨σ_o', horig_steps, horig_repr⟩ := execPath_sound dc.orig
    (dc.inv_orig.getD dic.pc_orig ([] : DInv)) σ_t
    dic.pc_orig dtc.origLabels pc_o'
    (fun v => ssGet_nil σ_t v) hinv_o hpath
  -- From execSymbolic_sound: the transformed instruction is tracked symbolically
  have htrans_repr : ∀ v, (ssGet (execSymbolic ([] : SymStore) instr) v).eval σ_t = σ_t' v :=
    execSymbolic_sound [] instr σ_t σ_t σ_t' pc_t pc_t' dc.trans
      (ssGet_nil σ_t) hstep hinstr
  -- We claim σ_o' satisfies idVarMap.consistent σ_o' σ_t'
  refine ⟨σ_o', horig_steps, ?_⟩
  intro v
  simp only [idVarMap, Expr.eval]
  -- Need: σ_t' v = σ_o' v, using the symbolic execution chain
  rw [← htrans_repr v, ← horig_repr v]
  -- From checkVarMapConsistency: simplified expressions are BEq for vars
  simp only [checkVarMapConsistency, List.all_eq_true, beq_iff_eq] at hvm
  by_cases hv : v ∈ collectAllVars dc.orig dc.trans
  · -- v ∈ vars: use the simplification chain
    have hvm_v := hvm v hv
    have h_orig_simp := Expr.simplify_sound
      (dc.inv_orig.getD dic.pc_orig ([] : DInv))
      (ssGet (execPath dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels) v) σ_t hinv_o
    have h_trans_simp := Expr.simplify_sound
      (dc.inv_trans.getD pc_t ([] : DInv))
      (ssGet (execSymbolic ([] : SymStore) instr) v) σ_t hinv_t
    rw [← h_orig_simp, ← h_trans_simp, hvm_v]
  · -- v not in any instruction → symbolic stores didn't modify v
    have hv_not_in_orig : ∀ (l : Label) (instr' : TAC),
        dc.orig[l]? = some instr' → v ∉ instrVars instr' := by
      intro l instr' horig hmem
      exact hv (instrVars_sub_collectAllVars_left dc.orig dc.trans instr'
        (getElem?_mem_toList horig) v hmem)
    have hv_not_in_trans : v ∉ instrVars instr := by
      intro hmem
      exact hv (instrVars_sub_collectAllVars_right dc.orig dc.trans instr
        (getElem?_mem_toList hinstr) v hmem)
    rw [execPath_preserves_var dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels v hv_not_in_orig,
        execSymbolic_preserves_var ([] : SymStore) instr v hv_not_in_trans]

/-- Extract Bool information from checkAllTransitions for a specific step. -/
private theorem extractTransCheck (dc : DCertificate)
    (h : checkAllTransitions dc = true)
    (pc_t pc_t' : Label) (instr : TAC)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ successors instr pc_t) :
    ∃ dic, dc.instrCerts[pc_t]? = some dic ∧
    ∃ dtc ∈ dic.transitions,
      checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : DInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig = true ∧
      checkVarMapConsistency (collectAllVars dc.orig dc.trans)
        dc.orig dic.pc_orig dtc.origLabels instr
        (dc.inv_orig.getD dic.pc_orig ([] : DInv))
        (dc.inv_trans.getD pc_t ([] : DInv)) = true := by
  simp only [checkAllTransitions] at h
  rw [List.all_eq_true] at h
  have h_pc := h pc_t (List.mem_range.mpr (bound_of_getElem? hinstr))
  simp only [hinstr] at h_pc
  have h_inner : (match dc.instrCerts[pc_t]? with
    | some ic =>
      (successors instr pc_t).all fun pc_t'' =>
        let ic' := dc.instrCerts.getD pc_t'' default
        ic.transitions.any fun tc =>
          checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD ic.pc_orig ([] : DInv))
            ic.pc_orig tc.origLabels ic'.pc_orig &&
          checkVarMapConsistency (collectAllVars dc.orig dc.trans)
            dc.orig ic.pc_orig tc.origLabels instr
            (dc.inv_orig.getD ic.pc_orig ([] : DInv))
            (dc.inv_trans.getD pc_t ([] : DInv))
    | none => false) = true := by
    revert h_pc; cases instr with
    | halt => exact absurd rfl hne
    | _ => exact id
  -- Now extract from the inner match on instrCerts[pc_t]?
  cases hic_opt : dc.instrCerts[pc_t]? with
  | none => simp [hic_opt] at h_inner
  | some dic =>
    simp only [hic_opt] at h_inner
    refine ⟨dic, rfl, ?_⟩
    rw [List.all_eq_true] at h_inner
    have h_succ := h_inner pc_t' hsucc
    rw [List.any_eq_true] at h_succ
    obtain ⟨dtc, hdtc_mem, hdtc_check⟩ := h_succ
    refine ⟨dtc, hdtc_mem, ?_⟩
    simp only [Bool.and_eq_true] at hdtc_check
    exact ⟨hdtc_check.1, hdtc_check.2⟩

/-- Relate getD to getElem? for arrays. -/
private theorem array_getD_of_getElem? {α : Type} {arr : Array α} {n : Nat} {val d : α}
    (h : arr[n]? = some val) : arr.getD n d = val := by
  have hb := bound_of_getElem? h
  have heq := (getElem?_eq_some_iff.mp h).2
  simp [Array.getD, dif_pos hb, heq]

/-- **Condition 3**: checkAllTransitions → check_all_transitions -/
theorem checkAllTransitions_sound (dc : DCertificate)
    (h : checkAllTransitions dc = true) :
    check_all_transitions (toCertificate dc) := by
  intro pc_t σ_t σ_t' pc_t' hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hne_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic (Step.halt hinstr) hstep)
  have hsucc := step_successor hstep hinstr
  -- Extract Bool-level information
  obtain ⟨dic, hdic, dtc, hdtc_mem, hpath, hvm⟩ :=
    extractTransCheck dc h pc_t pc_t' instr hinstr hne_halt hsucc
  -- The tc in toCertificate's transitions that corresponds to dtc
  let tc : TransCorr :=
    { origLabels := dtc.origLabels
      vm := idVarMap
      vm_next := idVarMap }
  -- Show tc is in (toCertificate dc).instrCerts pc_t).transitions
  have hgetD : dc.instrCerts.getD pc_t default = dic := array_getD_of_getElem? hdic
  have htc_mem : tc ∈ ((toCertificate dc).instrCerts pc_t).transitions := by
    simp only [toCertificate, hgetD]
    show tc ∈ dic.transitions.map _
    exact List.mem_map.mpr ⟨dtc, hdtc_mem, rfl⟩
  refine ⟨tc, htc_mem, ?_, ?_, ?_⟩
  -- 1. tc.vm = ic.vm
  · rfl
  -- 2. tc.vm_next = ic'.vm
  · rfl
  -- 3. check_transition_varmap
  · have h_pc_eq : (dc.instrCerts.getD pc_t default).pc_orig = dic.pc_orig := by
      rw [hgetD]
    simp only [toCertificate, hgetD]
    exact transVarmap_sound dc pc_t pc_t' dic dtc instr
      ((dc.instrCerts.getD pc_t' default).pc_orig) hinstr hpath hvm

-- ============================================================
-- § 8. Non-termination soundness
-- ============================================================

/-- Helper: extract inner check from checkNontermination for a non-halt instruction.
    Uses definitional equality (match reduction) to convert between the full
    match form and the instrCerts-level check. -/
private theorem nonterm_inner (dc : DCertificate)
    (h : checkNontermination dc = true) (pc_t pc_t' : Label)
    (instr : TAC) (hinstr : dc.trans[pc_t]? = some instr) (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ successors instr pc_t)
    (horig_eq : (dc.instrCerts.getD pc_t default).pc_orig =
                (dc.instrCerts.getD pc_t' default).pc_orig) :
    dc.measure.getD pc_t' 0 < dc.measure.getD pc_t 0 := by
  have hbound := bound_of_getElem? hinstr
  unfold checkNontermination at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  rw [hinstr] at hpc
  -- hpc has: (match some instr with | some .halt => ... | some i => body i | none => ...) = true
  -- For each non-halt constructor, Lean definitionally reduces match some (.const/copy/...)
  -- to the non-halt branch. Use `cases instr` + `exact hpc` to let the kernel reduce.
  -- First extract the body for the instrCerts match:
  suffices h_inner : ∀ pc_t' ∈ successors instr pc_t,
      (match dc.instrCerts[pc_t]? with
       | some ic =>
         let ic' := dc.instrCerts.getD pc_t' default
         if ic.pc_orig == ic'.pc_orig then
           decide (dc.measure.getD pc_t' 0 < dc.measure.getD pc_t 0)
         else true
       | none => false) = true by
    have hitem := h_inner pc_t' hsucc
    revert hitem
    cases hic : dc.instrCerts[pc_t]? with
    | none => simp
    | some ic =>
      have hgetD : dc.instrCerts.getD pc_t default = ic := by
        simp [Array.getD, dif_pos (bound_of_getElem? hic)]
        exact (Array.getElem?_eq_some_iff.mp hic).2
      rw [hgetD] at horig_eq
      simp only [beq_iff_eq.mpr horig_eq, ↓reduceIte]
      exact of_decide_eq_true
  -- Prove h_inner: extract from hpc via List.all and match reduction
  intro pc_t'' hmem
  -- hpc has the full match on some instr; after cases on instr, it reduces
  -- definitionally to the instrCerts-level check
  revert hpc; cases instr with
  | halt => exact absurd rfl hne
  | _ =>
    intro hpc
    -- For non-halt constructors, the kernel reduces the match on some (.const/copy/...)
    -- Use `generalize` to abstract the instrCerts lookup, then `exact` uses definitional eq
    revert hmem
    generalize dc.instrCerts[pc_t]? = opt_ic at hpc ⊢
    cases opt_ic with
    | none => simp at hpc
    | some ic =>
      rw [List.all_eq_true] at hpc
      exact hpc pc_t''

/-- **Condition 5**: checkNontermination → check_nontermination -/
theorem checkNontermination_sound (dc : DCertificate)
    (h : checkNontermination dc = true) :
    check_nontermination (toCertificate dc) (toMeasure dc) := by
  intro pc_t pc_t' σ_t σ_t' σ_o _ _ _ hexec horig_eq
  obtain ⟨c', hstep, hc'⟩ := hexec; subst hc'
  dsimp only [toCertificate, toMeasure] at horig_eq ⊢
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hinstr' : dc.trans[pc_t]? = some instr := hinstr
  have not_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic hstep (Step.halt hinstr))
  exact nonterm_inner dc h pc_t pc_t' instr hinstr' not_halt
    (step_successor hstep hinstr) horig_eq

-- ============================================================
-- § 9. Main soundness theorem
-- ============================================================

/-- **Main Theorem**: If the decidable checker accepts a certificate,
    then `CertificateValid` holds for the corresponding Prop-based certificate.

    This connects the executable world (`Bool`) to the proof world (`Prop`):
    running `checkCertificate dc = true` is sufficient to guarantee
    that the transformation preserves all program behaviors. -/
-- Helper: decompose a chain of Bool.and into individual conjuncts
private theorem and_true_of_and_eq_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simp [Bool.and_eq_true] at h; exact h

theorem soundness_bridge (dc : DCertificate)
    (h : checkCertificate dc = true) :
    CertificateValid (toCertificate dc) (toMeasure dc) := by
  -- checkCertificate is: c1 && c2 && c3 && c4 && c5 && c6 && c7
  -- && is left-associative, so decompose from right to left
  unfold checkCertificate at h
  have ⟨h16, h7⟩ := and_true_of_and_eq_true h
  have ⟨h15, h6⟩ := and_true_of_and_eq_true h16
  have ⟨h14, h5⟩ := and_true_of_and_eq_true h15
  have ⟨h13, h4⟩ := and_true_of_and_eq_true h14
  have ⟨h12, h3⟩ := and_true_of_and_eq_true h13
  have ⟨h1, h2⟩  := and_true_of_and_eq_true h12
  exact {
    start_corr    := checkStart_sound dc h1
    start_inv     := checkInvariantsAtStart_sound dc h2
    inv_preserved := checkInvariantsPreserved_sound dc h3
    transitions   := checkAllTransitions_sound dc h4
    halt_corr     := checkHaltCorrespondence_sound dc h5
    halt_obs      := checkHaltObservable_sound dc h6
    nonterm       := checkNontermination_sound dc h7
  }

-- ============================================================
-- § 10. Why not iff?
-- ============================================================

/-!
## The converse does NOT hold

`CertificateValid cert μ` does **not** imply `checkCertificate dc = true`
for several reasons:

1. **Expressiveness gap**: The Prop-based system supports arbitrary invariants
   (`Store → Prop`), while the decidable system only supports `var = val` atoms.
   A certificate using `x < y` as an invariant is valid in the Prop world
   but has no representation in `DCertificate`.

2. **Variable map generality**: The Prop system supports arbitrary `VarMap`s
   (`Var → Expr`), while the decidable system assumes identity maps throughout.

3. **Information loss**: `toCertificate` maps every `DCertificate` to a
   `Certificate` with identity var maps and `DInv.toProp` invariants.
   Many different `Certificate`s could satisfy `CertificateValid` for the
   same programs, but only those expressible as `toCertificate dc` for some `dc`
   are in the image of the translation.

The relationship is:

```
  checkCertificate dc = true
        ⟹
  CertificateValid (toCertificate dc) (toMeasure dc)
        ⟹
  ∀ σ₀ b, program_behavior dc.trans σ₀ b →
    ∃ b', program_behavior dc.orig σ₀ b' ∧ ...
```

The decidable checker is a **sufficient** but not **necessary** condition
for semantic preservation. It is a practical tool for certifying common
compiler optimizations (constant propagation, dead code elimination,
redundant assignment removal).
-/

-- ============================================================
-- § 11. End-to-end theorem
-- ============================================================

/-- **End-to-end correctness**: If the decidable checker accepts,
    then every behavior of the transformed program has a corresponding
    behavior in the original program (with observable equivalence at halt).

    This is the composition of `soundness_bridge` and
    `credible_compilation_soundness` — the complete pipeline from
    `checkCertificate dc = true` to semantic preservation. -/
theorem decidable_checker_correct (dc : DCertificate)
    (h : checkCertificate dc = true)
    (σ₀ : Store) (b : Behavior)
    (htrans : program_behavior dc.trans σ₀ b) :
    ∃ b', program_behavior dc.orig σ₀ b' ∧
      match b, b' with
      | .halts σ_t, .halts σ_o =>
          ∀ v ∈ dc.observable, σ_t v = σ_o v
      | .diverges, .diverges => True
      | _, _ => False := by
  cases b with
  | halts σ_t' =>
    obtain ⟨σ_o', ho, hobs⟩ := soundness_halt
      (toCertificate dc) (toMeasure dc) (soundness_bridge dc h) σ₀ σ_t' htrans
    exact ⟨.halts σ_o', ho, hobs⟩
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toCertificate dc) (toMeasure dc) (soundness_bridge dc h) f σ₀ hinf hf0
    exact ⟨.diverges, ⟨g, hg, hg0⟩, trivial⟩
