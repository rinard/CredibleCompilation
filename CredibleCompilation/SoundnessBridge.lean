import CredibleCompilation.ExecChecker
import CredibleCompilation.PropExamples
import Mathlib.Tactic

/-!
# Soundness Bridge: Executable Checker → Prop-based Checker

We prove that if the executable `checkCertificateExec` returns `true`,
then `PCertificateValid` holds for the corresponding `PCertificate`.

## Structure

1. **Translation**: `toPCertificate` lifts a `ECertificate` to a `PCertificate`
2. **Per-condition soundness**: each Bool check implies its Prop counterpart
3. **Main theorem**: `soundness_bridge`

## On the converse (completeness)

An iff is **not possible** in general:
- The Prop-based `PCertificate` uses `PInvariantMap := Label → Store → Prop`
  (arbitrary predicates on stores)
- The executable `ECertificate` uses `EInv := List (Var × Expr)`
  (only `var = expr` atoms, where `expr` is built from literals, variables, and binops)

Any `PCertificateValid` proof using invariants beyond `var = expr`
(e.g., inequalities like `x < y`) cannot be captured by `checkCertificateExec`.
The executable checker is **sound but incomplete**.
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
-- § 1. Lifting EInv to Prop
-- ============================================================

/-- A `EInv` as a proposition: every atom `(x, e)` asserts `σ x = e.eval σ`. -/
def EInv.toProp (inv : EInv) : PInvariant :=
  fun σ => ∀ p ∈ inv, σ p.1 = p.2.eval σ

theorem EInv.toProp_nil : EInv.toProp [] = fun _ => True := by
  funext σ; simp [EInv.toProp]

theorem EInv.toProp_cons (x : Var) (e : Expr) (rest : EInv) :
    EInv.toProp ((x, e) :: rest) = fun σ => σ x = e.eval σ ∧ EInv.toProp rest σ := by
  funext σ; simp [EInv.toProp]

-- ============================================================
-- § 2. Translation: ECertificate → PCertificate
-- ============================================================

/-- Convert an executable variable map to a Prop-level variable map.
    Unmapped variables default to `.var v` (identity). -/
def eVarMapToVarMap (evm : EVarMap) : PVarMap :=
  fun v => ssGet evm v

/-- Lift an executable certificate to a Prop-based certificate. -/
def toPCertificate (dc : ECertificate) : PCertificate :=
  { orig       := dc.orig
    trans      := dc.trans
    inv_orig   := fun l => (dc.inv_orig.getD l ([] : EInv)).toProp
    inv_trans  := fun l => (dc.inv_trans.getD l ([] : EInv)).toProp
    observable := dc.observable
    instrCerts := fun l =>
      let dic := dc.instrCerts.getD l default
      { pc_orig    := dic.pc_orig
        vm         := eVarMapToVarMap dic.vm
        transitions := dic.transitions.map fun dtc =>
          { origLabels   := dtc.origLabels
            vm           := eVarMapToVarMap dtc.vm
            vm_next      := eVarMapToVarMap dtc.vm_next }
      }
    haltCerts := fun l =>
      let dhc := dc.haltCerts.getD l default
      { pc_orig := dhc.pc_orig
        vm      := eVarMapToVarMap dhc.vm }
  }

/-- Lift the measure: ignores the store (depends only on label). -/
def toPMeasure (dc : ECertificate) : PTransMeasure :=
  fun l _ => dc.measure.getD l 0

@[simp] theorem toCertificate_orig (dc : ECertificate) :
    (toPCertificate dc).orig = dc.orig := rfl

@[simp] theorem toCertificate_trans (dc : ECertificate) :
    (toPCertificate dc).trans = dc.trans := rfl

-- ============================================================
-- § 3. lookupExpr soundness
-- ============================================================

theorem lookupExpr_sound (inv : EInv) (v : Var) (e : Expr) (σ : Store)
    (hlook : lookupExpr inv v = some e)
    (hinv : EInv.toProp inv σ) :
    σ v = e.eval σ := by
  induction inv with
  | nil => simp [lookupExpr] at hlook
  | cons p rest ih =>
    obtain ⟨x, expr⟩ := p
    rw [EInv.toProp_cons] at hinv
    simp only [lookupExpr, List.find?, Option.map] at hlook
    by_cases hxv : x == v
    · simp [hxv] at hlook
      rw [← hlook, ← beq_iff_eq.mp hxv]
      exact hinv.1
    · simp [hxv] at hlook
      exact ih hlook hinv.2

-- ============================================================
-- § 4. Expr.simplify soundness
-- ============================================================

/-- Reassociation preserves semantics. -/
private theorem Expr.reassoc_sound (op : BinOp) (a b : Expr) (σ : Store) :
    (Expr.reassoc op a b).eval σ = (Expr.bin op a b).eval σ := by
  unfold Expr.reassoc
  split
  · -- (na - x) - nb → (na - nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval]
    ring
  · rename_i na x nb
    simp only [Expr.eval, BinOp.eval]
    ring
  · rename_i na nb x
    simp only [Expr.eval, BinOp.eval]
    ring
  · rfl

/-- Simplification preserves semantics: evaluating `e.simplify inv` in `σ`
    gives the same result as evaluating `e` in `σ`, provided `σ` satisfies `inv`. -/
theorem Expr.simplify_sound (inv : EInv) (e : Expr) (σ : Store)
    (hinv : EInv.toProp inv σ) :
    (e.simplify inv).eval σ = e.eval σ := by
  induction e with
  | lit n => simp [Expr.simplify, Expr.eval]
  | var v =>
    simp only [Expr.simplify]
    split
    · case h_1 e hlook =>
      simp only [Expr.eval]
      exact (lookupExpr_sound inv v e σ hlook hinv).symm
    · case h_2 =>
      simp [Expr.eval]
  | bin op a b iha ihb =>
    simp only [Expr.simplify, Expr.eval]
    split
    · case h_1 na nb heqa heqb =>
      simp only [Expr.eval]
      rw [heqa] at iha; rw [heqb] at ihb
      simp only [Expr.eval] at iha ihb
      rw [iha, ihb]
    · case h_2 =>
      rw [Expr.reassoc_sound]
      simp only [Expr.eval]
      rw [iha, ihb]

-- ============================================================
-- § 5. Easy soundness lemmas
-- ============================================================

/-- **Condition 1**: checkStartCorrespondenceExec → checkStartCorrespondenceProp -/
theorem checkStartCorrespondenceExec_sound (dc : ECertificate)
    (h : checkStartCorrespondenceExec dc = true)
    (hvm0 : (dc.instrCerts.getD 0 default).vm = []) :
    checkStartCorrespondenceProp (toPCertificate dc) := by
  simp [checkStartCorrespondenceExec] at h
  split at h
  · rename_i ic hic
    have hbound := bound_of_getElem? hic
    have hget : dc.instrCerts[0] = ic := (Array.getElem?_eq_some_iff.mp hic).2
    have hpc : ic.pc_orig = 0 := beq_iff_eq.mp h
    constructor
    · -- (instrCerts 0).pc_orig = 0
      simp only [toPCertificate, Array.getD, dif_pos hbound]
      rw [show dc.instrCerts.getInternal 0 hbound = ic from hget]
      exact hpc
    · -- ∀ σ, vm.consistent σ σ
      have hvm_ic : ic.vm = [] := by
        have : (dc.instrCerts.getD 0 default).vm = ic.vm := by
          simp [Array.getD, dif_pos hbound, hget]
        rw [this] at hvm0; exact hvm0
      intro σ x
      simp only [toPCertificate, Array.getD, dif_pos hbound]
      rw [show dc.instrCerts.getInternal 0 hbound = ic from hget]
      simp [hvm_ic, eVarMapToVarMap, ssGet, Expr.eval]
  · contradiction

/-- **Condition 2a**: checkInvariantsAtStartExec → checkInvariantsAtStartProp -/
theorem checkInvariantsAtStartExec_sound (dc : ECertificate)
    (h : checkInvariantsAtStartExec dc = true) :
    checkInvariantsAtStartProp (toPCertificate dc) := by
  unfold checkInvariantsAtStartExec at h
  have h1 : (dc.inv_orig.getD 0 ([] : EInv)).isEmpty = true := by
    revert h; cases (dc.inv_orig.getD 0 ([] : EInv)).isEmpty <;> simp
  have h2 : (dc.inv_trans.getD 0 ([] : EInv)).isEmpty = true := by
    revert h; cases (dc.inv_trans.getD 0 ([] : EInv)).isEmpty <;> simp
  have horig_nil : dc.inv_orig.getD 0 ([] : EInv) = [] := by
    revert h1; cases dc.inv_orig.getD 0 ([] : EInv) <;> simp [List.isEmpty]
  have htrans_nil : dc.inv_trans.getD 0 ([] : EInv) = [] := by
    revert h2; cases dc.inv_trans.getD 0 ([] : EInv) <;> simp [List.isEmpty]
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · change (dc.inv_trans.getD 0 ([] : EInv)).toProp σ
    rw [htrans_nil]; simp [EInv.toProp]
  · change (dc.inv_orig.getD 0 ([] : EInv)).toProp σ
    rw [horig_nil]; simp [EInv.toProp]

/-- **Condition 4a**: checkHaltCorrespondenceExec → checkHaltCorrespondenceProp -/
theorem checkHaltCorrespondenceExec_sound (dc : ECertificate)
    (h : checkHaltCorrespondenceExec dc = true) :
    checkHaltCorrespondenceProp (toPCertificate dc) := by
  intro pc_t
  dsimp only [toPCertificate]
  intro hhalt
  have hbound : pc_t < dc.trans.size := bound_of_getElem? hhalt
  unfold checkHaltCorrespondenceExec at h
  rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  simp only [hhalt] at hpc
  revert hpc
  generalize dc.orig[(dc.instrCerts.getD pc_t default).pc_orig]? = opt
  cases opt with
  | none => simp
  | some instr => cases instr <;> simp

/-- **Condition 4b**: checkHaltObservableExec → checkHaltObservableProp -/
theorem checkHaltObservableExec_sound (dc : ECertificate)
    (h : checkHaltObservableExec dc = true) :
    checkHaltObservableProp (toPCertificate dc) := by
  intro pc_t σ_t σ_o hhalt
  dsimp only [toPCertificate, eVarMapToVarMap, PVarMap.consistent]
  intro hcons v hv
  -- From checker: ssGet ic.vm v == .var v for observable v at halt
  have hhalt' : dc.trans[pc_t]? = some .halt := hhalt
  unfold checkHaltObservableExec at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr (bound_of_getElem? hhalt'))
  rw [hhalt'] at hpc; rw [List.all_eq_true] at hpc
  have hvar : ssGet (dc.instrCerts.getD pc_t default).vm v = .var v :=
    beq_iff_eq.mp (hpc v hv)
  -- hcons v : σ_t v = (ssGet ... v).eval σ_o = (.var v).eval σ_o = σ_o v
  have hcons_v := hcons v
  rw [hvar] at hcons_v; simp [Expr.eval] at hcons_v; exact hcons_v

-- ============================================================
-- § 6. Symbolic execution infrastructure
-- ============================================================

/-- find? on filtered list equals find? on original when predicates are compatible. -/
private theorem find_filter_ne (ss : SymStore) (x y : Var) (hne : y ≠ x) :
    (ss.filter (fun p => !(p.1 == x))).find? (fun p => p.1 == y) =
    ss.find? (fun p => p.1 == y) := by
  induction ss with
  | nil => rfl
  | cons p rest ih =>
    by_cases hpx : p.1 == x <;> by_cases hpy : p.1 == y
    · exfalso; exact hne (beq_iff_eq.mp hpy ▸ beq_iff_eq.mp hpx)
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

/-- Empty EVarMap converts to identity PVarMap. -/
private theorem eVarMapToVarMap_nil : eVarMapToVarMap [] = idVarMap := by
  funext v; simp [eVarMapToVarMap, ssGet, List.find?, idVarMap]

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

/-- If `v` is not a key in the symbolic store, `ssGet` returns `.var v`. -/
private theorem ssGet_not_key {ss : SymStore} {v : Var}
    (h : v ∉ ss.map Prod.fst) : ssGet ss v = .var v := by
  simp only [ssGet]
  induction ss with
  | nil => simp [List.find?]
  | cons p rest ih =>
    simp only [List.map, List.mem_cons, not_or] at h
    have hne : ¬(p.1 = v) := fun heq => h.1 (heq ▸ rfl)
    have hrest : v ∉ rest.map Prod.fst := h.2
    simp only [List.find?, beq_eq_false_iff_ne.mpr hne]
    exact ih hrest

/-- substSym with empty store is identity. -/
private theorem Expr.substSym_nil : ∀ (e : Expr), e.substSym ([] : SymStore) = e := by
  intro e; induction e with
  | lit _ => simp [Expr.substSym]
  | var v => simp [Expr.substSym, ssGet_nil_var]
  | bin op a b iha ihb => simp [Expr.substSym, iha, ihb]

-- ============================================================
-- § 6b. Expr.substSym soundness
-- ============================================================

/-- Substituting variables in `e` with their symbolic post-values and evaluating
    at the initial store `σ₀` equals evaluating `e` at the post-store `σ'`. -/
theorem Expr.substSym_sound (ss : SymStore) (e : Expr) (σ₀ σ' : Store)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ' v) :
    (e.substSym ss).eval σ₀ = e.eval σ' := by
  induction e with
  | lit n => simp [Expr.substSym, Expr.eval]
  | var v => simp [Expr.substSym, Expr.eval]; exact hrepr v
  | bin op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]

-- ============================================================
-- § 6b. PInvariant preservation soundness
-- ============================================================

/-- Key lemma: checkInvAtom soundness.
    If checkInvAtom succeeds, then for any store satisfying inv_pre,
    after executing `instr`, the atom holds in the post-store.
    Uses symbolic execution: the checker verifies that the simplified
    post-value of `x` equals the simplified post-value of `e`
    (with variables substituted by their symbolic post-values). -/
theorem checkInvAtom_sound (inv_pre : EInv) (instr : TAC) (atom : Var × Expr)
    (σ σ' : Store) (pc pc' : Label) (prog : Prog)
    (hcheck : checkInvAtom inv_pre instr atom = true)
    (hinv : EInv.toProp inv_pre σ)
    (hstep : Step prog (Cfg.run pc σ) (Cfg.run pc' σ'))
    (hinstr : prog[pc]? = some instr) :
    σ' atom.1 = atom.2.eval σ' := by
  obtain ⟨x, e⟩ := atom; simp only
  -- checkInvAtom gives us BEq equality of simplified expressions
  simp only [checkInvAtom] at hcheck
  have hbeq := beq_iff_eq.mp hcheck
  -- execSymbolic_sound: symbolic store tracks the step
  have hrepr : ∀ v, (ssGet (execSymbolic ([] : SymStore) instr) v).eval σ = σ' v :=
    execSymbolic_sound [] instr σ σ σ' pc pc' prog (ssGet_nil σ) hstep hinstr
  -- Simplify_sound on both sides (evaluated at σ, which satisfies inv_pre)
  have hlhs := Expr.simplify_sound inv_pre
    (ssGet (execSymbolic ([] : SymStore) instr) x) σ hinv
  have hrhs := Expr.simplify_sound inv_pre
    (e.substSym (execSymbolic ([] : SymStore) instr)) σ hinv
  -- substSym_sound: substituting and evaluating at σ equals evaluating at σ'
  have hsub := Expr.substSym_sound (execSymbolic ([] : SymStore) instr) e σ σ' hrepr
  -- Chain: σ' x = ... = e.eval σ'
  calc σ' x
      = (ssGet (execSymbolic ([] : SymStore) instr) x).eval σ := (hrepr x).symm
    _ = ((ssGet (execSymbolic ([] : SymStore) instr) x).simplify inv_pre).eval σ := hlhs.symm
    _ = ((e.substSym (execSymbolic ([] : SymStore) instr)).simplify inv_pre).eval σ := by
          rw [hbeq]
    _ = (e.substSym (execSymbolic ([] : SymStore) instr)).eval σ := hrhs
    _ = e.eval σ' := hsub

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
private theorem checkProg_sound (prog : Prog) (inv : Array EInv)
    (h : (List.range prog.size).all (fun pc =>
      match prog[pc]? with
      | some instr =>
        (successors instr pc).all fun pc' =>
          (inv.getD pc' ([] : EInv)).all (checkInvAtom (inv.getD pc ([] : EInv)) instr)
      | none => true) = true) :
    PInvariantMap.preserved (fun l => (inv.getD l ([] : EInv)).toProp) prog := by
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
  exact checkInvAtom_sound (inv.getD pc ([] : EInv)) instr atom σ σ' pc pc' prog
    (hpc' atom hatom) hinvpc hstep hinstr

/-- **Condition 2b**: checkInvariantsPreservedExec → checkInvariantsPreservedProp -/
theorem checkInvariantsPreservedExec_sound (dc : ECertificate)
    (h : checkInvariantsPreservedExec dc = true) :
    checkInvariantsPreservedProp (toPCertificate dc) := by
  unfold checkInvariantsPreservedExec at h
  have ⟨h1, h2⟩ := and_true_split h
  exact ⟨checkProg_sound dc.orig dc.inv_orig h1,
         checkProg_sound dc.trans dc.inv_trans h2⟩

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
    The path check includes symbolic branch-direction verification for ifgoto.
    `branchInfo` provides the branch direction for the first step's ifgoto when
    symbolic analysis is inconclusive. `hbranch` guarantees the runtime store
    matches the branch direction. -/
private theorem execPath_sound_gen (orig : Prog) (ss : SymStore) (inv : EInv)
    (σ₀ σ : Store) (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (Var × Bool))
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ v)
    (hinv : EInv.toProp inv σ₀)
    (hpath : checkOrigPath orig ss inv pc labels pc' branchInfo = true)
    (hbranch : ∀ x taken, branchInfo = some (x, taken) →
        if taken then σ x ≠ 0 else σ x = 0) :
    ∃ σ', Steps orig (Cfg.run pc σ) (Cfg.run pc' σ') ∧
          ∀ v, (ssGet (execPath orig ss pc labels) v).eval σ₀ = σ' v := by
  induction labels generalizing pc σ ss branchInfo with
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
      -- Construct the step + symbolic tracking
      have ⟨σ₁, hstep_orig, hrepr'⟩ : ∃ σ₁,
          Step orig (Cfg.run pc σ) (Cfg.run nextPC σ₁) ∧
          ∀ v, (ssGet (execSymbolic ss instr) v).eval σ₀ = σ₁ v := by
        cases opt_next with
        | some nextPC' =>
          have hpc_eq : nextPC = nextPC' := (beq_iff_eq.mp hnext_eq).symm
          subst hpc_eq
          cases instr with
          | const x n =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ[x ↦ n], Step.const horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.const horig_opt) horig_opt⟩
          | copy x y =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ[x ↦ σ y], Step.copy horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.copy horig_opt) horig_opt⟩
          | binop x op y z =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ[x ↦ op.eval (σ y) (σ z)], Step.binop horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.binop horig_opt) horig_opt⟩
          | goto l =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, Step.goto horig_opt,
              execSymbolic_sound ss _ σ₀ σ σ pc l orig hrepr (Step.goto horig_opt) horig_opt⟩
          | ifgoto x l =>
            have hexec_id : execSymbolic ss (.ifgoto x l) = ss := rfl
            simp only [computeNextPC] at hnext_opt
            have hsimpl := Expr.simplify_sound inv (ssGet ss x) σ₀ hinv
            by_cases hnonzero : (ssGet ss x).simplify inv |>.isNonZeroLit
            · simp only [hnonzero, ↓reduceIte] at hnext_opt
              have hpc_eq : nextPC = l := Option.some.inj hnext_opt.symm
              rw [hpc_eq]
              obtain ⟨n, hsv, hne⟩ := isNonZeroLit_sound hnonzero
              rw [hsv, Expr.eval] at hsimpl
              have : σ x ≠ 0 := by rw [← hrepr x, ← hsimpl]; exact hne
              exact ⟨σ, Step.iftrue horig_opt this, hexec_id ▸ hrepr⟩
            · simp only [hnonzero, Bool.false_eq_true, ↓reduceIte] at hnext_opt
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
        | none =>
          -- computeNextPC returned none; use branchInfo fallback
          cases hbi : branchInfo with
          | none =>
            exfalso; revert hnext_eq; rw [hbi]; simp
          | some bi =>
            obtain ⟨xv, taken⟩ := bi
            cases instr with
            | ifgoto x l_orig =>
              have hexec_id : execSymbolic ss (.ifgoto x l_orig) = ss := rfl
              cases taken with
              | true =>
                -- Taken branch: nextPC = l_orig, σ x ≠ 0
                have hfb : (x == xv && nextPC == l_orig) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hxeq, hpc_eq⟩ := and_true_split hfb
                have hxeq := beq_iff_eq.mp hxeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have hσx : σ x ≠ 0 := by
                  have := hbranch xv true (hbi ▸ rfl); simp at this
                  rw [hxeq]; exact this
                exact ⟨σ, Step.iftrue horig_opt hσx, hexec_id ▸ hrepr⟩
              | false =>
                -- Fallthrough: nextPC = pc + 1, σ x = 0
                have hfb : (x == xv && nextPC == pc + 1) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hxeq, hpc_eq⟩ := and_true_split hfb
                have hxeq := beq_iff_eq.mp hxeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have hσx : σ x = 0 := by
                  have := hbranch xv false (hbi ▸ rfl); simp at this
                  rw [hxeq]; exact this
                exact ⟨σ, Step.iffall horig_opt hσx, hexec_id ▸ hrepr⟩
            | _ =>
              exfalso; revert hnext_eq; rw [hbi]; cases taken <;> simp
      -- Recursive step (branchInfo = none for rest)
      have hexec : execPath orig ss pc (nextPC :: rest) =
          execPath orig (execSymbolic ss instr) nextPC rest := by
        simp [execPath, horig_opt]
      obtain ⟨σ', hsteps_rest, hrepr_final⟩ :=
        ih (execSymbolic ss instr) σ₁ nextPC none hrepr'
          hpath_inner (fun _ _ h => by simp at h)
      exact ⟨σ', Steps.step hstep_orig hsteps_rest, hexec ▸ hrepr_final⟩

/-- Path execution soundness: specialization with empty initial symbolic store. -/
private theorem execPath_sound (orig : Prog) (inv : EInv) (σ : Store)
    (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (Var × Bool))
    (hrepr : ∀ v, (ssGet ([] : SymStore) v).eval σ = σ v)
    (hinv : EInv.toProp inv σ)
    (hpath : checkOrigPath orig ([] : SymStore) inv pc labels pc' branchInfo = true)
    (hbranch : ∀ x taken, branchInfo = some (x, taken) →
        if taken then σ x ≠ 0 else σ x = 0) :
    ∃ σ', Steps orig (Cfg.run pc σ) (Cfg.run pc' σ') ∧
          ∀ v, (ssGet (execPath orig ([] : SymStore) pc labels) v).eval σ = σ' v :=
  execPath_sound_gen orig ([] : SymStore) inv σ σ pc labels pc' branchInfo
    hrepr hinv hpath hbranch

/-- If `vm.consistent σ_o σ_t`, then evaluating `e` at `σ_t` equals
    evaluating `e.substSym vm` at `σ_o`. Follows from `substSym_sound`. -/
theorem Expr.substSym_consistent (vm : EVarMap) (e : Expr) (σ_o σ_t : Store)
    (hcons : ∀ x, σ_t x = (ssGet vm x).eval σ_o) :
    e.eval σ_t = (e.substSym vm).eval σ_o :=
  (Expr.substSym_sound vm e σ_o σ_t (fun v => (hcons v).symm)).symm

/-- BEq on Expr implies equality. -/
private theorem expr_beq_eq {e₁ e₂ : Expr} (h : (e₁ == e₂) = true) : e₁ = e₂ :=
  beq_iff_eq.mp h

/-- Array.getD on empty array returns the default. -/
private theorem Array_getD_empty {α : Type} (n : Nat) (d : α) :
    Array.getD #[] n d = d := by
  simp [Array.getD]

/-- Branch direction info from the transformed program's ifgoto instruction.
    For `ifgoto x l` with `l ≠ pc + 1`, returns `some (x, pc' == l)` indicating
    whether the branch was taken. -/
@[reducible] private def transBranchInfo (instr : TAC) (pc_t pc_t' : Label) : Option (Var × Bool) :=
  match instr with
  | .ifgoto x l => if !(l == pc_t + 1) then some (x, pc_t' == l) else none
  | _ => none

/-- Compute branchInfo from an instruction and a variable map. -/
@[reducible] private def branchInfoWithVm (instr : TAC) (vm : EVarMap) (pc_t pc_t' : Label)
    : Option (Var × Bool) :=
  match instr with
  | .ifgoto x l =>
    match ssGet vm x with
    | .var origX => if !(l == pc_t + 1) then some (origX, pc_t' == l) else none
    | _ => none
  | _ => none

/-- With empty varMap, branchInfoWithVm equals transBranchInfo. -/
private theorem branchInfoWithVm_nil (instr : TAC) (pc_t pc_t' : Label) :
    branchInfoWithVm instr ([] : EVarMap) pc_t pc_t' = transBranchInfo instr pc_t pc_t' := by
  cases instr <;> simp [branchInfoWithVm, transBranchInfo, ssGet, List.find?]

/-- When the branchInfo computed from `instr` and `pc_t'` says `some (xv, taken)`,
    we can derive the branch condition from any step. -/
private theorem branchInfo_of_step {prog : Prog} {pc pc' : Label} {σ σ' : Store}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ) (Cfg.run pc' σ'))
    {xv : Var} {taken : Bool}
    (hbi : transBranchInfo instr pc pc' = some (xv, taken)) :
    if taken then σ xv ≠ 0 else σ xv = 0 := by
  cases instr with
  | ifgoto x l =>
    -- hbi : (if !(l == pc + 1) then some (x, pc' == l) else none) = some (xv, taken)
    by_cases hguard : (!(l == pc + 1))
    · simp only [transBranchInfo, hguard, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hbi
      obtain ⟨rfl, rfl⟩ := hbi
      -- xv = x, taken = (pc' == l)
      cases hstep with
      | iftrue h hne =>
        have heq := Option.some.inj (hinstr.symm.trans h)
        simp only [TAC.ifgoto.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp [hne]
      | iffall h hz =>
        have heq := Option.some.inj (hinstr.symm.trans h)
        simp only [TAC.ifgoto.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have : ¬(l = pc + 1) := by simpa using hguard
        have : ¬(pc + 1 = l) := fun h => this h.symm
        simp [beq_eq_false_iff_ne.mpr this, hz]
      | const h => exact absurd (hinstr.symm.trans h) (by simp)
      | copy h => exact absurd (hinstr.symm.trans h) (by simp)
      | binop h => exact absurd (hinstr.symm.trans h) (by simp)
      | goto h => exact absurd (hinstr.symm.trans h) (by simp)
    · simp [transBranchInfo, hguard] at hbi
  | _ => simp [transBranchInfo] at hbi

/-- When `branchInfoWithVm` returns `some (origX, taken)`, a step on the
    transformed program transfers the branch condition to the original variable
    via the variable map consistency. Only fires when `ssGet vm x = .var origX`. -/
private theorem branchInfo_of_step_with_vm {prog : Prog} {pc pc' : Label} {σ_t σ_t' : Store}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ_t) (Cfg.run pc' σ_t'))
    {vm : EVarMap} {σ_o : Store}
    (hcons : ∀ x, σ_t x = (ssGet vm x).eval σ_o)
    {origX : Var} {taken : Bool}
    (hbi : branchInfoWithVm instr vm pc pc' = some (origX, taken)) :
    if taken then σ_o origX ≠ 0 else σ_o origX = 0 := by
  cases instr with
  | ifgoto x l =>
    simp only [branchInfoWithVm] at hbi
    -- Case split on ssGet vm x
    cases hssx : ssGet vm x with
    | var v =>
      simp only [hssx] at hbi
      by_cases hguard : (!(l == pc + 1))
      · simp only [hguard, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hbi
        obtain ⟨rfl, rfl⟩ := hbi
        -- origX = v, taken = (pc' == l)
        have hcons_x := hcons x
        rw [hssx, Expr.eval] at hcons_x
        -- hcons_x : σ_t x = σ_o v
        cases hstep with
        | iftrue h hne =>
          have heq := Option.some.inj (hinstr.symm.trans h)
          simp only [TAC.ifgoto.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          simp; rwa [← hcons_x]
        | iffall h hz =>
          have heq := Option.some.inj (hinstr.symm.trans h)
          simp only [TAC.ifgoto.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have : ¬(l = pc + 1) := by simpa using hguard
          have : ¬(pc + 1 = l) := fun h => this h.symm
          simp [beq_eq_false_iff_ne.mpr this]; rwa [← hcons_x]
        | const h => exact absurd (hinstr.symm.trans h) (by simp)
        | copy h => exact absurd (hinstr.symm.trans h) (by simp)
        | binop h => exact absurd (hinstr.symm.trans h) (by simp)
        | goto h => exact absurd (hinstr.symm.trans h) (by simp)
      · simp [hguard] at hbi
    | lit _ => simp [hssx] at hbi
    | bin _ _ _ => simp [hssx] at hbi
  | _ => simp [branchInfoWithVm] at hbi

/-- Soundness of checkTransitionVarmapProp from the Bool checks.
    Given: checkOrigPath and checkVarMapConsistency both pass, the original path
    produces steps reaching the target with variable map consistency preserved.
    Supports non-trivial variable maps. -/
private theorem transVarmap_sound (dc : ECertificate) (pc_t pc_t' : Label)
    (dic : EInstrCert) (dtc : ETransCorr) (instr : TAC)
    (pc_o' : Label)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hpath : checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dic.pc_orig dtc.origLabels pc_o'
      (branchInfoWithVm instr dtc.vm pc_t pc_t') = true)
    (hvm : checkVarMapConsistency (collectAllVars dc.orig dc.trans)
      dc.orig dic.pc_orig dtc.origLabels instr
      (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dtc.vm dtc.vm_next = true) :
    checkTransitionVarmapProp dc.orig dc.trans
      (fun l => (dc.inv_orig.getD l ([] : EInv)).toProp)
      (fun l => (dc.inv_trans.getD l ([] : EInv)).toProp)
      pc_t pc_t' dic.pc_orig pc_o'
      { origLabels := dtc.origLabels
        vm := eVarMapToVarMap dtc.vm
        vm_next := eVarMapToVarMap dtc.vm_next } := by
  intro σ_t σ_t' σ_o hinv_t hinv_o hcons hstep
  -- hcons : (eVarMapToVarMap dtc.vm).consistent σ_o σ_t, i.e. ∀ x, σ_t x = (ssGet dtc.vm x).eval σ_o
  change ∀ x, σ_t x = (ssGet dtc.vm x).eval σ_o at hcons
  -- Branch info transfers through the variable map
  have hbranch_orig : ∀ x taken,
      branchInfoWithVm instr dtc.vm pc_t pc_t' = some (x, taken) →
      if taken then σ_o x ≠ 0 else σ_o x = 0 :=
    fun x taken hbi => branchInfo_of_step_with_vm hinstr hstep hcons hbi
  -- Execute original path from σ_o
  obtain ⟨σ_o', horig_steps, horig_repr⟩ := execPath_sound dc.orig
    (dc.inv_orig.getD dic.pc_orig ([] : EInv)) σ_o
    dic.pc_orig dtc.origLabels pc_o'
    (branchInfoWithVm instr dtc.vm pc_t pc_t')
    (ssGet_nil σ_o) hinv_o hpath hbranch_orig
  -- horig_repr : ∀ v, (ssGet origSS v).eval σ_o = σ_o' v
  -- Trans symbolic execution from σ_t
  have htrans_repr : ∀ v, (ssGet (execSymbolic ([] : SymStore) instr) v).eval σ_t = σ_t' v :=
    execSymbolic_sound [] instr σ_t σ_t σ_t' pc_t pc_t' dc.trans
      (ssGet_nil σ_t) hstep hinstr
  -- Abbreviations for the symbolic stores
  let origSS := execPath dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels
  let transSS := execSymbolic ([] : SymStore) instr
  let inv := dc.inv_orig.getD dic.pc_orig ([] : EInv)
  -- Prove vm_next consistency: ∀ v, σ_t' v = (ssGet dtc.vm_next v).eval σ_o'
  refine ⟨σ_o', horig_steps, ?_⟩
  intro v
  show σ_t' v = (ssGet dtc.vm_next v).eval σ_o'
  -- Chain: σ_t' v = (ssGet transSS v).eval σ_t
  --              = ((ssGet transSS v).substSym dtc.vm).eval σ_o     [by substSym_consistent]
  -- And:  (ssGet dtc.vm_next v).eval σ_o'
  --              = ((ssGet dtc.vm_next v).substSym origSS).eval σ_o  [by substSym_consistent]
  rw [← htrans_repr v,
      Expr.substSym_consistent dtc.vm (ssGet transSS v) σ_o σ_t hcons]
  have horig_repr_sym : ∀ x, σ_o' x = (ssGet origSS x).eval σ_o :=
    fun x => (horig_repr x).symm
  rw [Expr.substSym_consistent origSS (ssGet dtc.vm_next v) σ_o σ_o' horig_repr_sym]
  -- Now need: ((ssGet transSS v).substSym dtc.vm).eval σ_o
  --         = ((ssGet dtc.vm_next v).substSym origSS).eval σ_o
  -- This is what checkVarMapConsistency verifies
  -- Extract from checkVarMapConsistency: for each v in the extended var list,
  -- the simplified trans-side and orig-side expressions agree
  have hvm_mem : ∀ w ∈ collectAllVars dc.orig dc.trans ++ dtc.vm.map Prod.fst ++ dtc.vm_next.map Prod.fst,
      ((ssGet transSS w).substSym dtc.vm).simplify inv =
      ((ssGet dtc.vm_next w).substSym origSS).simplify inv := by
    intro w hw
    dsimp only [checkVarMapConsistency] at hvm
    exact beq_iff_eq.mp (List.all_eq_true.mp hvm w hw)
  by_cases hv : v ∈ collectAllVars dc.orig dc.trans ++ dtc.vm.map Prod.fst ++ dtc.vm_next.map Prod.fst
  · -- v ∈ allVars: use the simplification chain
    have hvm_v := hvm_mem v hv
    -- Both sides agree after simplification under inv
    have h_trans_simp := Expr.simplify_sound inv
      ((ssGet transSS v).substSym dtc.vm) σ_o hinv_o
    have h_orig_simp := Expr.simplify_sound inv
      ((ssGet dtc.vm_next v).substSym origSS) σ_o hinv_o
    rw [← h_trans_simp, ← h_orig_simp, hvm_v]
  · -- v ∉ allVars: not in any instruction and not a key in either varmap
    have hv_prog : v ∉ collectAllVars dc.orig dc.trans :=
      fun h => hv (List.mem_append_left _ (List.mem_append_left _ h))
    have hv_vm : v ∉ dtc.vm.map Prod.fst :=
      fun h => hv (List.mem_append_left _ (List.mem_append_right _ h))
    have hv_vm_next : v ∉ dtc.vm_next.map Prod.fst :=
      fun h => hv (List.mem_append_right _ h)
    -- ssGet on the varmaps returns .var v
    have hvm_var : ssGet dtc.vm v = .var v := ssGet_not_key hv_vm
    have hvm_next_var : ssGet dtc.vm_next v = .var v := ssGet_not_key hv_vm_next
    -- v not in any instruction → symbolic stores preserve v
    have hv_not_in_orig : ∀ (l : Label) (instr' : TAC),
        dc.orig[l]? = some instr' → v ∉ instrVars instr' := by
      intro l instr' horig hmem
      exact hv_prog (instrVars_sub_collectAllVars_left dc.orig dc.trans instr'
        (getElem?_mem_toList horig) v hmem)
    have hv_not_in_trans : v ∉ instrVars instr := by
      intro hmem
      exact hv_prog (instrVars_sub_collectAllVars_right dc.orig dc.trans instr
        (getElem?_mem_toList hinstr) v hmem)
    -- Both symbolic stores map v to .var v
    have h_trans_v : ssGet transSS v = .var v := by
      rw [execSymbolic_preserves_var ([] : SymStore) instr v hv_not_in_trans]
      exact ssGet_nil_var v
    have h_orig_v : ssGet origSS v = .var v := by
      rw [execPath_preserves_var dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels v hv_not_in_orig]
      exact ssGet_nil_var v
    simp [h_trans_v, h_orig_v, hvm_var, hvm_next_var, Expr.substSym, Expr.eval]

/-- Extract Bool information from checkAllTransitionsExec for a specific step. -/
private theorem extractTransCheck (dc : ECertificate)
    (h : checkAllTransitionsExec dc = true)
    (pc_t pc_t' : Label) (instr : TAC)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ successors instr pc_t) :
    ∃ dic, dc.instrCerts[pc_t]? = some dic ∧
    ∃ dtc ∈ dic.transitions,
      dtc.vm = dic.vm ∧
      dtc.vm_next = (dc.instrCerts.getD pc_t' default).vm ∧
      checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithVm instr dic.vm pc_t pc_t') = true ∧
      checkVarMapConsistency (collectAllVars dc.orig dc.trans)
        dc.orig dic.pc_orig dtc.origLabels instr
        (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dtc.vm dtc.vm_next = true := by
  have hbound := bound_of_getElem? hinstr
  unfold checkAllTransitionsExec at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr hbound)
  rw [hinstr] at hpc
  -- Case split on instr to reduce the outer match on `some instr`
  revert hpc; cases instr with
  | halt => exact absurd rfl hne
  | ifgoto x l =>
    intro hpc
    cases hdic : dc.instrCerts[pc_t]? with
    | none => simp only [hdic] at hpc; exact absurd hpc (by decide)
    | some dic =>
      simp only [hdic] at hpc; rw [List.all_eq_true] at hpc
      have hitem := hpc pc_t' hsucc
      rw [List.any_eq_true] at hitem
      obtain ⟨dtc, hdtc_mem, hdtc_check⟩ := hitem
      -- Decompose: tc.vm == ic.vm && tc.vm_next == ic'.vm && path && vmcheck
      rw [Bool.and_eq_true] at hdtc_check
      obtain ⟨h123, hvm_check⟩ := hdtc_check
      rw [Bool.and_eq_true] at h123
      obtain ⟨h12, hpath⟩ := h123
      rw [Bool.and_eq_true] at h12
      obtain ⟨hvm_eq, hvm_next_eq⟩ := h12
      refine ⟨dic, rfl, dtc, hdtc_mem,
        beq_iff_eq.mp hvm_eq, beq_iff_eq.mp hvm_next_eq, hpath, hvm_check⟩
  | _ =>
    intro hpc
    cases hdic : dc.instrCerts[pc_t]? with
    | none => simp only [hdic] at hpc; exact absurd hpc (by decide)
    | some dic =>
      simp only [hdic] at hpc; rw [List.all_eq_true] at hpc
      have hitem := hpc pc_t' hsucc
      rw [List.any_eq_true] at hitem
      obtain ⟨dtc, hdtc_mem, hdtc_check⟩ := hitem
      rw [Bool.and_eq_true] at hdtc_check
      obtain ⟨h123, hvm_check⟩ := hdtc_check
      rw [Bool.and_eq_true] at h123
      obtain ⟨h12, hpath⟩ := h123
      rw [Bool.and_eq_true] at h12
      obtain ⟨hvm_eq, hvm_next_eq⟩ := h12
      refine ⟨dic, rfl, dtc, hdtc_mem,
        beq_iff_eq.mp hvm_eq, beq_iff_eq.mp hvm_next_eq, hpath, hvm_check⟩

/-- Relate getD to getElem? for arrays. -/
private theorem array_getD_of_getElem? {α : Type} {arr : Array α} {n : Nat} {val d : α}
    (h : arr[n]? = some val) : arr.getD n d = val := by
  have hb := bound_of_getElem? h
  have heq := (getElem?_eq_some_iff.mp h).2
  simp [Array.getD, dif_pos hb, heq]

/-- **Condition 3**: checkAllTransitionsExec → checkAllTransitionsProp -/
theorem checkAllTransitionsExec_sound (dc : ECertificate)
    (h : checkAllTransitionsExec dc = true) :
    checkAllTransitionsProp (toPCertificate dc) := by
  intro pc_t σ_t σ_t' pc_t' hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hne_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic (Step.halt hinstr) hstep)
  have hsucc := step_successor hstep hinstr
  -- Extract Bool-level information
  obtain ⟨dic, hdic, dtc, hdtc_mem, hvm_eq, hvm_next_eq, hpath, hvm⟩ :=
    extractTransCheck dc h pc_t pc_t' instr hinstr hne_halt hsucc
  -- The tc in toPCertificate's transitions that corresponds to dtc
  let tc : PTransCorr :=
    { origLabels := dtc.origLabels
      vm := eVarMapToVarMap dtc.vm
      vm_next := eVarMapToVarMap dtc.vm_next }
  -- Show tc is in (toPCertificate dc).instrCerts pc_t).transitions
  have hgetD : dc.instrCerts.getD pc_t default = dic := array_getD_of_getElem? hdic
  have htc_mem : tc ∈ ((toPCertificate dc).instrCerts pc_t).transitions := by
    simp only [toPCertificate, hgetD]
    show tc ∈ dic.transitions.map _
    exact List.mem_map.mpr ⟨dtc, hdtc_mem, rfl⟩
  refine ⟨tc, htc_mem, ?_, ?_, ?_⟩
  -- 1. tc.vm = ic.vm
  · simp only [toPCertificate, hgetD, tc]
    exact congrArg eVarMapToVarMap hvm_eq
  -- 2. tc.vm_next = ic'.vm
  · simp only [toPCertificate, tc]
    exact congrArg eVarMapToVarMap hvm_next_eq
  -- 3. checkTransitionVarmapProp
  · -- Use the branchInfo with the actual varmap (dtc.vm = dic.vm)
    have hpath' : checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithVm instr dtc.vm pc_t pc_t') = true := by
      rw [hvm_eq]; exact hpath
    simp only [toPCertificate, hgetD]
    exact transVarmap_sound dc pc_t pc_t' dic dtc instr
      ((dc.instrCerts.getD pc_t' default).pc_orig)
      hinstr hpath' hvm

-- ============================================================
-- § 8. Non-termination soundness
-- ============================================================

/-- Helper: extract inner check from checkNonterminationExec for a non-halt instruction.
    Uses definitional equality (match reduction) to convert between the full
    match form and the instrCerts-level check. -/
private theorem nonterm_inner (dc : ECertificate)
    (h : checkNonterminationExec dc = true) (pc_t pc_t' : Label)
    (instr : TAC) (hinstr : dc.trans[pc_t]? = some instr) (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ successors instr pc_t)
    (horig_eq : (dc.instrCerts.getD pc_t default).pc_orig =
                (dc.instrCerts.getD pc_t' default).pc_orig) :
    dc.measure.getD pc_t' 0 < dc.measure.getD pc_t 0 := by
  have hbound := bound_of_getElem? hinstr
  unfold checkNonterminationExec at h; rw [List.all_eq_true] at h
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

/-- **Condition 5**: checkNonterminationExec → checkNonterminationProp -/
theorem checkNonterminationExec_sound (dc : ECertificate)
    (h : checkNonterminationExec dc = true) :
    checkNonterminationProp (toPCertificate dc) (toPMeasure dc) := by
  intro pc_t pc_t' σ_t σ_t' σ_o _ _ _ hexec horig_eq
  obtain ⟨c', hstep, hc'⟩ := hexec; subst hc'
  dsimp only [toPCertificate, toPMeasure] at horig_eq ⊢
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

/-- **Main Theorem**: If the executable checker accepts a certificate,
    then `PCertificateValid` holds for the corresponding Prop-based certificate.

    This connects the executable world (`Bool`) to the proof world (`Prop`):
    running `checkCertificateExec dc = true` is sufficient to guarantee
    that the transformation preserves all program behaviors. -/
-- Helper: decompose a chain of Bool.and into individual conjuncts
private theorem and_true_of_and_eq_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simp [Bool.and_eq_true] at h; exact h

theorem soundness_bridge (dc : ECertificate)
    (h : checkCertificateExec dc = true) :
    PCertificateValid (toPCertificate dc) (toPMeasure dc) := by
  -- checkCertificateExec is: c1 && c2 && c2c && c3 && c4 && c5 && c6 && c7
  -- && is left-associative, so decompose from right to left
  unfold checkCertificateExec at h
  have ⟨h17, h8⟩ := and_true_of_and_eq_true h
  have ⟨h16, h7⟩ := and_true_of_and_eq_true h17
  have ⟨h15, h6⟩ := and_true_of_and_eq_true h16
  have ⟨h14, h5⟩ := and_true_of_and_eq_true h15
  have ⟨h13, h4⟩ := and_true_of_and_eq_true h14
  have ⟨h12, h3⟩ := and_true_of_and_eq_true h13
  have ⟨h1, h2⟩  := and_true_of_and_eq_true h12
  -- Derive vm=[] at start from checkVarMapAtStartExec (h3)
  have hvm0 : (dc.instrCerts.getD 0 default).vm = [] := by
    revert h3; simp only [checkVarMapAtStartExec]
    cases (dc.instrCerts.getD 0 default).vm with
    | nil => intro; rfl
    | cons => simp [List.isEmpty]
  exact {
    start_corr    := checkStartCorrespondenceExec_sound dc h1 hvm0
    start_inv     := checkInvariantsAtStartExec_sound dc h2
    inv_preserved := checkInvariantsPreservedExec_sound dc h4
    transitions   := checkAllTransitionsExec_sound dc h5
    halt_corr     := checkHaltCorrespondenceExec_sound dc h6
    halt_obs      := checkHaltObservableExec_sound dc h7
    nonterm       := checkNonterminationExec_sound dc h8
  }

-- ============================================================
-- § 10. Why not iff?
-- ============================================================

/-!
## The converse does NOT hold

`PCertificateValid cert μ` does **not** imply `checkCertificateExec dc = true`
for several reasons:

1. **Expressiveness gap**: The Prop-based system supports arbitrary invariants
   (`Store → Prop`), while the executable system only supports `var = val` atoms.
   A certificate using `x < y` as an invariant is valid in the Prop world
   but has no representation in `ECertificate`.

2. **Variable map generality**: The Prop system supports arbitrary `PVarMap`s
   (`Var → Expr`), while the executable system supports `EVarMap` (finite
   association lists). The soundness proof handles non-trivial variable maps,
   but the executable representation is still less general.

3. **Information loss**: `toPCertificate` maps every `ECertificate` to a
   `PCertificate` with `eVarMapToVarMap` var maps and `EInv.toProp` invariants.
   Many different `PCertificate`s could satisfy `PCertificateValid` for the
   same programs, but only those expressible as `toPCertificate dc` for some `dc`
   are in the image of the translation.

The relationship is:

```
  checkCertificateExec dc = true
        ⟹
  PCertificateValid (toPCertificate dc) (toPMeasure dc)
        ⟹
  ∀ σ₀ b, program_behavior dc.trans σ₀ b →
    ∃ b', program_behavior dc.orig σ₀ b' ∧ ...
```

The executable checker is a **sufficient** but not **necessary** condition
for semantic preservation. It is a practical tool for certifying common
compiler optimizations (constant propagation, dead code elimination,
redundant assignment removal).
-/

-- ============================================================
-- § 11. End-to-end theorem
-- ============================================================

/-- **End-to-end correctness**: If the executable checker accepts,
    then every behavior of the transformed program has a corresponding
    behavior in the original program (with observable equivalence at halt).

    This is the composition of `soundness_bridge` and
    `credible_compilation_soundness` — the complete pipeline from
    `checkCertificateExec dc = true` to semantic preservation. -/
theorem exec_checker_correct (dc : ECertificate)
    (h : checkCertificateExec dc = true)
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
      (toPCertificate dc) (toPMeasure dc) (soundness_bridge dc h) σ₀ σ_t' htrans
    exact ⟨.halts σ_o', ho, hobs⟩
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toPCertificate dc) (toPMeasure dc) (soundness_bridge dc h) f σ₀ hinf hf0
    exact ⟨.diverges, ⟨g, hg, hg0⟩, trivial⟩
