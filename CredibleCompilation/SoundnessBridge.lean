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
  exact of_decide_eq_true h

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

/-- Convert an executable expression relation to a Prop-level store relation.
    Uses `buildSubstMap` to create a total store relation: for every variable `v`,
    `σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o`.
    Empty relations yield identity (σ_o = σ_t). -/
def eRelToStoreRel (rel : EExprRel) : PStoreRel :=
  fun σ_o σ_t => ∀ v, σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o

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
        storeRel   := eRelToStoreRel dic.rel
        transitions := dic.transitions.map fun dtc =>
          { origLabels   := dtc.origLabels
            storeRel     := eRelToStoreRel dtc.rel
            storeRel_next := eRelToStoreRel dtc.rel_next }
      }
    haltCerts := fun l =>
      let dhc := dc.haltCerts.getD l default
      { pc_orig := dhc.pc_orig
        storeRel := eRelToStoreRel dhc.rel }
    measure := fun l _ => dc.measure.getD l 0
  }

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
  · -- (na - x) + nb → (na + nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]
    congr 1; ring
  · -- (na - x) - nb → (na - nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]
    congr 1; ring
  · rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]
    congr 1; ring
  · rename_i na nb x
    simp only [Expr.eval, BinOp.eval, Value.toInt]
    congr 1; ring
  · -- na - (x - nb) → (na + nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]
    congr 1; ring
  · rfl

/-- Simplification preserves semantics: evaluating `e.simplify inv` in `σ`
    gives the same result as evaluating `e` in `σ`, provided `σ` satisfies `inv`. -/
theorem Expr.simplify_sound (inv : EInv) (e : Expr) (σ : Store)
    (hinv : EInv.toProp inv σ) :
    (e.simplify inv).eval σ = e.eval σ := by
  induction e with
  | lit n => simp [Expr.simplify, Expr.eval]
  | blit b => simp [Expr.simplify, Expr.eval]
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
      congr 1
      rw [show (a.eval σ).toInt = na from by rw [← iha]; rfl,
          show (b.eval σ).toInt = nb from by rw [← ihb]; rfl]
    · case h_2 =>
      rw [Expr.reassoc_sound]
      simp only [Expr.eval]
      rw [iha, ihb]
  | tobool _ => rfl
  | cmpE _ _ _ => rfl
  | cmpLitE _ _ _ => rfl
  | notE _ => rfl
  | andE _ _ => rfl
  | orE _ _ => rfl

-- ============================================================
-- § 5. Easy soundness lemmas
-- ============================================================

/-- **Condition 1**: checkStartCorrespondenceExec → checkStartCorrespondenceProp -/
theorem checkStartCorrespondenceExec_sound (dc : ECertificate)
    (h : checkStartCorrespondenceExec dc = true)
    (hrel0 : (dc.instrCerts.getD 0 default).rel = []) :
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
    · -- ∀ σ, storeRel σ σ
      have hrel_ic : ic.rel = [] := by
        have : (dc.instrCerts.getD 0 default).rel = ic.rel := by
          simp [Array.getD, dif_pos hbound, hget]
        rw [this] at hrel0; exact hrel0
      intro σ v
      simp only [Array.getD, dif_pos hbound]
      rw [show dc.instrCerts.getInternal 0 hbound = ic from hget]
      simp [hrel_ic, buildSubstMap, ssGet, Expr.eval]
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
  dsimp only [toPCertificate, eRelToStoreRel]
  intro hcons v hv
  -- From checker: ic.rel has an identity pair (.var v, .var v) for observable v at halt
  have hhalt' : dc.trans[pc_t]? = some .halt := hhalt
  unfold checkHaltObservableExec at h; rw [List.all_eq_true] at h
  have hpc := h pc_t (List.mem_range.mpr (bound_of_getElem? hhalt'))
  rw [hhalt'] at hpc; rw [List.all_eq_true] at hpc
  have hany := hpc v hv
  -- hany : ssGet (buildSubstMap ic.rel) v == .var v = true
  -- So ssGet (buildSubstMap ic.rel) v = .var v
  have hid := beq_iff_eq.mp hany
  -- hcons v : σ_t v = (ssGet (buildSubstMap ic.rel) v).eval σ_o
  rw [hcons v, hid]
  simp [Expr.eval]

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

private theorem BoolExpr.toSymExpr_sound (be : BoolExpr) (ss : SymStore) (σ₀ σ : Store)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ v) :
    (be.toSymExpr ss).eval σ₀ = .bool (be.eval σ) := by
  induction be with
  | bvar x =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
    rw [hrepr x]
  | cmp op x y =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
    rw [hrepr x, hrepr y]
  | cmpLit op x n =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
    rw [hrepr x]
  | not e ih =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
    rw [ih]; simp [Value.toBool]
  | and a b iha ihb =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
    rw [iha, ihb]; simp [Value.toBool]
  | or a b iha ihb =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
    rw [iha, ihb]; simp [Value.toBool]

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
    -- execSymbolic splits on val's constructor, so we case-split on val
    cases val with
    | int n =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .int n] := (Cfg.run.inj this).2.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
    | bool b =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .bool b] := (Cfg.run.inj this).2.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
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
    -- Extract int witnesses from hstep (Step.binop requires σ a = .int _ and σ b = .int _)
    obtain ⟨ia, ib, hia, hib, hsafe⟩ : ∃ ia ib : Int, σ a = .int ia ∧ σ b = .int ib ∧ op.safe ia ib := by
      cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ) (Cfg.run (pc + 1) (σ[dest ↦ .int (op.eval ia ib)])) :=
      Step.binop hinstr hia hib hsafe
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .int (op.eval ia ib)] := (Cfg.run.inj this).2.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have ha : ((ssGet ss a).eval σ₀).toInt = ia := by
        rw [hrepr a, hia]; rfl
      have hb : ((ssGet ss b).eval σ₀).toInt = ib := by
        rw [hrepr b, hib]; rfl
      rw [ha, hb]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | boolop dest be =>
    simp only [execSymbolic]
    have := step_det _ (Step.boolop hinstr)
    have hσ' : σ' = σ[dest ↦ .bool (be.eval σ)] := (Cfg.run.inj this).2.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Store.update_self]
      exact BoolExpr.toSymExpr_sound be ss σ₀ σ hrepr
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | goto l =>
    simp only [execSymbolic]
    have := step_det _ (Step.goto hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.symm
    rw [hσ']; exact hrepr v
  | ifgoto b l =>
    simp only [execSymbolic]
    by_cases hb : b.eval σ = true
    · have := step_det _ (Step.iftrue hinstr hb)
      have hσ' : σ' = σ := (Cfg.run.inj this).2.symm
      rw [hσ']; exact hrepr v
    · have := step_det _ (Step.iffall hinstr (Bool.eq_false_iff.mpr hb))
      have hσ' : σ' = σ := (Cfg.run.inj this).2.symm
      rw [hσ']; exact hrepr v
  | halt =>
    exfalso
    have := step_det _ (Step.halt hinstr)
    exact Cfg.noConfusion this

/-- Empty expression relation yields identity store relation. -/
private theorem eRelToStoreRel_nil : eRelToStoreRel [] = fun σ_o σ_t => σ_o = σ_t := by
  funext σ_o σ_t; simp [eRelToStoreRel, buildSubstMap, ssGet]
  constructor
  · intro h; funext v; simp [Expr.eval] at h; exact (h v).symm
  · intro h v; rw [h]; simp [Expr.eval]

/-- Identity store relation from empty expression relation means stores are equal. -/
private theorem eRelToStoreRel_nil_eq {σ₁ σ₂ : Store} (h : eRelToStoreRel [] σ₁ σ₂) :
    σ₁ = σ₂ := by
  rw [eRelToStoreRel_nil] at h; exact h

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
  | blit _ => simp [Expr.substSym]
  | var v => simp [Expr.substSym, ssGet_nil_var]
  | bin op a b iha ihb => simp [Expr.substSym, iha, ihb]
  | tobool e ih => simp [Expr.substSym, ih]
  | cmpE op a b iha ihb => simp [Expr.substSym, iha, ihb]
  | cmpLitE op a n ih => simp [Expr.substSym, ih]
  | notE e ih => simp [Expr.substSym, ih]
  | andE a b iha ihb => simp [Expr.substSym, iha, ihb]
  | orE a b iha ihb => simp [Expr.substSym, iha, ihb]

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
  | blit b => simp [Expr.substSym, Expr.eval]
  | var v => simp [Expr.substSym, Expr.eval]; exact hrepr v
  | bin op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | tobool e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | cmpE op a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | cmpLitE op a n ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | notE e ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]
  | andE a b iha ihb =>
    simp only [Expr.substSym, Expr.eval]; rw [iha, ihb]
  | orE a b iha ihb =>
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
  | boolop h => exact ⟨_, h⟩
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
  | boolop h => have := instr_eq h; subst this; simp [successors]
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
  | .boolop x _    => [x]
  | .ifgoto b _    => b.vars
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
    simp [instrVars] at hv
    cases n with
    | int k => simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
    | bool b => simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
  | copy x y =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | binop x op y z =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | boolop x _ =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv
  | goto _ => rfl
  | ifgoto _ _ => simp only [execSymbolic]
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

/-- If `isNonZeroLit e = true`, then either `e = .lit n` for some `n ≠ 0`,
    or `e = .blit true`. -/
private theorem isNonZeroLit_sound {e : Expr} (h : e.isNonZeroLit = true) :
    (∃ n, e = .lit n ∧ n ≠ 0) ∨ e = .blit true := by
  cases e with
  | lit n =>
    left; refine ⟨n, rfl, ?_⟩
    intro heq; subst heq; simp [Expr.isNonZeroLit] at h
  | blit b =>
    cases b with
    | true  => right; rfl
    | false => simp [Expr.isNonZeroLit] at h
  | var => simp [Expr.isNonZeroLit] at h
  | bin => simp [Expr.isNonZeroLit] at h
  | tobool _ | cmpE _ _ _ | cmpLitE _ _ _ | notE _ | andE _ _ | orE _ _ => simp [Expr.isNonZeroLit] at h

/-- Soundness of `BoolExpr.symEval`: if symbolic evaluation returns a result,
    it agrees with runtime evaluation. -/
private theorem BoolExpr.symEval_sound (b : BoolExpr) (ss : SymStore) (inv : EInv)
    (σ₀ σ : Store)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ v)
    (hinv : EInv.toProp inv σ₀)
    (r : Bool) (heval : b.symEval ss inv = some r) :
    b.eval σ = r := by
  induction b generalizing r with
  | bvar x =>
    simp only [BoolExpr.symEval] at heval
    generalize hsx : (ssGet ss x).simplify inv = sx at heval
    cases sx <;> simp at heval
    case blit b =>
      simp [BoolExpr.eval]
      have hxa := Expr.simplify_sound inv (ssGet ss x) σ₀ hinv
      rw [hsx, Expr.eval] at hxa
      rw [← hrepr x, ← hxa]
      simp [Value.toBool, heval]
  | cmp op x y =>
    simp only [BoolExpr.symEval] at heval
    -- Both variables must simplify to literals
    generalize hsx : (ssGet ss x).simplify inv = sx at heval
    generalize hsy : (ssGet ss y).simplify inv = sy at heval
    cases sx <;> cases sy <;> simp at heval
    case lit.lit a b =>
      simp [BoolExpr.eval]
      have hxa := Expr.simplify_sound inv (ssGet ss x) σ₀ hinv
      have hya := Expr.simplify_sound inv (ssGet ss y) σ₀ hinv
      rw [hsx, Expr.eval] at hxa; rw [hsy, Expr.eval] at hya
      rw [← hrepr x, ← hxa, ← hrepr y, ← hya]
      exact heval
  | cmpLit op x n =>
    simp only [BoolExpr.symEval] at heval
    generalize hsx : (ssGet ss x).simplify inv = sx at heval
    cases sx <;> simp at heval
    case lit a =>
      simp [BoolExpr.eval]
      have hxa := Expr.simplify_sound inv (ssGet ss x) σ₀ hinv
      rw [hsx, Expr.eval] at hxa
      rw [← hrepr x, ← hxa]
      exact heval
  | not e ih =>
    simp only [BoolExpr.symEval, Option.map] at heval
    cases he : e.symEval ss inv <;> simp [he] at heval
    case some val =>
      have := ih val he
      simp [BoolExpr.eval, this]
      exact heval
  | and a b iha ihb =>
    simp only [BoolExpr.symEval] at heval
    cases ha : a.symEval ss inv <;> simp [ha] at heval
    case some va =>
      cases hb : b.symEval ss inv <;> simp [hb] at heval
      case some vb =>
        simp [BoolExpr.eval, iha va ha, ihb vb hb]
        exact heval
  | or a b iha ihb =>
    simp only [BoolExpr.symEval] at heval
    cases ha : a.symEval ss inv <;> simp [ha] at heval
    case some va =>
      cases hb : b.symEval ss inv <;> simp [hb] at heval
      case some vb =>
        simp [BoolExpr.eval, iha va ha, ihb vb hb]
        exact heval

/-- Generalized path execution soundness with arbitrary initial symbolic store.
    The path check includes symbolic branch-direction verification for ifgoto.
    `branchInfo` provides the branch direction for the first step's ifgoto when
    symbolic analysis is inconclusive. `hbranch` guarantees the runtime store
    matches the branch direction. -/
private theorem execPath_sound_gen (orig : Prog) (ss : SymStore) (inv : EInv)
    (σ₀ σ : Store) (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (BoolExpr × Bool))
    (Γ : TyCtx) (hwtp : WellTypedProg Γ orig) (hts : TypedStore Γ σ)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ = σ v)
    (hinv : EInv.toProp inv σ₀)
    (hpath : checkOrigPath orig ss inv pc labels pc' branchInfo = true)
    (hbranch : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.eval σ = taken) :
    ∃ σ', Steps orig (Cfg.run pc σ) (Cfg.run pc' σ') ∧
          ∀ v, (ssGet (execPath orig ss pc labels) v).eval σ₀ = σ' v := by
  induction labels generalizing pc σ ss branchInfo with
  | nil =>
    simp only [checkOrigPath, beq_iff_eq] at hpath
    exact ⟨σ, hpath ▸ Steps.refl, hrepr⟩
  | cons nextPC rest ih =>
    unfold checkOrigPath at hpath
    -- Extract the instruction at pc
    generalize horig_opt : orig[pc]? = opt_instr at hpath
    cases opt_instr with
    | none => simp at hpath
    | some instr =>
      rw [Bool.and_eq_true] at hpath
      have ⟨h12, hpath_inner⟩ := hpath
      rw [Bool.and_eq_true] at h12
      have ⟨hnext_eq, hsafe_check⟩ := h12
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
            -- Derive int witnesses from well-typedness
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .binop x op y z :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨a, hya⟩ : ∃ a : Int, σ y = .int a := by
              cases hwti with | binop _ hy _ =>
              exact Value.int_of_typeOf_int (by rw [hts y]; exact hy)
            obtain ⟨b, hzb⟩ : ∃ b : Int, σ z = .int b := by
              cases hwti with | binop _ _ hz =>
              exact Value.int_of_typeOf_int (by rw [hts z]; exact hz)
            have hsafe : op.safe a b := by
              cases op with
              | div =>
                simp only [checkBinopSafe] at hsafe_check
                generalize hz_simp : (ssGet ss z).simplify inv = sz at hsafe_check
                cases sz with
                | lit n =>
                  simp at hsafe_check
                  have hne : n ≠ 0 := hsafe_check
                  have hsimp := Expr.simplify_sound inv (ssGet ss z) σ₀ hinv
                  rw [hz_simp, Expr.eval] at hsimp
                  have hzval : σ z = .int n := by rw [← hrepr z]; exact hsimp.symm
                  rw [hzb] at hzval; exact Value.int.inj hzval ▸ hne
                | _ => simp at hsafe_check
              | add | sub | mul => trivial
            exact ⟨σ[x ↦ .int (op.eval a b)], Step.binop horig_opt hya hzb hsafe,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.binop horig_opt hya hzb hsafe) horig_opt⟩
          | boolop x be =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ[x ↦ .bool (be.eval σ)], Step.boolop horig_opt,
              execSymbolic_sound ss _ σ₀ σ _ pc _ orig hrepr (Step.boolop horig_opt) horig_opt⟩
          | goto l =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            exact ⟨σ, Step.goto horig_opt,
              execSymbolic_sound ss _ σ₀ σ σ pc l orig hrepr (Step.goto horig_opt) horig_opt⟩
          | ifgoto b l =>
            have hexec_id : execSymbolic ss (.ifgoto b l) = ss := rfl
            simp only [computeNextPC] at hnext_opt
            -- computeNextPC returned some, so b.symEval returned some
            cases hsym : b.symEval ss inv <;> simp [hsym] at hnext_opt
            case some r =>
              cases r with
              | true =>
                simp at hnext_opt
                have hpc_eq : nextPC = l := hnext_opt.symm
                rw [hpc_eq]
                have heval := BoolExpr.symEval_sound b ss inv σ₀ σ hrepr hinv true hsym
                exact ⟨σ, Step.iftrue horig_opt heval, hexec_id ▸ hrepr⟩
              | false =>
                simp at hnext_opt
                have hpc_eq : nextPC = pc + 1 := hnext_opt.symm
                rw [hpc_eq]
                have heval := BoolExpr.symEval_sound b ss inv σ₀ σ hrepr hinv false hsym
                exact ⟨σ, Step.iffall horig_opt heval, hexec_id ▸ hrepr⟩
          | halt =>
            simp [computeNextPC] at hnext_opt
        | none =>
          -- computeNextPC returned none; use branchInfo fallback
          cases hbi : branchInfo with
          | none =>
            exfalso; revert hnext_eq; rw [hbi]; simp
          | some bi =>
            obtain ⟨origCond, taken⟩ := bi
            cases instr with
            | ifgoto b l_orig =>
              have hexec_id : execSymbolic ss (.ifgoto b l_orig) = ss := rfl
              -- The fallback checks b == origCond
              cases taken with
              | true =>
                have hfb : (b == origCond && nextPC == l_orig) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hbeq, hpc_eq⟩ := and_true_split hfb
                have hbeq := beq_iff_eq.mp hbeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have heval : b.eval σ = true := by
                  rw [hbeq]; exact hbranch origCond true (hbi ▸ rfl)
                exact ⟨σ, Step.iftrue horig_opt heval, hexec_id ▸ hrepr⟩
              | false =>
                have hfb : (b == origCond && nextPC == pc + 1) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hbeq, hpc_eq⟩ := and_true_split hfb
                have hbeq := beq_iff_eq.mp hbeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have heval : b.eval σ = false := by
                  rw [hbeq]; exact hbranch origCond false (hbi ▸ rfl)
                exact ⟨σ, Step.iffall horig_opt heval, hexec_id ▸ hrepr⟩
            | _ =>
              exfalso; revert hnext_eq; rw [hbi]; cases taken <;> simp
      -- Recursive step (branchInfo = none for rest)
      have hexec : execPath orig ss pc (nextPC :: rest) =
          execPath orig (execSymbolic ss instr) nextPC rest := by
        simp [execPath, horig_opt]
      have hts₁ : TypedStore Γ σ₁ :=
        type_preservation hwtp hts (bound_of_getElem? horig_opt) hstep_orig
      obtain ⟨σ', hsteps_rest, hrepr_final⟩ :=
        ih (execSymbolic ss instr) σ₁ nextPC none hts₁ hrepr'
          hpath_inner (fun _ _ h => by simp at h)
      exact ⟨σ', Steps.step hstep_orig hsteps_rest, hexec ▸ hrepr_final⟩

/-- Path execution soundness: specialization with empty initial symbolic store. -/
private theorem execPath_sound (orig : Prog) (inv : EInv) (σ : Store)
    (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (BoolExpr × Bool))
    (Γ : TyCtx) (hwtp : WellTypedProg Γ orig) (hts : TypedStore Γ σ)
    (hrepr : ∀ v, (ssGet ([] : SymStore) v).eval σ = σ v)
    (hinv : EInv.toProp inv σ)
    (hpath : checkOrigPath orig ([] : SymStore) inv pc labels pc' branchInfo = true)
    (hbranch : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.eval σ = taken) :
    ∃ σ', Steps orig (Cfg.run pc σ) (Cfg.run pc' σ') ∧
          ∀ v, (ssGet (execPath orig ([] : SymStore) pc labels) v).eval σ = σ' v :=
  execPath_sound_gen orig ([] : SymStore) inv σ σ pc labels pc' branchInfo
    Γ hwtp hts hrepr hinv hpath hbranch

/-- If the store relation holds (∀ x, σ_t x = (ssGet ss x).eval σ_o), then evaluating
    `e` at `σ_t` equals evaluating `e.substSym ss` at `σ_o`. Follows from `substSym_sound`. -/
theorem Expr.substSym_consistent (ss : SymStore) (e : Expr) (σ_o σ_t : Store)
    (hcons : ∀ x, σ_t x = (ssGet ss x).eval σ_o) :
    e.eval σ_t = (e.substSym ss).eval σ_o :=
  (Expr.substSym_sound ss e σ_o σ_t (fun v => (hcons v).symm)).symm

/-- BEq on Expr implies equality. -/
private theorem expr_beq_eq {e₁ e₂ : Expr} (h : (e₁ == e₂) = true) : e₁ = e₂ :=
  beq_iff_eq.mp h

/-- Array.getD on empty array returns the default. -/
private theorem Array_getD_empty {α : Type} (n : Nat) (d : α) :
    Array.getD #[] n d = d := by
  simp [Array.getD]

/-- `relGetOrigExpr` and `ssGet (buildSubstMap ...)` agree: both find the first
    pair `(e_o, .var x)` in `rel` and return `e_o`, or default to `.var x`. -/
private theorem relGetOrigExpr_eq_ssGet_buildSubstMap (rel : EExprRel) (x : Var) :
    relGetOrigExpr rel x = ssGet (buildSubstMap rel) x := by
  induction rel with
  | nil => simp [relGetOrigExpr, buildSubstMap, ssGet, List.find?, List.filterMap]
  | cons p rest ih =>
    obtain ⟨e_o, e_t⟩ := p
    cases e_t with
    | var w =>
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, ssGet]
      by_cases hwx : w = x
      · subst hwx
        simp [BEq.beq]
      · have hbeq_expr : (Expr.var w == Expr.var x) = false := by
          rw [beq_eq_false_iff_ne]; intro h; exact hwx (Expr.var.inj h)
        have hbeq_var : (w == x) = false := beq_eq_false_iff_ne.mpr hwx
        simp only [hbeq_expr, hbeq_var]
        exact ih
    | lit n =>
      have hbeq : (Expr.lit n == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | blit b =>
      have hbeq : (Expr.blit b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | bin op a b =>
      have hbeq : (Expr.bin op a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | tobool e =>
      have hbeq : (Expr.tobool e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | cmpE op a b =>
      have hbeq : (Expr.cmpE op a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | cmpLitE op a n =>
      have hbeq : (Expr.cmpLitE op a n == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | notE e =>
      have hbeq : (Expr.notE e == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | andE a b =>
      have hbeq : (Expr.andE a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih
    | orE a b =>
      have hbeq : (Expr.orE a b == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih

/-- If `b.mapVarsRel rel = some origCond`, then `b.eval σ_t = origCond.eval σ_o`
    when the store relation holds through `buildSubstMap`. -/
private theorem BoolExpr.eval_mapVarsRel (b origCond : BoolExpr)
    (rel : EExprRel) (σ_t σ_o : Store)
    (hmap : b.mapVarsRel rel = some origCond)
    (hcons : ∀ x, σ_t x = (ssGet (buildSubstMap rel) x).eval σ_o) :
    b.eval σ_t = origCond.eval σ_o := by
  induction b generalizing origCond with
  | bvar x =>
    simp only [BoolExpr.mapVarsRel] at hmap
    cases hx : relGetOrigExpr rel x <;> simp [hx] at hmap
    case var x' =>
      rw [← hmap]
      simp [BoolExpr.eval]
      have hsx : ssGet (buildSubstMap rel) x = Expr.var x' := by
        rw [← relGetOrigExpr_eq_ssGet_buildSubstMap]; exact hx
      rw [hcons x, hsx]; simp [Expr.eval]
  | cmp op x y =>
    simp only [BoolExpr.mapVarsRel] at hmap
    cases hx : relGetOrigExpr rel x <;> simp [hx] at hmap
    case var x' =>
      cases hy : relGetOrigExpr rel y <;> simp [hy] at hmap
      case var y' =>
        rw [← hmap]
        simp [BoolExpr.eval]
        have hsx : ssGet (buildSubstMap rel) x = Expr.var x' := by
          rw [← relGetOrigExpr_eq_ssGet_buildSubstMap]; exact hx
        have hsy : ssGet (buildSubstMap rel) y = Expr.var y' := by
          rw [← relGetOrigExpr_eq_ssGet_buildSubstMap]; exact hy
        rw [hcons x, hsx, hcons y, hsy]; simp [Expr.eval]
  | cmpLit op x n =>
    simp only [BoolExpr.mapVarsRel] at hmap
    cases hx : relGetOrigExpr rel x <;> simp [hx] at hmap
    case var x' =>
      rw [← hmap]
      simp [BoolExpr.eval]
      have hsx : ssGet (buildSubstMap rel) x = Expr.var x' := by
        rw [← relGetOrigExpr_eq_ssGet_buildSubstMap]; exact hx
      rw [hcons x, hsx]; simp [Expr.eval]
  | not e ih =>
    simp only [BoolExpr.mapVarsRel, Option.map] at hmap
    cases he : e.mapVarsRel rel <;> simp [he] at hmap
    case some e' =>
      rw [← hmap]; simp [BoolExpr.eval, ih e' he]
  | and a b iha ihb =>
    simp only [BoolExpr.mapVarsRel] at hmap
    cases ha : a.mapVarsRel rel <;> simp [ha] at hmap
    case some a' =>
      cases hb : b.mapVarsRel rel <;> simp [hb] at hmap
      case some b' =>
        rw [← hmap]; simp [BoolExpr.eval, iha a' ha, ihb b' hb]
  | or a b iha ihb =>
    simp only [BoolExpr.mapVarsRel] at hmap
    cases ha : a.mapVarsRel rel <;> simp [ha] at hmap
    case some a' =>
      cases hb : b.mapVarsRel rel <;> simp [hb] at hmap
      case some b' =>
        rw [← hmap]; simp [BoolExpr.eval, iha a' ha, ihb b' hb]

/-- Branch direction info from the transformed program's ifgoto instruction.
    For `ifgoto b l` with `l ≠ pc + 1`, returns `some (b, pc' == l)` indicating
    the condition and whether the branch was taken. -/
@[reducible] private def transBranchInfo (instr : TAC) (pc_t pc_t' : Label) : Option (BoolExpr × Bool) :=
  match instr with
  | .ifgoto b l => if !(l == pc_t + 1) then some (b, pc_t' == l) else none
  | _ => none

/-- Compute branchInfo from an instruction and an expression relation.
    Maps the condition's variables through the relation. -/
@[reducible] private def branchInfoWithRel (instr : TAC) (rel : EExprRel) (pc_t pc_t' : Label)
    : Option (BoolExpr × Bool) :=
  match instr with
  | .ifgoto b l =>
    match b.mapVarsRel rel with
    | some origCond => if !(l == pc_t + 1) then some (origCond, pc_t' == l) else none
    | none => none
  | _ => none

/-- With empty relation, branchInfoWithRel equals transBranchInfo. -/
private theorem branchInfoWithRel_nil (instr : TAC) (pc_t pc_t' : Label) :
    branchInfoWithRel instr ([] : EExprRel) pc_t pc_t' = transBranchInfo instr pc_t pc_t' := by
  cases instr with
  | ifgoto b l =>
    simp only [branchInfoWithRel, transBranchInfo]
    -- With empty relation, mapVarsRel returns some b (identity mapping)
    suffices h : b.mapVarsRel ([] : EExprRel) = some b by simp [h]
    induction b with
    | bvar x => simp [BoolExpr.mapVarsRel, relGetOrigExpr, List.find?]
    | cmp op x y => simp [BoolExpr.mapVarsRel, relGetOrigExpr, List.find?]
    | cmpLit op x n => simp [BoolExpr.mapVarsRel, relGetOrigExpr, List.find?]
    | not e ih => simp [BoolExpr.mapVarsRel, ih, Option.map]
    | and a b iha ihb => simp [BoolExpr.mapVarsRel, iha, ihb]
    | or a b iha ihb => simp [BoolExpr.mapVarsRel, iha, ihb]
  | _ => simp [branchInfoWithRel, transBranchInfo]

/-- When `transBranchInfo` returns `some (cond, taken)`,
    we can derive `cond.eval σ = taken` from any step. -/
private theorem branchInfo_of_step {prog : Prog} {pc pc' : Label} {σ σ' : Store}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ) (Cfg.run pc' σ'))
    {cond : BoolExpr} {taken : Bool}
    (hbi : transBranchInfo instr pc pc' = some (cond, taken)) :
    cond.eval σ = taken := by
  cases instr with
  | ifgoto b l =>
    simp only [transBranchInfo] at hbi
    by_cases hguard : (!(l == pc + 1))
    · simp only [hguard, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hbi
      obtain ⟨rfl, rfl⟩ := hbi
      -- cond = b, taken = (pc' == l)
      cases hstep with
      | iftrue h heval =>
        have heq := Option.some.inj (hinstr.symm.trans h)
        simp only [TAC.ifgoto.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp [heval]
      | iffall h heval =>
        have heq := Option.some.inj (hinstr.symm.trans h)
        simp only [TAC.ifgoto.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have : ¬(l = pc + 1) := by simpa using hguard
        have : ¬(pc + 1 = l) := fun h => this h.symm
        simp [beq_eq_false_iff_ne.mpr this, heval]
      | const h => exact absurd (hinstr.symm.trans h) (by simp)
      | copy h => exact absurd (hinstr.symm.trans h) (by simp)
      | binop h => exact absurd (hinstr.symm.trans h) (by simp)
      | boolop h => exact absurd (hinstr.symm.trans h) (by simp)
      | goto h => exact absurd (hinstr.symm.trans h) (by simp)
    · simp [hguard] at hbi
  | _ => simp [transBranchInfo] at hbi

/-- When `branchInfoWithRel` returns `some (origCond, taken)`, a step on the
    transformed program implies `origCond.eval σ_o = taken`
    via the store relation and `eval_mapVarsRel`. -/
private theorem branchInfo_of_step_with_rel {prog : Prog} {pc pc' : Label} {σ_t σ_t' : Store}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ_t) (Cfg.run pc' σ_t'))
    {rel : EExprRel} {σ_o : Store}
    (hcons : ∀ x, σ_t x = (ssGet (buildSubstMap rel) x).eval σ_o)
    {origCond : BoolExpr} {taken : Bool}
    (hbi : branchInfoWithRel instr rel pc pc' = some (origCond, taken)) :
    origCond.eval σ_o = taken := by
  cases instr with
  | ifgoto b l =>
    simp only [branchInfoWithRel] at hbi
    cases hmap : b.mapVarsRel rel with
    | none => simp [hmap] at hbi
    | some origCond' =>
      simp only [hmap] at hbi
      by_cases hguard : (!(l == pc + 1))
      · simp only [hguard, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hbi
        obtain ⟨rfl, rfl⟩ := hbi
        -- Use transBranchInfo to get b.eval σ_t = taken
        have htbi : transBranchInfo (.ifgoto b l) pc pc' = some (b, pc' == l) := by
          simp [transBranchInfo, hguard]
        have hbranch := branchInfo_of_step hinstr hstep htbi
        -- Transfer via eval_mapVarsRel: b.eval σ_t = origCond'.eval σ_o
        have heval := BoolExpr.eval_mapVarsRel b origCond' rel σ_t σ_o hmap hcons
        rw [← heval]; exact hbranch
      · simp [hguard] at hbi
  | _ => simp [branchInfoWithRel] at hbi

/-- Soundness of checkTransitionRelProp from the Bool checks.
    Given: checkOrigPath and checkRelConsistency both pass, the original path
    produces steps reaching the target with store relation preserved.
    Supports non-trivial expression relations. -/
private theorem transRel_sound (dc : ECertificate)
    (Γ : TyCtx) (hwtp : WellTypedProg Γ dc.orig)
    (pc_t pc_t' : Label)
    (dic : EInstrCert) (dtc : ETransCorr) (instr : TAC)
    (pc_o' : Label)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hpath : checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dic.pc_orig dtc.origLabels pc_o'
      (branchInfoWithRel instr dtc.rel pc_t pc_t') = true)
    (hrelcheck : checkRelConsistency
      dc.orig dic.pc_orig dtc.origLabels instr
      (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dtc.rel dtc.rel_next (collectAllVars dc.orig dc.trans) = true) :
    checkTransitionRelProp Γ dc.orig dc.trans
      (fun l => (dc.inv_orig.getD l ([] : EInv)).toProp)
      (fun l => (dc.inv_trans.getD l ([] : EInv)).toProp)
      pc_t pc_t' dic.pc_orig pc_o'
      { origLabels := dtc.origLabels
        storeRel := eRelToStoreRel dtc.rel
        storeRel_next := eRelToStoreRel dtc.rel_next } := by
  intro σ_t σ_t' σ_o hinv_t hinv_o hcons hts_o hstep
  -- hcons : eRelToStoreRel dtc.rel σ_o σ_t, i.e. ∀ x, σ_t x = (ssGet (buildSubstMap dtc.rel) x).eval σ_o
  change ∀ x, σ_t x = (ssGet (buildSubstMap dtc.rel) x).eval σ_o at hcons
  -- Branch info transfers through the relation
  have hbranch_orig : ∀ cond taken,
      branchInfoWithRel instr dtc.rel pc_t pc_t' = some (cond, taken) →
      cond.eval σ_o = taken :=
    fun cond taken hbi => branchInfo_of_step_with_rel hinstr hstep hcons hbi
  -- Execute original path from σ_o
  obtain ⟨σ_o', horig_steps, horig_repr⟩ := execPath_sound dc.orig
    (dc.inv_orig.getD dic.pc_orig ([] : EInv)) σ_o
    dic.pc_orig dtc.origLabels pc_o'
    (branchInfoWithRel instr dtc.rel pc_t pc_t')
    Γ hwtp hts_o (ssGet_nil σ_o) hinv_o hpath hbranch_orig
  -- Prove store relation holds at the target: eRelToStoreRel dtc.rel_next σ_o' σ_t'
  refine ⟨σ_o', horig_steps, ?_⟩
  -- Goal: ∀ v, σ_t' v = (ssGet (buildSubstMap dtc.rel_next) v).eval σ_o'
  intro v
  -- Abbreviations
  let origSS := execPath dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels
  let transSS := execSymbolic ([] : SymStore) instr
  let preSubst := buildSubstMap dtc.rel
  let postSubst := buildSubstMap dtc.rel_next
  let inv := dc.inv_orig.getD dic.pc_orig ([] : EInv)
  let allVars := collectAllVars dc.orig dc.trans
  -- execSymbolic_sound: transSS tracks the transformed step
  have htrans_repr : ∀ w, (ssGet transSS w).eval σ_t = σ_t' w :=
    execSymbolic_sound ([] : SymStore) instr σ_t σ_t σ_t' pc_t pc_t' dc.trans
      (ssGet_nil σ_t) hstep hinstr
  -- preSubst soundness: (ssGet preSubst w).eval σ_o = σ_t w
  have hpre_sound : ∀ w, (ssGet preSubst w).eval σ_o = σ_t w :=
    fun w => (hcons w).symm
  -- substSym_sound for preSubst: for any expr e, (e.substSym preSubst).eval σ_o = e.eval σ_t
  have hpre_subst : ∀ (e : Expr), (e.substSym preSubst).eval σ_o = e.eval σ_t :=
    fun e => Expr.substSym_sound preSubst e σ_o σ_t hpre_sound
  -- Classify v: either in the checked variable set or not in any program variable
  by_cases hmem : v ∈ allVars ++ preSubst.map Prod.fst ++ postSubst.map Prod.fst
  · -- Case 1: v is in the checked set — use the checker result
    -- Extract the checker guarantee for v
    unfold checkRelConsistency at hrelcheck
    rw [List.all_eq_true] at hrelcheck
    have hcheck_v := hrelcheck v hmem
    have hbeq := beq_iff_eq.mp hcheck_v
    -- hbeq : ((ssGet postSubst v).substSym origSS).simplify inv =
    --         ((ssGet transSS v).substSym preSubst).simplify inv
    -- By simplify_sound (σ_o satisfies inv):
    have hlhs := Expr.simplify_sound inv ((ssGet postSubst v).substSym origSS) σ_o hinv_o
    have hrhs := Expr.simplify_sound inv ((ssGet transSS v).substSym preSubst) σ_o hinv_o
    -- Chain the equalities
    calc σ_t' v
        = (ssGet transSS v).eval σ_t := (htrans_repr v).symm
      _ = ((ssGet transSS v).substSym preSubst).eval σ_o := (hpre_subst _).symm
      _ = (((ssGet transSS v).substSym preSubst).simplify inv).eval σ_o := hrhs.symm
      _ = (((ssGet postSubst v).substSym origSS).simplify inv).eval σ_o := by rw [hbeq]
      _ = ((ssGet postSubst v).substSym origSS).eval σ_o := hlhs
      _ = (ssGet postSubst v).eval σ_o' :=
            Expr.substSym_sound origSS (ssGet postSubst v) σ_o σ_o' horig_repr
  · -- Case 2: v not in any program variable or relation key
    -- v ∉ allVars, v ∉ preSubst keys, v ∉ postSubst keys
    simp only [List.mem_append, not_or] at hmem
    obtain ⟨⟨hv_allvars, hv_pre⟩, hv_post⟩ := hmem
    -- postSubst doesn't map v: ssGet postSubst v = .var v
    have hpost_id : ssGet postSubst v = Expr.var v := ssGet_not_key hv_post
    -- preSubst doesn't map v: ssGet preSubst v = .var v
    have hpre_id : ssGet preSubst v = Expr.var v := ssGet_not_key hv_pre
    -- From hcons: σ_t v = (.var v).eval σ_o = σ_o v
    have hσ_eq : σ_t v = σ_o v := by rw [hcons v, hpre_id]; simp [Expr.eval]
    -- v not in any instruction of trans: transSS preserves v
    have hv_trans : v ∉ instrVars instr := by
      intro hv
      exact hv_allvars (instrVars_sub_collectAllVars_right dc.orig dc.trans instr
        (getElem?_mem_toList hinstr) v hv)
    have htrans_id : ssGet transSS v = Expr.var v := by
      show ssGet (execSymbolic ([] : SymStore) instr) v = Expr.var v
      rw [execSymbolic_preserves_var ([] : SymStore) instr v hv_trans]
      exact ssGet_nil_var v
    -- v not in any instruction of orig: origSS preserves v
    have horig_id : ssGet origSS v = Expr.var v := by
      show ssGet (execPath dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels) v = Expr.var v
      rw [execPath_preserves_var dc.orig ([] : SymStore) dic.pc_orig dtc.origLabels v
        (fun l instr' hinstr' hv => hv_allvars
          (instrVars_sub_collectAllVars_left dc.orig dc.trans instr'
            (getElem?_mem_toList hinstr') v hv))]
      exact ssGet_nil_var v
    -- Chain: σ_t' v = σ_t v = σ_o v = σ_o' v = (.var v).eval σ_o'
    calc σ_t' v
        = (ssGet transSS v).eval σ_t := (htrans_repr v).symm
      _ = (Expr.var v).eval σ_t := by rw [htrans_id]
      _ = σ_t v := by simp [Expr.eval]
      _ = σ_o v := hσ_eq
      _ = (Expr.var v).eval σ_o := by simp [Expr.eval]
      _ = (ssGet origSS v).eval σ_o := by rw [horig_id]
      _ = σ_o' v := horig_repr v
      _ = (Expr.var v).eval σ_o' := by simp [Expr.eval]
      _ = (ssGet postSubst v).eval σ_o' := by rw [hpost_id]

/-- Extract Bool information from checkAllTransitionsExec for a specific step. -/
private theorem extractTransCheck (dc : ECertificate)
    (h : checkAllTransitionsExec dc = true)
    (pc_t pc_t' : Label) (instr : TAC)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hne : instr ≠ .halt)
    (hsucc : pc_t' ∈ successors instr pc_t) :
    ∃ dic, dc.instrCerts[pc_t]? = some dic ∧
    ∃ dtc ∈ dic.transitions,
      dtc.rel = dic.rel ∧
      dtc.rel_next = (dc.instrCerts.getD pc_t' default).rel ∧
      checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithRel instr dic.rel pc_t pc_t') = true ∧
      checkRelConsistency
        dc.orig dic.pc_orig dtc.origLabels instr
        (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dtc.rel dtc.rel_next (collectAllVars dc.orig dc.trans) = true := by
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
      -- Decompose: tc.rel == ic.rel && tc.rel_next == ic'.rel && path && relcheck
      rw [Bool.and_eq_true] at hdtc_check
      obtain ⟨h123, hrel_check⟩ := hdtc_check
      rw [Bool.and_eq_true] at h123
      obtain ⟨h12, hpath⟩ := h123
      rw [Bool.and_eq_true] at h12
      obtain ⟨hrel_eq, hrel_next_eq⟩ := h12
      refine ⟨dic, rfl, dtc, hdtc_mem,
        beq_iff_eq.mp hrel_eq, beq_iff_eq.mp hrel_next_eq, hpath, hrel_check⟩
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
      obtain ⟨h123, hrel_check⟩ := hdtc_check
      rw [Bool.and_eq_true] at h123
      obtain ⟨h12, hpath⟩ := h123
      rw [Bool.and_eq_true] at h12
      obtain ⟨hrel_eq, hrel_next_eq⟩ := h12
      refine ⟨dic, rfl, dtc, hdtc_mem,
        beq_iff_eq.mp hrel_eq, beq_iff_eq.mp hrel_next_eq, hpath, hrel_check⟩

/-- Relate getD to getElem? for arrays. -/
private theorem array_getD_of_getElem? {α : Type} {arr : Array α} {n : Nat} {val d : α}
    (h : arr[n]? = some val) : arr.getD n d = val := by
  have hb := bound_of_getElem? h
  have heq := (getElem?_eq_some_iff.mp h).2
  simp [Array.getD, dif_pos hb, heq]

/-- **Condition 3**: checkAllTransitionsExec → checkAllTransitionsProp -/
theorem checkAllTransitionsExec_sound (dc : ECertificate)
    (Γ : TyCtx) (hwtp : WellTypedProg Γ dc.orig)
    (h : checkAllTransitionsExec dc = true) :
    checkAllTransitionsProp Γ (toPCertificate dc) := by
  intro pc_t σ_t σ_t' pc_t' hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hne_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic (Step.halt hinstr) hstep)
  have hsucc := step_successor hstep hinstr
  -- Extract Bool-level information
  obtain ⟨dic, hdic, dtc, hdtc_mem, hrel_eq, hrel_next_eq, hpath, hrelcheck⟩ :=
    extractTransCheck dc h pc_t pc_t' instr hinstr hne_halt hsucc
  -- The tc in toPCertificate's transitions that corresponds to dtc
  let tc : PTransCorr :=
    { origLabels := dtc.origLabels
      storeRel := eRelToStoreRel dtc.rel
      storeRel_next := eRelToStoreRel dtc.rel_next }
  -- Show tc is in (toPCertificate dc).instrCerts pc_t).transitions
  have hgetD : dc.instrCerts.getD pc_t default = dic := array_getD_of_getElem? hdic
  have htc_mem : tc ∈ ((toPCertificate dc).instrCerts pc_t).transitions := by
    simp only [toPCertificate, hgetD]
    show tc ∈ dic.transitions.map _
    exact List.mem_map.mpr ⟨dtc, hdtc_mem, rfl⟩
  refine ⟨tc, htc_mem, ?_, ?_, ?_⟩
  -- 1. tc.storeRel = ic.storeRel
  · simp only [toPCertificate, hgetD, tc]
    exact congrArg eRelToStoreRel hrel_eq
  -- 2. tc.storeRel_next = ic'.storeRel
  · simp only [toPCertificate, tc]
    exact congrArg eRelToStoreRel hrel_next_eq
  -- 3. checkTransitionRelProp
  · -- Use the branchInfo with the actual rel (dtc.rel = dic.rel)
    have hpath' : checkOrigPath dc.orig ([] : SymStore) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithRel instr dtc.rel pc_t pc_t') = true := by
      rw [hrel_eq]; exact hpath
    simp only [toPCertificate, hgetD]
    exact transRel_sound dc Γ hwtp pc_t pc_t' dic dtc instr
      ((dc.instrCerts.getD pc_t' default).pc_orig)
      hinstr hpath' hrelcheck

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
    checkNonterminationProp (toPCertificate dc) := by
  intro pc_t pc_t' σ_t σ_t' σ_o _ _ _ hexec horig_eq
  obtain ⟨c', hstep, hc'⟩ := hexec; subst hc'
  dsimp only [toPCertificate] at horig_eq ⊢
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hinstr' : dc.trans[pc_t]? = some instr := hinstr
  have not_halt : instr ≠ .halt := by
    intro heq; subst heq
    exact Cfg.noConfusion (Step.deterministic hstep (Step.halt hinstr))
  exact nonterm_inner dc h pc_t pc_t' instr hinstr' not_halt
    (step_successor hstep hinstr) horig_eq

-- ============================================================
-- § 8b. Div-preservation soundness
-- ============================================================

/-- If `checkDivPreservationExec` passes, then `checkStuckPreservationProp` holds. -/
theorem checkDivPreservationExec_sound (dc : ECertificate)
    (h : checkDivPreservationExec dc = true) :
    checkStuckPreservationProp (toPCertificate dc) := by
  intro pc_t σ_t σ_o hpc hrel hinv_t hinv_o hobs
  -- Extract the check result for this specific pc_t
  have hmem : pc_t ∈ List.range dc.trans.size := List.mem_range.mpr hpc
  have hcheck := (List.all_eq_true.mp h) pc_t hmem
  -- Since pc_t < dc.trans.size, dc.trans[pc_t]? = some instr
  obtain ⟨instr, hinstr⟩ : ∃ instr, dc.trans[pc_t]? = some instr :=
    ⟨dc.trans[pc_t], getElem?_eq_some_iff.mpr ⟨hpc, rfl⟩⟩
  -- Simplify toPCertificate in goal and hypotheses
  simp only [toPCertificate] at hobs hrel ⊢
  set dic := dc.instrCerts.getD pc_t default with hdic_def
  -- hobs: observe on trans side is stuck
  -- Unfold observe on the trans side
  simp only [observe, hinstr] at hobs
  -- Rewrite hcheck with hinstr so we see the match result
  simp only [hinstr] at hcheck
  -- Case split on the transformed instruction
  cases instr with
  | halt => simp at hobs
  | const _ _ | copy _ _ | boolop _ _ | goto _ | ifgoto _ _ => simp at hobs
  | binop x op y z =>
    -- For binop, observe is stuck when operands aren't both ints or op is unsafe
    -- The strengthened checker verifies: orig has same op, both operands related
    -- Reduce the let binding in the checker
    simp only [] at hcheck
    generalize horig : dc.orig[dic.pc_orig]? = orig_opt at hcheck
    cases orig_opt with
    | none => simp at hcheck
    | some orig_instr =>
      cases orig_instr with
      | binop x' op' y' z' =>
        -- hcheck: op == op' && ssGet ... y == .var y' && ssGet ... z == .var z'
        simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
        obtain ⟨⟨hop, hrel_y_eq⟩, hrel_z_eq⟩ := hcheck
        subst hop
        -- From the expression relation: σ_t y = σ_o y', σ_t z = σ_o z'
        have hrel_y : σ_t y = σ_o y' := by
          have := hrel y; rw [hrel_y_eq, Expr.eval] at this; exact this
        have hrel_z : σ_t z = σ_o z' := by
          have := hrel z; rw [hrel_z_eq, Expr.eval] at this; exact this
        -- Case split on σ_t y, σ_t z to determine why trans is stuck
        cases hvy : σ_t y <;> cases hvz : σ_t z <;> simp [hvy, hvz] at hobs
        · -- Both ints, op unsafe (only possible for div)
          rename_i a b
          have hy' : σ_o y' = .int a := by rw [← hrel_y, hvy]
          have hz' : σ_o z' = .int b := by rw [← hrel_z, hvz]
          simp only [observe, horig, hy', hz', hobs]
          simp
        · -- σ_t y = .int, σ_t z = .bool
          rename_i a b
          have hy' : σ_o y' = .int a := by rw [← hrel_y, hvy]
          have hz' : σ_o z' = .bool b := by rw [← hrel_z, hvz]
          simp only [observe, horig, hy', hz']
        · -- σ_t y = .bool, σ_t z = .int
          rename_i a b
          have hy' : σ_o y' = .bool a := by rw [← hrel_y, hvy]
          have hz' : σ_o z' = .int b := by rw [← hrel_z, hvz]
          simp only [observe, horig, hy', hz']
        · -- σ_t y = .bool, σ_t z = .bool
          rename_i a b
          have hy' : σ_o y' = .bool a := by rw [← hrel_y, hvy]
          have hz' : σ_o z' = .bool b := by rw [← hrel_z, hvz]
          simp only [observe, horig, hy', hz']
      | _ => simp at hcheck

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

/-- **Condition 9 soundness**: If `checkSuccessorsInBounds` passes, then
    the transformed program is step-closed in bounds. -/
theorem checkSuccessorsInBounds_sound (dc : ECertificate)
    (h : checkSuccessorsInBounds dc = true) :
    StepClosedInBounds dc.trans := by
  simp only [checkSuccessorsInBounds, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨hpos, hall⟩ := h
  constructor
  · exact hpos
  · intro pc pc' σ σ' hpc hstep
    cases hstep with
    | const hi =>
      have := hall pc hpc; simp [hi, successors] at this; exact this
    | copy hi =>
      have := hall pc hpc; simp [hi, successors] at this; exact this
    | binop hi =>
      have := hall pc hpc; simp [hi, successors] at this; exact this
    | boolop hi =>
      have := hall pc hpc; simp [hi, successors] at this; exact this
    | goto hi =>
      have := hall pc hpc; simp [hi, successors] at this; exact this
    | iftrue hi _ =>
      have := hall pc hpc; simp [hi, successors] at this; exact this.1
    | iffall hi _ =>
      have := hall pc hpc; simp [hi, successors] at this; exact this.2

theorem soundness_bridge (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true) :
    PCertificateValid Γ (toPCertificate dc) := by
  -- checkCertificateExec is: c1 && c2 && c2c && c3 && c4 && c5 && c6 && c7 && c8_div && c9
  -- && is left-associative, so decompose from right to left
  unfold checkCertificateExec at h
  have ⟨h19, h10⟩ := and_true_of_and_eq_true h     -- h10 = checkSuccessorsInBounds
  have ⟨h18, h9⟩  := and_true_of_and_eq_true h19   -- h9  = checkDivPreservationExec
  have ⟨h17, h8⟩  := and_true_of_and_eq_true h18
  have ⟨h16, h7⟩  := and_true_of_and_eq_true h17
  have ⟨h15, h6⟩  := and_true_of_and_eq_true h16
  have ⟨h14, h5⟩  := and_true_of_and_eq_true h15
  have ⟨h13, h4⟩  := and_true_of_and_eq_true h14
  have ⟨h12, h3⟩  := and_true_of_and_eq_true h13
  have ⟨h1, h2⟩   := and_true_of_and_eq_true h12
  -- Derive rel=[] at start from checkRelAtStartExec (h3)
  have hrel0 : (dc.instrCerts.getD 0 default).rel = [] := by
    revert h3; simp only [checkRelAtStartExec]
    cases (dc.instrCerts.getD 0 default).rel with
    | nil => intro; rfl
    | cons => simp [List.isEmpty]
  exact {
    well_typed_orig := by simp [toPCertificate]; exact hwtp
    start_corr    := checkStartCorrespondenceExec_sound dc h1 hrel0
    start_inv     := checkInvariantsAtStartExec_sound dc h2
    inv_preserved := checkInvariantsPreservedExec_sound dc h4
    transitions   := checkAllTransitionsExec_sound dc Γ hwtp h5
    halt_corr     := checkHaltCorrespondenceExec_sound dc h6
    halt_obs      := checkHaltObservableExec_sound dc h7
    nonterm       := checkNonterminationExec_sound dc h8
    stuck_pres    := checkDivPreservationExec_sound dc h9
    step_closed   := checkSuccessorsInBounds_sound dc h10
  }

-- ============================================================
-- § 10. Why not iff?
-- ============================================================

/-!
## The converse does NOT hold

`PCertificateValid cert` does **not** imply `checkCertificateExec dc = true`
for several reasons:

1. **Expressiveness gap**: The Prop-based system supports arbitrary invariants
   (`Store → Prop`), while the executable system only supports `var = val` atoms.
   A certificate using `x < y` as an invariant is valid in the Prop world
   but has no representation in `ECertificate`.

2. **Store relation generality**: The Prop system supports arbitrary `PStoreRel`s
   (`Store → Store → Prop`), while the executable system supports `EExprRel` (finite
   lists of expression pairs). The soundness proof handles non-trivial relations,
   but the executable representation is still less general.

3. **Information loss**: `toPCertificate` maps every `ECertificate` to a
   `PCertificate` with `eRelToStoreRel` store relations and `EInv.toProp` invariants.
   Many different `PCertificate`s could satisfy `PCertificateValid` for the
   same programs, but only those expressible as `toPCertificate dc` for some `dc`
   are in the image of the translation.

The relationship is:

```
  checkCertificateExec dc = true
        ⟹
  PCertificateValid (toPCertificate dc)
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


/-- **Totality**: If the executable checker accepts, the transformed
    program has a behavior for every initial store. -/
theorem trans_has_behavior (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true)
    (σ₀ : Store) :
    ∃ b, program_behavior dc.trans σ₀ b :=
  has_behavior dc.trans σ₀ (soundness_bridge Γ dc hwtp h).step_closed

/-- If no step exists from a run config, then `observe` returns `stuck`. -/
private theorem no_step_stuck_observe {p : Prog} {obs : List Var} {pc : Nat} {σ : Store}
    (hnostep : ¬ ∃ c', Step p (Cfg.run pc σ) c') :
    observe p obs (Cfg.run pc σ) = Observation.stuck := by
  simp only [observe]
  match h : p[pc]? with
  | none => rfl
  | some .halt => exact absurd ⟨_, Step.halt h⟩ hnostep
  | some (.const x n) => exact absurd ⟨_, Step.const h⟩ hnostep
  | some (.copy x y) => exact absurd ⟨_, Step.copy h⟩ hnostep
  | some (.boolop x be) => exact absurd ⟨_, Step.boolop h⟩ hnostep
  | some (.binop x op y z) =>
    -- observe pattern-matches on σ y, σ z; split on both being .int or not
    simp only [observe, h]
    -- bring σ y and σ z into scope as named values
    cases hy : σ y with
    | int a =>
      cases hz : σ z with
      | int m =>
        -- σ y = .int a, σ z = .int m
        -- if op.safe a m, a step would exist (contradiction with hnostep)
        by_cases hs : op.safe a m
        · exact absurd ⟨_, Step.binop h hy hz hs⟩ hnostep
        · simp [hs]
      | bool _ =>
        -- σ z = .bool _: observe returns stuck directly
        simp
    | bool _ =>
      -- σ y = .bool _: observe returns stuck directly
      simp
  | some (.goto l) => exact absurd ⟨_, Step.goto h⟩ hnostep
  | some (.ifgoto b l) =>
    by_cases hcond : b.eval σ = true
    · exact absurd ⟨_, Step.iftrue h hcond⟩ hnostep
    · have : b.eval σ = false := Bool.eq_false_iff.mpr (by simp_all)
      exact absurd ⟨_, Step.iffall h this⟩ hnostep

/-- If `observe` returns `stuck`, then no step exists. -/
private theorem stuck_observe_no_step {p : Prog} {obs : List Var} {pc : Nat} {σ : Store}
    (hobs : observe p obs (Cfg.run pc σ) = Observation.stuck) :
    ¬ ∃ c', Step p (Cfg.run pc σ) c' := by
  intro ⟨c', hstep⟩
  cases hstep with
  | halt h => simp [observe, h] at hobs
  | const h => simp [observe, h] at hobs
  | copy h => simp [observe, h] at hobs
  | boolop h => simp [observe, h] at hobs
  | binop h ha hb hs => simp [observe, h, ha, hb, hs] at hobs
  | goto h => simp [observe, h] at hobs
  | iftrue h _ => simp [observe, h] at hobs
  | iffall h _ => simp [observe, h] at hobs

/-- **End-to-end correctness**: If the executable checker accepts,
    then every behavior of the transformed program has a corresponding
    behavior in the original program (with observable equivalence at halt).

    This is the composition of `soundness_bridge` and
    `credible_compilation_soundness` — the complete pipeline from
    `checkCertificateExec dc = true` to semantic preservation. -/
theorem exec_checker_correct (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true)
    (σ₀ : Store) (hts₀ : TypedStore Γ σ₀) (b : Behavior)
    (htrans : program_behavior dc.trans σ₀ b) :
    ∃ b', program_behavior dc.orig σ₀ b' ∧
      match b, b' with
      | .halts σ_t, .halts σ_o =>
          ∀ v ∈ dc.observable, σ_t v = σ_o v
      | .stuck, .stuck => True
      | .diverges, .diverges => True
      | _, _ => False := by
  cases b with
  | halts σ_t' =>
    obtain ⟨σ_o', ho, hobs⟩ := soundness_halt
      (toPCertificate dc) (soundness_bridge Γ dc hwtp h) σ₀ σ_t' hts₀ htrans
    exact ⟨.halts σ_o', ho, hobs⟩
  | stuck =>
    obtain ⟨pc_t, σ_t, hreach, hnostep⟩ := htrans
    have hobs_t := @no_step_stuck_observe _ dc.observable _ _ hnostep
    obtain ⟨c_o, hreach_o, hobs_o⟩ := stuck_preservation
      (toPCertificate dc) (soundness_bridge Γ dc hwtp h) σ₀ hts₀ _ hreach hobs_t
    cases c_o with
    | halt σ_o => simp [observe] at hobs_o
    | run pc_o σ_o =>
      exact ⟨.stuck, ⟨pc_o, σ_o, hreach_o, stuck_observe_no_step hobs_o⟩, trivial⟩
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toPCertificate dc) (soundness_bridge Γ dc hwtp h) f σ₀ hts₀ hinf hf0
    exact ⟨.diverges, ⟨g, hg, hg0⟩, trivial⟩

/-- **Complete end-to-end**: checker accepts → every initial store has a behavior
    in the transformed program, and that behavior is matched by the original. -/
theorem exec_checker_total (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true)
    (σ₀ : Store) (hts₀ : TypedStore Γ σ₀) :
    ∃ b, program_behavior dc.trans σ₀ b ∧
      ∃ b', program_behavior dc.orig σ₀ b' ∧
        match b, b' with
        | .halts σ_t, .halts σ_o => ∀ v ∈ dc.observable, σ_t v = σ_o v
        | .stuck, .stuck => True
        | .diverges, .diverges => True
        | _, _ => False := by
  obtain ⟨b, hb⟩ := trans_has_behavior Γ dc hwtp h σ₀
  have hvalid := soundness_bridge Γ dc hwtp h
  cases b with
  | halts σ_t =>
    obtain ⟨σ_o', ho, hobs⟩ := soundness_halt
      (toPCertificate dc) hvalid σ₀ σ_t hts₀ hb
    exact ⟨.halts σ_t, hb, .halts σ_o', ho, hobs⟩
  | stuck =>
    obtain ⟨pc_t, σ_t, hreach, hnostep⟩ := hb
    have hobs_t := @no_step_stuck_observe _ dc.observable _ _ hnostep
    obtain ⟨c_o, hreach_o, hobs_o⟩ := stuck_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ _ hreach hobs_t
    cases c_o with
    | halt σ_o => simp [observe] at hobs_o
    | run pc_o σ_o =>
      exact ⟨.stuck, ⟨pc_t, σ_t, hreach, hnostep⟩, .stuck,
        ⟨pc_o, σ_o, hreach_o, stuck_observe_no_step hobs_o⟩, trivial⟩
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := hb
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toPCertificate dc) hvalid f σ₀ hts₀ hinf hf0
    exact ⟨.diverges, ⟨f, hinf, hf0⟩, .diverges, ⟨g, hg, hg0⟩, trivial⟩

-- ============================================================
-- § 15. Per-behavior preservation for ECertificates
-- ============================================================

/-- **Halt preservation (executable)**: If the executable checker accepts and
    the transformed program halts, the original halts with the same
    observable values. -/
theorem exec_halt_preservation (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true)
    (σ₀ σ_t' : Store) (hts₀ : TypedStore Γ σ₀)
    (hexec : haltsWithResult dc.trans 0 σ₀ σ_t') :
    ∃ σ_o', haltsWithResult dc.orig 0 σ₀ σ_o' ∧
      ∀ v ∈ dc.observable, σ_t' v = σ_o' v :=
  soundness_halt (toPCertificate dc) (soundness_bridge Γ dc hwtp h) σ₀ σ_t' hts₀ hexec

/-- **Stuck preservation (executable)**: If the executable checker accepts and
    the transformed program gets stuck (e.g. div-by-zero), the original
    program also gets stuck. -/
theorem exec_stuck_preservation (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true)
    (σ₀ : Store) (hts₀ : TypedStore Γ σ₀) (c_t : Cfg)
    (hreach : dc.trans ⊩ Cfg.run 0 σ₀ ⟶* c_t)
    (hobs : observe dc.trans dc.observable c_t = Observation.stuck) :
    ∃ c_o, (dc.orig ⊩ Cfg.run 0 σ₀ ⟶* c_o) ∧
      observe dc.orig dc.observable c_o = Observation.stuck :=
  stuck_preservation (toPCertificate dc) (soundness_bridge Γ dc hwtp h) σ₀ hts₀ c_t hreach hobs

/-- **Divergence preservation (executable)**: If the executable checker accepts
    and the transformed program diverges, the original program also diverges. -/
theorem exec_diverge_preservation (Γ : TyCtx)
    (dc : ECertificate) (hwtp : WellTypedProg Γ dc.orig) (h : checkCertificateExec dc = true)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore Γ σ₀)
    (hinf : IsInfiniteExec dc.trans f)
    (hf0 : f 0 = Cfg.run 0 σ₀) :
    ∃ g : Nat → Cfg, IsInfiniteExec dc.orig g ∧ g 0 = Cfg.run 0 σ₀ :=
  soundness_diverge (toPCertificate dc) (soundness_bridge Γ dc hwtp h) f σ₀ hts₀ hinf hf0
