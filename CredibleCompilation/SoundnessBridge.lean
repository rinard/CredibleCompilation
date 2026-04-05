import CredibleCompilation.ExecChecker
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

/-- A `EInv` as a proposition: every atom `(x, e)` asserts `σ x = e.eval σ am`. -/
def EInv.toProp (inv : EInv) : PInvariant :=
  fun σ am => ∀ p ∈ inv, σ p.1 = p.2.eval σ am

theorem EInv.toProp_nil : EInv.toProp [] = fun _ _ => True := by
  funext σ am; simp [EInv.toProp]

theorem EInv.toProp_cons (x : Var) (e : Expr) (rest : EInv) :
    EInv.toProp ((x, e) :: rest) = fun σ am => σ x = e.eval σ am ∧ EInv.toProp rest σ am := by
  funext σ am; simp [EInv.toProp]

/-- If all invariant atoms are arrRead-free, the invariant holds at any array memory. -/
theorem EInv.toProp_am_indep (inv : EInv) (σ : Store) (am₁ am₂ : ArrayMem)
    (hnoarr : inv.all (fun (_, e) => !e.hasArrRead) = true)
    (hinv : EInv.toProp inv σ am₁) :
    EInv.toProp inv σ am₂ := by
  intro p hp
  have := hinv p hp
  rw [List.all_eq_true] at hnoarr
  have hna := hnoarr p hp
  simp at hna
  rw [this, Expr.eval_noArrRead p.2 σ am₁ am₂ hna]

/-- SamCoherent relates the symbolic array memory to the runtime array memory
    via a chain of writes.  Most-recent write is at the head. -/
inductive SamCoherent : SymArrayMem → Store → ArrayMem → ArrayMem → Prop where
  | nil {σ₀ : Store} {am : ArrayMem} : SamCoherent [] σ₀ am am
  | cons {rest : SymArrayMem} {σ₀ : Store} {am₀ am_prev am : ArrayMem}
         (arr : ArrayName) (idx_e val_e : Expr) (bv : BitVec 64)
         (hprev : SamCoherent rest σ₀ am₀ am_prev)
         (hvalint : val_e.eval σ₀ am₀ = .int bv)
         (hwrite : am = am_prev.write arr (idx_e.eval σ₀ am₀).toInt.toNat bv) :
    SamCoherent ((arr, idx_e, val_e) :: rest) σ₀ am₀ am

theorem samCoherent_nil (σ₀ : Store) (am : ArrayMem) :
    SamCoherent [] σ₀ am am := .nil

private theorem samGet_cons (arr_h : ArrayName) (idx_h val_h : Expr) (rest : SymArrayMem)
    (arr : ArrayName) (idx : Expr) :
    samGet ((arr_h, idx_h, val_h) :: rest) arr idx =
    if arr_h == arr && idx_h == idx then val_h else samGet rest arr idx := by
  simp only [samGet, List.find?]
  cases arr_h == arr && idx_h == idx <;> simp

/-- samGet_sound: under a no-alias condition, `samGet` at am₀ gives the same as
    reading the current runtime am.  Proved by induction on the SAM list.
    Well-typing (values are .int) is encoded in SamCoherent.cons. -/
theorem samGet_sound (sam : SymArrayMem) (σ₀ : Store) (am₀ am : ArrayMem)
    (hcoh : SamCoherent sam σ₀ am₀ am)
    (arr : ArrayName) (idx_expr : Expr)
    (hnoalias : ∀ a i v, (a, i, v) ∈ sam → a = arr → ¬(i == idx_expr) →
      (i.eval σ₀ am₀).toInt.toNat ≠ (idx_expr.eval σ₀ am₀).toInt.toNat) :
    (samGet sam arr idx_expr).eval σ₀ am₀ =
    Value.int (am.read arr (idx_expr.eval σ₀ am₀).toInt.toNat) := by
  induction sam generalizing am with
  | nil => cases hcoh; simp [samGet, List.find?, Expr.eval]
  | cons entry rest ih =>
    obtain ⟨arr_h, idx_h, val_h⟩ := entry
    match hcoh with
    | .cons _ _ _ bv hprev hvalint hwrite =>
    rw [samGet_cons]
    by_cases hmatch : (arr_h == arr && idx_h == idx_expr) = true
    · -- Match case: head entry matches
      simp [hmatch]
      simp [Bool.and_eq_true] at hmatch
      have harr : arr_h = arr := hmatch.1
      have hidx : idx_h = idx_expr := hmatch.2
      rw [hwrite, harr, hidx, ArrayMem.read_write_same, hvalint]
    · -- Non-match case: recurse into rest
      simp [hmatch]
      have ih_noalias : ∀ a i v, (a, i, v) ∈ rest → a = arr → ¬(i == idx_expr) →
          (i.eval σ₀ am₀).toInt.toNat ≠ (idx_expr.eval σ₀ am₀).toInt.toNat :=
        fun a i v hmem ha hi => hnoalias a i v (List.Mem.tail _ hmem) ha hi
      rw [ih _ hprev ih_noalias]
      congr 1; rw [hwrite]
      by_cases harr : arr_h = arr
      · have hidx_ne : ¬(idx_h == idx_expr) := by
          intro h; exact hmatch (by simp [beq_iff_eq.mpr harr, h])
        have hsem_ne := hnoalias arr_h idx_h val_h (List.Mem.head _) harr hidx_ne
        subst harr
        exact (ArrayMem.read_write_ne_idx _ _ _ _ _ hsem_ne.symm).symm
      · exact (ArrayMem.read_write_ne_arr _ _ _ _ _ _ (fun h => harr h.symm)).symm

-- ============================================================
-- § 2. Translation: ECertificate → PCertificate
-- ============================================================

/-- Convert an executable expression relation to a Prop-level store relation.
    Uses `buildSubstMap` to create a total store relation: for every variable `v`,
    `σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o am_o`.
    Empty relations yield identity (σ_o = σ_t). -/
def eRelToStoreRel (rel : EExprRel) : PStoreRel :=
  fun σ_o am_o σ_t _am_t => ∀ v, σ_t v = (ssGet (buildSubstMap rel) v).eval σ_o am_o

/-- Lift an executable certificate to a Prop-based certificate. -/
def toPCertificate (dc : ECertificate) : PCertificate :=
  { orig       := dc.orig
    trans      := dc.trans
    inv_orig   := fun l => (dc.inv_orig.getD l ([] : EInv)).toProp
    inv_trans  := fun l => (dc.inv_trans.getD l ([] : EInv)).toProp
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

@[simp] theorem toCertificate_tyCtx (dc : ECertificate) :
    (toPCertificate dc).tyCtx = dc.tyCtx := by
  simp [PCertificate.tyCtx, ECertificate.tyCtx, toPCertificate]

@[simp] theorem toCertificate_observable (dc : ECertificate) :
    (toPCertificate dc).observable = dc.observable := by
  simp [PCertificate.observable, ECertificate.observable, toPCertificate]

-- ============================================================
-- § 3. lookupExpr soundness
-- ============================================================

theorem lookupExpr_sound (inv : EInv) (v : Var) (e : Expr) (σ : Store) (am : ArrayMem)
    (hlook : lookupExpr inv v = some e)
    (hinv : EInv.toProp inv σ am) :
    σ v = e.eval σ am := by
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
private theorem Expr.reassoc_sound (op : BinOp) (a b : Expr) (σ : Store) (am : ArrayMem) :
    (Expr.reassoc op a b).eval σ am = (Expr.bin op a b).eval σ am := by
  unfold Expr.reassoc
  split
  · -- (na - x) + nb → (na + nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · -- (na - x) - nb → (na - nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · rename_i na nb x
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · -- na - (x - nb) → (na + nb) - x
    rename_i na x nb
    simp only [Expr.eval, BinOp.eval, Value.toInt]; congr 1; bv_omega
  · rfl

/-- Simplification preserves semantics: evaluating `e.simplify inv` in `σ`
    gives the same result as evaluating `e` in `σ`, provided `σ` satisfies `inv`. -/
theorem Expr.simplify_sound (inv : EInv) (e : Expr) (σ : Store) (am : ArrayMem)
    (hinv : EInv.toProp inv σ am) :
    (e.simplify inv).eval σ am = e.eval σ am := by
  induction e with
  | lit n => simp [Expr.simplify, Expr.eval]
  | blit b => simp [Expr.simplify, Expr.eval]
  | var v =>
    simp only [Expr.simplify]
    split
    · case h_1 e hlook =>
      simp only [Expr.eval]
      have h := lookupExpr_sound inv v e σ am hlook hinv
      exact h.symm
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
      rw [show (a.eval σ am).toInt = na from by rw [← iha]; rfl,
          show (b.eval σ am).toInt = nb from by rw [← ihb]; rfl]
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
  | arrRead arr idx ih =>
    simp only [Expr.simplify, Expr.eval]
    rw [ih]

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
    · -- ∀ σ am, storeRel σ am σ am
      have hrel_ic : ic.rel = [] := by
        have : (dc.instrCerts.getD 0 default).rel = ic.rel := by
          simp [Array.getD, dif_pos hbound, hget]
        rw [this] at hrel0; exact hrel0
      intro σ am v
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
  refine ⟨fun σ am => ?_, fun σ am => ?_⟩
  · change (dc.inv_trans.getD 0 ([] : EInv)).toProp σ am
    rw [htrans_nil]; simp [EInv.toProp]
  · change (dc.inv_orig.getD 0 ([] : EInv)).toProp σ am
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
  intro pc_t σ_t σ_o am_t am_o hhalt
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
  -- hcons v : σ_t v = (ssGet (buildSubstMap ic.rel) v).eval σ_o am_o
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
    (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ v) :
    (be.toSymExpr ss).eval σ₀ am = .bool (be.eval σ) := by
  induction be with
  | lit b =>
    simp only [BoolExpr.toSymExpr, Expr.eval, BoolExpr.eval]
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

/-- Symbolic execution soundness: if the symbolic store `ss` correctly represents
    the relationship between an initial store `σ₀` and a current store `σ`,
    then after executing `instr`, the updated symbolic store correctly represents
    the relationship with the post-store `σ'`. -/
theorem execSymbolic_sound (ss : SymStore) (sam : SymArrayMem) (instr : TAC)
    (σ₀ σ σ' : Store) (pc pc' : Label) (prog : Prog) (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ v)
    (hstep : Step prog (Cfg.run pc σ _sbam) (Cfg.run pc' σ' _sbam'))
    (hinstr : prog[pc]? = some instr)
    (hscalar : instr.isScalar = true) :
    ∀ v, (ssGet (execSymbolic ss sam instr).1 v).eval σ₀ am = σ' v := by
  have step_det : ∀ c, Step prog (Cfg.run pc σ _sbam) c → c = Cfg.run pc' σ' _sbam' :=
    fun c hc => Step.deterministic hc hstep
  intro v
  cases instr with
  | const dest val =>
    -- execSymbolic splits on val's constructor, so we case-split on val
    cases val with
    | int n =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .int n] := (Cfg.run.inj this).2.1.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
    | bool b =>
      simp only [execSymbolic]
      have := step_det _ (Step.const hinstr)
      have hσ' : σ' = σ[dest ↦ .bool b] := (Cfg.run.inj this).2.1.symm
      rw [hσ']
      by_cases hvd : v = dest
      · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
      · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
        exact (Store.update_other σ dest v _ hvd).symm
  | copy dest src =>
    simp only [execSymbolic]
    have := step_det _ (Step.copy hinstr)
    have hσ' : σ' = σ[dest ↦ σ src] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same, hrepr]; exact (Store.update_self σ dest (σ src)).symm
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | binop dest op a b =>
    simp only [execSymbolic]
    -- Extract int witnesses from hstep (Step.binop requires σ a = .int _ and σ b = .int _)
    obtain ⟨ia, ib, hia, hib, hsafe⟩ : ∃ ia ib : BitVec 64, σ a = .int ia ∧ σ b = .int ib ∧ op.safe ia ib := by
      revert hstep; generalize _sbam = am; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hstep' : Step prog (Cfg.run pc σ _sbam) (Cfg.run (pc + 1) (σ[dest ↦ .int (op.eval ia ib)]) _sbam) :=
      Step.binop hinstr hia hib hsafe
    have := step_det _ hstep'
    have hσ' : σ' = σ[dest ↦ .int (op.eval ia ib)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Expr.eval, Store.update_self]
      have ha : ((ssGet ss a).eval σ₀ am).toInt = ia := by
        rw [hrepr a, hia]; rfl
      have hb : ((ssGet ss b).eval σ₀ am).toInt = ib := by
        rw [hrepr b, hib]; rfl
      rw [ha, hb]
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | boolop dest be =>
    simp only [execSymbolic]
    have := step_det _ (Step.boolop hinstr)
    have hσ' : σ' = σ[dest ↦ .bool (be.eval σ)] := (Cfg.run.inj this).2.1.symm
    rw [hσ']
    by_cases hvd : v = dest
    · rw [hvd, ssGet_ssSet_same]
      simp only [Store.update_self]
      exact BoolExpr.toSymExpr_sound be ss σ₀ σ am hrepr
    · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
      exact (Store.update_other σ dest v _ hvd).symm
  | goto l =>
    simp only [execSymbolic]
    have := step_det _ (Step.goto hinstr)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v
  | ifgoto b l =>
    simp only [execSymbolic]
    by_cases hb : b.eval σ = true
    · have := step_det _ (Step.iftrue hinstr hb)
      have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
      rw [hσ']; exact hrepr v
    · have := step_det _ (Step.iffall hinstr (Bool.eq_false_iff.mpr hb))
      have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
      rw [hσ']; exact hrepr v
  | halt =>
    exfalso
    have := step_det _ (Step.halt hinstr)
    exact Cfg.noConfusion this
  | arrLoad dest arr idx =>
    exact absurd hscalar (by simp [TAC.isScalar])
  | arrStore arr idx val =>
    simp only [execSymbolic]
    -- arrStore only changes ArrayMem, not Store: σ' = σ
    obtain ⟨idxVal, hv⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
      revert hstep; generalize _sbam = am; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    obtain ⟨vv, hvv⟩ : ∃ vv : BitVec 64, σ val = .int vv := by
      revert hstep; generalize _sbam = am; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have hbnd : idxVal.toNat < prog.arraySize arr := by
      revert hstep; generalize _sbam = am; generalize _sbam' = am'; intro hstep; cases hstep <;> simp_all
    have := step_det _ (Step.arrStore hinstr hv hvv hbnd)
    have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
    rw [hσ']; exact hrepr v

/-- Empty expression relation yields identity store relation. -/
private theorem eRelToStoreRel_nil : eRelToStoreRel [] = fun σ_o _am_o σ_t _am_t => σ_o = σ_t := by
  funext σ_o am_o σ_t am_t; simp [eRelToStoreRel, buildSubstMap, ssGet, Expr.eval]
  constructor
  · intro h; funext v; exact (h v).symm
  · intro h v; rw [h]

/-- Identity store relation from empty expression relation means stores are equal. -/
private theorem eRelToStoreRel_nil_eq {σ₁ σ₂ : Store} {am₁ am₂ : ArrayMem}
    (h : eRelToStoreRel [] σ₁ am₁ σ₂ am₂) : σ₁ = σ₂ := by
  rw [eRelToStoreRel_nil] at h; exact h

/-- Initial symbolic store represents identity: ssGet [] v evaluates to σ v. -/
private theorem ssGet_nil (σ : Store) (am : ArrayMem) (v : Var) :
    (ssGet ([] : SymStore) v).eval σ am = σ v := by
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
  | arrRead arr idx ih => simp [Expr.substSym, ih]

-- ============================================================
-- § 6b. Expr.substSym soundness
-- ============================================================

/-- Substituting variables in `e` with their symbolic post-values and evaluating
    at the initial store `σ₀` equals evaluating `e` at the post-store `σ'`. -/
theorem Expr.substSym_sound (ss : SymStore) (e : Expr) (σ₀ σ' : Store)
    (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ' v) :
    (e.substSym ss).eval σ₀ am = e.eval σ' am := by
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
  | arrRead arr idx ih =>
    simp only [Expr.substSym, Expr.eval]; rw [ih]

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
    (σ σ' : Store) (pc pc' : Label) (prog : Prog) {am am' : ArrayMem}
    (hcheck : checkInvAtom inv_pre instr atom = true)
    (hinv : EInv.toProp inv_pre σ am)
    (hstep : Step prog (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    (hinstr : prog[pc]? = some instr)
    (hnoarr : atom.2.hasArrRead = false) :
    σ' atom.1 = atom.2.eval σ' am' := by
  obtain ⟨x, e⟩ := atom; simp only
  -- checkInvAtom gives us BEq equality of simplified expressions
  simp only [checkInvAtom] at hcheck
  have hbeq := beq_iff_eq.mp hcheck
  -- Build hrepr with runtime am: symbolic store tracks the step
  have hrepr : ∀ v, (ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) v).eval σ am = σ' v := by
    by_cases hscalar : instr.isScalar = true
    · exact execSymbolic_sound ([] : SymStore) ([] : SymArrayMem) instr σ σ σ' pc pc' prog am
        (ssGet_nil σ am) hstep hinstr hscalar
    · cases instr with
      | arrStore arr idx val =>
        simp only [execSymbolic]
        have step_det : ∀ c, Step prog (Cfg.run pc σ am) c → c = Cfg.run pc' σ' am' :=
          fun c hc => Step.deterministic hc hstep
        obtain ⟨idxVal, hv⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        obtain ⟨vv, hvv⟩ : ∃ vv : BitVec 64, σ val = .int vv := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hbnd : idxVal.toNat < prog.arraySize arr := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have := step_det _ (Step.arrStore hinstr hv hvv hbnd)
        have hσ' : σ' = σ := (Cfg.run.inj this).2.1.symm
        rw [hσ']; exact ssGet_nil σ am
      | arrLoad dest arr idx =>
        simp only [execSymbolic, Prod.fst]
        have step_det : ∀ c, Step prog (Cfg.run pc σ am) c → c = Cfg.run pc' σ' am' :=
          fun c hc => Step.deterministic hc hstep
        obtain ⟨idxVal, hidx⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hbnd : idxVal.toNat < prog.arraySize arr := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have := step_det _ (Step.arrLoad hinstr hidx hbnd)
        have hσ' : σ' = σ[dest ↦ .int (am.read arr idxVal.toNat)] :=
          (Cfg.run.inj this).2.1.symm
        intro v
        by_cases hvd : v = dest
        · rw [hvd, ssGet_ssSet_same, hσ']
          simp only [samGet, List.find?, Expr.eval, ssGet, List.find?, Expr.eval, Store.update_self]
          rw [hidx]; simp [Value.toInt]
        · rw [ssGet_ssSet_other _ _ _ _ hvd, hσ', ssGet_nil]
          exact (Store.update_other σ dest v _ hvd).symm
      | _ => exact absurd rfl hscalar
  -- Build the chain using am, then bridge to am'.
  have hlhs := Expr.simplify_sound inv_pre
    (ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) x) σ am hinv
  have hrhs := Expr.simplify_sound inv_pre
    (e.substSym ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1)) σ am hinv
  have hsub := Expr.substSym_sound ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) e σ σ'
    am hrepr
  -- Chain: σ' x = ... = e.eval σ' am
  have hchain : σ' x = e.eval σ' am :=
    calc σ' x
        = (ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) x).eval σ am := (hrepr x).symm
      _ = ((ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) x).simplify inv_pre).eval σ am := hlhs.symm
      _ = ((e.substSym ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1)).simplify inv_pre).eval σ am := by
            rw [hbeq]
      _ = (e.substSym ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1)).eval σ am := hrhs
      _ = e.eval σ' am := hsub
  -- Bridge: e.eval σ' am = e.eval σ' am' via arrRead-free
  rw [hchain]
  exact Expr.eval_noArrRead e σ' am am' hnoarr

/-- Extract instruction from a step to a run configuration. -/
theorem step_run_instr {p : Prog} {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ instr, p[pc]? = some instr := by
  cases hstep with
  | const h => exact ⟨_, h⟩
  | copy h => exact ⟨_, h⟩
  | binop h => exact ⟨_, h⟩
  | boolop h => exact ⟨_, h⟩
  | goto h => exact ⟨_, h⟩
  | iftrue h _ => exact ⟨_, h⟩
  | iffall h _ => exact ⟨_, h⟩
  | arrLoad h _ => exact ⟨_, h⟩
  | arrStore h _ _ => exact ⟨_, h⟩

/-- A step target is always in the successors list. -/
theorem step_successor {p : Prog} {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
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
  | arrLoad h _ => have := instr_eq h; subst this; simp [successors]
  | arrStore h _ _ => have := instr_eq h; subst this; simp [successors]

private theorem and_true_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  simp [Bool.and_eq_true] at h; exact h

/-- Helper: checkProg soundness for one program/invariant pair. -/
private theorem noArrRead_of_inv_all (inv : Array EInv)
    (hnoarr : checkNoArrReadInInvs inv = true)
    (l : Nat) :
    (inv.getD l ([] : EInv)).all (fun (_, e) => !e.hasArrRead) = true := by
  unfold checkNoArrReadInInvs at hnoarr
  by_cases hlt : l < inv.size
  · have hgetD : inv.getD l ([] : EInv) = inv[l] := by simp [Array.getD, hlt]
    rw [hgetD]; exact (Array.all_eq_true.mp hnoarr) l hlt
  · have hgetD : inv.getD l ([] : EInv) = [] := by simp [Array.getD, Nat.not_lt.mp hlt]
    rw [hgetD]; rfl

private theorem noArrRead_of_inv (inv : Array EInv)
    (hnoarr : checkNoArrReadInInvs inv = true)
    (l : Nat) (atom : Var × Expr) (hmem : atom ∈ inv.getD l ([] : EInv)) :
    atom.2.hasArrRead = false := by
  unfold checkNoArrReadInInvs at hnoarr
  by_cases hlt : l < inv.size
  · -- inv.getD l [] = inv[l] when l < inv.size
    have hgetD : inv.getD l ([] : EInv) = inv[l] := by simp [Array.getD, hlt]
    rw [hgetD] at hmem
    -- Extract from inv.all
    have hall : (inv[l]).all (fun x => !x.2.hasArrRead) = true :=
      (Array.all_eq_true.mp hnoarr) l hlt
    rw [List.all_eq_true] at hall
    have := hall atom hmem
    simp [Bool.not_eq_true] at this
    exact this
  · -- l ≥ inv.size → inv.getD l [] = []
    have hgetD : inv.getD l ([] : EInv) = [] := by simp [Array.getD, Nat.not_lt.mp hlt]
    rw [hgetD] at hmem; exact absurd hmem (by simp)

private theorem checkProg_sound (prog : Prog) (inv : Array EInv)
    (h : (List.range prog.size).all (fun pc =>
      match prog[pc]? with
      | some instr =>
        (successors instr pc).all fun pc' =>
          (inv.getD pc' ([] : EInv)).all (checkInvAtom (inv.getD pc ([] : EInv)) instr)
      | none => true) = true)
    (hnoarr : checkNoArrReadInInvs inv = true) :
    PInvariantMap.preserved (fun l => (inv.getD l ([] : EInv)).toProp) prog := by
  intro pc σ am hinvpc pc' σ' am' hstep
  obtain ⟨instr, hinstr⟩ := step_run_instr hstep
  have hbound := bound_of_getElem? hinstr
  rw [List.all_eq_true] at h
  have hpc := h pc (List.mem_range.mpr hbound)
  simp only [hinstr] at hpc
  rw [List.all_eq_true] at hpc
  have hsucc := step_successor hstep hinstr
  have hpc' := hpc pc' hsucc
  rw [List.all_eq_true] at hpc'
  intro atom hatom
  exact checkInvAtom_sound (inv.getD pc ([] : EInv)) instr atom σ σ' pc pc' prog
    (hpc' atom hatom) hinvpc hstep hinstr (noArrRead_of_inv inv hnoarr pc' atom hatom)

/-- **Condition 2b**: checkInvariantsPreservedExec → checkInvariantsPreservedProp -/
theorem checkInvariantsPreservedExec_sound (dc : ECertificate)
    (h : checkInvariantsPreservedExec dc = true)
    (hnoarr_orig : checkNoArrReadInInvs dc.inv_orig = true)
    (hnoarr_trans : checkNoArrReadInInvs dc.inv_trans = true) :
    checkInvariantsPreservedProp (toPCertificate dc) := by
  unfold checkInvariantsPreservedExec at h
  have ⟨h1, h2⟩ := and_true_split h
  exact ⟨checkProg_sound dc.orig dc.inv_orig h1 hnoarr_orig,
         checkProg_sound dc.trans dc.inv_trans h2 hnoarr_trans⟩

/-- Variable names appearing in an instruction (matching collectAllVars.extract). -/
private def instrVars (instr : TAC) : List Var :=
  match instr with
  | .const x _     => [x]
  | .copy x y      => [x, y]
  | .binop x _ y z => [x, y, z]
  | .boolop x _    => [x]
  | .arrLoad x _ idx => [x, idx]
  | .arrStore _ idx val => [idx, val]
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
    (hmem : instr ∈ p1.code.toList) (v : Var) (hv : v ∈ instrVars instr) :
    v ∈ collectAllVars p1 p2 := by
  unfold collectAllVars
  apply List.mem_append_left
  exact mem_foldl_elem p1.code.toList ([] : List Var) hmem hv

/-- If v ∈ instrVars of an instruction in p2, then v ∈ collectAllVars p1 p2. -/
private theorem instrVars_sub_collectAllVars_right (p1 p2 : Prog) (instr : TAC)
    (hmem : instr ∈ p2.code.toList) (v : Var) (hv : v ∈ instrVars instr) :
    v ∈ collectAllVars p1 p2 := by
  unfold collectAllVars
  apply List.mem_append_right
  exact mem_foldl_elem p2.code.toList ([] : List Var) hmem hv

/-- Array getElem? to toList membership. -/
private theorem getElem?_mem_toList {arr : Prog} {i : Nat} {x : TAC}
    (h : arr[i]? = some x) : x ∈ arr.code.toList := by
  rw [Prog.getElem?_code] at h
  have hb := bound_of_getElem? h
  have heq := (Array.getElem?_eq_some_iff.mp h).2
  exact heq ▸ Array.getElem_mem_toList (h := hb)

/-- If v is not the dest of instr, execSymbolic preserves ssGet v. -/
private theorem execSymbolic_preserves_var (ss : SymStore) (sam : SymArrayMem)
    (instr : TAC) (v : Var)
    (hv : v ∉ instrVars instr) :
    ssGet (execSymbolic ss sam instr).1 v = ssGet ss v := by
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
  | arrLoad x _ idx =>
    simp [instrVars] at hv; simp only [execSymbolic]; exact ssGet_ssSet_other ss x v _ hv.1
  | arrStore _ _ _ => rfl

/-- If v is not the dest of any instruction in the program, execPath preserves ssGet v. -/
private theorem execPath_preserves_var (orig : Prog) (ss : SymStore) (sam : SymArrayMem)
    (pc : Label) (labels : List Label) (v : Var)
    (hv : ∀ (l : Label) (instr : TAC), orig[l]? = some instr → v ∉ instrVars instr) :
    ssGet (execPath orig ss sam pc labels).1 v = ssGet ss v := by
  induction labels generalizing ss sam pc with
  | nil => rfl
  | cons nextPC rest ih =>
    simp only [execPath]
    cases horig : orig[pc]? with
    | none => rfl
    | some instr =>
      have h1 := execSymbolic_preserves_var ss sam instr v (hv pc instr horig)
      have h2 := ih (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 nextPC
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
  | tobool _ | cmpE _ _ _ | cmpLitE _ _ _ | notE _ | andE _ _ | orE _ _ | arrRead _ _ => simp [Expr.isNonZeroLit] at h

/-- Soundness of `BoolExpr.symEval`: if symbolic evaluation returns a result,
    it agrees with runtime evaluation. -/
private theorem BoolExpr.symEval_sound (b : BoolExpr) (ss : SymStore) (inv : EInv)
    (σ₀ σ : Store) (am : ArrayMem)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am = σ v)
    (hinv : EInv.toProp inv σ₀ am)
    (r : Bool) (heval : b.symEval ss inv = some r) :
    b.eval σ = r := by
  induction b generalizing r with
  | lit b =>
    simp only [BoolExpr.symEval] at heval
    exact Option.some.inj heval
  | bvar x =>
    simp only [BoolExpr.symEval] at heval
    generalize hsx : (ssGet ss x).simplify inv = sx at heval
    cases sx <;> simp at heval
    case blit b =>
      simp [BoolExpr.eval]
      have hxa := Expr.simplify_sound inv (ssGet ss x) σ₀ am hinv
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
      have hxa := Expr.simplify_sound inv (ssGet ss x) σ₀ am hinv
      have hya := Expr.simplify_sound inv (ssGet ss y) σ₀ am hinv
      rw [hsx, Expr.eval] at hxa; rw [hsy, Expr.eval] at hya
      rw [← hrepr x, ← hxa, ← hrepr y, ← hya]
      exact heval
  | cmpLit op x n =>
    simp only [BoolExpr.symEval] at heval
    generalize hsx : (ssGet ss x).simplify inv = sx at heval
    cases sx <;> simp at heval
    case lit a =>
      simp [BoolExpr.eval]
      have hxa := Expr.simplify_sound inv (ssGet ss x) σ₀ am hinv
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

/-- From checkInstrAliasOk for arrLoad, derive the no-alias condition for samGet_sound. -/
private theorem checkInstrAliasOk_arrLoad_noalias
    (ss : SymStore) (sam : SymArrayMem) (inv : EInv)
    (x : Var) (arr : ArrayName) (idx : Var)
    (σ₀ : Store) (am₀ : ArrayMem)
    (hinv : EInv.toProp inv σ₀ am₀)
    (halias : checkInstrAliasOk (.arrLoad x arr idx) ss sam inv = true) :
    ∀ a i v, (a, i, v) ∈ sam → a = arr → ¬(i == ssGet ss idx) →
      (i.eval σ₀ am₀).toInt.toNat ≠ ((ssGet ss idx).eval σ₀ am₀).toInt.toNat := by
  intro a ie ve hmem ha hne
  simp only [checkInstrAliasOk, List.all_eq_true] at halias
  have hentry := halias (a, ie, ve) hmem
  simp only [ha, beq_self_eq_true, Bool.not_true, Bool.false_or] at hentry
  -- hentry now: (ie == ssGet ss idx || match ...) = true
  rw [show (ie == ssGet ss idx) = false from Bool.eq_false_iff.mpr hne] at hentry
  simp only [Bool.false_or] at hentry
  -- hentry: match ie.simplify inv, (ssGet ss idx).simplify inv with | .lit n, .lit m => !(n==m) | _ => false = true
  generalize hsi : ie.simplify inv = si at hentry
  generalize hsk : (ssGet ss idx).simplify inv = sk at hentry
  match si, sk, hentry with
  | .lit n, .lit m, hlit =>
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at hlit
    have hs1 := (Expr.simplify_sound inv ie σ₀ am₀ hinv).symm
    have hs2 := (Expr.simplify_sound inv (ssGet ss idx) σ₀ am₀ hinv).symm
    rw [hsi, Expr.eval] at hs1; rw [hsk, Expr.eval] at hs2
    rw [hs1, hs2]; simp [Value.toInt]
    exact fun h => hlit (BitVec.eq_of_toNat_eq h)

/-- Generalized path execution soundness with arbitrary initial symbolic store.
    The path check includes symbolic branch-direction verification for ifgoto.
    `branchInfo` provides the branch direction for the first step's ifgoto when
    symbolic analysis is inconclusive. `hbranch` guarantees the runtime store
    matches the branch direction. -/
private theorem execPath_sound_gen (orig : Prog) (ss : SymStore) (sam : SymArrayMem) (inv : EInv)
    (σ₀ σ : Store) (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (BoolExpr × Bool))
    (am₀ am : ArrayMem)
    (Γ : TyCtx) (hwtp : WellTypedProg Γ orig) (hts : TypedStore Γ σ)
    (hrepr : ∀ v, (ssGet ss v).eval σ₀ am₀ = σ v)
    (hinv : EInv.toProp inv σ₀ am₀)
    (hsamCoh : SamCoherent sam σ₀ am₀ am)
    (hInvNoArrRead : inv.all (fun (_, e) => !e.hasArrRead) = true)
    (hpath : checkOrigPath orig ss sam inv pc labels pc' branchInfo = true)
    (hbranch : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.eval σ = taken) :
    ∃ σ' am', Steps orig (Cfg.run pc σ am) (Cfg.run pc' σ' am') ∧
          (∀ v, (ssGet (execPath orig ss sam pc labels).1 v).eval σ₀ am₀ = σ' v) ∧
          SamCoherent (execPath orig ss sam pc labels).2 σ₀ am₀ am' := by
  induction labels generalizing pc σ ss sam branchInfo am with
  | nil =>
    simp only [checkOrigPath, beq_iff_eq] at hpath
    simp only [execPath]
    exact ⟨σ, am, hpath ▸ Steps.refl, hrepr, hsamCoh⟩
  | cons nextPC rest ih =>
    unfold checkOrigPath at hpath
    -- Extract the instruction at pc
    generalize horig_opt : orig[pc]? = opt_instr at hpath
    cases opt_instr with
    | none => simp at hpath
    | some instr =>
      rw [Bool.and_eq_true] at hpath
      have ⟨h123, hpath_inner⟩ := hpath
      rw [Bool.and_eq_true] at h123
      have ⟨h12, hsafe_check⟩ := h123
      rw [Bool.and_eq_true] at h12
      have ⟨hnext_eq, halias_check⟩ := h12
      -- Extract computeNextPC result
      generalize hnext_opt : computeNextPC instr pc ss inv = opt_next at hnext_eq
      -- Construct the step + symbolic tracking (hrepr'/hinv at am₀, hsamCoh₁ for new am₁)
      have ⟨σ₁, am₁, hstep_orig, hrepr', hinv₁, hsamCoh₁⟩ : ∃ σ₁ am₁,
          Step orig (Cfg.run pc σ am) (Cfg.run nextPC σ₁ am₁) ∧
          (∀ v, (ssGet (execSymbolic ss sam instr).1 v).eval σ₀ am₀ = σ₁ v) ∧
          EInv.toProp inv σ₀ am₀ ∧
          SamCoherent (execSymbolic ss sam instr).2 σ₀ am₀ am₁ := by
        cases opt_next with
        | some nextPC' =>
          have hpc_eq : nextPC = nextPC' := (beq_iff_eq.mp hnext_eq).symm
          subst hpc_eq
          cases instr with
          | const x n =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ n]) am) := Step.const horig_opt
            cases n with
            | int k =>
              exact ⟨σ[x ↦ .int k], am, hs, (fun v => by
                simp only [execSymbolic]
                by_cases hvd : v = x
                · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
                · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                  exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh⟩
            | bool b =>
              exact ⟨σ[x ↦ .bool b], am, hs, (fun v => by
                simp only [execSymbolic]
                by_cases hvd : v = x
                · rw [hvd, ssGet_ssSet_same]; simp [Expr.eval, Store.update_self]
                · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                  exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh⟩
          | copy x y =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ σ y]) am) := Step.copy horig_opt
            exact ⟨σ[x ↦ σ y], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same, hrepr]; exact (Store.update_self σ x (σ y)).symm
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh⟩
          | binop x op y z =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .binop x op y z :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨a, hya⟩ : ∃ a : BitVec 64, σ y = .int a := by
              cases hwti with | binop _ hy _ =>
              exact Value.int_of_typeOf_int (by rw [hts y]; exact hy)
            obtain ⟨b, hzb⟩ : ∃ b : BitVec 64, σ z = .int b := by
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
                  have hsimp := Expr.simplify_sound inv (ssGet ss z) σ₀ am₀ hinv
                  rw [hz_simp, Expr.eval] at hsimp
                  have hzval : σ z = .int n := by rw [← hrepr z]; exact hsimp.symm
                  rw [hzb] at hzval; exact Value.int.inj hzval ▸ hne
                | _ => simp at hsafe_check
              | mod =>
                simp only [checkBinopSafe] at hsafe_check
                generalize hz_simp : (ssGet ss z).simplify inv = sz at hsafe_check
                cases sz with
                | lit n =>
                  simp at hsafe_check
                  have hne : n ≠ 0 := hsafe_check
                  have hsimp := Expr.simplify_sound inv (ssGet ss z) σ₀ am₀ hinv
                  rw [hz_simp, Expr.eval] at hsimp
                  have hzval : σ z = .int n := by rw [← hrepr z]; exact hsimp.symm
                  rw [hzb] at hzval; exact Value.int.inj hzval ▸ hne
                | _ => simp at hsafe_check
              | add | sub | mul => trivial
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .int (op.eval a b)]) am) :=
              Step.binop horig_opt hya hzb hsafe
            exact ⟨σ[x ↦ .int (op.eval a b)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]
                simp only [Expr.eval, Store.update_self]
                have ha : ((ssGet ss y).eval σ₀ am₀).toInt = a := by
                  rw [hrepr y, hya]; rfl
                have hb : ((ssGet ss z).eval σ₀ am₀).toInt = b := by
                  rw [hrepr z, hzb]; rfl
                rw [ha, hb]
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh⟩
          | boolop x be =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .bool (be.eval σ)]) am) := Step.boolop horig_opt
            exact ⟨σ[x ↦ .bool (be.eval σ)], am, hs, (fun v => by
              simp only [execSymbolic]
              by_cases hvd : v = x
              · rw [hvd, ssGet_ssSet_same]; simp only [Store.update_self]
                exact BoolExpr.toSymExpr_sound be ss σ₀ σ am₀ hrepr
              · rw [ssGet_ssSet_other _ _ _ _ hvd, hrepr]
                exact (Store.update_other σ x v _ hvd).symm), hinv, hsamCoh⟩
          | goto l =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hs : Step orig (.run pc σ am) (.run l σ am) := Step.goto horig_opt
            exact ⟨σ, am, hs, (fun v => by simp only [execSymbolic]; exact hrepr v), hinv, hsamCoh⟩
          | ifgoto b l =>
            have hexec_id : (execSymbolic ss sam (.ifgoto b l)).1 = ss := rfl
            simp only [computeNextPC] at hnext_opt
            cases hsym : b.symEval ss inv <;> simp [hsym] at hnext_opt
            case some r =>
              cases r with
              | true =>
                simp at hnext_opt
                have hpc_eq : nextPC = l := hnext_opt.symm
                rw [hpc_eq]
                have heval := BoolExpr.symEval_sound b ss inv σ₀ σ am₀ hrepr hinv true hsym
                exact ⟨σ, am, Step.iftrue horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh⟩
              | false =>
                simp at hnext_opt
                have hpc_eq : nextPC = pc + 1 := hnext_opt.symm
                rw [hpc_eq]
                have heval := BoolExpr.symEval_sound b ss inv σ₀ σ am₀ hrepr hinv false hsym
                exact ⟨σ, am, Step.iffall horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh⟩
          | halt =>
            simp [computeNextPC] at hnext_opt
          | arrLoad x arr idx =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .arrLoad x arr idx :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨idxVal, hidxVal⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
              cases hwti with | arrLoad _ hidx =>
              exact Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
            -- TODO: bounds proof should come from the fact that the program
            -- is executing successfully (not erroring). Need arrayDecls equality
            -- or a hypothesis that the index is in bounds for orig.
            have hbnd : idxVal.toNat < orig.arraySize arr := by sorry
            have hs : Step orig (.run pc σ am) (.run (pc + 1) (σ[x ↦ .int (am.read arr idxVal.toNat)]) am) :=
              Step.arrLoad horig_opt hidxVal hbnd
            -- arrLoad: execSymbolic returns ssSet ss x (samGet sam arr (ssGet ss idx))
            exact ⟨σ[x ↦ .int (am.read arr idxVal.toNat)], am, hs, (fun v => by
              show (ssGet (ssSet ss x (samGet sam arr (ssGet ss idx))) v).eval σ₀ am₀ = _
              by_cases hvx : v = x
              · rw [hvx, ssGet_ssSet_same]
                simp only [Store.update_self]
                have hsc := samGet_sound sam σ₀ am₀ am hsamCoh arr (ssGet ss idx)
                  (checkInstrAliasOk_arrLoad_noalias ss sam inv x arr idx σ₀ am₀ hinv halias_check)
                rw [hsc]; congr 1
                have hidx_eval : (ssGet ss idx).eval σ₀ am₀ = σ idx := hrepr idx
                rw [hidx_eval, hidxVal]; simp [Value.toInt]
              · rw [ssGet_ssSet_other _ _ _ _ hvx]
                have hupd := Store.update_other σ x v (.int (am.read arr idxVal.toNat)) hvx
                rw [hupd]; exact hrepr v), hinv, hsamCoh⟩
          | arrStore arr idx val =>
            simp [computeNextPC] at hnext_opt
            rw [hnext_opt.symm]
            have hpc_lt : pc < orig.size := bound_of_getElem? horig_opt
            have hwti := hwtp pc hpc_lt
            have hinstr_eq : orig[pc] = .arrStore arr idx val :=
              Option.some.inj ((Array.getElem?_eq_getElem hpc_lt).symm.trans horig_opt)
            rw [hinstr_eq] at hwti
            obtain ⟨idxVal, hidxVal⟩ : ∃ idxVal : BitVec 64, σ idx = .int idxVal := by
              cases hwti with | arrStore hidx _ =>
              exact Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
            obtain ⟨vv, hvv⟩ : ∃ vv : BitVec 64, σ val = .int vv := by
              cases hwti with | arrStore _ hval =>
              exact Value.int_of_typeOf_int (by rw [hts val]; exact hval)
            -- TODO: bounds proof should come from arrayDecls equality or
            -- a hypothesis that the index is in bounds for orig.
            have hbnd : idxVal.toNat < orig.arraySize arr := by sorry
            have hs : Step orig (.run pc σ am) (.run (pc + 1) σ (am.write arr idxVal.toNat vv)) :=
              Step.arrStore horig_opt hidxVal hvv hbnd
            -- arrStore: ss unchanged, σ unchanged. hrepr at am₀ transfers trivially.
            have hexec : (execSymbolic ss sam (.arrStore arr idx val)).1 = ss := rfl
            have hval_eval : (ssGet ss val).eval σ₀ am₀ = .int vv := by
              rw [hrepr val, hvv]
            have hwrite_eq : am.write arr idxVal.toNat vv =
                am.write arr ((ssGet ss idx).eval σ₀ am₀).toInt.toNat vv := by
              have h1 : (ssGet ss idx).eval σ₀ am₀ = .int idxVal := by
                rw [hrepr idx, hidxVal]
              simp [h1, Value.toInt]
            exact ⟨σ, am.write arr idxVal.toNat vv, hs,
              (fun v => by rw [hexec]; exact hrepr v), hinv,
              SamCoherent.cons arr (ssGet ss idx) (ssGet ss val) vv hsamCoh hval_eval hwrite_eq⟩
        | none =>
          -- computeNextPC returned none; use branchInfo fallback
          cases hbi : branchInfo with
          | none =>
            exfalso; revert hnext_eq; rw [hbi]; simp
          | some bi =>
            obtain ⟨origCond, taken⟩ := bi
            cases instr with
            | ifgoto b l_orig =>
              have hexec_id : (execSymbolic ss sam (.ifgoto b l_orig)).1 = ss := rfl
              cases taken with
              | true =>
                have hfb : (b == origCond && nextPC == l_orig) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hbeq, hpc_eq⟩ := and_true_split hfb
                have hbeq := beq_iff_eq.mp hbeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have heval : b.eval σ = true := by
                  rw [hbeq]; exact hbranch origCond true (hbi ▸ rfl)
                exact ⟨σ, am, Step.iftrue horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh⟩
              | false =>
                have hfb : (b == origCond && nextPC == pc + 1) = true := by
                  revert hnext_eq; rw [hbi]; simp
                have ⟨hbeq, hpc_eq⟩ := and_true_split hfb
                have hbeq := beq_iff_eq.mp hbeq
                have hpc_eq := beq_iff_eq.mp hpc_eq; subst hpc_eq
                have heval : b.eval σ = false := by
                  rw [hbeq]; exact hbranch origCond false (hbi ▸ rfl)
                exact ⟨σ, am, Step.iffall horig_opt heval, hexec_id ▸ hrepr, hinv, hsamCoh⟩
            | _ =>
              exfalso; revert hnext_eq; rw [hbi]; cases taken <;> simp
      -- Recursive step (branchInfo = none for rest)
      have hexec : ∀ v, ssGet (execPath orig ss sam pc (nextPC :: rest)).1 v =
          ssGet (execPath orig (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 nextPC rest).1 v := by
        intro v; simp [execPath, horig_opt]
      have hts₁ : TypedStore Γ σ₁ :=
        type_preservation hwtp hts (bound_of_getElem? horig_opt) hstep_orig
      obtain ⟨σ', am', hsteps_rest, hrepr_final, hsamCoh'⟩ :=
        ih (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 σ₁ nextPC none am₁ hts₁ hrepr'
          hsamCoh₁ hpath_inner (fun _ _ h => by simp at h)
      have hexec_sam : (execPath orig ss sam pc (nextPC :: rest)).2 =
          (execPath orig (execSymbolic ss sam instr).1 (execSymbolic ss sam instr).2 nextPC rest).2 := by
        simp [execPath, horig_opt]
      refine ⟨σ', am', Steps.step hstep_orig hsteps_rest, fun v => ?_, hexec_sam ▸ hsamCoh'⟩
      rw [hexec v]; exact hrepr_final v

/-- Path execution soundness: specialization with empty initial symbolic store.
    With empty ss/sam and am₀ = am, the conclusion evaluates at the initial am. -/
private theorem execPath_sound (orig : Prog) (inv : EInv) (σ : Store)
    (pc : Label) (labels : List Label) (pc' : Label)
    (branchInfo : Option (BoolExpr × Bool))
    (am : ArrayMem)
    (Γ : TyCtx) (hwtp : WellTypedProg Γ orig) (hts : TypedStore Γ σ)
    (hrepr : ∀ v, (ssGet ([] : SymStore) v).eval σ am = σ v)
    (hinv : EInv.toProp inv σ am)
    (hInvNoArrRead : inv.all (fun (_, e) => !e.hasArrRead) = true)
    (hpath : checkOrigPath orig ([] : SymStore) ([] : SymArrayMem) inv pc labels pc' branchInfo = true)
    (hbranch : ∀ cond taken, branchInfo = some (cond, taken) →
        cond.eval σ = taken) :
    ∃ σ' am', Steps orig (Cfg.run pc σ am) (Cfg.run pc' σ' am') ∧
          (∀ v, (ssGet (execPath orig ([] : SymStore) ([] : SymArrayMem) pc labels).1 v).eval σ am = σ' v) ∧
          SamCoherent (execPath orig ([] : SymStore) ([] : SymArrayMem) pc labels).2 σ am am' :=
  execPath_sound_gen orig ([] : SymStore) ([] : SymArrayMem) inv σ σ pc labels pc' branchInfo am am
    Γ hwtp hts hrepr hinv (samCoherent_nil σ am) hInvNoArrRead hpath hbranch

/-- If the store relation holds (∀ x, σ_t x = (ssGet ss x).eval σ_o), then evaluating
    `e` at `σ_t` equals evaluating `e.substSym ss` at `σ_o`. Follows from `substSym_sound`. -/
theorem Expr.substSym_consistent (ss : SymStore) (e : Expr) (σ_o σ_t : Store) (am : ArrayMem)
    (hcons : ∀ x, σ_t x = (ssGet ss x).eval σ_o am) :
    e.eval σ_t am = (e.substSym ss).eval σ_o am :=
  (Expr.substSym_sound ss e σ_o σ_t am (fun v => (hcons v).symm)).symm

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
    | arrRead arr idx =>
      have hbeq : (Expr.arrRead arr idx == Expr.var x) = false := by
        rw [beq_eq_false_iff_ne]; exact Expr.noConfusion
      simp only [relGetOrigExpr, List.find?, buildSubstMap, List.filterMap, hbeq]
      exact ih

/-- If `b.mapVarsRel rel = some origCond`, then `b.eval σ_t = origCond.eval σ_o`
    when the store relation holds through `buildSubstMap`. -/
private theorem BoolExpr.eval_mapVarsRel (b origCond : BoolExpr)
    (rel : EExprRel) (σ_t σ_o : Store) (am : ArrayMem)
    (hmap : b.mapVarsRel rel = some origCond)
    (hcons : ∀ x, σ_t x = (ssGet (buildSubstMap rel) x).eval σ_o am) :
    b.eval σ_t = origCond.eval σ_o := by
  induction b generalizing origCond with
  | lit b =>
    simp only [BoolExpr.mapVarsRel] at hmap
    rw [← Option.some.inj hmap]; simp [BoolExpr.eval]
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
    | lit _ => simp [BoolExpr.mapVarsRel]
    | bvar x => simp [BoolExpr.mapVarsRel, relGetOrigExpr, List.find?]
    | cmp op x y => simp [BoolExpr.mapVarsRel, relGetOrigExpr, List.find?]
    | cmpLit op x n => simp [BoolExpr.mapVarsRel, relGetOrigExpr, List.find?]
    | not e ih => simp [BoolExpr.mapVarsRel, ih, Option.map]
  | _ => simp [branchInfoWithRel, transBranchInfo]

/-- When `transBranchInfo` returns `some (cond, taken)`,
    we can derive `cond.eval σ = taken` from any step. -/
private theorem branchInfo_of_step {prog : Prog} {pc pc' : Label} {σ σ' : Store} {am am' : ArrayMem}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
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
      | arrLoad h _ => exact absurd (hinstr.symm.trans h) (by simp)
      | arrStore h _ _ => exact absurd (hinstr.symm.trans h) (by simp)
    · simp [hguard] at hbi
  | _ => simp [transBranchInfo] at hbi

/-- When `branchInfoWithRel` returns `some (origCond, taken)`, a step on the
    transformed program implies `origCond.eval σ_o = taken`
    via the store relation and `eval_mapVarsRel`. -/
private theorem branchInfo_of_step_with_rel {prog : Prog} {pc pc' : Label} {σ_t σ_t' : Store} {am_t am_t' : ArrayMem}
    {instr : TAC} (hinstr : prog[pc]? = some instr)
    (hstep : Step prog (Cfg.run pc σ_t am_t) (Cfg.run pc' σ_t' am_t'))
    {rel : EExprRel} {σ_o : Store} {am_o : ArrayMem}
    (hcons : ∀ x, σ_t x = (ssGet (buildSubstMap rel) x).eval σ_o am_o)
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
        have heval := BoolExpr.eval_mapVarsRel b origCond' rel σ_t σ_o am_o hmap hcons
        rw [← heval]; exact hbranch
      · simp [hguard] at hbi
  | _ => simp [branchInfoWithRel] at hbi

/-- ssGet from an arrRead-free SymStore returns arrRead-free expressions. -/
private theorem ssGet_noArrRead_of_all (ss : SymStore) (v : Var)
    (hall : ss.all (fun (_, e) => !e.hasArrRead) = true) :
    (ssGet ss v).hasArrRead = false := by
  unfold ssGet
  generalize hfind : ss.find? (fun p => p.1 == v) = result
  cases result with
  | none => simp [Expr.hasArrRead]
  | some entry =>
    have hmem : entry ∈ ss := List.mem_of_find?_eq_some hfind
    rw [List.all_eq_true] at hall
    have h := hall entry hmem; simp at h; exact h

/-- buildSubstMap preserves arrRead-freeness from the original-side expressions. -/
private theorem buildSubstMap_noArrRead (rel : EExprRel)
    (hnoarr : rel.all (fun (e, _) => !e.hasArrRead) = true) :
    (buildSubstMap rel).all (fun (_, e) => !e.hasArrRead) = true := by
  rw [List.all_eq_true]; intro ⟨w, e⟩ hmem
  simp only [buildSubstMap, List.mem_filterMap] at hmem
  obtain ⟨⟨e_o, e_t⟩, hmem_rel, hsome⟩ := hmem
  rw [List.all_eq_true] at hnoarr
  cases e_t with
  | var x => simp at hsome; obtain ⟨rfl, rfl⟩ := hsome; exact hnoarr _ hmem_rel
  | _ => simp at hsome

/-- If all original-side expressions in a relation are arrRead-free,
    then ssGet of the corresponding buildSubstMap is arrRead-free for any variable. -/
private theorem ssGet_buildSubstMap_noArrRead (rel : EExprRel) (v : Var)
    (hnoarr : rel.all (fun (e, _) => !e.hasArrRead) = true) :
    (ssGet (buildSubstMap rel) v).hasArrRead = false :=
  ssGet_noArrRead_of_all _ v (buildSubstMap_noArrRead rel hnoarr)

/-- BoolExpr.toSymExpr on the empty store is arrRead-free. -/
private theorem BoolExpr.toSymExpr_nil_noArrRead (be : BoolExpr) :
    (be.toSymExpr ([] : SymStore)).hasArrRead = false := by
  induction be with
  | lit _ => simp [BoolExpr.toSymExpr, Expr.hasArrRead]
  | bvar x => simp [BoolExpr.toSymExpr, Expr.hasArrRead, ssGet_nil_var]
  | cmp _ x y => simp [BoolExpr.toSymExpr, Expr.hasArrRead, ssGet_nil_var]
  | cmpLit _ x _ => simp [BoolExpr.toSymExpr, Expr.hasArrRead, ssGet_nil_var]
  | not _ ih => simp [BoolExpr.toSymExpr, Expr.hasArrRead, ih]

/-- ssGet from ssSet on [] is arrRead-free when the stored expression is. -/
private theorem ssGet_ssSet_nil_noArrRead (x : Var) (e : Expr) (v : Var)
    (he : e.hasArrRead = false) :
    (ssGet (ssSet ([] : SymStore) x e) v).hasArrRead = false := by
  by_cases hv : v = x
  · subst hv; rw [ssGet_ssSet_same]; exact he
  · rw [ssGet_ssSet_other _ _ _ _ hv, ssGet_nil_var]; simp [Expr.hasArrRead]

/-- If SamCoherent relates the empty SAM, the array memory is unchanged. -/
private theorem samCoherent_nil_am_eq {σ : Store} {am am' : ArrayMem}
    (h : SamCoherent [] σ am am') : am' = am := by
  cases h; rfl

/-- Extract index/value types from an arrStore step that produces Cfg.run. -/
private theorem arrStore_step_values {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    {arr : ArrayName} {idx val : Var}
    (hinstr : p[pc]? = some (.arrStore arr idx val))
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am')) :
    ∃ iv vv : BitVec 64, σ idx = .int iv ∧ σ val = .int vv ∧
      am' = am.write arr iv.toNat vv ∧ σ' = σ := by
  cases hstep with
  | arrStore h hidx hval =>
    rw [hinstr] at h; cases h; exact ⟨_, _, hidx, hval, rfl, rfl⟩
  | _ => all_goals simp_all

/-- A non-arrStore step preserves array memory. -/
private theorem step_am_preserved {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : Step p (Cfg.run pc σ am) (Cfg.run pc' σ' am'))
    (h : ∀ arr idx val, p[pc]? ≠ some (.arrStore arr idx val)) : am' = am := by
  cases hstep with
  | arrStore hinstr _ _ => exact absurd hinstr (h _ _ _)
  | _ => rfl

private theorem checkRelConsistency_amCheck
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel) (allVars : List Var)
    (h : checkRelConsistency orig pc_orig origLabels transInstr inv_orig rel_pre rel_post allVars = true) :
    (execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels).2.length =
      (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).2.length ∧
    ((execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels).2.zip
      (execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr).2).all
      (fun ((a_o, i_o, v_o), (a_t, i_t, v_t)) =>
        a_o == a_t &&
        i_o.simplify inv_orig == (i_t.substSym (buildSubstMap rel_pre)).simplify inv_orig &&
        v_o.simplify inv_orig == (v_t.substSym (buildSubstMap rel_pre)).simplify inv_orig) = true := by
  unfold checkRelConsistency at h
  rw [Bool.and_eq_true] at h
  have ham := h.2
  rw [Bool.and_eq_true] at ham
  exact ⟨beq_iff_eq.mp ham.1, ham.2⟩

set_option maxHeartbeats 400000 in
/-- Soundness of checkTransitionRelProp from the Bool checks.
    Given: checkOrigPath and checkRelConsistency both pass, the original path
    produces steps reaching the target with store relation preserved.
    Supports non-trivial expression relations. -/
private theorem transRel_sound (dc : ECertificate)
    (hwtp : WellTypedProg dc.tyCtx dc.orig)
    (hnoarr_orig : checkNoArrReadInInvs dc.inv_orig = true)
    (pc_t pc_t' : Label)
    (dic : EInstrCert) (dtc : ETransCorr) (instr : TAC)
    (pc_o' : Label)
    (hnoarr_rel : dtc.rel.all (fun (e, _) => !e.hasArrRead) = true)
    (hnoarr_rel_next : dtc.rel_next.all (fun (e, _) => !e.hasArrRead) = true)
    (hinstr : dc.trans[pc_t]? = some instr)
    (hpath : checkOrigPath dc.orig ([] : SymStore) ([] : SymArrayMem) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dic.pc_orig dtc.origLabels pc_o'
      (branchInfoWithRel instr dtc.rel pc_t pc_t') = true)
    (hrelcheck : checkRelConsistency
      dc.orig dic.pc_orig dtc.origLabels instr
      (dc.inv_orig.getD dic.pc_orig ([] : EInv))
      dtc.rel dtc.rel_next (collectAllVars dc.orig dc.trans) = true) :
    checkTransitionRelProp dc.tyCtx dc.orig dc.trans
      (fun l => (dc.inv_orig.getD l ([] : EInv)).toProp)
      (fun l => (dc.inv_trans.getD l ([] : EInv)).toProp)
      pc_t pc_t' dic.pc_orig pc_o'
      { origLabels := dtc.origLabels
        storeRel := eRelToStoreRel dtc.rel
        storeRel_next := eRelToStoreRel dtc.rel_next } := by
  intro σ_t σ_t' σ_o am_t am_t' am_o hinv_t hinv_o hcons ham_eq hts_o hstep
  -- hcons : eRelToStoreRel dtc.rel σ_o am_o σ_t am_t, i.e. ∀ x, σ_t x = (ssGet (buildSubstMap dtc.rel) x).eval σ_o am_o
  change ∀ x, σ_t x = (ssGet (buildSubstMap dtc.rel) x).eval σ_o am_o at hcons
  -- Branch info transfers through the relation
  have hbranch_orig : ∀ cond taken,
      branchInfoWithRel instr dtc.rel pc_t pc_t' = some (cond, taken) →
      cond.eval σ_o = taken :=
    fun cond taken hbi => branchInfo_of_step_with_rel hinstr hstep hcons hbi
  -- Execute original path from σ_o
  obtain ⟨σ_o', am_o', horig_steps, horig_repr, hsamCoh_orig⟩ := execPath_sound dc.orig
    (dc.inv_orig.getD dic.pc_orig ([] : EInv)) σ_o
    dic.pc_orig dtc.origLabels pc_o'
    (branchInfoWithRel instr dtc.rel pc_t pc_t')
    am_o
    dc.tyCtx hwtp hts_o (ssGet_nil σ_o am_o) hinv_o
    (noArrRead_of_inv_all dc.inv_orig hnoarr_orig dic.pc_orig)
    hpath hbranch_orig
  -- Prove am_t' = am_o' (uses separate helper to avoid large context)
  have ham_eq' : am_t' = am_o' := by
    have ⟨hlen_eq, hzip_check⟩ := checkRelConsistency_amCheck dc.orig dic.pc_orig dtc.origLabels instr
      (dc.inv_orig.getD dic.pc_orig ([] : EInv)) dtc.rel dtc.rel_next
      (collectAllVars dc.orig dc.trans) hrelcheck
    by_cases hinstr_arr : ∃ arr idx val, instr = .arrStore arr idx val
    · -- arrStore case: both sides write the same thing
      obtain ⟨arr, idx, val, rfl⟩ := hinstr_arr
      obtain ⟨idxVal, vv, hidxV, hvv, ham_t'_eq, _⟩ :=
        arrStore_step_values hinstr hstep
      -- origSAM must be a singleton (transSAM has length 1)
      simp only [execSymbolic] at hlen_eq hzip_check
      obtain ⟨⟨a_o, i_o, v_o⟩, horigSAM_eq⟩ :
          ∃ e, (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 = [e] := by
        match hm : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 with
        | [] => simp_all [List.length]
        | [e] => exact ⟨e, rfl⟩
        | _ :: _ :: _ => simp_all [List.length]
      rw [horigSAM_eq] at hzip_check
      have hsamCoh_eq : SamCoherent [(a_o, i_o, v_o)] σ_o am_o am_o' := horigSAM_eq ▸ hsamCoh_orig
      simp only [List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil,
        Bool.and_true] at hzip_check
      have hzc := hzip_check
      rw [Bool.and_eq_true] at hzc
      have h12 := hzc.1; have hv_match := hzc.2
      rw [Bool.and_eq_true] at h12
      have harr_eq : a_o = arr := beq_iff_eq.mp h12.1
      have hidx_eq := beq_iff_eq.mp h12.2
      have hval_eq := beq_iff_eq.mp hv_match
      cases hsamCoh_eq with
      | cons _ _ _ bv_o hprev hvalint hwrite =>
        cases hprev
        have inv_def := dc.inv_orig.getD dic.pc_orig ([] : EInv)
        set inv_e := dc.inv_orig.getD dic.pc_orig ([] : EInv)
        have hidx_sem : i_o.eval σ_o am_o = σ_t idx :=
          calc i_o.eval σ_o am_o
              = (i_o.simplify inv_e).eval σ_o am_o :=
                  (Expr.simplify_sound inv_e i_o σ_o am_o hinv_o).symm
            _ = (((ssGet ([] : SymStore) idx).substSym (buildSubstMap dtc.rel)).simplify inv_e).eval σ_o am_o :=
                  by rw [hidx_eq]
            _ = ((ssGet ([] : SymStore) idx).substSym (buildSubstMap dtc.rel)).eval σ_o am_o :=
                  Expr.simplify_sound inv_e _ σ_o am_o hinv_o
            _ = (ssGet ([] : SymStore) idx).eval σ_t am_o :=
                  Expr.substSym_sound _ _ σ_o σ_t am_o (fun w => (hcons w).symm)
            _ = σ_t idx := by simp [ssGet, List.find?, Expr.eval]
        have hval_sem : v_o.eval σ_o am_o = σ_t val :=
          calc v_o.eval σ_o am_o
              = (v_o.simplify inv_e).eval σ_o am_o :=
                  (Expr.simplify_sound inv_e v_o σ_o am_o hinv_o).symm
            _ = (((ssGet ([] : SymStore) val).substSym (buildSubstMap dtc.rel)).simplify inv_e).eval σ_o am_o :=
                  by rw [hval_eq]
            _ = ((ssGet ([] : SymStore) val).substSym (buildSubstMap dtc.rel)).eval σ_o am_o :=
                  Expr.simplify_sound inv_e _ σ_o am_o hinv_o
            _ = (ssGet ([] : SymStore) val).eval σ_t am_o :=
                  Expr.substSym_sound _ _ σ_o σ_t am_o (fun w => (hcons w).symm)
            _ = σ_t val := by simp [ssGet, List.find?, Expr.eval]
        -- Chain: am_t' = am_t.write ... = am_o.write ... = am_o'
        have hvv_eq : vv = bv_o := by
          have := hval_sem; rw [hvv] at this; rw [this] at hvalint
          exact Value.int.inj hvalint
        rw [ham_t'_eq, ham_eq, hwrite, harr_eq, hidx_sem, hidxV, hvv_eq]
        simp [Value.toInt]
    · -- Non-arrStore: AM unchanged on both sides
      push_neg at hinstr_arr
      have ham_t : am_t' = am_t := step_am_preserved hstep (fun a i v h =>
        hinstr_arr a i v (by rw [hinstr] at h; exact Option.some.inj h))
      have htransSAM_nil : (execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).2 = [] := by
        cases instr with
        | arrStore a i v => exact absurd rfl (hinstr_arr a i v)
        | const x v => cases v <;> rfl
        | _ => rfl
      rw [htransSAM_nil] at hlen_eq
      have horigSAM_nil : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 = [] := by
        match hm : (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).2 with
        | [] => rfl
        | _ :: _ => simp_all [List.length]
      have ham_o : am_o' = am_o :=
        samCoherent_nil_am_eq (show SamCoherent [] σ_o am_o am_o' by rw [← horigSAM_nil]; exact hsamCoh_orig)
      rw [ham_t, ham_o, ham_eq]
  -- Prove store relation holds at the target: eRelToStoreRel dtc.rel_next σ_o' σ_t'
  refine ⟨σ_o', am_o', horig_steps, ?_, ham_eq'⟩
  -- Goal: ∀ v, σ_t' v = (ssGet (buildSubstMap dtc.rel_next) v).eval σ_o' am_o'
  intro v
  -- Abbreviations
  let origSS := (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).1
  let transSS := (execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1
  let preSubst := buildSubstMap dtc.rel
  let postSubst := buildSubstMap dtc.rel_next
  let inv := dc.inv_orig.getD dic.pc_orig ([] : EInv)
  let allVars := collectAllVars dc.orig dc.trans
  -- execSymbolic_sound: transSS tracks the transformed step
  have htrans_repr : ∀ w, (ssGet transSS w).eval σ_t am_t = σ_t' w := by
    by_cases hscalar : instr.isScalar = true
    · exact execSymbolic_sound ([] : SymStore) ([] : SymArrayMem) instr σ_t σ_t σ_t' pc_t pc_t' dc.trans am_t
        (ssGet_nil σ_t am_t) hstep hinstr hscalar
    · cases instr with
      | arrStore arr idx val =>
        show ∀ w, (ssGet (execSymbolic ([] : SymStore) ([] : SymArrayMem) (.arrStore arr idx val)).1 w).eval σ_t am_t = σ_t' w
        simp only [execSymbolic]
        have step_det : ∀ c, Step dc.trans (Cfg.run pc_t σ_t am_t) c → c = Cfg.run pc_t' σ_t' am_t' :=
          fun c hc => Step.deterministic hc hstep
        obtain ⟨idxVal, hv⟩ : ∃ idxVal : BitVec 64, σ_t idx = .int idxVal := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        obtain ⟨vv, hvv⟩ : ∃ vv : BitVec 64, σ_t val = .int vv := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hbnd : idxVal.toNat < dc.trans.arraySize arr := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have := step_det _ (Step.arrStore hinstr hv hvv hbnd)
        have hσ' : σ_t' = σ_t := (Cfg.run.inj this).2.1.symm
        rw [hσ']; exact ssGet_nil σ_t am_t
      | arrLoad dest arr idx =>
        -- arrLoad on transformed side: uses am_t for consistency with relation
        show ∀ w, (ssGet (ssSet [] dest (.arrRead arr (ssGet [] idx))) w).eval σ_t am_t = σ_t' w
        have step_det : ∀ c, Step dc.trans (Cfg.run pc_t σ_t am_t) c → c = Cfg.run pc_t' σ_t' am_t' :=
          fun c hc => Step.deterministic hc hstep
        obtain ⟨idxVal, hidx⟩ : ∃ idxVal : BitVec 64, σ_t idx = .int idxVal := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have hbnd : idxVal.toNat < dc.trans.arraySize arr := by
          revert hstep; intro hstep; cases hstep <;> simp_all
        have := step_det _ (Step.arrLoad hinstr hidx hbnd)
        have hσ' : σ_t' = σ_t[dest ↦ .int (am_t.read arr idxVal.toNat)] :=
          (Cfg.run.inj this).2.1.symm
        intro w
        by_cases hwd : w = dest
        · -- v = dest: symbolic store has .arrRead arr (.var idx)
          rw [hwd, ssGet_ssSet_same]
          simp only [Expr.eval, ssGet_nil, Expr.eval]
          rw [hidx]; simp [Value.toInt, hσ', Store.update_self]
        · rw [ssGet_ssSet_other _ _ _ _ hwd, hσ', ssGet_nil]
          exact (Store.update_other σ_t dest w _ hwd).symm
      | _ => exact absurd rfl hscalar
  -- preSubst soundness: (ssGet preSubst w).eval σ_o am_o = σ_t w
  have hpre_sound : ∀ w, (ssGet preSubst w).eval σ_o am_o = σ_t w :=
    fun w => (hcons w).symm
  -- substSym_sound for preSubst: for any expr e, (e.substSym preSubst).eval σ_o am_o = e.eval σ_t am_o
  have hpre_subst : ∀ (e : Expr), (e.substSym preSubst).eval σ_o am_o = e.eval σ_t am_o :=
    fun e => Expr.substSym_sound preSubst e σ_o σ_t am_o hpre_sound
  -- Classify v: either in the checked variable set or not in any program variable
  by_cases hmem : v ∈ allVars ++ preSubst.map Prod.fst ++ postSubst.map Prod.fst
  · -- Case 1: v is in the checked set — use the checker result
    -- Extract the checker guarantee for v
    unfold checkRelConsistency at hrelcheck
    rw [Bool.and_eq_true] at hrelcheck
    rw [List.all_eq_true] at hrelcheck
    have hcheck_v := hrelcheck.1 v hmem
    have hbeq := beq_iff_eq.mp hcheck_v
    -- hbeq : ((ssGet postSubst v).substSym origSS).simplify inv =
    --         ((ssGet transSS v).substSym preSubst).simplify inv
    -- By simplify_sound (σ_o satisfies inv):
    have hlhs := Expr.simplify_sound inv ((ssGet postSubst v).substSym origSS) σ_o am_o hinv_o
    have hrhs := Expr.simplify_sound inv ((ssGet transSS v).substSym preSubst) σ_o am_o hinv_o
    -- Chain the equalities.
    -- htrans_repr evaluates at am_t, hpre_subst at am_o, horig_repr at am_o'.
    -- The checker compares simplified expressions (syntactically), which bridge across ams.
    -- For arrRead-free expressions these all agree; for arrRead expressions Part B fixes this.
    -- horig_repr now evaluates at am_o (fixed initial am), so substSym_sound gives am_o
    have horig_subst : ∀ (e : Expr), (e.substSym origSS).eval σ_o am_o = e.eval σ_o' am_o :=
      fun e => Expr.substSym_sound origSS e σ_o σ_o' am_o horig_repr
    -- preSubst soundness at am_o: (e.substSym preSubst).eval σ_o am_o = e.eval σ_t am_o
    have hpre_subst_ao : ∀ (e : Expr), (e.substSym preSubst).eval σ_o am_o = e.eval σ_t am_o :=
      fun e => Expr.substSym_sound preSubst e σ_o σ_t am_o hpre_sound
    -- The chain goes entirely through am_o (fixed array mem):
    -- htrans_repr at am_t, then bridge am_t→am_o, then all at am_o, then bridge am_o→am_o'
    -- Bridge am_t→am_o: use ham_eq (am_t = am_o)
    -- Bridge am_o→am_o' for postSubst (arrRead-free from checkNoArrReadInRels)
    have hpostSubst_noarr : (ssGet postSubst v).hasArrRead = false :=
      ssGet_buildSubstMap_noArrRead dtc.rel_next v hnoarr_rel_next
    calc σ_t' v
        = (ssGet transSS v).eval σ_t am_t := (htrans_repr v).symm
      _ = (ssGet transSS v).eval σ_t am_o := by rw [ham_eq]
      _ = ((ssGet transSS v).substSym preSubst).eval σ_o am_o := (hpre_subst_ao _).symm
      _ = (((ssGet transSS v).substSym preSubst).simplify inv).eval σ_o am_o := hrhs.symm
      _ = (((ssGet postSubst v).substSym origSS).simplify inv).eval σ_o am_o := by rw [hbeq]
      _ = ((ssGet postSubst v).substSym origSS).eval σ_o am_o := hlhs
      _ = (ssGet postSubst v).eval σ_o' am_o := horig_subst _
      _ = (ssGet postSubst v).eval σ_o' am_o' :=
            Expr.eval_noArrRead _ σ_o' am_o am_o' hpostSubst_noarr
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
      show ssGet ((execSymbolic ([] : SymStore) ([] : SymArrayMem) instr).1) v = Expr.var v
      rw [execSymbolic_preserves_var ([] : SymStore) ([] : SymArrayMem) instr v hv_trans]
      exact ssGet_nil_var v
    -- v not in any instruction of orig: origSS preserves v
    have horig_id : ssGet origSS v = Expr.var v := by
      show ssGet (execPath dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels).1 v = Expr.var v
      rw [execPath_preserves_var dc.orig ([] : SymStore) ([] : SymArrayMem) dic.pc_orig dtc.origLabels v
        (fun l instr' hinstr' hv => hv_allvars
          (instrVars_sub_collectAllVars_left dc.orig dc.trans instr'
            (getElem?_mem_toList hinstr') v hv))]
      exact ssGet_nil_var v
    -- Chain: σ_t' v = σ_t v = σ_o v = σ_o' v = (.var v).eval σ_o' am_o'
    calc σ_t' v
        = (ssGet transSS v).eval σ_t am_t := (htrans_repr v).symm
      _ = (Expr.var v).eval σ_t am_t := by rw [htrans_id]
      _ = σ_t v := by simp [Expr.eval]
      _ = σ_o v := hσ_eq
      _ = (ssGet origSS v).eval σ_o am_o := by rw [horig_id]; simp [Expr.eval]
      _ = σ_o' v := horig_repr v
      _ = (Expr.var v).eval σ_o' am_o' := by simp [Expr.eval]
      _ = (ssGet postSubst v).eval σ_o' am_o' := by rw [hpost_id]

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
      checkOrigPath dc.orig ([] : SymStore) ([] : SymArrayMem) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
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
    (hwtp : WellTypedProg dc.tyCtx dc.orig)
    (hnoarr_orig : checkNoArrReadInInvs dc.inv_orig = true)
    (hnoarr_rels : checkNoArrReadInRels dc.instrCerts = true)
    (h : checkAllTransitionsExec dc = true) :
    checkAllTransitionsProp dc.tyCtx (toPCertificate dc) := by
  intro pc_t σ_t σ_t' pc_t' am_t am_t' hstep
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
    have hpath' : checkOrigPath dc.orig ([] : SymStore) ([] : SymArrayMem) (dc.inv_orig.getD dic.pc_orig ([] : EInv))
        dic.pc_orig dtc.origLabels (dc.instrCerts.getD pc_t' default).pc_orig
        (branchInfoWithRel instr dtc.rel pc_t pc_t') = true := by
      rw [hrel_eq]; exact hpath
    simp only [toPCertificate, hgetD]
    -- Extract arrRead-free conditions for dtc's relations from hnoarr_rels
    have hnoarr_dtc : dtc.rel.all (fun (e, _) => !e.hasArrRead) = true ∧
        dtc.rel_next.all (fun (e, _) => !e.hasArrRead) = true := by
      unfold checkNoArrReadInRels at hnoarr_rels
      have hbound := bound_of_getElem? hdic
      have hget := (Array.getElem?_eq_some_iff.mp hdic).2
      have hic := (Array.all_eq_true.mp hnoarr_rels) pc_t hbound
      rw [hget, Bool.and_eq_true] at hic
      have htrans_all := List.all_eq_true.mp hic.2 dtc hdtc_mem
      rw [Bool.and_eq_true] at htrans_all
      exact htrans_all
    have hnoarr_dtc_rel := hnoarr_dtc.1
    have hnoarr_dtc_rel_next := hnoarr_dtc.2
    exact transRel_sound dc hwtp hnoarr_orig pc_t pc_t' dic dtc instr
      ((dc.instrCerts.getD pc_t' default).pc_orig)
      hnoarr_dtc_rel hnoarr_dtc_rel_next
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
  intro pc_t pc_t' σ_t σ_t' σ_o am_t am_o _ _ _ hexec horig_eq
  obtain ⟨c', hstep, am_t', hc'⟩ := hexec; subst hc'
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

/-- If `checkDivPreservationExec` passes, then `checkErrorPreservationProp` holds. -/
theorem checkDivPreservationExec_sound (dc : ECertificate)
    (h : checkDivPreservationExec dc = true) :
    checkErrorPreservationProp (toPCertificate dc) := by
  intro pc_t σ_t σ_o am_t am_o hpc hrel hinv_t hinv_o herr_step
  -- Extract the check result for this specific pc_t
  have hmem : pc_t ∈ List.range dc.trans.size := List.mem_range.mpr hpc
  have hcheck := (List.all_eq_true.mp h) pc_t hmem
  -- Since pc_t < dc.trans.size, dc.trans[pc_t]? = some instr
  obtain ⟨instr, hinstr⟩ : ∃ instr, dc.trans[pc_t]? = some instr :=
    ⟨dc.trans[pc_t], getElem?_eq_some_iff.mpr ⟨hpc, rfl⟩⟩
  -- Simplify toPCertificate in goal and hypotheses
  simp only [toPCertificate] at herr_step hrel ⊢
  set dic := dc.instrCerts.getD pc_t default with hdic_def
  cases herr_step with
  | error hinstr_binop hya hzb hunsafe =>
    rename_i x op y z a b
    simp only [hinstr_binop] at hcheck
    generalize horig : dc.orig[dic.pc_orig]? = orig_opt at hcheck
    cases orig_opt with
    | none => simp at hcheck
    | some orig_instr =>
      cases orig_instr with
      | binop x' op' y' z' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
        obtain ⟨⟨hop, hrel_y_eq⟩, hrel_z_eq⟩ := hcheck
        subst hop
        -- From the expression relation: σ_t y = σ_o y', σ_t z = σ_o z'
        have hrel_y : σ_t y = σ_o y' := by
          have := hrel y; rw [hrel_y_eq, Expr.eval] at this; exact this
        have hrel_z : σ_t z = σ_o z' := by
          have := hrel z; rw [hrel_z_eq, Expr.eval] at this; exact this
        -- Transfer to original side
        have hy' : σ_o y' = .int a := by rw [← hrel_y, hya]
        have hz' : σ_o z' = .int b := by rw [← hrel_z, hzb]
        -- Construct Step.error on the original side
        exact ⟨σ_o, am_o, Steps.step (Step.error horig hy' hz' hunsafe) .refl⟩
      | _ => simp at hcheck
  | arrLoad_boundsError hinstr_arr hidxVal hbnd =>
    -- TODO: prove via checkBoundsPreservationExec
    -- Need to show that the original program also has a bounds error
    -- at the corresponding array instruction. Requires arrayDecls equality.
    exact ⟨σ_o, am_o, by sorry⟩
  | arrStore_boundsError hinstr_arr hidxVal hvv hbnd =>
    -- TODO: prove via checkBoundsPreservationExec
    -- Need to show that the original program also has a bounds error
    -- at the corresponding array instruction. Requires arrayDecls equality.
    exact ⟨σ_o, am_o, by sorry⟩

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
  · intro pc pc' σ σ' am am' hpc hstep
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
    | arrLoad hi _ =>
      have := hall pc hpc; simp [hi, successors] at this; exact this
    | arrStore hi _ _ =>
      have := hall pc hpc; simp [hi, successors] at this; exact this

theorem soundness_bridge
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx) :
    PCertificateValid (toPCertificate dc) := by
  -- checkCertificateExec is: wt_orig && wt_trans && same_obs && c1..c14
  -- && is left-associative, so decompose from right to left (17 conjuncts, 16 steps)
  unfold checkCertificateExec at h
  have ⟨ha, h_step_bounds⟩ := and_true_of_and_eq_true h
  have ⟨hb, h_arrsize⟩    := and_true_of_and_eq_true ha
  have ⟨hc, h_bndpres⟩    := and_true_of_and_eq_true hb
  have ⟨hd, h_div⟩        := and_true_of_and_eq_true hc
  have ⟨he, h_nonterm⟩    := and_true_of_and_eq_true hd
  have ⟨hf, h_haltobs⟩    := and_true_of_and_eq_true he
  have ⟨hg, h_haltcorr⟩   := and_true_of_and_eq_true hf
  have ⟨hh, h_trans⟩      := and_true_of_and_eq_true hg
  have ⟨hh2, h_noarr_rels⟩ := and_true_of_and_eq_true hh
  have ⟨hi, h_noarr_t⟩    := and_true_of_and_eq_true hh2
  have ⟨hj, h_noarr_o⟩    := and_true_of_and_eq_true hi
  have ⟨hk, h_invpres⟩    := and_true_of_and_eq_true hj
  have ⟨hl, h_relstart⟩   := and_true_of_and_eq_true hk
  have ⟨hm, h_invstart⟩   := and_true_of_and_eq_true hl
  have ⟨hn, h_startcorr⟩  := and_true_of_and_eq_true hm
  have ⟨ho, hobs_eq⟩      := and_true_of_and_eq_true hn
  have ⟨hwt_orig, hwt_trans⟩ := and_true_of_and_eq_true ho
  -- Derive rel=[] at start from checkRelAtStartExec (h3)
  have hrel0 : (dc.instrCerts.getD 0 default).rel = [] := by
    revert h_relstart; simp only [checkRelAtStartExec]
    cases (dc.instrCerts.getD 0 default).rel with
    | nil => intro; rfl
    | cons => simp [List.isEmpty]
  exact {
    well_typed_orig  := by simp [toPCertificate]; exact checkWellTypedProg_sound hwt_orig
    well_typed_trans := by simp [toPCertificate]; exact checkWellTypedProg_sound hwt_trans
    same_tyCtx       := by simp [toPCertificate]; exact htyctx
    same_observable  := by
      simp [toPCertificate]
      exact beq_iff_eq.mp hobs_eq
    start_corr    := checkStartCorrespondenceExec_sound dc h_startcorr hrel0
    start_inv     := checkInvariantsAtStartExec_sound dc h_invstart
    inv_preserved := checkInvariantsPreservedExec_sound dc h_invpres h_noarr_o h_noarr_t
    transitions   := checkAllTransitionsExec_sound dc (checkWellTypedProg_sound hwt_orig) h_noarr_o h_noarr_rels h_trans
    halt_corr     := checkHaltCorrespondenceExec_sound dc h_haltcorr
    halt_obs      := checkHaltObservableExec_sound dc h_haltobs
    nonterm       := checkNonterminationExec_sound dc h_nonterm
    error_pres    := checkDivPreservationExec_sound dc h_div
    step_closed   := checkSuccessorsInBounds_sound dc h_step_bounds
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


/-- **Totality**: If the executable checker accepts, the transformed program
    has a behavior for every well-typed initial store. -/
theorem trans_has_behavior
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx)
    (σ₀ : Store) :
    ∃ b, program_behavior dc.trans σ₀ b :=
  has_behavior dc.trans σ₀ (soundness_bridge dc h htyctx).step_closed

/-- **End-to-end correctness**: If the executable checker accepts,
    then every behavior of the transformed program has a corresponding
    behavior in the original program (with observable equivalence at halt).

    This is the composition of `soundness_bridge` and
    `credible_compilation_soundness` — the complete pipeline from
    `checkCertificateExec dc = true` to semantic preservation. -/
theorem exec_checker_correct
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx)
    (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀) (b : Behavior)
    (htrans : program_behavior dc.trans σ₀ b) :
    ∃ b', program_behavior dc.orig σ₀ b' ∧
      match b, b' with
      | .halts σ_t, .halts σ_o =>
          ∀ v ∈ dc.observable, σ_t v = σ_o v
      | .errors _, .errors _ => True
      | .typeErrors _, _ => True
      | .diverges, .diverges => True
      | _, _ => False := by
  have hvalid := soundness_bridge dc h htyctx
  cases b with
  | halts σ_t' =>
    obtain ⟨σ_o', ho, hobs⟩ := soundness_halt
      (toPCertificate dc) hvalid σ₀ σ_t' hts₀ htrans
    exact ⟨.halts σ_o', ho, hobs⟩
  | errors σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := htrans
    obtain ⟨σ_o, am_o, am_o', ho⟩ := error_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ hreach
    exact ⟨.errors σ_o, ⟨am_o, am_o', ho⟩, trivial⟩
  | typeErrors σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := htrans
    have hwt : WellTypedProg dc.tyCtx dc.trans := by
      rw [ECertificate.tyCtx, htyctx]; exact hvalid.well_typed_trans
    exact absurd hreach (type_safety hwt hts₀ hvalid.step_closed)
  | diverges =>
    obtain ⟨f, hinf, hf0⟩ := htrans
    obtain ⟨g, hg, hg0⟩ := soundness_diverge
      (toPCertificate dc) hvalid f σ₀ hts₀ hinf hf0
    exact ⟨.diverges, ⟨g, hg, hg0⟩, trivial⟩

/-- **Complete end-to-end**: checker accepts → every initial store has a behavior
    in the transformed program, and that behavior is matched by the original. -/
theorem exec_checker_total
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx)
    (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀) :
    ∃ b, program_behavior dc.trans σ₀ b ∧
      ∃ b', program_behavior dc.orig σ₀ b' ∧
        match b, b' with
        | .halts σ_t, .halts σ_o => ∀ v ∈ dc.observable, σ_t v = σ_o v
        | .errors _, .errors _ => True
        | .typeErrors _, _ => True
        | .diverges, .diverges => True
        | _, _ => False := by
  obtain ⟨b, hb⟩ := trans_has_behavior dc h htyctx σ₀
  have hvalid := soundness_bridge dc h htyctx
  cases b with
  | halts σ_t =>
    obtain ⟨σ_o', ho, hobs⟩ := soundness_halt
      (toPCertificate dc) hvalid σ₀ σ_t hts₀ hb
    exact ⟨.halts σ_t, hb, .halts σ_o', ho, hobs⟩
  | errors σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := hb
    obtain ⟨σ_o, am_o, am_o', ho⟩ := error_preservation
      (toPCertificate dc) hvalid σ₀ hts₀ hreach
    exact ⟨.errors σ_e, ⟨am₀, am_e, hreach⟩, .errors σ_o, ⟨am_o, am_o', ho⟩, trivial⟩
  | typeErrors σ_e =>
    obtain ⟨am₀, am_e, hreach⟩ := hb
    have hwt : WellTypedProg dc.tyCtx dc.trans := by
      rw [ECertificate.tyCtx, htyctx]; exact hvalid.well_typed_trans
    exact absurd hreach (type_safety hwt hts₀ hvalid.step_closed)
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
theorem exec_halt_preservation
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx)
    (σ₀ σ_t' : Store) (hts₀ : TypedStore dc.tyCtx σ₀)
    (hexec : ∃ am am', haltsWithResult dc.trans 0 σ₀ σ_t' am am') :
    ∃ σ_o', (∃ am am', haltsWithResult dc.orig 0 σ₀ σ_o' am am') ∧
      ∀ v ∈ dc.observable, σ_t' v = σ_o' v :=
  soundness_halt (toPCertificate dc) (soundness_bridge dc h htyctx) σ₀ σ_t' hts₀ hexec

/-- **Error preservation (executable)**: If the executable checker accepts and
    the transformed program reaches an error state, the original
    program also reaches an error state. -/
theorem exec_error_preservation
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx)
    (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀) {σ_e : Store} {am₀ am_e : ArrayMem}
    (hreach : dc.trans ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.error σ_e am_e) :
    ∃ σ_o am_o am_o', dc.orig ⊩ Cfg.run 0 σ₀ am_o ⟶* Cfg.error σ_o am_o' :=
  error_preservation (toPCertificate dc) (soundness_bridge dc h htyctx) σ₀ hts₀ hreach

/-- **Divergence preservation (executable)**: If the executable checker accepts
    and the transformed program diverges, the original program also diverges. -/
theorem exec_diverge_preservation
    (dc : ECertificate) (h : checkCertificateExec dc = true)
    (htyctx : dc.orig.tyCtx = dc.trans.tyCtx)
    (f : Nat → Cfg) (σ₀ : Store) (hts₀ : TypedStore dc.tyCtx σ₀)
    (hinf : IsInfiniteExec dc.trans f)
    (hf0 : f 0 = Cfg.run 0 σ₀ ArrayMem.init) :
    ∃ g : Nat → Cfg, IsInfiniteExec dc.orig g ∧ g 0 = Cfg.run 0 σ₀ ArrayMem.init :=
  soundness_diverge (toPCertificate dc) (soundness_bridge dc h htyctx) f σ₀ hts₀ hinf hf0
