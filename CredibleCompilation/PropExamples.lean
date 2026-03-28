import CredibleCompilation.PropChecker
import Mathlib.Tactic

set_option maxRecDepth 2048

/-!
# Prop-level Certificate Examples

Full Lean 4 proofs that specific `PCertificate`s satisfy the checking
conditions (`PCertificateValid`).

1. **Constant propagation** — propagate a constant through a chain of copies
2. **Copy propagation** — replace a copied variable in a binop with the original
3. **CSE** — reuse an already-computed expression
4. **INVALID transformation** — checker must reject; proved that no valid
   certificate exists for the buggy transform
-/

-- ============================================================
-- Helpers
-- ============================================================

def idStoreRel : PStoreRel := fun σ_o σ_t => σ_o = σ_t

theorem idStoreRel_refl (σ : Store) : idStoreRel σ σ := rfl

def defaultInstrCert : PInstrCert :=
  { pc_orig := 0, storeRel := idStoreRel, transitions := [] }

def defaultHaltCert : PHaltCert :=
  { pc_orig := 0, storeRel := idStoreRel }

theorem bound_of_getElem? {a : Array α} {i : Nat} {v : α}
    (h : a[i]? = some v) : i < a.size := by
  rw [getElem?_eq_some_iff] at h; exact h.1

/-- All-int typing context for examples that only use integer values. -/
def allIntCtx : TyCtx := fun _ => .int

/-- Any store of all-int values is well-typed under `allIntCtx`. -/
theorem allIntCtx_typed_of_all_int {σ : Store}
    (h : ∀ x, ∃ n, σ x = .int n) : TypedStore allIntCtx σ := by
  intro x; obtain ⟨n, hn⟩ := h x; rw [hn]; rfl

/-- WellTypedProg for a program where all instructions are int-typed. -/
private theorem allIntCtx_wtp_by_decide {p : Prog}
    (h : ∀ i, (hi : i < p.size) → WellTypedInstr allIntCtx p[i]) :
    WellTypedProg allIntCtx p := h

-- ============================================================
-- § 1. Constant propagation (chain)
-- ============================================================
/-
  Original:                    Transformed:
    0: x := 7                    0: x := 7
    1: y := x       →           1: y := 7       (propagated)
    2: z := y                    2: z := 7       (propagated)
    3: halt                      3: halt

  Invariant: x = 7 at labels ≥ 1, y = 7 at labels ≥ 2.
-/

namespace Example1

def origProg : Prog := #[
  .const "x" (.int 7),       -- 0
  .copy  "y" "x",     -- 1
  .copy  "z" "y",     -- 2
  .halt                -- 3
]

def transProg : Prog := #[
  .const "x" (.int 7),       -- 0
  .const "y" (.int 7),       -- 1
  .const "z" (.int 7),       -- 2
  .halt                -- 3
]

def inv : PInvariantMap := fun pc σ =>
  (if pc ≥ 1 then σ "x" = .int 7 else True) ∧
  (if pc ≥ 2 then σ "y" = .int 7 else True)

def cert : PCertificate :=
  { orig       := origProg
    trans      := transProg
    inv_orig   := inv
    inv_trans  := inv
    observable := ["z"]
    instrCerts := (fun pc =>
      match pc with
      | 0 => { pc_orig := 0, storeRel := idStoreRel,
                transitions := [⟨[1], idStoreRel, idStoreRel⟩] }
      | 1 => { pc_orig := 1, storeRel := idStoreRel,
                transitions := [⟨[2], idStoreRel, idStoreRel⟩] }
      | 2 => { pc_orig := 2, storeRel := idStoreRel,
                transitions := [⟨[3], idStoreRel, idStoreRel⟩] }
      | 3 => { pc_orig := 3, storeRel := idStoreRel, transitions := [] }
      | _ => defaultInstrCert)
    haltCerts := fun pc =>
      match pc with
      | 3 => { pc_orig := 3, storeRel := idStoreRel }
      | _ => defaultHaltCert
    measure := fun _ _ => 0 }

theorem start_ok : checkStartCorrespondenceProp cert :=
  ⟨rfl, idStoreRel_refl⟩

theorem inv_ok : checkInvariantsPreservedProp cert := by
  constructor
  · -- orig
    intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.orig.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
      | boolop h => exact bound_of_getElem? h
    have : cert.orig[0]? = some (.const "x" (.int 7)) := by native_decide
    have : cert.orig[1]? = some (.copy "y" "x") := by native_decide
    have : cert.orig[2]? = some (.copy "z" "y") := by native_decide
    have : cert.orig[3]? = some .halt := by native_decide
    change pc < 4 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update]
  · -- trans
    intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.trans.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
      | boolop h => exact bound_of_getElem? h
    have : cert.trans[0]? = some (.const "x" (.int 7)) := by native_decide
    have : cert.trans[1]? = some (.const "y" (.int 7)) := by native_decide
    have : cert.trans[2]? = some (.const "z" (.int 7)) := by native_decide
    have : cert.trans[3]? = some .halt := by native_decide
    change pc < 4 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update]

theorem halt_corr_ok : checkHaltCorrespondenceProp cert := by
  intro pc_t h
  have hlt := bound_of_getElem? h; change pc_t < 4 at hlt
  interval_cases pc_t <;> simp_all [cert, origProg, transProg]

theorem halt_obs_ok : checkHaltObservableProp cert := by
  intro pc_t σ_t σ_o h
  change transProg[pc_t]? = some .halt at h
  have hlt := bound_of_getElem? h; change pc_t < 4 at hlt
  simp only [cert]; intro hvm v hv
  interval_cases pc_t <;> simp_all [transProg]
  simp [idStoreRel] at hvm; subst hvm; rfl

theorem transitions_ok : checkAllTransitionsProp allIntCtx cert := by
  intro pc_t σ_t σ_t' pc_t' hstep
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
    | boolop h => exact bound_of_getElem? h
  change pc_t < 4 at hlt
  have ct0 : cert.trans[0]? = some (.const "x" (.int 7)) := by native_decide
  have ct1 : cert.trans[1]? = some (.const "y" (.int 7)) := by native_decide
  have ct2 : cert.trans[2]? = some (.const "z" (.int 7)) := by native_decide
  have ct3 : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: const "x" 7
    cases hstep with
    | const h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm _ hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | const h' =>
          simp_all
          exact ⟨σ_o_["x" ↦ .int 7], Steps.single (.const (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: const "y" 7 (trans) vs copy "y" "x" (orig)
    cases hstep with
    | const h =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm _ hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        cases hstep' with
        | const h' =>
          simp_all
          refine ⟨σ_o_["y" ↦ σ_o_ "x"], Steps.single (.copy (by native_decide)), ?_⟩
          simp [idStoreRel]; funext v; simp [Store.update]; split <;> simp_all
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 2: const "z" 7 (trans) vs copy "z" "y" (orig)
    cases hstep with
    | const h =>
      refine ⟨⟨[3], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm _ hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        cases hstep' with
        | const h' =>
          simp_all
          refine ⟨σ_o_["z" ↦ σ_o_ "y"], Steps.single (.copy (by native_decide)), ?_⟩
          simp [idStoreRel]; funext v; simp [Store.update]; split <;> simp_all
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 3: halt
    cases hstep <;> simp_all

theorem nonterm_ok : checkNonterminationProp cert := by
  intro pc_t pc_t' σ_t σ_t' σ_o _ _ _ ⟨c', hstep, hc'⟩ horig_eq
  subst hc'
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
    | boolop h => exact bound_of_getElem? h
  change pc_t < 4 at hlt
  have : cert.trans[0]? = some (.const "x" (.int 7)) := by native_decide
  have : cert.trans[1]? = some (.const "y" (.int 7)) := by native_decide
  have : cert.trans[2]? = some (.const "z" (.int 7)) := by native_decide
  have : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

theorem stuck_pres_ok : checkStuckPreservationProp cert := by
  intro pc_t σ_t σ_o hpc _ _ _ hobs
  exfalso
  have : pc_t < 4 := by rw [show cert.trans.size = 4 from rfl] at hpc; exact hpc
  interval_cases pc_t <;> dsimp [observe, cert, transProg] at hobs <;> exact Observation.noConfusion hobs

theorem valid : PCertificateValid allIntCtx cert :=
  { well_typed_orig := by
      intro i hi; simp [cert, origProg] at hi ⊢
      change i < 4 at hi; interval_cases i <;> constructor <;> rfl
    start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok
    stuck_pres    := stuck_pres_ok
    step_closed   := checkStepClosed_sound (by native_decide) }

end Example1

-- ============================================================
-- § 2. Copy propagation
-- ============================================================
/-
  Original:                    Transformed:
    0: a := b                    0: a := b
    1: c := a + d     →         1: c := b + d   (replaced a with b)
    2: halt                      2: halt

  Invariant: `a = b` at labels ≥ 1.
-/

namespace Example2

def origProg : Prog := #[
  .copy "a" "b",                 -- 0
  .binop "c" .add "a" "d",      -- 1
  .halt                          -- 2
]

def transProg : Prog := #[
  .copy "a" "b",                 -- 0
  .binop "c" .add "b" "d",      -- 1 (replaced a with b)
  .halt                          -- 2
]

/-- `a = b` at labels ≥ 1 (after the copy). -/
def inv : PInvariantMap := fun pc σ =>
  if pc ≥ 1 then σ "a" = σ "b" else True

def cert : PCertificate :=
  { orig       := origProg
    trans      := transProg
    inv_orig   := inv
    inv_trans  := inv
    observable := ["c"]
    instrCerts := (fun pc =>
      match pc with
      | 0 => { pc_orig := 0, storeRel := idStoreRel,
                transitions := [⟨[1], idStoreRel, idStoreRel⟩] }
      | 1 => { pc_orig := 1, storeRel := idStoreRel,
                transitions := [⟨[2], idStoreRel, idStoreRel⟩] }
      | 2 => { pc_orig := 2, storeRel := idStoreRel, transitions := [] }
      | _ => defaultInstrCert)
    haltCerts := fun pc =>
      match pc with
      | 2 => { pc_orig := 2, storeRel := idStoreRel }
      | _ => defaultHaltCert
    measure := fun _ _ => 0 }

theorem start_ok : checkStartCorrespondenceProp cert :=
  ⟨rfl, idStoreRel_refl⟩

theorem inv_ok : checkInvariantsPreservedProp cert := by
  constructor
  · intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.orig.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
      | boolop h => exact bound_of_getElem? h
    have : cert.orig[0]? = some (.copy "a" "b") := by native_decide
    have : cert.orig[1]? = some (.binop "c" .add "a" "d") := by native_decide
    have : cert.orig[2]? = some .halt := by native_decide
    change pc < 3 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update]
  · intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.trans.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
      | boolop h => exact bound_of_getElem? h
    have : cert.trans[0]? = some (.copy "a" "b") := by native_decide
    have : cert.trans[1]? = some (.binop "c" .add "b" "d") := by native_decide
    have : cert.trans[2]? = some .halt := by native_decide
    change pc < 3 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update]

theorem halt_corr_ok : checkHaltCorrespondenceProp cert := by
  intro pc_t h
  have hlt := bound_of_getElem? h; change pc_t < 3 at hlt
  interval_cases pc_t <;> simp_all [cert, origProg, transProg]

theorem halt_obs_ok : checkHaltObservableProp cert := by
  intro pc_t σ_t σ_o h
  change transProg[pc_t]? = some .halt at h
  have hlt := bound_of_getElem? h; change pc_t < 3 at hlt
  simp only [cert]; intro hvm v hv
  interval_cases pc_t <;> simp_all [transProg]
  simp [idStoreRel] at hvm; subst hvm; rfl

theorem transitions_ok : checkAllTransitionsProp allIntCtx cert := by
  intro pc_t σ_t σ_t' pc_t' hstep
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
    | boolop h => exact bound_of_getElem? h
  change pc_t < 3 at hlt
  have ct0 : cert.trans[0]? = some (.copy "a" "b") := by native_decide
  have ct1 : cert.trans[1]? = some (.binop "c" .add "b" "d") := by native_decide
  have ct2 : cert.trans[2]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: copy "a" "b"
    cases hstep with
    | copy h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm _ hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | copy h' =>
          simp_all
          exact ⟨σ_o_["a" ↦ σ_o_ "b"], Steps.single (.copy (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: binop "c" .add "b" "d" (trans) vs binop "c" .add "a" "d" (orig)
    cases hstep with
    | binop h _ _ _ =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm _ hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        -- hstep' : cert.trans ⊩ Cfg.run 1 σ_o_ ⟶ Cfg.run 2 σ_t'_
        -- hinv_o : σ_o_ "a" = σ_o_ "b"
        cases hstep' with
        | binop h' hb hd hsafe =>
          -- h' : cert.trans[1]? = some (.binop "c" .add y✝ z✝)
          -- hb : σ_o_ y✝ = .int av,  hd : σ_o_ z✝ = .int dv
          -- simp_all unifies y✝ = "b", z✝ = "d" via ct1
          rename_i av dv
          simp_all
          -- Now hinv_o : σ_o_ "a" = σ_o_ "b", hb : σ_o_ "b" = Value.int av,
          --     hd : σ_o_ "d" = Value.int dv
          have ha : σ_o_ "a" = Value.int av := by rw [hinv_o]
          exact ⟨σ_o_["c" ↦ Value.int (BinOp.add.eval av dv)],
                  Steps.single (Step.binop (by native_decide) ha hd hsafe), rfl⟩
        | const h' => simp_all
        | copy h' => simp_all
        | boolop h' => simp_all
        | goto h' => simp_all
        | iftrue h' _ => simp_all
        | iffall h' _ => simp_all
    | const h => simp_all
    | copy h => simp_all
    | boolop h => simp_all
    | goto h => simp_all
    | iftrue h _ => simp_all
    | iffall h _ => simp_all
  · -- pc_t = 2: halt
    cases hstep <;> simp_all

theorem nonterm_ok : checkNonterminationProp cert := by
  intro pc_t pc_t' σ_t σ_t' σ_o _ _ _ ⟨c', hstep, hc'⟩ horig_eq
  subst hc'
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
    | boolop h => exact bound_of_getElem? h
  change pc_t < 3 at hlt
  have : cert.trans[0]? = some (.copy "a" "b") := by native_decide
  have : cert.trans[1]? = some (.binop "c" .add "b" "d") := by native_decide
  have : cert.trans[2]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

theorem stuck_pres_ok : checkStuckPreservationProp cert := by
  intro pc_t σ_t σ_o hpc hrel hinv_t hinv_o hobs
  have hlt : pc_t < 3 := by rw [show cert.trans.size = 3 from rfl] at hpc; exact hpc
  interval_cases pc_t
  · -- pc_t = 0: copy "a" "b" → observe = nothing, not stuck
    simp [observe, cert, transProg] at hobs
  · -- pc_t = 1: binop "c" .add "b" "d"
    simp only [cert] at hrel hinv_o
    simp only [idStoreRel] at hrel; subst hrel
    simp only [inv, show (1 : Nat) ≥ 1 from le_refl _, ite_true] at hinv_o
    -- hinv_o : σ_o "a" = σ_o "b"
    -- Unfold observe and reduce the array lookups by native_decide
    simp only [observe, cert, transProg, origProg] at hobs ⊢
    -- Both hobs and goal now contain `#[...][1]?`; use norm_num/simp to evaluate
    simp only [show (#[TAC.copy "a" "b", TAC.binop "c" BinOp.add "b" "d",
        TAC.halt] : Array TAC)[1]? = some (.binop "c" .add "b" "d") from by native_decide] at hobs
    simp only [show (#[TAC.copy "a" "b", TAC.binop "c" BinOp.add "a" "d",
        TAC.halt] : Array TAC)[1]? = some (.binop "c" .add "a" "d") from by native_decide]
    rw [hinv_o]; exact hobs
  · -- pc_t = 2: halt → observe = halt observation, not stuck
    simp [observe, cert, transProg] at hobs

theorem valid : PCertificateValid allIntCtx cert :=
  { well_typed_orig := by
      intro i hi; simp [cert, origProg] at hi ⊢
      change i < 3 at hi; interval_cases i <;> constructor <;> rfl
    start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok
    stuck_pres    := stuck_pres_ok
    step_closed   := checkStepClosed_sound (by native_decide) }

end Example2

-- ============================================================
-- § 3. Common subexpression elimination
-- ============================================================
/-
  Original:                        Transformed:
    0: a := x + y                    0: a := x + y
    1: b := x + y     →             1: b := a       (CSE: reuse a)
    2: c := a + b                    2: c := a + b
    3: halt                          3: halt
-/

namespace Example3

def origProg : Prog := #[
  .binop "a" .add "x" "y",      -- 0
  .binop "b" .add "x" "y",      -- 1
  .binop "c" .add "a" "b",      -- 2
  .halt                          -- 3
]

def transProg : Prog := #[
  .binop "a" .add "x" "y",      -- 0
  .copy  "b" "a",               -- 1 (CSE)
  .binop "c" .add "a" "b",      -- 2
  .halt                          -- 3
]

def inv : PInvariantMap := fun pc σ =>
  if pc ≥ 1 then
    (∃ xv : Int, σ "x" = .int xv) ∧
    (∃ yv : Int, σ "y" = .int yv) ∧
    σ "a" = .int ((σ "x").toInt + (σ "y").toInt)
  else True

def cert : PCertificate :=
  { orig       := origProg
    trans      := transProg
    inv_orig   := inv
    inv_trans  := inv
    observable := ["c"]
    instrCerts := (fun pc =>
      match pc with
      | 0 => { pc_orig := 0, storeRel := idStoreRel,
                transitions := [⟨[1], idStoreRel, idStoreRel⟩] }
      | 1 => { pc_orig := 1, storeRel := idStoreRel,
                transitions := [⟨[2], idStoreRel, idStoreRel⟩] }
      | 2 => { pc_orig := 2, storeRel := idStoreRel,
                transitions := [⟨[3], idStoreRel, idStoreRel⟩] }
      | 3 => { pc_orig := 3, storeRel := idStoreRel, transitions := [] }
      | _ => defaultInstrCert)
    haltCerts := fun pc =>
      match pc with
      | 3 => { pc_orig := 3, storeRel := idStoreRel }
      | _ => defaultHaltCert
    measure := fun _ _ => 0 }

theorem start_ok : checkStartCorrespondenceProp cert :=
  ⟨rfl, idStoreRel_refl⟩

theorem inv_ok : checkInvariantsPreservedProp cert := by
  constructor
  · intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.orig.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
      | boolop h => exact bound_of_getElem? h
    have : cert.orig[0]? = some (.binop "a" .add "x" "y") := by native_decide
    have : cert.orig[1]? = some (.binop "b" .add "x" "y") := by native_decide
    have : cert.orig[2]? = some (.binop "c" .add "a" "b") := by native_decide
    have : cert.orig[3]? = some .halt := by native_decide
    change pc < 4 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update, BinOp.eval]
  · intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.trans.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
      | boolop h => exact bound_of_getElem? h
    have : cert.trans[0]? = some (.binop "a" .add "x" "y") := by native_decide
    have : cert.trans[1]? = some (.copy "b" "a") := by native_decide
    have : cert.trans[2]? = some (.binop "c" .add "a" "b") := by native_decide
    have : cert.trans[3]? = some .halt := by native_decide
    change pc < 4 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update, BinOp.eval]

theorem halt_corr_ok : checkHaltCorrespondenceProp cert := by
  intro pc_t h
  have hlt := bound_of_getElem? h; change pc_t < 4 at hlt
  interval_cases pc_t <;> simp_all [cert, origProg, transProg]

theorem halt_obs_ok : checkHaltObservableProp cert := by
  intro pc_t σ_t σ_o h
  change transProg[pc_t]? = some .halt at h
  have hlt := bound_of_getElem? h; change pc_t < 4 at hlt
  simp only [cert]; intro hvm v hv
  interval_cases pc_t <;> simp_all [transProg]
  simp [idStoreRel] at hvm; subst hvm; rfl

theorem transitions_ok : checkAllTransitionsProp allIntCtx cert := by
  intro pc_t σ_t σ_t' pc_t' hstep
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h _ _ _ => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
    | boolop h => exact bound_of_getElem? h
  change pc_t < 4 at hlt
  have ct0 : cert.trans[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have ct1 : cert.trans[1]? = some (.copy "b" "a") := by native_decide
  have ct2 : cert.trans[2]? = some (.binop "c" .add "a" "b") := by native_decide
  have ct3 : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: trans and orig both do binop "a" .add "x" "y"
    cases hstep with
    | binop h _ _ _ =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      intro σ_t_ σ_t'_ σ_o_ _ _ hvm _ hstep'
      simp only [idStoreRel] at hvm; subst hvm
      -- hstep' : cert.trans ⊩ run 0 σ_o_ ⟶ run 1 σ_t'_
      cases hstep' with
      | binop h' hx' hy' hsafe' =>
        -- hx' : σ_o_ y✝ = .int xv,  hy' : σ_o_ z✝ = .int yv  (abstract var names)
        -- simp_all resolves y✝="x", z✝="y" from ct0/h'
        simp_all
        -- After simp_all: hx' : σ_o_ "x" = .int ?, hy' : σ_o_ "y" = .int ?
        -- The goal: ∃ σ_o', orig ⊩ run 0 σ_o_ ⟶* run 1 σ_o' ∧ idStoreRel σ_o' σ_t'_
        have co0 : cert.orig[0]? = some (.binop "a" .add "x" "y") := by native_decide
        exact ⟨σ_o_["a" ↦ Value.int (BinOp.add.eval _ _)],
               Steps.single (Step.binop co0 hx' hy' hsafe'), rfl⟩
      | const h' => simp_all | copy h' => simp_all | boolop h' => simp_all
      | goto h' => simp_all | iftrue h' _ => simp_all | iffall h' _ => simp_all
    | const h => simp_all | copy h => simp_all | boolop h => simp_all
    | goto h => simp_all | iftrue h _ => simp_all | iffall h _ => simp_all
  · -- pc_t = 1: trans does copy "b" "a", orig does binop "b" .add "x" "y"
    -- inv at pc≥1 gives: σ "x"=.int xv, σ "y"=.int yv, σ "a"=.int (xv+yv)
    cases hstep with
    | copy h =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm _ hstep'
      simp only [idStoreRel] at hvm; subst hvm
      simp only [cert, inv, show (1 : Nat) ≥ 1 from le_refl _, ite_true] at hinv_o
      obtain ⟨⟨xv, hxv⟩, ⟨yv, hyv⟩, ha⟩ := hinv_o
      -- hstep' : cert.trans ⊩ run 1 σ_o_ ⟶ run 2 σ_t'_  (a copy step)
      cases hstep' with
      | copy h' =>
        -- h' resolves to cert.trans[1]? = some (copy "b" "a"); σ_t'_ = σ_o_["b"↦σ_o_ "a"]
        simp_all
        -- After simp_all: ha : σ_o_ "a" = .int (xv+yv), σ_t'_ eliminated
        have co1 : cert.orig[1]? = some (.binop "b" .add "x" "y") := by native_decide
        -- Construct orig step: binop "b" add "x" "y"  (need σ "x", σ "y" = .int)
        refine ⟨σ_o_["b" ↦ Value.int (BinOp.add.eval xv yv)],
                Steps.single (Step.binop co1 hxv hyv (by simp [BinOp.safe])), ?_⟩
        simp [idStoreRel, BinOp.eval]
      | binop h' _ _ _ => simp_all | const h' => simp_all | boolop h' => simp_all
      | goto h' => simp_all | iftrue h' _ => simp_all | iffall h' _ => simp_all
    | const h => simp_all | binop h _ _ _ => simp_all | boolop h => simp_all
    | goto h => simp_all | iftrue h _ => simp_all | iffall h _ => simp_all
  · -- pc_t = 2: trans and orig both do binop "c" .add "a" "b"
    cases hstep with
    | binop h _ _ _ =>
      refine ⟨⟨[3], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      intro σ_t_ σ_t'_ σ_o_ _ _ hvm _ hstep'
      simp only [idStoreRel] at hvm; subst hvm
      cases hstep' with
      | binop h' ha' hb' hsafe' =>
        simp_all
        have co2 : cert.orig[2]? = some (.binop "c" .add "a" "b") := by native_decide
        exact ⟨σ_o_["c" ↦ Value.int (BinOp.add.eval _ _)],
               Steps.single (Step.binop co2 ha' hb' hsafe'), rfl⟩
      | const h' => simp_all | copy h' => simp_all | boolop h' => simp_all
      | goto h' => simp_all | iftrue h' _ => simp_all | iffall h' _ => simp_all
    | const h => simp_all | copy h => simp_all | boolop h => simp_all
    | goto h => simp_all | iftrue h _ => simp_all | iffall h _ => simp_all
  · -- pc_t = 3: halt — no transitions
    cases hstep <;> simp_all

theorem nonterm_ok : checkNonterminationProp cert := by
  intro pc_t pc_t' σ_t σ_t' σ_o _ _ _ ⟨c', hstep, hc'⟩ horig_eq
  subst hc'
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
    | boolop h => exact bound_of_getElem? h
  change pc_t < 4 at hlt
  have : cert.trans[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have : cert.trans[1]? = some (.copy "b" "a") := by native_decide
  have : cert.trans[2]? = some (.binop "c" .add "a" "b") := by native_decide
  have : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

theorem stuck_pres_ok : checkStuckPreservationProp cert := by
  intro pc_t σ_t σ_o hpc hrel hinv_t hinv_o hobs
  have hlt : pc_t < 4 := by rw [show cert.trans.size = 4 from rfl] at hpc; exact hpc
  -- Concrete array lookup facts
  have ht0 : transProg[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have ht1 : transProg[1]? = some (.copy "b" "a") := by native_decide
  have ht2 : transProg[2]? = some (.binop "c" .add "a" "b") := by native_decide
  have ho0 : origProg[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have ho2 : origProg[2]? = some (.binop "c" .add "a" "b") := by native_decide
  -- After interval_cases, `simp only [observe, cert, transProg/origProg]` unfolds
  -- the definitions but leaves array literal indexing like `#[...][pc]?` unreduced.
  -- We use `simp only` with `getElem?`-reducing lemmas, then handle each case.
  -- Reduce the concrete array lookups used inside `observe`
  have ht0r : transProg[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have ht1r : transProg[1]? = some (.copy "b" "a") := by native_decide
  have ht2r : transProg[2]? = some (.binop "c" .add "a" "b") := by native_decide
  have ht3r : transProg[3]? = some .halt := by native_decide
  have ho0r : origProg[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have ho2r : origProg[2]? = some (.binop "c" .add "a" "b") := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: trans and orig both have binop "a" .add "x" "y"; observe is identical
    simp only [cert] at hrel; simp only [idStoreRel] at hrel; subst hrel
    simp only [observe, cert] at hobs ⊢
    rw [ht0r] at hobs; rw [ho0r]; exact hobs
  · -- pc_t = 1: trans has copy "b" "a"; observe = nothing, contradiction with stuck
    simp only [observe, cert] at hobs
    rw [ht1r] at hobs; exact absurd hobs (by simp)
  · -- pc_t = 2: trans and orig both have binop "c" .add "a" "b"; observe is identical
    simp only [cert] at hrel; simp only [idStoreRel] at hrel; subst hrel
    simp only [observe, cert] at hobs ⊢
    rw [ht2r] at hobs; rw [ho2r]; exact hobs
  · -- pc_t = 3: halt; observe = halt observation, not stuck
    simp only [observe, cert] at hobs
    rw [ht3r] at hobs; exact absurd hobs (by simp)

theorem valid : PCertificateValid allIntCtx cert :=
  { well_typed_orig := by
      intro i hi; simp [cert, origProg] at hi ⊢
      change i < 4 at hi; interval_cases i <;> constructor <;> rfl
    start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok
    stuck_pres    := stuck_pres_ok
    step_closed   := checkStepClosed_sound (by native_decide) }

end Example3

-- ============================================================
-- § 4. INVALID transformation (checker must reject)
-- ============================================================
/-
  Original:                    "Transformed" (BUGGY):
    0: x := 5                    0: x := 5
    1: y := x                   1: y := 3       ← WRONG (should be 5)
    2: halt                      2: halt

  Observable variable: y
  The original produces y = 5, but the buggy transform produces y = 3.
  No valid certificate exists — the checker rejects every attempt.
-/

namespace PBadExample

def origProg : Prog := #[
  .const "x" (.int 5),       -- 0
  .copy  "y" "x",     -- 1
  .halt                -- 2
]

def transProg : Prog := #[
  .const "x" (.int 5),       -- 0
  .const "y" (.int 3),       -- 1  ← BUG: should be 5
  .halt                -- 2
]

def inv : PInvariantMap := fun pc σ =>
  if pc ≥ 1 then σ "x" = .int 5 else True

def cert : PCertificate :=
  { orig       := origProg
    trans      := transProg
    inv_orig   := inv
    inv_trans  := inv
    observable := ["y"]
    instrCerts := (fun pc =>
      match pc with
      | 0 => { pc_orig := 0, storeRel := idStoreRel,
                transitions := [⟨[1], idStoreRel, idStoreRel⟩] }
      | 1 => { pc_orig := 1, storeRel := idStoreRel,
                transitions := [⟨[2], idStoreRel, idStoreRel⟩] }
      | 2 => { pc_orig := 2, storeRel := idStoreRel, transitions := [] }
      | _ => defaultInstrCert)
    haltCerts := fun pc =>
      match pc with
      | 2 => { pc_orig := 2, storeRel := idStoreRel }
      | _ => defaultHaltCert
    measure := fun _ _ => 0 }

/-- The transition correspondence FAILS at pc_t = 1.
    The transformed program sets y := 3, but the original sets y := x = 5.
    With identity variable maps, we'd need σ_t'("y") = σ_o'("y"),
    but 3 ≠ 5. -/
theorem transitions_fail : ¬ checkAllTransitionsProp allIntCtx cert := by
  intro h
  let σ₀ : Store := fun v => if v == "x" then .int 5 else .int 0
  have hstep : Step cert.trans (.run 1 σ₀) (.run 2 (σ₀["y" ↦ .int 3])) :=
    .const (by native_decide)
  obtain ⟨tc, _, hvm_eq, hvmn_eq, hcheck⟩ := h 1 σ₀ (σ₀["y" ↦ .int 3]) 2 hstep
  simp [cert] at hvm_eq hvmn_eq
  have hinv_t : cert.inv_trans 1 σ₀ := by simp [cert, inv, σ₀]
  have hinv_o : cert.inv_orig 1 σ₀ := by simp [cert, inv, σ₀]
  have hcons : tc.storeRel σ₀ σ₀ := by rw [hvm_eq]; rfl
  have hpc1 : (cert.instrCerts 1).pc_orig = 1 := by simp [cert]
  have hpc2 : (cert.instrCerts 2).pc_orig = 2 := by simp [cert]
  rw [hpc1, hpc2] at hcheck
  have hts : TypedStore allIntCtx σ₀ := by
    intro x; simp [σ₀, allIntCtx]; split <;> rfl
  obtain ⟨σ_o', hsteps, hcons'⟩ := hcheck σ₀ (σ₀["y" ↦ .int 3]) σ₀ hinv_t hinv_o hcons hts
    (.const (by native_decide))
  have heq : Value.int 3 = σ_o' "y" := by
    have := hcons'; rw [hvmn_eq] at this; simp [idStoreRel] at this
    rw [this]; simp [Store.update]
  have ho1 : cert.orig[1]? = some (.copy "y" "x") := by native_decide
  have ho2 : cert.orig[2]? = some .halt := by native_decide
  have no_halt_to_run : ∀ (σ σ' : Store) (pc' : Label),
      ¬ (cert.orig ⊩ Cfg.halt σ ⟶* Cfg.run pc' σ') := by
    intro σ σ' pc' h
    cases h with
    | step s _ => exact Step.no_step_from_halt s
  cases hsteps with
  | step s rest =>
    cases s with
    | copy h =>
      simp_all
      cases rest with
      | refl => simp [Store.update, σ₀] at heq
      | step s' rest' =>
        cases s' with
        | halt _ => exact no_halt_to_run _ _ _ rest'
        | _ => simp_all
    | halt h => exact no_halt_to_run _ _ _ rest
    | const h => exact absurd (ho1.symm.trans h) (by simp)
    | binop h => exact absurd (ho1.symm.trans h) (by simp)
    | goto h => exact absurd (ho1.symm.trans h) (by simp)
    | iftrue h _ => exact absurd (ho1.symm.trans h) (by simp)
    | iffall h _ => exact absurd (ho1.symm.trans h) (by simp)
    | boolop h => exact absurd (ho1.symm.trans h) (by simp)

/-- Therefore, no valid certificate exists for this buggy transformation. -/
theorem no_valid_cert : ¬ PCertificateValid allIntCtx cert := by
  intro ⟨_, _, _, _, htrans, _, _, _, _, _⟩
  exact transitions_fail htrans

end PBadExample
