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
  .const "x" 7,       -- 0
  .copy  "y" "x",     -- 1
  .copy  "z" "y",     -- 2
  .halt                -- 3
]

def transProg : Prog := #[
  .const "x" 7,       -- 0
  .const "y" 7,       -- 1
  .const "z" 7,       -- 2
  .halt                -- 3
]

def inv : PInvariantMap := fun pc σ =>
  (if pc ≥ 1 then σ "x" = 7 else True) ∧
  (if pc ≥ 2 then σ "y" = 7 else True)

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
    have : cert.orig[0]? = some (.const "x" 7) := by native_decide
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
    have : cert.trans[0]? = some (.const "x" 7) := by native_decide
    have : cert.trans[1]? = some (.const "y" 7) := by native_decide
    have : cert.trans[2]? = some (.const "z" 7) := by native_decide
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

theorem transitions_ok : checkAllTransitionsProp cert := by
  intro pc_t σ_t σ_t' pc_t' hstep
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
  change pc_t < 4 at hlt
  have ct0 : cert.trans[0]? = some (.const "x" 7) := by native_decide
  have ct1 : cert.trans[1]? = some (.const "y" 7) := by native_decide
  have ct2 : cert.trans[2]? = some (.const "z" 7) := by native_decide
  have ct3 : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: const "x" 7
    cases hstep with
    | const h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | const h' =>
          simp_all
          exact ⟨σ_o_["x" ↦ 7], Steps.single (.const (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: const "y" 7 (trans) vs copy "y" "x" (orig)
    cases hstep with
    | const h =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm hstep'
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
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm hstep'
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
  change pc_t < 4 at hlt
  have : cert.trans[0]? = some (.const "x" 7) := by native_decide
  have : cert.trans[1]? = some (.const "y" 7) := by native_decide
  have : cert.trans[2]? = some (.const "z" 7) := by native_decide
  have : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

theorem valid : PCertificateValid cert :=
  { start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok
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

theorem transitions_ok : checkAllTransitionsProp cert := by
  intro pc_t σ_t σ_t' pc_t' hstep
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
  change pc_t < 3 at hlt
  have ct0 : cert.trans[0]? = some (.copy "a" "b") := by native_decide
  have ct1 : cert.trans[1]? = some (.binop "c" .add "b" "d") := by native_decide
  have ct2 : cert.trans[2]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: copy "a" "b"
    cases hstep with
    | copy h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | copy h' =>
          simp_all
          exact ⟨σ_o_["a" ↦ σ_o_ "b"], Steps.single (.copy (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: binop "c" .add "b" "d" (trans) vs binop "c" .add "a" "d" (orig)
    cases hstep with
    | binop h =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        cases hstep' with
        | binop h' =>
          simp_all
          refine ⟨σ_o_["c" ↦ BinOp.add.eval (σ_o_ "a") (σ_o_ "d")],
            Steps.single (.binop (by native_decide)), ?_⟩
          simp [idStoreRel]; funext v; simp [Store.update]; split <;> simp_all
        | _ => simp_all
    | _ => simp_all
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
  change pc_t < 3 at hlt
  have : cert.trans[0]? = some (.copy "a" "b") := by native_decide
  have : cert.trans[1]? = some (.binop "c" .add "b" "d") := by native_decide
  have : cert.trans[2]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

theorem valid : PCertificateValid cert :=
  { start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok
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
  if pc ≥ 1 then σ "a" = σ "x" + σ "y" else True

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

theorem transitions_ok : checkAllTransitionsProp cert := by
  intro pc_t σ_t σ_t' pc_t' hstep
  have hlt : pc_t < cert.trans.size := by
    cases hstep with
    | const h => exact bound_of_getElem? h
    | copy h => exact bound_of_getElem? h
    | binop h => exact bound_of_getElem? h
    | goto h => exact bound_of_getElem? h
    | iftrue h _ => exact bound_of_getElem? h
    | iffall h _ => exact bound_of_getElem? h
  change pc_t < 4 at hlt
  have ct0 : cert.trans[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have ct1 : cert.trans[1]? = some (.copy "b" "a") := by native_decide
  have ct2 : cert.trans[2]? = some (.binop "c" .add "a" "b") := by native_decide
  have ct3 : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: binop "a" .add "x" "y" (same in both)
    cases hstep with
    | binop h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | binop h' =>
          simp_all
          exact ⟨σ_o_["a" ↦ BinOp.add.eval (σ_o_ "x") (σ_o_ "y")],
            Steps.single (.binop (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: copy "b" "a" (trans) vs binop "b" .add "x" "y" (orig)
    cases hstep with
    | copy h =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        cases hstep' with
        | copy h' =>
          simp_all
          -- orig step: binop "b" .add "x" "y", σ_o'("b") = x+y
          -- trans step: copy "b" "a", σ_t'("b") = a = x+y (by invariant)
          refine ⟨σ_o_["b" ↦ BinOp.add.eval (σ_o_ "x") (σ_o_ "y")],
            Steps.single (.binop (by native_decide)), ?_⟩
          simp [idStoreRel]; funext v; simp [Store.update, BinOp.eval]
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 2: binop "c" .add "a" "b" (same in both)
    cases hstep with
    | binop h =>
      refine ⟨⟨[3], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | binop h' =>
          simp_all
          exact ⟨σ_o_["c" ↦ BinOp.add.eval (σ_o_ "a") (σ_o_ "b")],
            Steps.single (.binop (by native_decide)), rfl⟩
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
  change pc_t < 4 at hlt
  have : cert.trans[0]? = some (.binop "a" .add "x" "y") := by native_decide
  have : cert.trans[1]? = some (.copy "b" "a") := by native_decide
  have : cert.trans[2]? = some (.binop "c" .add "a" "b") := by native_decide
  have : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

theorem valid : PCertificateValid cert :=
  { start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok
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
  .const "x" 5,       -- 0
  .copy  "y" "x",     -- 1
  .halt                -- 2
]

def transProg : Prog := #[
  .const "x" 5,       -- 0
  .const "y" 3,       -- 1  ← BUG: should be 5
  .halt                -- 2
]

def inv : PInvariantMap := fun pc σ =>
  if pc ≥ 1 then σ "x" = 5 else True

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
theorem transitions_fail : ¬ checkAllTransitionsProp cert := by
  intro h
  let σ₀ : Store := fun v => if v == "x" then 5 else 0
  have hstep : Step cert.trans (.run 1 σ₀) (.run 2 (σ₀["y" ↦ 3])) :=
    .const (by native_decide)
  obtain ⟨tc, _, hvm_eq, hvmn_eq, hcheck⟩ := h 1 σ₀ (σ₀["y" ↦ 3]) 2 hstep
  simp [cert] at hvm_eq hvmn_eq
  have hinv_t : cert.inv_trans 1 σ₀ := by simp [cert, inv, σ₀]
  have hinv_o : cert.inv_orig 1 σ₀ := by simp [cert, inv, σ₀]
  have hcons : tc.storeRel σ₀ σ₀ := by rw [hvm_eq]; rfl
  have hpc1 : (cert.instrCerts 1).pc_orig = 1 := by simp [cert]
  have hpc2 : (cert.instrCerts 2).pc_orig = 2 := by simp [cert]
  rw [hpc1, hpc2] at hcheck
  obtain ⟨σ_o', hsteps, hcons'⟩ := hcheck σ₀ (σ₀["y" ↦ 3]) σ₀ hinv_t hinv_o hcons
    (.const (by native_decide))
  have heq : 3 = σ_o' "y" := by
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

/-- Therefore, no valid certificate exists for this buggy transformation. -/
theorem no_valid_cert : ¬ PCertificateValid cert := by
  intro ⟨_, _, _, htrans, _, _, _, _⟩
  exact transitions_fail htrans

end PBadExample
