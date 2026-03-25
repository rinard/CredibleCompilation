import CredibleCompilation.PropChecker
import Mathlib.Tactic

set_option maxRecDepth 2048

/-!
# Example Certificates for Constant Propagation

Three examples of increasing complexity:
1. **Simple**: propagate a constant through a copy instruction
2. **Binop operand**: propagate a constant through a copy into a binop
3. **Loop**: remove a redundant constant re-assignment inside a loop
   (different-sized programs; multi-step original correspondence)

Each example defines the original and transformed programs, invariants,
variable maps, and the certificate. The proofs that each certificate
satisfies the checking conditions are provided; invariant preservation
proofs are left as exercises (marked `sorry`).

Note: `simp_all` cannot reduce `Array.getElem?` on concrete arrays,
so transition correspondence and non-termination proofs use `sorry`
for the mechanical case-analysis steps. The proof *structure* is
correct; a custom tactic or `native_decide` could close these.
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
-- § 1. Simple constant propagation: copy → const
-- ============================================================
/-
  Original:                    Transformed:
    0: x := 5                    0: x := 5
    1: y := x       →           1: y := 5       (propagated)
    2: halt                      2: halt

  PInvariant x=5 at labels ≥ 1 justifies replacing `y := x` with `y := 5`.
-/

namespace Example1

def origProg : Prog := #[
  .const "x" 5,       -- 0
  .copy  "y" "x",     -- 1
  .halt                -- 2
]

def transProg : Prog := #[
  .const "x" 5,       -- 0
  .const "y" 5,       -- 1  (was: copy "y" "x")
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
      | _ => defaultHaltCert }

theorem start_ok : checkStartCorrespondenceProp cert :=
  ⟨rfl, idStoreRel_refl⟩

theorem inv_ok : checkInvariantsPreservedProp cert := by
  constructor
  · -- orig program preserves inv
    intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.orig.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
    have : cert.orig[0]? = some (.const "x" 5) := by native_decide
    have : cert.orig[1]? = some (.copy "y" "x") := by native_decide
    have : cert.orig[2]? = some .halt := by native_decide
    change pc < 3 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update]
  · -- trans program preserves inv
    intro pc σ hinv pc' σ' hstep; simp only [cert, inv] at hinv ⊢
    have hlt : pc < cert.trans.size := by
      cases hstep with
      | const h => exact bound_of_getElem? h
      | copy h => exact bound_of_getElem? h
      | binop h => exact bound_of_getElem? h
      | goto h => exact bound_of_getElem? h
      | iftrue h _ => exact bound_of_getElem? h
      | iffall h _ => exact bound_of_getElem? h
    have : cert.trans[0]? = some (.const "x" 5) := by native_decide
    have : cert.trans[1]? = some (.const "y" 5) := by native_decide
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
  have ct0 : cert.trans[0]? = some (.const "x" 5) := by native_decide
  have ct1 : cert.trans[1]? = some (.const "y" 5) := by native_decide
  have ct2 : cert.trans[2]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0
    cases hstep with
    | const h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | const h' =>
          simp_all
          exact ⟨σ_o_["x" ↦ 5], Steps.single (.const (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1
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
  · -- pc_t = 2: halt
    cases hstep <;> simp_all

theorem nonterm_ok : checkNonterminationProp cert (fun _ _ => 0) := by
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
  have ct0 : cert.trans[0]? = some (.const "x" 5) := by native_decide
  have ct1 : cert.trans[1]? = some (.const "y" 5) := by native_decide
  have ct2 : cert.trans[2]? = some .halt := by native_decide
  -- Every trans step changes pc_orig, so horig_eq yields contradiction
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

/-- The certificate for Example 1 is valid: the checker accepts it. -/
theorem valid : PCertificateValid cert (fun _ _ => 0) :=
  { start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok }

end Example1

-- ============================================================
-- § 2. Constant propagation into binop operand
-- ============================================================
/-
  Original:                        Transformed:
    0: a := 10                       0: a := 10
    1: b := a          (copy)        1: b := 10       (propagated)
    2: c := b + y                    2: c := b + y    (unchanged)
    3: halt                          3: halt
-/

namespace Example2

def origProg : Prog := #[
  .const "a" 10,                  -- 0
  .copy  "b" "a",                 -- 1
  .binop "c" .add "b" "y",       -- 2
  .halt                           -- 3
]

def transProg : Prog := #[
  .const "a" 10,                  -- 0
  .const "b" 10,                  -- 1  (propagated)
  .binop "c" .add "b" "y",       -- 2
  .halt                           -- 3
]

def inv : PInvariantMap := fun pc σ =>
  (if pc ≥ 1 then σ "a" = 10 else True) ∧
  (if pc ≥ 2 then σ "b" = 10 else True)

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
      | _ => defaultHaltCert }

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
    have : cert.orig[0]? = some (.const "a" 10) := by native_decide
    have : cert.orig[1]? = some (.copy "b" "a") := by native_decide
    have : cert.orig[2]? = some (.binop "c" .add "b" "y") := by native_decide
    have : cert.orig[3]? = some .halt := by native_decide
    change pc < 4 at hlt
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
    have : cert.trans[0]? = some (.const "a" 10) := by native_decide
    have : cert.trans[1]? = some (.const "b" 10) := by native_decide
    have : cert.trans[2]? = some (.binop "c" .add "b" "y") := by native_decide
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
  have : cert.trans[0]? = some (.const "a" 10) := by native_decide
  have : cert.trans[1]? = some (.const "b" 10) := by native_decide
  have : cert.trans[2]? = some (.binop "c" .add "b" "y") := by native_decide
  have : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: const "a" 10
    cases hstep with
    | const h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | const h' =>
          simp_all
          exact ⟨σ_o_["a" ↦ 10], Steps.single (.const (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: const "b" 10 (trans) vs copy "b" "a" (orig)
    cases hstep with
    | const h =>
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        cases hstep' with
        | const h' =>
          simp_all
          refine ⟨σ_o_["b" ↦ σ_o_ "a"], Steps.single (.copy (by native_decide)), ?_⟩
          simp [idStoreRel]; funext v; simp [Store.update]; split <;> simp_all
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 2: binop "c" .add "b" "y" (same in both)
    cases hstep with
    | binop h =>
      refine ⟨⟨[3], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | binop h' =>
          simp_all
          exact ⟨σ_o_["c" ↦ BinOp.add.eval (σ_o_ "b") (σ_o_ "y")],
            Steps.single (.binop (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 3: halt
    cases hstep <;> simp_all

theorem nonterm_ok : checkNonterminationProp cert (fun _ _ => 0) := by
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
  have : cert.trans[0]? = some (.const "a" 10) := by native_decide
  have : cert.trans[1]? = some (.const "b" 10) := by native_decide
  have : cert.trans[2]? = some (.binop "c" .add "b" "y") := by native_decide
  have : cert.trans[3]? = some .halt := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

/-- The certificate for Example 2 is valid: the checker accepts it. -/
theorem valid : PCertificateValid cert (fun _ _ => 0) :=
  { start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok }

end Example2

-- ============================================================
-- § 3. Constant propagation in a loop (different-sized programs)
-- ============================================================
/-
  Original (7 instructions):           Transformed (6 instructions):
    0: step := 2                         0: step := 2
    1: if n goto 3                       1: if n goto 3
    2: halt                              2: halt
    3: acc := acc + n                    3: acc := acc + n
    4: step := 2       ← redundant      4: n := n - step    (was orig 5)
    5: n := n - step                     5: goto 1           (was orig 6)
    6: goto 1

  Trans 3→4 maps to orig 3→(4→)5 (two original steps, absorbing redundant step:=2).
  PInvariant: step = 2 at all labels ≥ 1.
-/

namespace Example3

def origProg : Prog := #[
  .const  "step" 2,                     -- 0
  .ifgoto (.var "n") 3,                        -- 1
  .halt,                                -- 2
  .binop  "acc" .add "acc" "n",         -- 3
  .const  "step" 2,                     -- 4  ← redundant
  .binop  "n" .sub "n" "step",          -- 5
  .goto   1                             -- 6
]

def transProg : Prog := #[
  .const  "step" 2,                     -- 0
  .ifgoto (.var "n") 3,                        -- 1
  .halt,                                -- 2
  .binop  "acc" .add "acc" "n",         -- 3
  .binop  "n" .sub "n" "step",          -- 4
  .goto   1                             -- 5
]

def inv : PInvariantMap := fun pc σ =>
  if pc ≥ 1 then σ "step" = 2 else True

def cert : PCertificate :=
  { orig       := origProg
    trans      := transProg
    inv_orig   := inv
    inv_trans  := inv
    observable := ["acc"]
    instrCerts := (fun pc =>
      match pc with
      | 0 => { pc_orig := 0, storeRel := idStoreRel,
                transitions := [⟨[1], idStoreRel, idStoreRel⟩] }
      | 1 => { pc_orig := 1, storeRel := idStoreRel,
                transitions := [⟨[3], idStoreRel, idStoreRel⟩,   -- branch taken
                                ⟨[2], idStoreRel, idStoreRel⟩] } -- fall through
      | 2 => { pc_orig := 2, storeRel := idStoreRel, transitions := [] }
      -- KEY: trans 3→4 maps to orig 3→(4→)5 — two original steps
      | 3 => { pc_orig := 3, storeRel := idStoreRel,
                transitions := [⟨[4, 5], idStoreRel, idStoreRel⟩] }
      | 4 => { pc_orig := 5, storeRel := idStoreRel,
                transitions := [⟨[6], idStoreRel, idStoreRel⟩] }
      | 5 => { pc_orig := 6, storeRel := idStoreRel,
                transitions := [⟨[1], idStoreRel, idStoreRel⟩] }
      | _ => defaultInstrCert)
    haltCerts := fun pc =>
      match pc with
      | 2 => { pc_orig := 2, storeRel := idStoreRel }
      | _ => defaultHaltCert }

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
    have : cert.orig[0]? = some (.const "step" 2) := by native_decide
    have : cert.orig[1]? = some (.ifgoto (.var "n") 3) := by native_decide
    have : cert.orig[2]? = some .halt := by native_decide
    have : cert.orig[3]? = some (.binop "acc" .add "acc" "n") := by native_decide
    have : cert.orig[4]? = some (.const "step" 2) := by native_decide
    have : cert.orig[5]? = some (.binop "n" .sub "n" "step") := by native_decide
    have : cert.orig[6]? = some (.goto 1) := by native_decide
    change pc < 7 at hlt
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
    have : cert.trans[0]? = some (.const "step" 2) := by native_decide
    have : cert.trans[1]? = some (.ifgoto (.var "n") 3) := by native_decide
    have : cert.trans[2]? = some .halt := by native_decide
    have : cert.trans[3]? = some (.binop "acc" .add "acc" "n") := by native_decide
    have : cert.trans[4]? = some (.binop "n" .sub "n" "step") := by native_decide
    have : cert.trans[5]? = some (.goto 1) := by native_decide
    change pc < 6 at hlt
    interval_cases pc <;> cases hstep <;> simp_all [Store.update]

theorem halt_corr_ok : checkHaltCorrespondenceProp cert := by
  intro pc_t h
  have hlt := bound_of_getElem? h; change pc_t < 6 at hlt
  interval_cases pc_t <;> simp_all [cert, origProg, transProg]

theorem halt_obs_ok : checkHaltObservableProp cert := by
  intro pc_t σ_t σ_o h
  change transProg[pc_t]? = some .halt at h
  have hlt := bound_of_getElem? h; change pc_t < 6 at hlt
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
  change pc_t < 6 at hlt
  have : cert.trans[0]? = some (.const "step" 2) := by native_decide
  have : cert.trans[1]? = some (.ifgoto (.var "n") 3) := by native_decide
  have : cert.trans[2]? = some .halt := by native_decide
  have : cert.trans[3]? = some (.binop "acc" .add "acc" "n") := by native_decide
  have : cert.trans[4]? = some (.binop "n" .sub "n" "step") := by native_decide
  have : cert.trans[5]? = some (.goto 1) := by native_decide
  interval_cases pc_t
  · -- pc_t = 0: const "step" 2
    cases hstep with
    | const h =>
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        cases hstep' with
        | const h' =>
          simp_all
          exact ⟨σ_o_["step" ↦ 2], Steps.single (.const (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 1: ifgoto "n" 3
    cases hstep with
    | iftrue h hne =>
      have h1 : cert.trans[1]? = some (.ifgoto (.var "n") 3) := by native_decide
      have := h ▸ h1; simp at this; obtain ⟨rfl, rfl⟩ := this
      -- Now: x = "n", pc_t' = 3
      refine ⟨⟨[3], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
      simp [idStoreRel] at hvm; subst hvm
      have ho : cert.orig[1]? = some (.ifgoto (.var "n") 3) := by native_decide
      cases hstep' with
      | iftrue h' hne' =>
        simp_all
        exact ⟨σ_t'_, Steps.single (.iftrue ho hne'), rfl⟩
      | _ => simp_all
    | iffall h heq =>
      have h1 : cert.trans[1]? = some (.ifgoto (.var "n") 3) := by native_decide
      have := h ▸ h1; simp at this; obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨[2], idStoreRel, idStoreRel⟩, List.Mem.tail _ (List.Mem.head _), rfl, rfl, ?_⟩
      intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
      simp [idStoreRel] at hvm; subst hvm
      have ho : cert.orig[1]? = some (.ifgoto (.var "n") 3) := by native_decide
      cases hstep' with
      | iffall h' heq' =>
        simp_all
        exact ⟨σ_t'_, Steps.single (.iffall ho heq'), rfl⟩
      | _ => simp_all
    | _ => simp_all
  · -- pc_t = 2: halt
    cases hstep <;> simp_all
  · -- pc_t = 3: binop "acc" .add "acc" "n", trans 3→4 maps to orig 3→(4→)5
    cases hstep with
    | binop h =>
      refine ⟨⟨[4, 5], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ hinv_o hvm hstep'
        simp [idStoreRel] at hvm; subst hvm
        simp [cert, inv] at hinv_o
        cases hstep' with
        | binop h' =>
          simp_all
          -- orig steps: 3→4 (binop acc), then 4→5 (const step 2)
          refine ⟨(σ_o_["acc" ↦ BinOp.add.eval (σ_o_ "acc") (σ_o_ "n")])["step" ↦ 2],
            Steps.step (.binop (by native_decide))
              (Steps.single (.const (by native_decide))), ?_⟩
          simp [idStoreRel]; funext v; simp [Store.update]; split <;> simp_all
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 4: binop "n" .sub "n" "step"
    cases hstep with
    | binop h =>
      refine ⟨⟨[6], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      · intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
        rw [show σ_o_ = σ_t_ from hvm] at *
        cases hstep' with
        | binop h' =>
          simp_all
          exact ⟨σ_t_["n" ↦ BinOp.sub.eval (σ_t_ "n") (σ_t_ "step")],
            Steps.single (.binop (by native_decide)), rfl⟩
        | _ => simp_all
    | _ => simp_all
  · -- pc_t = 5: goto 1
    cases hstep with
    | goto h =>
      have h1 : cert.trans[5]? = some (.goto 1) := by native_decide
      have := h ▸ h1; simp at this; subst this
      refine ⟨⟨[1], idStoreRel, idStoreRel⟩, List.Mem.head _, rfl, rfl, ?_⟩
      intro σ_t_ σ_t'_ σ_o_ _ _ hvm hstep'
      cases hstep' with
      | goto h' =>
        exact ⟨σ_o_, Steps.single (.goto (by native_decide)), hvm⟩
      | _ => simp_all
    | _ => simp_all

theorem nonterm_ok : checkNonterminationProp cert (fun _ _ => 0) := by
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
  change pc_t < 6 at hlt
  have : cert.trans[0]? = some (.const "step" 2) := by native_decide
  have : cert.trans[1]? = some (.ifgoto (.var "n") 3) := by native_decide
  have : cert.trans[2]? = some .halt := by native_decide
  have : cert.trans[3]? = some (.binop "acc" .add "acc" "n") := by native_decide
  have : cert.trans[4]? = some (.binop "n" .sub "n" "step") := by native_decide
  have : cert.trans[5]? = some (.goto 1) := by native_decide
  interval_cases pc_t <;> cases hstep <;> simp_all <;>
    (simp [cert] at horig_eq)

theorem start_inv_ok : checkInvariantsAtStartProp cert :=
  ⟨fun σ => by simp [cert, inv], fun σ => by simp [cert, inv]⟩

/-- The certificate for Example 3 is valid: the checker accepts it. -/
theorem valid : PCertificateValid cert (fun _ _ => 0) :=
  { start_corr    := start_ok
    start_inv     := start_inv_ok
    inv_preserved := inv_ok
    transitions   := transitions_ok
    halt_corr     := halt_corr_ok
    halt_obs      := halt_obs_ok
    nonterm       := nonterm_ok }

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

namespace BadExample

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

/-- No matter what invariants we pick, we cannot build a valid certificate.
    Here we demonstrate the checker rejects the natural attempt. -/
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
      | _ => defaultHaltCert }

/-- The transition correspondence FAILS at pc_t = 1.
    The transformed program sets y := 3, but the original sets y := x = 5.
    With identity variable maps, we'd need σ_t'("y") = σ_o'("y"),
    but 3 ≠ 5. -/
theorem transitions_fail : ¬ checkAllTransitionsProp cert := by
  intro h
  -- Use a store where x = 5 (required by invariant at pc ≥ 1)
  let σ₀ : Store := fun v => if v == "x" then 5 else 0
  -- Trans step at pc 1: const "y" 3, goes to pc 2
  have hstep : Step cert.trans (.run 1 σ₀) (.run 2 (σ₀["y" ↦ 3])) :=
    .const (by native_decide)
  obtain ⟨tc, _, hvm_eq, hvmn_eq, hcheck⟩ := h 1 σ₀ (σ₀["y" ↦ 3]) 2 hstep
  -- Resolve ALL tc fields to concrete values
  simp [cert] at hvm_eq hvmn_eq
  -- Now: tc.storeRel = idStoreRel, tc.storeRel_next = idStoreRel
  -- Invariants hold: inv 1 σ₀ requires σ₀ "x" = 5
  have hinv_t : cert.inv_trans 1 σ₀ := by simp [cert, inv, σ₀]
  have hinv_o : cert.inv_orig 1 σ₀ := by simp [cert, inv, σ₀]
  have hcons : tc.storeRel σ₀ σ₀ := by rw [hvm_eq]; rfl
  -- Simplify pc_orig values
  have hpc1 : (cert.instrCerts 1).pc_orig = 1 := by simp [cert]
  have hpc2 : (cert.instrCerts 2).pc_orig = 2 := by simp [cert]
  rw [hpc1, hpc2] at hcheck
  -- Apply the store relation proof
  obtain ⟨σ_o', hsteps, hcons'⟩ := hcheck σ₀ (σ₀["y" ↦ 3]) σ₀ hinv_t hinv_o hcons
    (.const (by native_decide))
  -- The identity store relation says σ_o' = σ_t', i.e. σ_o'("y") = 3
  have heq : 3 = σ_o' "y" := by
    have := hcons'; rw [hvmn_eq] at this; simp [idStoreRel] at this
    rw [this]; simp [Store.update]
  -- Determine σ_o' from the original execution
  have ho1 : cert.orig[1]? = some (.copy "y" "x") := by native_decide
  have ho2 : cert.orig[2]? = some .halt := by native_decide
  -- The only step from pc 1 is copy "y" "x" → pc 2
  -- At pc 2 (halt), no further Cfg.run steps are possible
  -- So σ_o' = σ₀["y" ↦ σ₀ "x"] = σ₀["y" ↦ 5], and σ_o'("y") = 5 ≠ 3
  -- Helper: Steps from Cfg.halt to Cfg.run is impossible
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
    | const h => simp_all
    | binop h => simp_all
    | goto h => simp_all
    | iftrue h => simp_all
    | iffall h => simp_all

/-- Therefore, no valid certificate exists for this buggy transformation. -/
theorem no_valid_cert : ¬ PCertificateValid cert μ := by
  intro ⟨_, _, _, htrans, _, _, _⟩
  exact transitions_fail htrans

end BadExample
