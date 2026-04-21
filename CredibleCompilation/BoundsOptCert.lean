import CredibleCompilation.BoundsOpt
import CredibleCompilation.PropChecker

/-!
# BoundsOpt certificate-based checker

BoundsOpt (CredibleCompilation/BoundsOpt.lean) is untrusted — it runs a
forward interval analysis that may be buggy or incomplete. This file
provides a verified *checker* that validates BoundsOpt's output on a
per-PC local-preservation basis: `checkLocalPreservation` is decidable,
and `checkLocalPreservation_sound` proves that if the checker accepts,
the interval claims form a `PInvariantMap.preserved` invariant suitable
for feeding into `inv_preserved_steps`.

Phase 1 (this file):
* `IntervalInv.satisfies` — concretization of an `IRange` on a `BitVec 64`.
* `IMap.satisfies` — concretization of an `IMap` (list of var→range) on a store.
* `intervalMap` — lifting an `Array (Option IMap)` into a `PInvariantMap`.
* `validInterval` — structural well-formedness: `0 ≤ lo ≤ hi ≤ 2³¹`, the
  overflow-safe range for all bitvec-arithmetic-based transfers.

Phase 2: the local preservation checker `checkLocalPreservation`.
Phase 3: soundness `checkLocalPreservation_sound`.
-/

namespace BoundsOpt

-- ============================================================
-- § 1. Well-formedness of intervals
-- ============================================================

/-- `2 ^ 31`, the upper bound we require on interval `hi` for bitvec-safe transfers.
    Any value below this is representable as a nonnegative `BitVec 64` and addition
    of two such values still fits in 63 bits (so no wrap-around). -/
def intervalCap : Int := 2147483648  -- 2^31

/-- Well-formed interval: `0 ≤ lo ≤ hi ≤ 2³¹`. Required by every transfer
    soundness lemma; the checker filters out any unverified BoundsOpt claim
    that doesn't meet this bar. -/
def validInterval (r : IRange) : Bool :=
  decide (0 ≤ r.lo) && decide (r.lo ≤ r.hi) && decide (r.hi ≤ intervalCap)

-- ============================================================
-- § 2. Concretization
-- ============================================================

/-- A `BitVec 64` value `bv` satisfies the range `r` iff
    `r.lo ≤ bv (as Nat) < r.hi` and `r.lo ≥ 0`. The `r.lo ≥ 0` clause makes the
    concretization trivially False for `irTop`-shaped ranges, so they fall
    out automatically without special-case handling downstream. -/
def IntervalInv.satisfies (r : IRange) (bv : BitVec 64) : Prop :=
  0 ≤ r.lo ∧ r.lo.toNat ≤ bv.toNat ∧ bv.toNat < r.hi.toNat

/-- A store satisfies an `IMap` iff every explicit `(v, r)` entry holds:
    `σ v = .int bv` with `bv ∈ r`. Entries are only positive claims — an
    absent variable imposes no obligation. Array memory is ignored; this
    domain tracks integer variables only. -/
def IMap.satisfies (m : IMap) (σ : Store) : Prop :=
  ∀ v r, (v, r) ∈ m → ∃ bv, σ v = .int bv ∧ IntervalInv.satisfies r bv

-- ============================================================
-- § 3. Lifting to PInvariantMap
-- ============================================================

/-- Lift `Array (Option IMap)` (BoundsOpt's output) into a `PInvariantMap`.
    PCs outside the array, or where BoundsOpt claims `none` (unreachable),
    give the trivial invariant `True` — they impose no downstream obligation. -/
def intervalMap (inv : Array (Option IMap)) : PInvariantMap :=
  fun pc σ _am =>
    match inv[pc]? with
    | some (some m) => IMap.satisfies m σ
    | _             => True

-- ============================================================
-- § 4. Small lemmas we'll need downstream
-- ============================================================

theorem validInterval_iff (r : IRange) :
    validInterval r = true ↔ 0 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ intervalCap := by
  simp [validInterval, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem intervalCap_pos : (0 : Int) < intervalCap := by decide

end BoundsOpt
