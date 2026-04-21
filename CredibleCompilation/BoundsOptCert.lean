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

-- ============================================================
-- § 5. Certified transfer function (Phase 2)
-- ============================================================

/-- Remove any entry for `v` from `m`. BoundsOpt uses this pattern inline via
    `imSet` (which filters before prepending); we break it out because many of
    our transfer cases just drop a variable without making a new claim. -/
def imRemove (m : IMap) (v : Var) : IMap :=
  m.filter (fun p => !(p.1 == v))

/-- Total, structurally-recursive variant of BoundsOpt's `refineCondition`.
    We need a `def` (not `partial def`) so Phase 3 can case-split on it. The
    recursion on `.not inner` descends into a strict subterm, so this
    terminates structurally.

    Covers the same syntactic patterns as the partial version. Every other
    boolean shape falls through unchanged (trivially sound). -/
def refineCond (m : IMap) (be : BoolExpr) (isTrue : Bool) : IMap :=
  match be with
  | .not inner => refineCond m inner (!isTrue)
  | .cmp .lt (.var x) (.lit n) =>
      let iv := imLookup m x
      if isTrue then imSet m x ⟨iv.lo, min iv.hi n.toInt⟩
      else imSet m x ⟨max iv.lo n.toInt, iv.hi⟩
  | .cmp .lt (.var x) (.var bnd) =>
      let biv := imLookup m bnd; let iv := imLookup m x
      if biv.lo + 1 == biv.hi then
        if isTrue then imSet m x ⟨iv.lo, min iv.hi biv.lo⟩
        else imSet m x ⟨max iv.lo biv.lo, iv.hi⟩
      else m
  | .cmp .le (.var x) (.lit n) =>
      let iv := imLookup m x
      if isTrue then imSet m x ⟨iv.lo, min iv.hi (n.toInt + 1)⟩
      else imSet m x ⟨max iv.lo (n.toInt + 1), iv.hi⟩
  | .cmp .le (.var x) (.var bnd) =>
      let biv := imLookup m bnd; let iv := imLookup m x
      if biv.lo + 1 == biv.hi then
        if isTrue then imSet m x ⟨iv.lo, min iv.hi (biv.lo + 1)⟩
        else imSet m x ⟨max iv.lo (biv.lo + 1), iv.hi⟩
      else m
  | _ => m

/-- Upper bound for `mul`-transfer operands. `2^16 * 2^16 = 2^32 < 2^63`, so
    bitvec multiplication can't overflow when both ranges fit. -/
def mulCap : Int := 65536  -- 2^16

/-- Certified transfer: computes a sound post-state `IMap` for each TAC
    constructor. For operations whose result we can't bound (div, array reads,
    float ops, untracked binops), the destination var is removed — so the
    successor claim can only be vacuous (`validInterval` rejects any entry
    trying to constrain such a var). The `.ifgoto` case dispatches on whether
    the successor is the true-branch target, feeding the flipped flag into
    `refineCond`.

    Operations not covered by the run-to-run Step constructors (e.g. `.halt`)
    are irrelevant — they never appear as a live predecessor in a preservation
    proof — so we return `m` unchanged. -/
def certSuccessor (m : IMap) (instr : TAC) (succPC : Nat) : IMap :=
  match instr with
  | .const x (.int n) => imSet (imRemove m x) x ⟨n.toInt, n.toInt + 1⟩
  | .const x (.bool _) => imRemove m x
  | .const x (.float _) => imRemove m x
  | .copy x y =>
      let iy := imLookup m y
      imSet (imRemove m x) x iy
  | .binop x .add y z =>
      let iy := imLookup m y; let iz := imLookup m z
      imSet (imRemove m x) x ⟨iy.lo + iz.lo, iy.hi + iz.hi - 1⟩
  | .binop x .sub y z =>
      let iy := imLookup m y; let iz := imLookup m z
      imSet (imRemove m x) x ⟨iy.lo - iz.hi + 1, iy.hi - iz.lo⟩
  | .binop x .mul y z =>
      let iy := imLookup m y; let iz := imLookup m z
      if decide (0 ≤ iy.lo) && decide (iy.hi ≤ mulCap)
         && decide (0 ≤ iz.lo) && decide (iz.hi ≤ mulCap) then
        imSet (imRemove m x) x ⟨0, (iy.hi - 1) * (iz.hi - 1) + 1⟩
      else
        imRemove m x
  | .binop x _ _ _ => imRemove m x
  | .boolop x _ => imRemove m x
  | .goto _ => m
  | .ifgoto be l =>
      if succPC == l then refineCond m be true else refineCond m be false
  | .halt => m
  | .arrLoad x _ _ _ => imRemove m x
  | .arrStore _ _ _ _ => m
  | .fbinop x _ _ _ => imRemove m x
  | .intToFloat x _ => imRemove m x
  | .floatToInt x _ => imRemove m x
  | .floatUnary x _ _ => imRemove m x
  | .fternop x _ _ _ _ => imRemove m x
  | .print _ _ => m
  | .printInt _ => m
  | .printBool _ => m
  | .printFloat _ => m
  | .printString _ => m

-- ============================================================
-- § 6. Refinement
-- ============================================================

/-- A single claim `(v, r')` is *refined* by `m_strong` if `m_strong` has an
    explicit, well-formed entry for `v` whose interval sits inside `r'`.
    Absent entries fail — the checker will not accept a successor claim that
    isn't backed by the transfer's output. -/
def refinesSingle (m_strong : IMap) (v : Var) (r' : IRange) : Bool :=
  match m_strong.find? (fun p => p.1 == v) with
  | some (_, r) =>
      validInterval r && validInterval r' &&
        decide (r'.lo ≤ r.lo) && decide (r.hi ≤ r'.hi)
  | none => false

/-- `m_strong` refines `m_weak` pointwise: every entry in `m_weak` has a
    stronger, well-formed counterpart in `m_strong`. -/
def refines (m_strong m_weak : IMap) : Bool :=
  m_weak.all fun (v, r') => refinesSingle m_strong v r'

-- ============================================================
-- § 7. Local preservation checker
-- ============================================================

/-- The Phase 2 checker. Returns `true` only when `inv` is a pointwise
    over-approximation of the certified transfer function at every PC.

    Structure:
    * `inv.size = p.size` — the invariant array covers the program exactly
      so `inv[pc]? = none ↔ pc ≥ p.size`, used in Phase 3 to rule out
      out-of-bounds-PC Step cases by contradiction.
    * For each `pc < p.size` at which `inv` claims `some m`: for each
      `pc' ∈ instr.successors pc`, check that the certified-transfer image
      `certSuccessor m instr pc'` refines whatever `inv` claims at `pc'`.
      Successors with no claim (`none` / `some none`) or outside the program
      (`pc' ≥ p.size`) impose no obligation — `intervalMap` lifts them to
      `True` and the step preserves trivially.
    * PCs with `inv[pc]? ≠ some (some m)` have `intervalMap = True`, so no
      check needed at the source side. -/
def checkLocalPreservation (p : Prog) (inv : Array (Option IMap)) : Bool :=
  decide (inv.size = p.size) &&
  (List.range p.size).all fun pc =>
    match inv[pc]? with
    | some (some m) =>
        match p[pc]? with
        | some instr =>
            (instr.successors pc).all fun pc' =>
              decide (pc' ≥ p.size) ||
                (match inv[pc']? with
                 | some (some m') => refines (certSuccessor m instr pc') m'
                 | _ => true)
        | none => true
    | _ => true

end BoundsOpt
