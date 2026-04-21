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
    * `some (some m)` — oracle's positive claim; concretizes via `satisfies`.
    * `some none` — oracle claims unreachable; if we ever prove it holds at a
      running configuration, the oracle was wrong. Encoded as `False` so
      preservation is vacuously discharged at such PCs; the checker also
      rejects any `some (some m) → some none` transition, ensuring we can't
      actually land here from a reachable predecessor.
    * `none` — out-of-bounds PC (past `inv.size`). Trivially `True`; under
      the checker's `inv.size = p.size` requirement this forces `p[pc]? = none`,
      so no `Step` constructor can fire and preservation is vacuous. -/
def intervalMap (inv : Array (Option IMap)) : PInvariantMap :=
  fun pc σ _am =>
    match inv[pc]? with
    | some (some m) => IMap.satisfies m σ
    | some none     => False
    | none          => True

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
def certSuccessor (m : IMap) (instr : TAC) (_succPC : Nat) : IMap :=
  match instr with
  | .const x (.int n) => imSet (imRemove m x) x ⟨n.toInt, n.toInt + 1⟩
  | .const x (.bool _) => imRemove m x
  | .const x (.float _) => imRemove m x
  | .copy x y =>
      let iy := imLookup m y
      imSet (imRemove m x) x iy
  | .binop x .add y z =>
      let iy := imLookup m y; let iz := imLookup m z
      if validInterval iy && validInterval iz then
        imSet (imRemove m x) x ⟨iy.lo + iz.lo, iy.hi + iz.hi - 1⟩
      else imRemove m x
  | .binop x .sub y z =>
      let iy := imLookup m y; let iz := imLookup m z
      if validInterval iy && validInterval iz then
        imSet (imRemove m x) x ⟨iy.lo - iz.hi + 1, iy.hi - iz.lo⟩
      else imRemove m x
  | .binop x .mul _ _ =>
      -- Phase 3 drops the destination for `.mul`. A future phase can re-enable
      -- the `[0, 2¹⁶)` product bound with a dedicated `mul_sound` lemma.
      imRemove m x
  | .binop x _ _ _ => imRemove m x
  | .boolop x _ => imRemove m x
  | .goto _ => m
  | .ifgoto _ _ =>
      -- Phase 3 soundness stops short of the condition-refinement patterns;
      -- Phase 3 ships `m` unchanged at `.ifgoto` so the `cmp .lt/.le` refinements
      -- can land in a follow-up that proves `refineCond_sound` case-by-case.
      m
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
                 | some none      => false  -- reachable → unreachable = oracle bug
                 | none           => true)
        | none => true
    | _ => true

-- ============================================================
-- § 8. Soundness bridge lemmas (Phase 3)
-- ============================================================

/-- If a `BitVec 64` fits under `intervalCap = 2³¹`, its signed and unsigned
    interpretations agree — needed to bridge between signed `slt`/`sle`
    (TAC/Step level) and unsigned `toNat` (our interval domain). -/
theorem toInt_eq_toNat_of_lt_cap {bv : BitVec 64}
    (h : bv.toNat < intervalCap.toNat) : bv.toInt = bv.toNat := by
  have : intervalCap.toNat = 2 ^ 31 := by decide
  have : bv.toNat < 2 ^ 63 := by omega
  simp only [BitVec.toInt_eq_toNat_cond]; omega

/-- `Int.toNat` is monotone on nonnegative ints (no wrap-at-zero). -/
theorem Int.toNat_mono_of_nonneg {a b : Int} (h : a ≤ b) : a.toNat ≤ b.toNat :=
  Int.toNat_le_toNat h

-- ============================================================
-- § 9. Structural lemmas on `imRemove` / `imSet` / `imLookup`
-- ============================================================

/-- Membership in `imRemove m v` peels off the filter. -/
theorem mem_imRemove {m : IMap} {v u : Var} {r : IRange}
    (h : (u, r) ∈ imRemove m v) : u ≠ v ∧ (u, r) ∈ m := by
  simp only [imRemove, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact ⟨h.2, h.1⟩

/-- Membership in `imSet m v r`: either the new `(v, r)` entry, or an old
    entry with a different variable. -/
theorem mem_imSet {m : IMap} {v u : Var} {r r' : IRange} :
    (u, r') ∈ imSet m v r ↔ (u = v ∧ r' = r) ∨ (u ≠ v ∧ (u, r') ∈ m) := by
  simp only [imSet, List.mem_cons, List.mem_filter, Prod.mk.injEq,
    Bool.not_eq_true', beq_eq_false_iff_ne]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hm, hne⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hne, hm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hne, hm⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hm, hne⟩

/-- `List.find?` with a `.1 == v` predicate returns a pair whose first
    component equals `v`, and which belongs to the list. -/
theorem find?_pair_spec {m : IMap} {v : Var} {q : Var × IRange}
    (h : m.find? (fun p => p.1 == v) = some q) :
    q.1 = v ∧ q ∈ m := by
  refine ⟨?_, List.mem_of_find?_eq_some h⟩
  have hpred := List.find?_some h
  simp only at hpred
  exact by simpa using hpred

/-- If `imLookup m v` passes `validInterval`, the lookup didn't fall through
    to `irTop` — there's an explicit `(v, imLookup m v)` entry in `m`. -/
theorem imLookup_mem_of_valid {m : IMap} {v : Var}
    (h : validInterval (imLookup m v) = true) :
    (v, imLookup m v) ∈ m := by
  -- If find? = none, imLookup = irTop, validInterval irTop = false.
  have hIrTopInvalid : validInterval irTop = false := by decide
  unfold imLookup at h ⊢
  split at h
  · next q hFind =>
      have ⟨hq1, hqm⟩ := find?_pair_spec hFind
      obtain ⟨v', r⟩ := q
      simp only at hq1; subst hq1
      exact hqm
  · next hFind =>
      exfalso
      rw [hIrTopInvalid] at h
      exact Bool.noConfusion h

-- ============================================================
-- § 10. Refinement soundness
-- ============================================================

/-- If `m_strong` refines `m_weak` pointwise and every valid-interval entry in
    `m_strong` is concretized by `σ`, then so is `m_weak`. The decisive step
    in `checkLocalPreservation_sound`: refinement transports transfer
    soundness to the oracle's claims. -/
theorem refines_sound {m_strong m_weak : IMap} {σ : Store}
    (hRefines : refines m_strong m_weak = true)
    (hStrong : ∀ v r, (v, r) ∈ m_strong → validInterval r = true →
               ∃ bv, σ v = .int bv ∧ IntervalInv.satisfies r bv) :
    IMap.satisfies m_weak σ := by
  intro v r' hVR
  simp only [refines, List.all_eq_true] at hRefines
  have hSingle := hRefines (v, r') hVR
  simp only [refinesSingle] at hSingle
  -- Drive the `match` in `refinesSingle` by cases on `find?`.
  cases hFind : m_strong.find? (fun p => p.1 == v) with
  | none =>
      rw [hFind] at hSingle; exact absurd hSingle (by simp)
  | some q =>
      obtain ⟨v', r_strong⟩ := q
      rw [hFind] at hSingle
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hSingle
      obtain ⟨⟨⟨hValidStrong, hValidWeak⟩, hLo⟩, hHi⟩ := hSingle
      have ⟨hveq, hmem⟩ := find?_pair_spec hFind
      simp only at hveq
      -- hveq : v' = v; eliminate v' (replace with v) by subst hveq.symm-like flip
      subst hveq
      have hValidWeakUnfold := (validInterval_iff _).mp hValidWeak
      have ⟨bv, hσv, hSat⟩ := hStrong v' r_strong hmem hValidStrong
      obtain ⟨hLoStrong, hLoNat, hHiNat⟩ := hSat
      refine ⟨bv, hσv, hValidWeakUnfold.1, ?_, ?_⟩
      · have h1 : r'.lo.toNat ≤ r_strong.lo.toNat :=
          Int.toNat_mono_of_nonneg hLo
        omega
      · have h1 : r_strong.hi.toNat ≤ r'.hi.toNat :=
          Int.toNat_mono_of_nonneg hHi
        omega

-- ============================================================
-- § 11. Transfer-soundness helpers
-- ============================================================

/-- Soundness template for transfers that leave `x` as the only possibly-
    modified variable: every `(v, r) ∈ imRemove m x` gives `v ≠ x`, so
    `σ' v = σ v`, and `m.satisfies σ` carries the claim through. -/
theorem imRemove_sound {m : IMap} {x : Var} {σ σ' : Store}
    (hM : IMap.satisfies m σ)
    (hAgree : ∀ y, y ≠ x → σ' y = σ y) :
    ∀ v r, (v, r) ∈ imRemove m x → validInterval r = true →
    ∃ bv, σ' v = .int bv ∧ IntervalInv.satisfies r bv := by
  intro v r hMem _
  have ⟨hNe, hMemM⟩ := mem_imRemove hMem
  have ⟨bv, hσv, hSat⟩ := hM v r hMemM
  exact ⟨bv, by rw [hAgree v hNe]; exact hσv, hSat⟩

/-- Soundness template when the transfer preserves `m` and the store stays
    the same. Used by `goto`, `print`, `arrStore` (stores to array memory
    don't change `σ`). -/
theorem identity_sound {m : IMap} {σ : Store}
    (hM : IMap.satisfies m σ) :
    ∀ v r, (v, r) ∈ m → validInterval r = true →
    ∃ bv, σ v = .int bv ∧ IntervalInv.satisfies r bv :=
  fun v r hMem _ => hM v r hMem

-- ============================================================
-- § 12. Store-update soundness for the three int-producing transfers
-- ============================================================

/-- For a BitVec 64 whose signed `toInt` is non-negative and bounded by
    `intervalCap`, the signed and unsigned interpretations coincide and the
    unsigned value fits the `[n.toInt.toNat, (n.toInt+1).toNat)` window. -/
theorem constInt_satisfies (n : BitVec 64)
    (hlo : 0 ≤ n.toInt) (hhi : n.toInt + 1 ≤ intervalCap) :
    IntervalInv.satisfies ⟨n.toInt, n.toInt + 1⟩ n := by
  have hcap : intervalCap = (2147483648 : Int) := by decide
  have hnat : n.toNat < 2 ^ 64 := n.isLt
  have heq : n.toInt = (n.toNat : Int) := by
    simp only [BitVec.toInt_eq_toNat_cond] at hlo ⊢
    split at hlo <;> omega
  have hlo' : (0 : Int) ≤ (n.toNat : Int) := by rw [← heq]; exact hlo
  refine ⟨hlo, ?_, ?_⟩
  · show n.toInt.toNat ≤ n.toNat
    rw [heq]; simp
  · show n.toNat < (n.toInt + 1).toNat
    rw [heq]
    have : ((n.toNat : Int) + 1).toNat = n.toNat + 1 := by
      have h : (0 : Int) ≤ (n.toNat : Int) + 1 := by omega
      omega
    rw [this]; omega

/-- `.const x (.int n)` soundness: after `σ[x ↦ .int n]`, every valid entry
    in `imSet (imRemove m x) x ⟨n.toInt, n.toInt+1⟩` holds. -/
theorem constInt_sound {m : IMap} {x : Var} {n : BitVec 64} {σ : Store}
    (hM : IMap.satisfies m σ) :
    ∀ v r, (v, r) ∈ imSet (imRemove m x) x ⟨n.toInt, n.toInt + 1⟩ →
    validInterval r = true →
    ∃ bv, (σ[x ↦ .int n]) v = .int bv ∧ IntervalInv.satisfies r bv := by
  intro v r hMem hValid
  rcases (mem_imSet.mp hMem) with ⟨rfl, rfl⟩ | ⟨hNe, hMemIR⟩
  · refine ⟨n, by simp [Store.update], ?_⟩
    obtain ⟨hlo, _, hhi⟩ := (validInterval_iff _).mp hValid
    simp only at hlo hhi
    exact constInt_satisfies n hlo hhi
  · have ⟨hNeIR, hMemM⟩ := mem_imRemove hMemIR
    have ⟨bv, hσv, hSat⟩ := hM v r hMemM
    exact ⟨bv, by simp [Store.update, hNeIR, hσv], hSat⟩

/-- `.copy x y` soundness. After `σ[x ↦ σ y]`, the transferred entry
    `(x, imLookup m y)` concretizes iff the lookup was well-formed — which is
    guaranteed by `validInterval`. -/
theorem copy_sound {m : IMap} {x y : Var} {σ : Store}
    (hM : IMap.satisfies m σ) :
    ∀ v r, (v, r) ∈ imSet (imRemove m x) x (imLookup m y) →
    validInterval r = true →
    ∃ bv, (σ[x ↦ σ y]) v = .int bv ∧ IntervalInv.satisfies r bv := by
  intro v r hMem hValid
  rcases (mem_imSet.mp hMem) with ⟨rfl, rfl⟩ | ⟨hNe, hMemIR⟩
  · -- x entry: r = imLookup m y; use m.satisfies on (y, imLookup m y)
    have hMemY := imLookup_mem_of_valid hValid
    have ⟨bv, hσy, hSat⟩ := hM y (imLookup m y) hMemY
    exact ⟨bv, by simp [Store.update, hσy], hSat⟩
  · have ⟨hNeIR, hMemM⟩ := mem_imRemove hMemIR
    have ⟨bv, hσv, hSat⟩ := hM v r hMemM
    exact ⟨bv, by simp [Store.update, hNeIR, hσv], hSat⟩

/-- Bridge: if both operands `a, b` sit in `[0, 2³¹)` as unsigned bitvecs,
    then `(a + b).toNat = a.toNat + b.toNat` with no overflow, and the sum
    stays under `2³²`. Core arithmetic fact for the `.add` transfer. -/
theorem BitVec64.toNat_add_small {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) :
    (a + b).toNat = a.toNat + b.toNat := by
  have : a.toNat + b.toNat < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt this]

/-- Companion: `(a - b).toNat = a.toNat - b.toNat` whenever `b ≤ a`
    (unsigned), both within `[0, 2³¹)`. -/
theorem BitVec64.toNat_sub_small {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) (hle : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have hBV : b.toNat ≤ a.toNat := hle
  rw [BitVec.toNat_sub]
  have : 2 ^ 64 - b.toNat + a.toNat = 2 ^ 64 + (a.toNat - b.toNat) := by omega
  rw [this]
  have : a.toNat - b.toNat < 2 ^ 64 := by omega
  omega

/-- `.binop x .add y z` soundness. Both input intervals must be `validInterval`
    so each operand fits `[0, 2³¹)` — no overflow on `a + b`. -/
theorem add_sound {m : IMap} {x y z : Var} {σ : Store}
    (hM : IMap.satisfies m σ)
    (hValY : validInterval (imLookup m y) = true)
    (hValZ : validInterval (imLookup m z) = true)
    {a b : BitVec 64} (hσy : σ y = .int a) (hσz : σ z = .int b) :
    ∀ v r, (v, r) ∈
      imSet (imRemove m x) x
        ⟨(imLookup m y).lo + (imLookup m z).lo,
         (imLookup m y).hi + (imLookup m z).hi - 1⟩ →
    validInterval r = true →
    ∃ bv, (σ[x ↦ .int (a + b)]) v = .int bv ∧ IntervalInv.satisfies r bv := by
  intro v r hMem hValid
  rcases (mem_imSet.mp hMem) with ⟨rfl, rfl⟩ | ⟨hNe, hMemIR⟩
  · -- x entry: sum interval
    refine ⟨a + b, by simp [Store.update], ?_⟩
    -- Extract: σ y = .int a with a.toNat ∈ iy; σ z = .int b with b.toNat ∈ iz.
    have hMemY := imLookup_mem_of_valid hValY
    have hMemZ := imLookup_mem_of_valid hValZ
    have ⟨a', hσy', hSatY⟩ := hM y (imLookup m y) hMemY
    have ⟨b', hσz', hSatZ⟩ := hM z (imLookup m z) hMemZ
    have ha : a = a' := Value.int.inj (hσy.symm.trans hσy')
    have hb : b = b' := Value.int.inj (hσz.symm.trans hσz')
    subst ha; subst hb
    obtain ⟨hyLo, hyLoHi, hyHi⟩ := (validInterval_iff _).mp hValY
    obtain ⟨hzLo, hzLoHi, hzHi⟩ := (validInterval_iff _).mp hValZ
    obtain ⟨hrLo, _, _⟩ := (validInterval_iff _).mp hValid
    obtain ⟨_, hSatYLoNat, hSatYHiNat⟩ := hSatY
    obtain ⟨_, hSatZLoNat, hSatZHiNat⟩ := hSatZ
    -- Each operand's toNat < 2^31 via iy.hi ≤ 2^31 and bv.toNat < iy.hi.toNat.
    have hyHiNat : (imLookup m y).hi.toNat ≤ intervalCap.toNat :=
      Int.toNat_mono_of_nonneg hyHi
    have hzHiNat : (imLookup m z).hi.toNat ≤ intervalCap.toNat :=
      Int.toNat_mono_of_nonneg hzHi
    have hCapNat : intervalCap.toNat = 2 ^ 31 := by decide
    have hy31 : a.toNat < 2 ^ 31 := by omega
    have hz31 : b.toNat < 2 ^ 31 := by omega
    have hSum : (a + b).toNat = a.toNat + b.toNat :=
      BitVec64.toNat_add_small hy31 hz31
    -- The target lo / hi as nonneg Ints, so `toNat` unfolds via omega.
    have hYhiNn : (0 : Int) ≤ (imLookup m y).hi := by omega
    have hZhiNn : (0 : Int) ≤ (imLookup m z).hi := by omega
    simp only at hrLo
    refine ⟨hrLo, ?_, ?_⟩
    · show ((imLookup m y).lo + (imLookup m z).lo).toNat ≤ (a + b).toNat
      rw [hSum]
      have hLoSum :
          ((imLookup m y).lo + (imLookup m z).lo).toNat
            = (imLookup m y).lo.toNat + (imLookup m z).lo.toNat :=
        Int.toNat_add hyLo hzLo
      omega
    · show (a + b).toNat < ((imLookup m y).hi + (imLookup m z).hi - 1).toNat
      rw [hSum]
      -- Both `hi` are nonneg ints, sum - 1 ≥ 0, so toNat is plain.
      omega
  · have ⟨hNeIR, hMemM⟩ := mem_imRemove hMemIR
    have ⟨bv, hσv, hSat⟩ := hM v r hMemM
    exact ⟨bv, by simp [Store.update, hNeIR, hσv], hSat⟩

/-- `.binop x .sub y z` soundness. Same `validInterval` gating as `add`. The
    `validInterval` of the output range forces `b.toNat ≤ a.toNat` (no wrap)
    via `iz.hi ≤ iy.lo + 1`. -/
theorem sub_sound {m : IMap} {x y z : Var} {σ : Store}
    (hM : IMap.satisfies m σ)
    (hValY : validInterval (imLookup m y) = true)
    (hValZ : validInterval (imLookup m z) = true)
    {a b : BitVec 64} (hσy : σ y = .int a) (hσz : σ z = .int b) :
    ∀ v r, (v, r) ∈
      imSet (imRemove m x) x
        ⟨(imLookup m y).lo - (imLookup m z).hi + 1,
         (imLookup m y).hi - (imLookup m z).lo⟩ →
    validInterval r = true →
    ∃ bv, (σ[x ↦ .int (a - b)]) v = .int bv ∧ IntervalInv.satisfies r bv := by
  intro v r hMem hValid
  rcases (mem_imSet.mp hMem) with ⟨rfl, rfl⟩ | ⟨hNe, hMemIR⟩
  · refine ⟨a - b, by simp [Store.update], ?_⟩
    have hMemY := imLookup_mem_of_valid hValY
    have hMemZ := imLookup_mem_of_valid hValZ
    have ⟨a', hσy', hSatY⟩ := hM y (imLookup m y) hMemY
    have ⟨b', hσz', hSatZ⟩ := hM z (imLookup m z) hMemZ
    have ha : a = a' := Value.int.inj (hσy.symm.trans hσy')
    have hb : b = b' := Value.int.inj (hσz.symm.trans hσz')
    subst ha; subst hb
    obtain ⟨hyLo, hyLoHi, hyHi⟩ := (validInterval_iff _).mp hValY
    obtain ⟨hzLo, hzLoHi, hzHi⟩ := (validInterval_iff _).mp hValZ
    obtain ⟨hrLo, hrLoHi, hrHi⟩ := (validInterval_iff _).mp hValid
    obtain ⟨_, hSatYLoNat, hSatYHiNat⟩ := hSatY
    obtain ⟨_, hSatZLoNat, hSatZHiNat⟩ := hSatZ
    have hCapNat : intervalCap.toNat = 2 ^ 31 := by decide
    have hyHiNat : (imLookup m y).hi.toNat ≤ intervalCap.toNat :=
      Int.toNat_mono_of_nonneg hyHi
    have hzHiNat : (imLookup m z).hi.toNat ≤ intervalCap.toNat :=
      Int.toNat_mono_of_nonneg hzHi
    have hy31 : a.toNat < 2 ^ 31 := by omega
    have hz31 : b.toNat < 2 ^ 31 := by omega
    -- b.toNat ≤ a.toNat via iz.hi ≤ iy.lo + 1 (from validInterval new).
    simp only at hrLo hrHi
    -- hrLo : 0 ≤ iy.lo - iz.hi + 1, so iz.hi ≤ iy.lo + 1
    have hzHi_le_yLo : (imLookup m z).hi.toNat ≤ (imLookup m y).lo.toNat + 1 := by
      have : (imLookup m z).hi ≤ (imLookup m y).lo + 1 := by omega
      have h1 : (imLookup m z).hi.toNat ≤ ((imLookup m y).lo + 1).toNat :=
        Int.toNat_mono_of_nonneg this
      have h2 : ((imLookup m y).lo + 1).toNat = (imLookup m y).lo.toNat + 1 := by
        omega
      omega
    have hbLeA : b.toNat ≤ a.toNat := by omega
    have hSub : (a - b).toNat = a.toNat - b.toNat :=
      BitVec64.toNat_sub_small hy31 hz31 hbLeA
    refine ⟨hrLo, ?_, ?_⟩
    · show ((imLookup m y).lo - (imLookup m z).hi + 1).toNat ≤ (a - b).toNat
      rw [hSub]
      -- new.lo ≥ 0; rest by omega
      omega
    · show (a - b).toNat < ((imLookup m y).hi - (imLookup m z).lo).toNat
      rw [hSub]
      omega
  · have ⟨hNeIR, hMemM⟩ := mem_imRemove hMemIR
    have ⟨bv, hσv, hSat⟩ := hM v r hMemM
    exact ⟨bv, by simp [Store.update, hNeIR, hσv], hSat⟩

-- ============================================================
-- § 13. Weakened imLookup membership
-- ============================================================

/-- `validInterval irTop = false`. Handy to contradict the `none`/`irTop`
    fallback of `imLookup`. -/
theorem validInterval_irTop_false : validInterval irTop = false := by decide

/-- `decide (0 ≤ irTop.lo) = false`. Subsumed by `validInterval_irTop_false`;
    broken out for the weaker-than-`validInterval` membership lemma. -/
theorem decide_zero_le_irTop_lo : decide ((0 : Int) ≤ irTop.lo) = false := by decide

/-- Weaker version of `imLookup_mem_of_valid`: only `decide (0 ≤ (imLookup m v).lo)
    = true` is needed to rule out the fallback. Used in `refineCond_sound`
    where the refined range's validity constrains the lookup's `.lo` but not
    its `.hi`. -/
theorem imLookup_mem_of_lo_decide {m : IMap} {v : Var}
    (h : decide ((0 : Int) ≤ (imLookup m v).lo) = true) :
    (v, imLookup m v) ∈ m := by
  unfold imLookup at h ⊢
  split at h
  · next q hFind =>
      have ⟨hq1, hqm⟩ := find?_pair_spec hFind
      obtain ⟨v', r⟩ := q
      simp only at hq1; subst hq1
      exact hqm
  · next hFind =>
      -- imLookup = irTop; decide_zero_le_irTop_lo contradicts h.
      exact absurd h (by rw [decide_zero_le_irTop_lo]; simp)

/-- `(0 : Int) ≤ (imLookup m v).lo` propositionally (not as `decide`). -/
theorem imLookup_mem_of_lo_nn {m : IMap} {v : Var}
    (h : (0 : Int) ≤ (imLookup m v).lo) :
    (v, imLookup m v) ∈ m :=
  imLookup_mem_of_lo_decide (by simpa using h)

-- ============================================================
-- § 14. Transfer soundness via case analysis on `Step`
-- ============================================================

/-- Soundness of `certSuccessor`: if the precondition `m` holds and the TAC
    program takes one step, then every valid entry in `certSuccessor m instr pc'`
    holds at the successor state. Case analysis on `Step`. -/
theorem certSuccessor_sound {p : Prog} {pc pc' : Nat} {σ σ' : Store}
    {am am' : ArrayMem} {m : IMap} {instr : TAC}
    (hInstr : p[pc]? = some instr)
    (hStep : p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am')
    (hM : IMap.satisfies m σ) :
    ∀ v r, (v, r) ∈ certSuccessor m instr pc' →
    validInterval r = true →
    ∃ bv, σ' v = .int bv ∧ IntervalInv.satisfies r bv := by
  -- Common lemma: `imRemove_sound` with the agree-except-at-x predicate
  -- tailored to `σ[x ↦ _]`.
  cases hStep with
  | @const _ _ _ _ val h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      cases val with
      | int n =>
          simp only [certSuccessor]; exact constInt_sound hM
      | bool _ =>
          simp only [certSuccessor]
          exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
      | float _ =>
          simp only [certSuccessor]
          exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | copy h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact copy_sound hM
  | @binop _ _ _ _ op _ _ _ _ h hy hz _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      cases op with
      | add =>
          simp only [certSuccessor]
          split
          · rename_i hVal
            simp only [Bool.and_eq_true] at hVal
            exact add_sound hM hVal.1 hVal.2 hy hz
          · exact imRemove_sound hM fun _ hy' => by simp [Store.update, hy']
      | sub =>
          simp only [certSuccessor]
          split
          · rename_i hVal
            simp only [Bool.and_eq_true] at hVal
            exact sub_sound hM hVal.1 hVal.2 hy hz
          · exact imRemove_sound hM fun _ hy' => by simp [Store.update, hy']
      | mul | div | mod | band | bor | bxor | shl | shr =>
          simp only [certSuccessor]
          exact imRemove_sound hM fun _ hy' => by simp [Store.update, hy']
  | boolop h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | goto h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | iftrue h _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | iffall h _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | arrLoad h _ _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | arrStore h _ _ _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | fbinop h _ _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | intToFloat h _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | floatToInt h _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | floatUnary h _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | fternop h _ _ _ =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]
      exact imRemove_sound hM fun _ hy => by simp [Store.update, hy]
  | print h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | printInt h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | printBool h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | printFloat h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM
  | printString h =>
      rw [hInstr] at h
      obtain ⟨rfl⟩ := Option.some.inj h
      simp only [certSuccessor]; exact identity_sound hM

-- ============================================================
-- § 15. Main theorem
-- ============================================================

/-- **Checker soundness.** If `checkLocalPreservation` accepts, the lifted
    `intervalMap inv` is a `PInvariantMap.preserved` invariant on `p`. -/
theorem checkLocalPreservation_sound (p : Prog) (inv : Array (Option IMap))
    (hChk : checkLocalPreservation p inv = true) :
    (intervalMap inv).preserved p := by
  simp only [checkLocalPreservation, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hChk
  obtain ⟨hSize, hAll⟩ := hChk
  intro pc σ am hInv pc' σ' am' hStep
  obtain ⟨instr, hInstr, hSucc⟩ := Step.mem_successors hStep
  have hpc : pc < p.size := (Prog.getElem?_eq_some_iff.mp hInstr).1
  have hpc_inv : pc < inv.size := by rw [hSize]; exact hpc
  -- Pull the oracle entry at pc as an actual value (not via case-split).
  have hinvPc : inv[pc]? = some (inv[pc]'hpc_inv) :=
    Array.getElem?_eq_getElem (by simpa using hpc_inv)
  -- Oracle's claim at pc must be `some (some m)` (the other cases contradict hInv).
  have hMσ : ∃ m, inv[pc]'hpc_inv = some m ∧ IMap.satisfies m σ := by
    simp only [intervalMap, hinvPc] at hInv
    cases hOptPc : inv[pc]'hpc_inv with
    | none => rw [hOptPc] at hInv; exact absurd hInv id
    | some m => rw [hOptPc] at hInv; exact ⟨m, rfl, hInv⟩
  obtain ⟨m, hOptPc, hM⟩ := hMσ
  have hinvPc' : inv[pc]? = some (some m) := by rw [hinvPc, hOptPc]
  -- Extract per-pc check
  have hCheck := hAll pc (List.mem_range.mpr hpc)
  rw [hinvPc', hInstr] at hCheck
  simp only [List.all_eq_true] at hCheck
  have hPerSucc := hCheck pc' hSucc
  rw [Bool.or_eq_true, decide_eq_true_eq] at hPerSucc
  -- Case on pc' < p.size vs not.
  by_cases hpc'lt : pc' < p.size
  · have hpc'_inv : pc' < inv.size := by rw [hSize]; exact hpc'lt
    have hinvPc'_eq : inv[pc']? = some (inv[pc']'hpc'_inv) :=
      Array.getElem?_eq_getElem (by simpa using hpc'_inv)
    -- Extract pc'-side obligation (pc' ≥ p.size is false).
    have hR : (match inv[pc']? with
               | some (some m') => refines (certSuccessor m instr pc') m'
               | some none      => false
               | none           => true) = true := by
      rcases hPerSucc with hGe | hR
      · exact absurd hGe (Nat.not_le.mpr hpc'lt)
      · exact hR
    rw [hinvPc'_eq] at hR
    simp only [intervalMap, hinvPc'_eq]
    cases hOptPc' : inv[pc']'hpc'_inv with
    | none =>
        rw [hOptPc'] at hR; exact absurd hR (by simp)
    | some m' =>
        rw [hOptPc'] at hR
        exact refines_sound hR (certSuccessor_sound hInstr hStep hM)
  · -- pc' ≥ p.size → inv[pc']? = none → goal is True.
    have : inv.size ≤ pc' := by rw [hSize]; omega
    have hinvPc'_none : inv[pc']? = none := Array.getElem?_eq_none_iff.mpr this
    simp [intervalMap, hinvPc'_none]

-- ============================================================
-- § 16. Phase 3 follow-up prep: refineCond soundness groundwork
-- ============================================================
--
-- Nothing in this section is consumed by `checkLocalPreservation_sound` yet.
-- The pieces here de-risk the follow-up phase that proves `refineCond_sound`
-- and wires the refined interval into `certSuccessor`'s `.ifgoto` arm. The
-- shape was validated by a probe on the livermore kernels (2026-04-21
-- session): BoundsOpt's widened loop-counter ranges have `hi` up to ~5·10¹²,
-- so the gate on `iv.hi` in `refineCond` must be *looser* than `validInterval`
-- (which caps at 2³¹) — otherwise the whole widened-loop-counter case is
-- rejected and no elision fires on the common `while (k <= N) { arr[k] }`
-- pattern. `validIntervalLoose` uses a 2⁶² cap: accepts every empirical
-- BoundsOpt output, stays comfortably under 2⁶³ so the `slt/sle` bridge
-- produces unsigned comparisons.

/-- Loose upper cap (`2⁶²`) for intermediate interval `hi` fields. Any value
    under this cap is representable as an unsigned `BitVec 64` value with
    top bit 0, so signed and unsigned comparisons agree. BoundsOpt's
    empirical outputs stay ~5·10¹² (≈2⁴³), well under this bound. -/
def looseCap : Int := 4611686018427387904  -- 2^62

/-- `looseCap`-gated well-formedness: `0 ≤ lo ≤ hi ≤ 2⁶²`. Strictly weaker
    than `validInterval` (which caps at `2³¹`); used as a precondition in the
    refineCond soundness proofs to rule out the `irTop` fallback and force
    `hi < 2⁶³` for the signed-unsigned bridge. -/
def validIntervalLoose (r : IRange) : Bool :=
  decide (0 ≤ r.lo) && decide (r.lo ≤ r.hi) && decide (r.hi ≤ looseCap)

theorem validIntervalLoose_iff (r : IRange) :
    validIntervalLoose r = true ↔ 0 ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ looseCap := by
  simp [validIntervalLoose, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- `validInterval r ⇒ validIntervalLoose r`: the tight cap is stricter. Used
    when we want a single source of truth on intermediate interval bounds. -/
theorem validInterval_imp_loose {r : IRange} (h : validInterval r = true) :
    validIntervalLoose r = true := by
  obtain ⟨h1, h2, h3⟩ := (validInterval_iff _).mp h
  rw [validIntervalLoose_iff]
  refine ⟨h1, h2, ?_⟩
  have : intervalCap ≤ looseCap := by decide
  omega

-- ============================================================
-- § 17. Signed-to-unsigned bridges for BitVec 64
-- ============================================================

/-- If `bv.toNat < 2⁶³`, top bit is `0` so signed and unsigned agree. This
    is the factored form of the `split <;> omega` idiom used inline in
    `constInt_satisfies`; extracted here so the eight refineCond-leaf proofs
    can share it. -/
theorem BitVec64.toInt_eq_toNat_of_lt_pow63 {bv : BitVec 64}
    (h : bv.toNat < 2 ^ 63) : bv.toInt = (bv.toNat : Int) := by
  simp only [BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- Signed-to-unsigned bridge for `BitVec.slt`: when both operands fit under
    `2⁶³` (so top bits are 0), signed strict-less-than matches unsigned. -/
theorem BitVec64.slt_toNat_lt {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (h : BitVec.slt a b = true) : a.toNat < b.toNat := by
  rw [BitVec.slt_iff_toInt_lt] at h
  have haInt : a.toInt = (a.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 ha
  have hbInt : b.toInt = (b.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 hb
  omega

/-- Negation: signed `¬ slt` at small values gives unsigned `≥`. Used in the
    false-branch of `.cmp .lt`. -/
theorem BitVec64.not_slt_toNat_ge {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (h : BitVec.slt a b = false) : b.toNat ≤ a.toNat := by
  have h' : ¬ (BitVec.slt a b = true) := by rw [h]; simp
  rw [BitVec.slt_iff_toInt_lt] at h'
  have haInt : a.toInt = (a.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 ha
  have hbInt : b.toInt = (b.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 hb
  omega

/-- Signed-to-unsigned bridge for `BitVec.sle`. -/
theorem BitVec64.sle_toNat_le {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (h : BitVec.sle a b = true) : a.toNat ≤ b.toNat := by
  rw [BitVec.sle_iff_toInt_le] at h
  have haInt : a.toInt = (a.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 ha
  have hbInt : b.toInt = (b.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 hb
  omega

/-- Negation companion for `sle`. -/
theorem BitVec64.not_sle_toNat_lt {a b : BitVec 64}
    (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (h : BitVec.sle a b = false) : b.toNat < a.toNat := by
  have h' : ¬ (BitVec.sle a b = true) := by rw [h]; simp
  rw [BitVec.sle_iff_toInt_le] at h'
  have haInt : a.toInt = (a.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 ha
  have hbInt : b.toInt = (b.toNat : Int) :=
    BitVec64.toInt_eq_toNat_of_lt_pow63 hb
  omega

-- ============================================================
-- § 18. Prototype leaf: `.cmp .lt (.var x) (.lit n)` true branch
-- ============================================================

/-- Prototype soundness for the true branch of
    `refineCond m (.cmp .lt (.var x) (.lit n)) true`. Establishes the pattern
    the other seven leaves will copy: `validIntervalLoose iv` gates the
    lookup membership; `validInterval new` gates the output claim; the slt
    bridge does the signed→unsigned transport.

    **Shape validated** — the other leaves (`.cmp .lt .var`, `.cmp .le .lit`,
    `.cmp .le .var`, each × true/false) follow the same outline. -/
theorem refineCond_lt_lit_true_sound
    {m : IMap} {σ : Store} {am : ArrayMem} {x : Var} {n : BitVec 64}
    (hM : IMap.satisfies m σ)
    (hIvLoose : validIntervalLoose (imLookup m x) = true)
    (hEval : (BoolExpr.cmp CmpOp.lt (Expr.var x) (Expr.lit n)).eval σ am = true) :
    ∀ v r, (v, r) ∈
      imSet m x ⟨(imLookup m x).lo, min (imLookup m x).hi n.toInt⟩ →
    validInterval r = true →
    ∃ bv, σ v = .int bv ∧ IntervalInv.satisfies r bv := by
  intro v r hMem hValid
  rcases (mem_imSet.mp hMem) with ⟨rfl, rfl⟩ | ⟨hNe, hMemM⟩
  · -- After `rcases ⟨rfl, rfl⟩`, `x` is gone (substituted to `v`); all
    -- hypotheses that mentioned `x` — `hIvLoose`, `hEval`, the new range —
    -- now reference `v` instead. Proof body uses `v` throughout.
    obtain ⟨hNewLoNn, hNewLoHi, _⟩ := (validInterval_iff _).mp hValid
    simp only at hNewLoNn hNewLoHi
    obtain ⟨hIvLoNn, _, hIvHiLooseCap⟩ :=
      (validIntervalLoose_iff _).mp hIvLoose
    have hMemV : (v, imLookup m v) ∈ m := imLookup_mem_of_lo_nn hIvLoNn
    have ⟨bv, hσv, hSat⟩ := hM v (imLookup m v) hMemV
    obtain ⟨_, hIvLoNat, hIvHiNat⟩ := hSat
    have hIvHiNat' : (imLookup m v).hi.toNat ≤ looseCap.toNat :=
      Int.toNat_mono_of_nonneg hIvHiLooseCap
    have hLooseNat : looseCap.toNat = 2 ^ 62 := by decide
    have hBv63 : bv.toNat < 2 ^ 63 := by omega
    -- Unfold `hEval` to `BitVec.slt bv n = true`
    have hSlt : BitVec.slt bv n = true := by
      have h := hEval
      simp only [BoolExpr.eval, Expr.eval, CmpOp.eval] at h
      rw [hσv] at h
      simpa [Value.toInt] using h
    -- `n.toInt ≥ 0` via the new-range validity chain
    have hNtoInt : (0 : Int) ≤ n.toInt := by
      have h1 : (imLookup m v).lo ≤ n.toInt := by
        have : (imLookup m v).lo ≤ min (imLookup m v).hi n.toInt := hNewLoHi
        omega
      omega
    have hNNat63 : n.toNat < 2 ^ 63 := by
      have : n.toNat < 2 ^ 64 := n.isLt
      simp only [BitVec.toInt_eq_toNat_cond] at hNtoInt
      split at hNtoInt <;> omega
    have hBvLtN : bv.toNat < n.toNat :=
      BitVec64.slt_toNat_lt hBv63 hNNat63 hSlt
    have hNIntEqToNat : n.toInt.toNat = n.toNat := by
      have : n.toInt = (n.toNat : Int) :=
        BitVec64.toInt_eq_toNat_of_lt_pow63 hNNat63
      omega
    refine ⟨bv, hσv, hNewLoNn, ?_, ?_⟩
    · show (imLookup m v).lo.toNat ≤ bv.toNat
      exact hIvLoNat
    · show bv.toNat < (min (imLookup m v).hi n.toInt).toNat
      -- `Int.min a b = if a ≤ b then a else b`; split and use the matching fact.
      rw [Int.min_def]
      split
      · -- iv.hi selected → bv.toNat < iv.hi.toNat
        exact hIvHiNat
      · -- n.toInt selected → bv.toNat < n.toInt.toNat = n.toNat
        rw [hNIntEqToNat]; exact hBvLtN
  · -- Fall-through: pre-existing entry unchanged
    exact hM v r hMemM

end BoundsOpt
