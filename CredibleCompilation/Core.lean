/-!
# Core Domains and Expressions

Basic domains (Var, Label, Value, VarTy, Store, TyCtx, TypedStore),
binary and comparison operators, expressions, and boolean expressions.

Split from `Semantics.lean`.
-/

-- ============================================================
-- § 1. Basic domains
-- ============================================================

abbrev Var   := String
abbrev Label := Nat        -- program counter / jump target

/-- Runtime values: a 64-bit integer, a boolean, or a 64-bit float.
    Integers and floats both use `BitVec 64` to match ARM64 register semantics.
    Float operations are opaque/uninterpreted in proofs. -/
inductive Value where
  | int   : BitVec 64 → Value
  | bool  : Bool → Value
  | float : BitVec 64 → Value
  deriving Repr, DecidableEq, Inhabited

/-- Variable types. -/
inductive VarTy where
  | int | bool | float
  deriving Repr, DecidableEq, Inhabited

namespace VarTy

/-- The default `Value` for a variable type: `0` for int, `false` for bool. -/
def defaultVal : VarTy → Value
  | .int   => .int (0 : BitVec 64)
  | .bool  => .bool false
  | .float => .float (0 : BitVec 64)

end VarTy

namespace Value

def toInt : Value → BitVec 64
  | .int n   => n
  | .bool _  => 0
  | .float _ => 0

def toBool : Value → Bool
  | .bool b  => b
  | .int _   => false
  | .float _ => false

def toFloat : Value → BitVec 64
  | .float f => f
  | .int _   => 0
  | .bool _  => 0

def typeOf : Value → VarTy
  | .int _   => .int
  | .bool _  => .bool
  | .float _ => .float

theorem int_of_typeOf_int {v : Value} (h : v.typeOf = .int) : ∃ n, v = .int n := by
  cases v with
  | int n => exact ⟨n, rfl⟩
  | bool _ => simp [typeOf] at h
  | float _ => simp [typeOf] at h

theorem bool_of_typeOf_bool {v : Value} (h : v.typeOf = .bool) : ∃ b, v = .bool b := by
  cases v with
  | int _ => simp [typeOf] at h
  | bool b => exact ⟨b, rfl⟩
  | float _ => simp [typeOf] at h

theorem float_of_typeOf_float {v : Value} (h : v.typeOf = .float) : ∃ f, v = .float f := by
  cases v with
  | int _ => simp [typeOf] at h
  | bool _ => simp [typeOf] at h
  | float f => exact ⟨f, rfl⟩

@[simp] theorem toInt_int (n : BitVec 64) : (Value.int n).toInt = n := rfl
@[simp] theorem toBool_bool (b : Bool) : (Value.bool b).toBool = b := rfl
@[simp] theorem toFloat_float (f : BitVec 64) : (Value.float f).toFloat = f := rfl
@[simp] theorem typeOf_int (n : BitVec 64) : (Value.int n).typeOf = .int := rfl
@[simp] theorem typeOf_bool (b : Bool) : (Value.bool b).typeOf = .bool := rfl
@[simp] theorem typeOf_float (f : BitVec 64) : (Value.float f).typeOf = .float := rfl

/-- Wrap a BitVec 64 as a Value of the given type. -/
def ofBitVec : VarTy → BitVec 64 → Value
  | .int,   v => .int v
  | .bool,  v => .bool (v != 0)
  | .float, v => .float v

/-- Extract the BitVec 64 payload from a Value (booleans become 0 or 1). -/
def toBits : Value → BitVec 64
  | .int v   => v
  | .bool b  => if b then 1 else 0
  | .float v => v

@[simp] theorem ofBitVec_int (v : BitVec 64) : ofBitVec .int v = .int v := rfl
@[simp] theorem ofBitVec_bool (v : BitVec 64) : ofBitVec .bool v = .bool (v != 0) := rfl
@[simp] theorem ofBitVec_float (v : BitVec 64) : ofBitVec .float v = .float v := rfl
@[simp] theorem toBits_int (v : BitVec 64) : (Value.int v).toBits = v := rfl
@[simp] theorem toBits_bool (b : Bool) : (Value.bool b).toBits = if b then 1 else 0 := rfl
@[simp] theorem toBits_float (v : BitVec 64) : (Value.float v).toBits = v := rfl

@[simp] theorem typeOf_ofBitVec (ty : VarTy) (v : BitVec 64) : (ofBitVec ty v).typeOf = ty := by
  cases ty <;> simp [ofBitVec, typeOf]

/-- Roundtrip: if a value has type `ty`, wrapping its bits gives back the same value. -/
theorem ofBitVec_toBits {v : Value} {ty : VarTy} (h : v.typeOf = ty) :
    Value.ofBitVec ty v.toBits = v := by
  cases v with
  | int n => cases ty <;> simp [typeOf] at h <;> simp [ofBitVec, toBits, h]
  | bool b => cases ty <;> simp [typeOf] at h <;> simp [ofBitVec, toBits, h]; cases b <;> rfl
  | float f => cases ty <;> simp [typeOf] at h <;> simp [ofBitVec, toBits, h]

end Value

/-- A store (state) maps every variable to a typed value. -/
def Store := Var → Value

/-- A typing context assigns a type to every variable. -/
abbrev TyCtx := Var → VarTy

/-- A store is well-typed w.r.t. a typing context if every variable's
    runtime value matches its declared type. -/
def TypedStore (Γ : TyCtx) (σ : Store) : Prop :=
  ∀ x, (σ x).typeOf = Γ x

namespace Store

def init : Store := fun _ => .int (0 : BitVec 64)

/-- Type-respecting zero store: each variable gets the zero value of its declared type. -/
def typedInit (Γ : TyCtx) : Store := fun v => Value.ofBitVec (Γ v) 0

/-- Functional update  σ[x ↦ v] -/
def update (σ : Store) (x : Var) (v : Value) : Store :=
  fun y => if y == x then v else σ y

theorem update_self (σ : Store) (x : Var) (v : Value) :
    σ.update x v x = v := by simp [update]

theorem update_other (σ : Store) (x y : Var) (v : Value) (h : y ≠ x) :
    σ.update x v y = σ y := by simp only [update, beq_iff_eq, if_neg h]

theorem update_shadow (σ : Store) (x : Var) (u v : Value) :
    (σ.update x u).update x v = σ.update x v := by
  funext y; simp [update]; split <;> simp_all

theorem update_comm (σ : Store) (x y : Var) (u v : Value) (h : x ≠ y) :
    (σ.update x u).update y v = (σ.update y v).update x u := by
  funext z; simp [update]; split <;> split <;> simp_all [Ne.symm]

/-- Updating a variable with its current value is a no-op. -/
theorem update_of_eq (σ : Store) (x : Var) (v : Value) (h : σ x = v) :
    σ.update x v = σ := by
  funext y; simp only [update]; split
  next heq => rw [beq_iff_eq] at heq; rw [heq, h]
  next => rfl

end Store

-- Notation  σ[x ↦ v]
notation:max σ "[" x " ↦ " v "]" => Store.update σ x v

-- ============================================================
-- § 1a. TypedStore lemmas
-- ============================================================

theorem TypedStore.init (Γ : TyCtx) (h : ∀ x, Γ x = .int) :
    TypedStore Γ Store.init := by
  intro x; simp [Store.init, Value.typeOf, h]

theorem TypedStore.typedInit (Γ : TyCtx) : TypedStore Γ (Store.typedInit Γ) := by
  intro x; simp [Store.typedInit]


theorem TypedStore.update_typed {Γ : TyCtx} {σ : Store} {x : Var} {v : Value}
    (hts : TypedStore Γ σ) (hv : v.typeOf = Γ x) :
    TypedStore Γ (σ[x ↦ v]) := by
  intro y; simp only [Store.update]
  split
  · next h => rw [beq_iff_eq] at h; rw [h]; exact hv
  · exact hts y

-- ============================================================
-- § 1b. Array memory
-- ============================================================

abbrev ArrayName := String

/-- Array memory: maps array name and index to a 64-bit value.
    Arrays are global, statically allocated, and separate from the variable store.
    Indices are `BitVec 64` to match register/value semantics directly. -/
def ArrayMem := ArrayName → BitVec 64 → BitVec 64

namespace ArrayMem

def init : ArrayMem := fun _ _ => 0

def read (am : ArrayMem) (arr : ArrayName) (idx : BitVec 64) : BitVec 64 :=
  am arr idx

def write (am : ArrayMem) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) : ArrayMem :=
  fun a i => if a == arr && i == idx then v else am a i

@[simp] theorem read_write_same (am : ArrayMem) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (am.write arr idx v).read arr idx = v := by
  simp [read, write]

theorem read_write_ne_arr (am : ArrayMem) (arr arr' : ArrayName) (idx idx' : BitVec 64)
    (v : BitVec 64) (h : arr' ≠ arr) :
    (am.write arr idx v).read arr' idx' = am.read arr' idx' := by
  simp [read, write, h]

theorem read_write_ne_idx (am : ArrayMem) (arr : ArrayName) (idx idx' : BitVec 64)
    (v : BitVec 64) (h : idx' ≠ idx) :
    (am.write arr idx v).read arr idx' = am.read arr idx' := by
  simp [read, write, h]

end ArrayMem

/-- Look up an array's declared size.  Returns 0 for undeclared arrays
    (meaning all accesses are out-of-bounds). -/
def arraySize (decls : List (ArrayName × Nat × VarTy)) (arr : ArrayName) : Nat :=
  match decls.find? (fun p => p.1 == arr) with
  | some (_, n, _) => n
  | none => 0

/-- Array size as `BitVec 64`, for direct comparison with bitvec indices. -/
def arraySizeBv (decls : List (ArrayName × Nat × VarTy)) (arr : ArrayName) : BitVec 64 :=
  BitVec.ofNat 64 (arraySize decls arr)

/-- Look up an array's declared element type.  Returns `.int` for undeclared arrays. -/
def arrayElemTy (decls : List (ArrayName × Nat × VarTy)) (arr : ArrayName) : VarTy :=
  match decls.find? (fun p => p.1 == arr) with
  | some (_, _, ty) => ty
  | none => .int

-- ============================================================
-- § 2. Binary operators
-- ============================================================

inductive BinOp | add | sub | mul | div | mod | band | bor | bxor | shl | shr
  deriving Repr, DecidableEq

def BinOp.eval : BinOp → BitVec 64 → BitVec 64 → BitVec 64
  | .add,  a, b => a + b
  | .sub,  a, b => a - b
  | .mul,  a, b => a * b
  | .div,  a, b => BitVec.sdiv a b
  | .mod,  a, b => BitVec.srem a b
  | .band, a, b => a &&& b
  | .bor,  a, b => a ||| b
  | .bxor, a, b => a ^^^ b
  | .shl,  a, b => a <<< b
  | .shr,  a, b => BitVec.sshiftRight a b.toNat

/-- An operation is safe if it will not cause the program to get stuck.
    Only `div` and `mod` can fault — when the divisor is zero. -/
def BinOp.safe : BinOp → BitVec 64 → BitVec 64 → Prop
  | .div, _, b => b ≠ 0
  | .mod, _, b => b ≠ 0
  | _, _, _    => True

instance {op : BinOp} {a b : BitVec 64} : Decidable (op.safe a b) := by
  unfold BinOp.safe; cases op <;> exact inferInstance

-- ============================================================
-- § 2a. Comparison operators
-- ============================================================

inductive CmpOp | eq | ne | lt | le deriving Repr, DecidableEq

def CmpOp.eval : CmpOp → BitVec 64 → BitVec 64 → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => BitVec.slt a b
  | .le, a, b => BitVec.sle a b

-- ============================================================
-- § 2a'. Float binary operators
-- ============================================================

inductive FloatBinOp | fadd | fsub | fmul | fdiv | fpow | fmin | fmax deriving Repr, DecidableEq

/-- Evaluate a float binary operation. Opaque in proofs — FP operations
    are uninterpreted functions over BitVec 64. -/
opaque FloatBinOp.eval : FloatBinOp → BitVec 64 → BitVec 64 → BitVec 64

/-- IEEE 754 addition is commutative for all values (including NaN, ±0, ±∞). -/
axiom FloatBinOp.fadd_comm (a b : BitVec 64) :
  FloatBinOp.eval .fadd a b = FloatBinOp.eval .fadd b a

-- ============================================================
-- § 2a''. Float comparison operators
-- ============================================================

inductive FloatCmpOp | feq | fne | flt | fle deriving Repr, DecidableEq

/-- Evaluate a float comparison. Opaque in proofs — FP comparisons
    are uninterpreted predicates over BitVec 64. -/
opaque FloatCmpOp.eval : FloatCmpOp → BitVec 64 → BitVec 64 → Bool

/-- IEEE 754: `a < b ↔ ¬(b ≤ a)` for all bit patterns (including NaN, where
    both sides are false/true consistently since `flt` and `fle` both return
    false for NaN operands). -/
axiom FloatCmpOp.flt_iff_not_fle (a b : BitVec 64) :
  FloatCmpOp.eval .flt a b = !FloatCmpOp.eval .fle b a

/-- IEEE 754: `a ≤ b ↔ ¬(b < a)`. Flip of `flt_iff_not_fle`. -/
axiom FloatCmpOp.fle_iff_not_flt (a b : BitVec 64) :
  FloatCmpOp.eval .fle a b = !FloatCmpOp.eval .flt b a

/-- IEEE 754: equality is symmetric. -/
axiom FloatCmpOp.feq_comm (a b : BitVec 64) :
  FloatCmpOp.eval .feq a b = FloatCmpOp.eval .feq b a

/-- IEEE 754: inequality is symmetric. -/
axiom FloatCmpOp.fne_comm (a b : BitVec 64) :
  FloatCmpOp.eval .fne a b = FloatCmpOp.eval .fne b a

/-- Convert a signed integer (BitVec 64) to float (BitVec 64).
    Opaque — corresponds to ARM64 `scvtf`. -/
opaque intToFloatBv : BitVec 64 → BitVec 64

/-- Convert a float (BitVec 64) to signed integer (BitVec 64).
    Opaque — corresponds to ARM64 `fcvtzs`. -/
opaque floatToIntBv : BitVec 64 → BitVec 64

/-- Float unary intrinsic operations. Each is opaque in proofs. -/
inductive FloatUnaryOp
  | exp | sqrt
  | sin | cos | tan
  | log | log2 | log10
  | abs | neg | round
  deriving Repr, DecidableEq

/-- True for ops that have native ARM64 instructions (fsqrt, fabs, fneg).
    False for library calls (bl _exp, etc.) that clobber caller-saved registers. -/
def FloatUnaryOp.isNative : FloatUnaryOp → Bool
  | .sqrt | .abs | .neg => true
  | .exp | .sin | .cos | .tan | .log | .log2 | .log10 | .round => false

/-- Evaluate a float unary op. Opaque — each is an uninterpreted function over BitVec 64. -/
opaque FloatUnaryOp.eval : FloatUnaryOp → BitVec 64 → BitVec 64

/-- Ternary floating-point operations (fused multiply-add / multiply-subtract). -/
inductive FloatTernOp | fmadd | fmsub deriving Repr, DecidableEq

/-- Evaluate a float ternary op using the two-rounding model.
    fmadd: a + b*c,  fmsub: a - b*c  (each sub-op rounds separately).
    NOT opaque — proofs need to unfold this to match ARM step rules. -/
def FloatTernOp.eval : FloatTernOp → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64
  | .fmadd, a, b, c => FloatBinOp.eval .fadd a (FloatBinOp.eval .fmul b c)
  | .fmsub, a, b, c => FloatBinOp.eval .fsub a (FloatBinOp.eval .fmul b c)

/-- Convert a Lean Float to its IEEE 754 bit representation as BitVec 64.
    Uses `Float.toBits` for proper bit reinterpretation (not truncation). -/
def floatToBits (f : Float) : BitVec 64 :=
  BitVec.ofNat 64 f.toBits.toNat

/-- Convert a BinOp to the corresponding FloatBinOp (mod has no float equivalent). -/
def BinOp.toFloat? : BinOp → Option FloatBinOp
  | .add => some .fadd
  | .sub => some .fsub
  | .mul => some .fmul
  | .div => some .fdiv
  | .mod | .band | .bor | .bxor | .shl | .shr => none

/-- Convert a CmpOp to the corresponding FloatCmpOp. -/
def CmpOp.toFloat : CmpOp → FloatCmpOp
  | .eq => .feq
  | .ne => .fne
  | .lt => .flt
  | .le => .fle

-- ============================================================
-- § 2b. Expressions over stores
-- ============================================================

/-- Expressions that can be evaluated in a store. Used to describe
    how transformed-program variables map to original-program values. -/
inductive Expr where
  | lit    : BitVec 64 → Expr
  | blit   : Bool → Expr
  | var    : Var → Expr
  | bin    : BinOp → Expr → Expr → Expr
  -- Symbolic boolean expression constructors (for tracking boolop results)
  | tobool  : Expr → Expr                  -- .bool (e.eval σ).toBool
  | cmpE    : CmpOp → Expr → Expr → Expr  -- .bool (op.eval (a.eval σ).toInt (b.eval σ).toInt)
  | cmpLitE : CmpOp → Expr → BitVec 64 → Expr   -- .bool (op.eval (a.eval σ).toInt n)
  | notE    : Expr → Expr                  -- .bool (!(e.eval σ).toBool)
  | andE    : Expr → Expr → Expr           -- .bool ((a.eval σ).toBool && (b.eval σ).toBool)
  | orE     : Expr → Expr → Expr           -- .bool ((a.eval σ).toBool || (b.eval σ).toBool)
  -- Symbolic array read (for tracking arrLoad results)
  | arrRead : ArrayName → Expr → Expr      -- .int (am.read arr (idx.eval σ am).toInt)
  -- Float expression constructors
  | flit     : BitVec 64 → Expr                       -- float literal
  | fbin     : FloatBinOp → Expr → Expr → Expr        -- float binary op
  | fcmpE    : FloatCmpOp → Expr → Expr → Expr        -- .bool (fop.eval a b)
  | intToFloat : Expr → Expr                           -- .float (intToFloat (e.toInt))
  | floatToInt : Expr → Expr                           -- .int (floatToInt (e.toFloat))
  | floatUnary : FloatUnaryOp → Expr → Expr             -- .float (op.eval(e.toFloat))
  | ftern     : FloatTernOp → Expr → Expr → Expr → Expr -- .float (op.eval a b c)
  | farrRead : ArrayName → Expr → Expr                -- .float (am.read arr idx)
  deriving Repr, DecidableEq

def Expr.eval (σ : Store) (am : ArrayMem) : Expr → Value
  | .lit n          => .int n
  | .blit b         => .bool b
  | .var x          => σ x
  | .bin op a b     => .int (op.eval (a.eval σ am).toInt (b.eval σ am).toInt)
  | .tobool e       => .bool (e.eval σ am).toBool
  | .cmpE op a b    => .bool (op.eval (a.eval σ am).toInt (b.eval σ am).toInt)
  | .cmpLitE op a n => .bool (op.eval (a.eval σ am).toInt n)
  | .notE e         => .bool (!(e.eval σ am).toBool)
  | .andE a b       => .bool ((a.eval σ am).toBool && (b.eval σ am).toBool)
  | .orE a b        => .bool ((a.eval σ am).toBool || (b.eval σ am).toBool)
  | .arrRead arr idx => .int (am.read arr (idx.eval σ am).toInt)
  | .flit f            => .float f
  | .fbin op a b       => .float (op.eval (a.eval σ am).toFloat (b.eval σ am).toFloat)
  | .fcmpE op a b      => .bool (FloatCmpOp.eval op (a.eval σ am).toFloat (b.eval σ am).toFloat)
  | .intToFloat e      => .float (intToFloatBv (e.eval σ am).toInt)
  | .floatToInt e      => .int (floatToIntBv (e.eval σ am).toFloat)
  | .floatUnary op e   => .float (op.eval (e.eval σ am).toFloat)
  | .ftern op a b c    => .float (FloatTernOp.eval op (a.eval σ am).toFloat (b.eval σ am).toFloat (c.eval σ am).toFloat)
  | .farrRead arr idx  => .float (am.read arr (idx.eval σ am).toInt)

/-- Does an expression contain any `arrRead` or `farrRead` sub-expression? -/
def Expr.hasArrRead : Expr → Bool
  | .lit _ | .blit _ | .var _ | .flit _ => false
  | .bin _ a b     => a.hasArrRead || b.hasArrRead
  | .tobool e      => e.hasArrRead
  | .cmpE _ a b    => a.hasArrRead || b.hasArrRead
  | .cmpLitE _ a _ => a.hasArrRead
  | .notE e        => e.hasArrRead
  | .andE a b      => a.hasArrRead || b.hasArrRead
  | .orE a b       => a.hasArrRead || b.hasArrRead
  | .arrRead _ _   => true
  | .fbin _ a b    => a.hasArrRead || b.hasArrRead
  | .fcmpE _ a b   => a.hasArrRead || b.hasArrRead
  | .intToFloat e  => e.hasArrRead
  | .floatToInt e  => e.hasArrRead
  | .floatUnary _ e => e.hasArrRead
  | .ftern _ a b c => a.hasArrRead || b.hasArrRead || c.hasArrRead
  | .farrRead _ _  => true

/-- Collect all variable names appearing in an expression (with possible duplicates). -/
def Expr.freeVars : Expr → List Var
  | .lit _ | .blit _ | .flit _ => []
  | .var v          => [v]
  | .bin _ a b      => a.freeVars ++ b.freeVars
  | .tobool e       => e.freeVars
  | .cmpE _ a b     => a.freeVars ++ b.freeVars
  | .cmpLitE _ a _  => a.freeVars
  | .notE e         => e.freeVars
  | .andE a b       => a.freeVars ++ b.freeVars
  | .orE a b        => a.freeVars ++ b.freeVars
  | .arrRead _ idx  => idx.freeVars
  | .fbin _ a b     => a.freeVars ++ b.freeVars
  | .fcmpE _ a b    => a.freeVars ++ b.freeVars
  | .intToFloat e   => e.freeVars
  | .floatToInt e   => e.freeVars
  | .floatUnary _ e => e.freeVars
  | .ftern _ a b c => a.freeVars ++ b.freeVars ++ c.freeVars
  | .farrRead _ idx => idx.freeVars

/-- For arrRead-free expressions, evaluation is independent of the array memory. -/
theorem Expr.eval_noArrRead (e : Expr) (σ : Store) (am₁ am₂ : ArrayMem)
    (h : e.hasArrRead = false) : e.eval σ am₁ = e.eval σ am₂ := by
  induction e with
  | lit _ | blit _ | var _ => rfl
  | bin _ a b iha ihb =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1, ihb h.2]
  | tobool e ih =>
    simp only [hasArrRead] at h; simp only [Expr.eval]; rw [ih h]
  | cmpE _ a b iha ihb =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1, ihb h.2]
  | cmpLitE _ a _ ih =>
    simp only [hasArrRead] at h; simp only [Expr.eval]; rw [ih h]
  | notE e ih =>
    simp only [hasArrRead] at h; simp only [Expr.eval]; rw [ih h]
  | andE a b iha ihb =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1, ihb h.2]
  | orE a b iha ihb =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1, ihb h.2]
  | arrRead _ _ => simp [hasArrRead] at h
  | flit _ => rfl
  | fbin _ a b iha ihb =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1, ihb h.2]
  | fcmpE _ a b iha ihb =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1, ihb h.2]
  | intToFloat e ih =>
    simp only [hasArrRead] at h; simp only [Expr.eval]; rw [ih h]
  | floatToInt e ih =>
    simp only [hasArrRead] at h; simp only [Expr.eval]; rw [ih h]
  | floatUnary _ e ih =>
    simp only [hasArrRead] at h; simp only [Expr.eval]; rw [ih h]
  | ftern _ a b c iha ihb ihc =>
    simp only [hasArrRead, Bool.or_eq_false_iff] at h
    simp only [Expr.eval]; rw [iha h.1.1, ihb h.1.2, ihc h.2]
  | farrRead _ _ => simp [hasArrRead] at h

-- ============================================================
-- § 2c. Boolean expressions
-- ============================================================

/-- Boolean expressions for conditional branches. -/
inductive BoolExpr where
  | lit    : Bool → BoolExpr                   -- true / false literal
  | bvar   : Var → BoolExpr                    -- read a boolean variable
  | cmp    : CmpOp → Var → Var → BoolExpr     -- x op y (integer comparison)
  | cmpLit : CmpOp → Var → BitVec 64 → BoolExpr     -- x op n (variable vs literal)
  | not    : BoolExpr → BoolExpr
  | fcmp    : FloatCmpOp → Var → Var → BoolExpr      -- float comparison
  | fcmpLit : FloatCmpOp → Var → BitVec 64 → BoolExpr  -- x fop n (variable vs float literal)
  deriving Repr, DecidableEq

/-- Evaluate a boolean expression. Uses `.toInt`/`.toBool` extractors;
    under well-typedness the extractors are faithful. -/
def BoolExpr.eval (σ : Store) : BoolExpr → Bool
  | .lit b         => b
  | .bvar x        => (σ x).toBool
  | .cmp op x y    => op.eval (σ x).toInt (σ y).toInt
  | .cmpLit op x n => op.eval (σ x).toInt n
  | .not e         => !e.eval σ
  | .fcmp op x y      => FloatCmpOp.eval op (σ x).toFloat (σ y).toFloat
  | .fcmpLit op x n   => FloatCmpOp.eval op (σ x).toFloat n

theorem BoolExpr.eval_congr (cond : BoolExpr) (σ τ : Store)
    (hagree : ∀ y, σ y = τ y) : cond.eval σ = cond.eval τ := by
  induction cond with
  | lit b => simp [BoolExpr.eval]
  | bvar x => simp [BoolExpr.eval, hagree]
  | cmp op x y => simp [BoolExpr.eval, hagree]
  | cmpLit op x n => simp [BoolExpr.eval, hagree]
  | not e ih => simp [BoolExpr.eval, ih]
  | fcmp op x y => simp [BoolExpr.eval, hagree]
  | fcmpLit op x n => simp [BoolExpr.eval, hagree]

/-- Collect all variable names from a boolean expression. -/
def BoolExpr.vars : BoolExpr → List Var
  | .lit _          => []
  | .bvar x         => [x]
  | .cmp _ x y      => [x, y]
  | .cmpLit _ x _   => [x]
  | .not e          => e.vars
  | .fcmp _ x y     => [x, y]
  | .fcmpLit _ x _  => [x]
