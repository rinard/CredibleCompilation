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

/-- Runtime values: either a 64-bit integer or a boolean.
    Integers use `BitVec 64` to match ARM64 register semantics. -/
inductive Value where
  | int  : BitVec 64 → Value
  | bool : Bool → Value
  deriving Repr, DecidableEq, Inhabited

/-- Variable types. -/
inductive VarTy where
  | int | bool
  deriving Repr, DecidableEq

namespace VarTy

/-- The default `Value` for a variable type: `0` for int, `false` for bool. -/
def defaultVal : VarTy → Value
  | .int  => .int (0 : BitVec 64)
  | .bool => .bool false

end VarTy

namespace Value

def toInt : Value → BitVec 64
  | .int n  => n
  | .bool _ => 0

def toBool : Value → Bool
  | .bool b => b
  | .int _  => false

def typeOf : Value → VarTy
  | .int _  => .int
  | .bool _ => .bool

theorem int_of_typeOf_int {v : Value} (h : v.typeOf = .int) : ∃ n, v = .int n := by
  cases v with
  | int n => exact ⟨n, rfl⟩
  | bool _ => simp [typeOf] at h

theorem bool_of_typeOf_bool {v : Value} (h : v.typeOf = .bool) : ∃ b, v = .bool b := by
  cases v with
  | int _ => simp [typeOf] at h
  | bool b => exact ⟨b, rfl⟩

@[simp] theorem toInt_int (n : BitVec 64) : (Value.int n).toInt = n := rfl
@[simp] theorem toBool_bool (b : Bool) : (Value.bool b).toBool = b := rfl
@[simp] theorem typeOf_int (n : BitVec 64) : (Value.int n).typeOf = .int := rfl
@[simp] theorem typeOf_bool (b : Bool) : (Value.bool b).typeOf = .bool := rfl

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
    Arrays are global, statically allocated, and separate from the variable store. -/
def ArrayMem := ArrayName → Nat → BitVec 64

namespace ArrayMem

def init : ArrayMem := fun _ _ => 0

def read (am : ArrayMem) (arr : ArrayName) (idx : Nat) : BitVec 64 :=
  am arr idx

def write (am : ArrayMem) (arr : ArrayName) (idx : Nat) (v : BitVec 64) : ArrayMem :=
  fun a i => if a == arr && i == idx then v else am a i

@[simp] theorem read_write_same (am : ArrayMem) (arr : ArrayName) (idx : Nat) (v : BitVec 64) :
    (am.write arr idx v).read arr idx = v := by
  simp [read, write]

theorem read_write_ne_arr (am : ArrayMem) (arr arr' : ArrayName) (idx idx' : Nat)
    (v : BitVec 64) (h : arr' ≠ arr) :
    (am.write arr idx v).read arr' idx' = am.read arr' idx' := by
  simp [read, write, h]

theorem read_write_ne_idx (am : ArrayMem) (arr : ArrayName) (idx idx' : Nat)
    (v : BitVec 64) (h : idx' ≠ idx) :
    (am.write arr idx v).read arr idx' = am.read arr idx' := by
  simp [read, write, h]

end ArrayMem

-- ============================================================
-- § 2. Binary operators
-- ============================================================

inductive BinOp | add | sub | mul | div | mod deriving Repr, DecidableEq

def BinOp.eval : BinOp → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => BitVec.sdiv a b
  | .mod, a, b => BitVec.srem a b

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
  | arrRead : ArrayName → Expr → Expr      -- .int (am.read arr (idx.eval σ am).toInt.toNat)
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
  | .arrRead arr idx => .int (am.read arr (idx.eval σ am).toInt.toNat)

/-- Does an expression contain any `arrRead` sub-expression? -/
def Expr.hasArrRead : Expr → Bool
  | .lit _ | .blit _ | .var _ => false
  | .bin _ a b     => a.hasArrRead || b.hasArrRead
  | .tobool e      => e.hasArrRead
  | .cmpE _ a b    => a.hasArrRead || b.hasArrRead
  | .cmpLitE _ a _ => a.hasArrRead
  | .notE e        => e.hasArrRead
  | .andE a b      => a.hasArrRead || b.hasArrRead
  | .orE a b       => a.hasArrRead || b.hasArrRead
  | .arrRead _ _   => true

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
  deriving Repr, DecidableEq

/-- Evaluate a boolean expression. Uses `.toInt`/`.toBool` extractors;
    under well-typedness the extractors are faithful. -/
def BoolExpr.eval (σ : Store) : BoolExpr → Bool
  | .lit b         => b
  | .bvar x        => (σ x).toBool
  | .cmp op x y    => op.eval (σ x).toInt (σ y).toInt
  | .cmpLit op x n => op.eval (σ x).toInt n
  | .not e         => !e.eval σ

theorem BoolExpr.eval_congr (cond : BoolExpr) (σ τ : Store)
    (hagree : ∀ y, σ y = τ y) : cond.eval σ = cond.eval τ := by
  induction cond with
  | lit b => simp [BoolExpr.eval]
  | bvar x => simp [BoolExpr.eval, hagree]
  | cmp op x y => simp [BoolExpr.eval, hagree]
  | cmpLit op x n => simp [BoolExpr.eval, hagree]
  | not e ih => simp [BoolExpr.eval, ih]

/-- Collect all variable names from a boolean expression. -/
def BoolExpr.vars : BoolExpr → List Var
  | .lit _        => []
  | .bvar x       => [x]
  | .cmp _ x y    => [x, y]
  | .cmpLit _ x _ => [x]
  | .not e        => e.vars
