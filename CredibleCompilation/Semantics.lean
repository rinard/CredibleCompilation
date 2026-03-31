/-!
# Operational Semantics for Three-Address Code

Following Winskel, "The Formal Semantics of Programming Languages."

We define a simple imperative language in three-address code (TAC) form,
with typed (integer and boolean) variables, and give it a small-step structural
operational semantics.  Big-step termination and basic metatheory follow.

A static type system ensures well-typed programs cannot get stuck from
type errors — the only stuck condition is division by zero.

Note: Lean reserves `⊢`, so we use `⊩` as the program-turnstile.
-/

-- ============================================================
-- § 1. Basic domains
-- ============================================================

abbrev Var   := String
abbrev Label := Nat        -- program counter / jump target

/-- Runtime values: either an integer or a boolean. -/
inductive Value where
  | int  : Int → Value
  | bool : Bool → Value
  deriving Repr, DecidableEq, Inhabited

/-- Variable types. -/
inductive VarTy where
  | int | bool
  deriving Repr, DecidableEq

namespace VarTy

/-- The default `Value` for a variable type: `0` for int, `false` for bool. -/
def defaultVal : VarTy → Value
  | .int  => .int 0
  | .bool => .bool false

end VarTy

namespace Value

def toInt : Value → Int
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

@[simp] theorem toInt_int (n : Int) : (Value.int n).toInt = n := rfl
@[simp] theorem toBool_bool (b : Bool) : (Value.bool b).toBool = b := rfl
@[simp] theorem typeOf_int (n : Int) : (Value.int n).typeOf = .int := rfl
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

def init : Store := fun _ => .int 0

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
-- § 1b. 64-bit wrapping arithmetic
-- ============================================================

/-- The 64-bit modulus. -/
def Word : Int := 2 ^ 64

/-- Wrap an integer to the unsigned 64-bit range `[0, 2^64)`.
    This models the behavior of ARM64 integer arithmetic. -/
def wrap64 (n : Int) : Int := ((n % Word) + Word) % Word

theorem wrap64_nonneg (n : Int) : 0 ≤ wrap64 n := Int.emod_nonneg _ (by decide)

theorem wrap64_lt (n : Int) : wrap64 n < Word := by
  unfold wrap64 Word
  omega

theorem wrap64_toNat_lt (n : Int) : (wrap64 n).toNat < 2 ^ 64 := by
  have h1 := wrap64_nonneg n
  have h2 := wrap64_lt n
  exact Int.toNat_lt h1 |>.mpr h2

theorem wrap64_idempotent (n : Int) : wrap64 (wrap64 n) = wrap64 n := by
  unfold wrap64 Word; omega

theorem wrap64_of_nonneg_lt {n : Int} (h1 : 0 ≤ n) (h2 : n < Word) :
    wrap64 n = n := by
  unfold wrap64 Word at *; omega

theorem wrap64_add_left (a b : Int) : wrap64 (wrap64 a + b) = wrap64 (a + b) := by
  unfold wrap64 Word; omega

theorem wrap64_add_right (a b : Int) : wrap64 (a + wrap64 b) = wrap64 (a + b) := by
  unfold wrap64 Word; omega

theorem wrap64_sub_left (a b : Int) : wrap64 (wrap64 a - b) = wrap64 (a - b) := by
  unfold wrap64 Word; omega

theorem wrap64_sub_right (a b : Int) : wrap64 (a - wrap64 b) = wrap64 (a - b) := by
  unfold wrap64 Word; omega


/-- Wrap a `Value`, leaving booleans unchanged. -/
def Value.wrap : Value → Value
  | .int n  => .int (wrap64 n)
  | .bool b => .bool b

@[simp] theorem Value.wrap_typeOf (v : Value) : v.wrap.typeOf = v.typeOf := by
  cases v <;> simp [Value.wrap, Value.typeOf]

-- ============================================================
-- § 2. Binary operators
-- ============================================================

inductive BinOp | add | sub | mul | div deriving Repr, DecidableEq

def BinOp.eval : BinOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- An operation is safe if it will not cause the program to get stuck.
    Only `div` can fault — when the divisor is zero. -/
def BinOp.safe : BinOp → Int → Int → Prop
  | .div, _, b => b ≠ 0
  | _, _, _    => True

instance {op : BinOp} {a b : Int} : Decidable (op.safe a b) := by
  unfold BinOp.safe; cases op <;> exact inferInstance

-- ============================================================
-- § 2a. Comparison operators
-- ============================================================

inductive CmpOp | eq | ne | lt | le deriving Repr, DecidableEq

def CmpOp.eval : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)

-- ============================================================
-- § 2b. Expressions over stores
-- ============================================================

/-- Expressions that can be evaluated in a store. Used to describe
    how transformed-program variables map to original-program values. -/
inductive Expr where
  | lit    : Int → Expr
  | blit   : Bool → Expr
  | var    : Var → Expr
  | bin    : BinOp → Expr → Expr → Expr
  -- Symbolic boolean expression constructors (for tracking boolop results)
  | tobool  : Expr → Expr                  -- .bool (e.eval σ).toBool
  | cmpE    : CmpOp → Expr → Expr → Expr  -- .bool (op.eval (a.eval σ).toInt (b.eval σ).toInt)
  | cmpLitE : CmpOp → Expr → Int → Expr   -- .bool (op.eval (a.eval σ).toInt n)
  | notE    : Expr → Expr                  -- .bool (!(e.eval σ).toBool)
  | andE    : Expr → Expr → Expr           -- .bool ((a.eval σ).toBool && (b.eval σ).toBool)
  | orE     : Expr → Expr → Expr           -- .bool ((a.eval σ).toBool || (b.eval σ).toBool)
  deriving Repr, DecidableEq

def Expr.eval (σ : Store) : Expr → Value
  | .lit n          => .int n
  | .blit b         => .bool b
  | .var x          => σ x
  | .bin op a b     => .int (wrap64 (op.eval (a.eval σ).toInt (b.eval σ).toInt))
  | .tobool e       => .bool (e.eval σ).toBool
  | .cmpE op a b    => .bool (op.eval (a.eval σ).toInt (b.eval σ).toInt)
  | .cmpLitE op a n => .bool (op.eval (a.eval σ).toInt n)
  | .notE e         => .bool (!(e.eval σ).toBool)
  | .andE a b       => .bool ((a.eval σ).toBool && (b.eval σ).toBool)
  | .orE a b        => .bool ((a.eval σ).toBool || (b.eval σ).toBool)

-- ============================================================
-- § 2c. Boolean expressions
-- ============================================================

/-- Boolean expressions for conditional branches. -/
inductive BoolExpr where
  | lit    : Bool → BoolExpr                   -- true / false literal
  | bvar   : Var → BoolExpr                    -- read a boolean variable
  | cmp    : CmpOp → Var → Var → BoolExpr     -- x op y (integer comparison)
  | cmpLit : CmpOp → Var → Int → BoolExpr     -- x op n (variable vs literal)
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

-- ============================================================
-- § 3. Syntax – Three-Address Code instructions
-- ============================================================

/--
TAC instructions.  A **program** is an `Array TAC`; the program counter
is a `Nat` index into that array.

```
x := v          -- assign constant (integer or boolean)
x := y          -- copy
x := y ⊕ z     -- binary operation  (⊕ ∈ {+, -, *, /})
x := bexpr      -- evaluate boolean expression and store result
goto l          -- unconditional jump
if cond goto l  -- conditional jump (branch if cond is true, else fall through)
halt            -- normal termination
```
-/
inductive TAC where
  | const  : Var → Value → TAC                 -- x := v
  | copy   : Var → Var → TAC                   -- x := y
  | binop  : Var → BinOp → Var → Var → TAC    -- x := y ⊕ z
  | boolop : Var → BoolExpr → TAC              -- x := bexpr
  | goto   : Label → TAC                       -- goto l
  | ifgoto : BoolExpr → Label → TAC            -- if cond then goto l
  | halt   : TAC
  deriving Repr, DecidableEq

/-- A program: TAC code together with its type context and observable variables. -/
structure Prog where
  code       : Array TAC
  tyCtx      : TyCtx
  observable : List Var

instance : Repr Prog where
  reprPrec p n := reprPrec p.code n

instance : GetElem Prog Nat TAC (fun p i => i < p.code.size) where
  getElem p i h := p.code[i]

def Prog.size (p : Prog) : Nat := p.code.size

@[simp] theorem Prog.getElem_eq (p : Prog) (i : Nat) (h : i < p.code.size) :
    p[i] = p.code[i] := rfl

@[simp] theorem Prog.size_eq (p : Prog) : p.size = p.code.size := rfl

theorem Prog.getElem?_eq_getElem {p : Prog} {i : Nat} (h : i < p.size) :
    p[i]? = some p[i] := by
  have hlt : i < p.code.size := h
  simp [getElem?, dif_pos hlt]

theorem Prog.getElem?_none {p : Prog} {i : Nat} (h : ¬ i < p.size) :
    p[i]? = none := by
  simp [getElem?, show ¬ i < p.code.size from h]

/-- Reduce `Prog` indexing to `Array` indexing. -/
@[simp] theorem Prog.getElem?_code (p : Prog) (i : Nat) : p[i]? = p.code[i]? := by
  by_cases h : i < p.code.size
  · rw [Prog.getElem?_eq_getElem h, Array.getElem?_eq_getElem h]; rfl
  · rw [Prog.getElem?_none h]
    simp [getElem?, h]

theorem Prog.getElem?_eq_some_iff {p : Prog} {i : Nat} {v : TAC} :
    p[i]? = some v ↔ ∃ h : i < p.size, p[i] = v := by
  constructor
  · intro hsome
    by_cases h : i < p.size
    · rw [Prog.getElem?_eq_getElem h] at hsome
      exact ⟨h, Option.some.inj hsome⟩
    · rw [Prog.getElem?_none h] at hsome; exact absurd hsome (by simp)
  · rintro ⟨h, rfl⟩; exact Prog.getElem?_eq_getElem h

/-- Construct a Prog from just an array of instructions (default empty type context and observables). -/
def Prog.ofCode (code : Array TAC) : Prog :=
  ⟨code, fun _ => .int, []⟩

-- ============================================================
-- § 3a. Type system definitions
-- ============================================================

/-- Well-typedness for boolean expressions. -/
inductive WellTypedBoolExpr (Γ : TyCtx) : BoolExpr → Prop where
  | lit    : WellTypedBoolExpr Γ (.lit b)
  | bvar   : Γ x = .bool → WellTypedBoolExpr Γ (.bvar x)
  | cmp    : Γ x = .int → Γ y = .int → WellTypedBoolExpr Γ (.cmp op x y)
  | cmpLit : Γ x = .int → n.toNat < 2 ^ 64 → WellTypedBoolExpr Γ (.cmpLit op x n)
  | not    : WellTypedBoolExpr Γ b → WellTypedBoolExpr Γ (.not b)

theorem WellTypedBoolExpr.cmpLit_range {Γ : TyCtx} {op x n}
    (h : WellTypedBoolExpr Γ (.cmpLit op x n)) : n.toNat < 2 ^ 64 := by
  cases h with | cmpLit _ h => exact h

/-- Well-typedness for a single TAC instruction. -/
inductive WellTypedInstr (Γ : TyCtx) : TAC → Prop where
  | const  : v.typeOf = Γ x → (∀ n, v = .int n → n.toNat < 2 ^ 64) → WellTypedInstr Γ (.const x v)
  | copy   : Γ x = Γ y → WellTypedInstr Γ (.copy x y)
  | binop  : Γ x = .int → Γ y = .int → Γ z = .int →
      WellTypedInstr Γ (.binop x op y z)
  | boolop : Γ x = .bool → WellTypedBoolExpr Γ be →
      WellTypedInstr Γ (.boolop x be)
  | goto   : WellTypedInstr Γ (.goto l)
  | ifgoto : WellTypedBoolExpr Γ b → WellTypedInstr Γ (.ifgoto b l)
  | halt   : WellTypedInstr Γ .halt

/-- A program is well-typed if every instruction is well-typed. -/
def WellTypedProg (Γ : TyCtx) (p : Prog) : Prop :=
  ∀ i, (h : i < p.size) → WellTypedInstr Γ p[i]

-- ============================================================
-- § 4. Machine configurations
-- ============================================================

/--
A **configuration** is either:
- `Cfg.run pc σ`       — about to execute instruction `pc` in store `σ`
- `Cfg.halt σ`         — terminated with final store `σ`
- `Cfg.error σ`        — runtime error (e.g. division by zero) with store `σ`
- `Cfg.typeError σ`    — type error (e.g. binop on non-integer operands)
-/
inductive Cfg where
  | run       : Nat → Store → Cfg
  | halt      : Store → Cfg
  | error     : Store → Cfg
  | typeError : Store → Cfg

-- ============================================================
-- § 5. Small-step operational semantics   ⟶
-- ============================================================

/--
`Step p c c'`  (written  `p ⊩ c ⟶ c'`)

One execution step of program `p`.  Each constructor reads the instruction
at the current program counter and produces the next configuration.

The `binop` constructor requires explicit integer extraction.  If the
operands are not both integers, `binop_typeError` fires instead.
-/
inductive Step (p : Prog) : Cfg → Cfg → Prop where

  | const  : p[pc]? = some (.const x v) →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ v]))

  | copy   : p[pc]? = some (.copy x y) →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ σ y]))

  | binop  {a b : Int} : p[pc]? = some (.binop x op y z) →
      σ y = .int a → σ z = .int b → op.safe a b →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ .int (wrap64 (op.eval a b))]))

  | boolop : p[pc]? = some (.boolop x be) →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ .bool (be.eval σ)]))

  | goto   : p[pc]? = some (.goto l) →
      Step p (.run pc σ) (.run l σ)

  | iftrue : p[pc]? = some (.ifgoto b l) → b.eval σ = true →
      Step p (.run pc σ) (.run l σ)

  | iffall : p[pc]? = some (.ifgoto b l) → b.eval σ = false →
      Step p (.run pc σ) (.run (pc + 1) σ)

  | halt   : p[pc]? = some .halt →
      Step p (.run pc σ) (.halt σ)

  | error  {a b : Int} : p[pc]? = some (.binop x op y z) →
      σ y = .int a → σ z = .int b → ¬ op.safe a b →
      Step p (.run pc σ) (.error σ)

  | binop_typeError : p[pc]? = some (.binop x op y z) →
      (σ y).typeOf ≠ .int ∨ (σ z).typeOf ≠ .int →
      Step p (.run pc σ) (.typeError σ)

-- p ⊩ c ⟶ c'   (⊩ avoids conflict with Lean's reserved ⊢)
notation:50 p " ⊩ " c " ⟶ " c' => Step p c c'

/-- Successor PCs of a TAC instruction (for bounds checking). -/
def TAC.successors (instr : TAC) (pc : Label) : List Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _ => [pc + 1]
  | .goto l        => [l]
  | .ifgoto _ l    => [l, pc + 1]
  | .halt          => []

/-- A step from `Cfg.run pc σ` to `Cfg.run pc' σ'` implies `pc'` is
    a successor of the instruction at `pc`. -/
theorem Step.mem_successors {p : Prog} {pc pc' : Nat} {σ σ' : Store}
    (hstep : p ⊩ Cfg.run pc σ ⟶ Cfg.run pc' σ') :
    ∃ instr, p[pc]? = some instr ∧ pc' ∈ instr.successors pc := by
  cases hstep with
  | const h        => exact ⟨_, h, by simp [TAC.successors]⟩
  | copy h         => exact ⟨_, h, by simp [TAC.successors]⟩
  | binop h _ _ _  => exact ⟨_, h, by simp [TAC.successors]⟩
  | boolop h       => exact ⟨_, h, by simp [TAC.successors]⟩
  | goto h         => exact ⟨_, h, by simp [TAC.successors]⟩
  | iftrue h _     => exact ⟨_, h, by simp [TAC.successors]⟩
  | iffall h _     => exact ⟨_, h, by simp [TAC.successors]⟩

/-- A step from an in-bounds PC to a run-config stays in-bounds.
    This is the Prop-level condition for totality. -/
def StepClosedInBounds (p : Prog) : Prop :=
  p.size > 0 ∧
  ∀ pc pc' : Nat, ∀ σ σ' : Store,
    pc < p.size → (p ⊩ Cfg.run pc σ ⟶ Cfg.run pc' σ') → pc' < p.size

/-- Decidable check: all successors of every in-bounds PC are in bounds. -/
def checkStepClosed (p : Prog) : Bool :=
  p.size > 0 &&
  (List.range p.size).all fun pc =>
    match p[pc]? with
    | some instr => (instr.successors pc).all (· < p.size)
    | none => true

/-- Soundness: `checkStepClosed` implies `StepClosedInBounds`. -/
theorem checkStepClosed_sound {p : Prog} (h : checkStepClosed p = true) :
    StepClosedInBounds p := by
  simp only [checkStepClosed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨hpos, hall⟩ := h
  constructor
  · exact hpos
  · intro pc pc' σ σ' hpc hstep
    obtain ⟨instr, hinstr, hmem⟩ := Step.mem_successors hstep
    have := hall pc hpc
    rw [hinstr] at this
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this pc' hmem

-- ============================================================
-- § 6. Multi-step closure   ⟶*
-- ============================================================

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (p : Prog) : Cfg → Cfg → Prop where
  | refl : Steps p c c
  | step : Step p c c' → Steps p c' c'' → Steps p c c''

-- p ⊩ c ⟶* c'
notation:50 p " ⊩ " c " ⟶* " c' => Steps p c c'

theorem Steps.single {p : Prog} {c c' : Cfg} (h : p ⊩ c ⟶ c') :
    p ⊩ c ⟶* c' :=
  .step h .refl

theorem Steps.trans {p : Prog} {c c' c'' : Cfg}
    (h₁ : p ⊩ c ⟶* c') (h₂ : p ⊩ c' ⟶* c'') : p ⊩ c ⟶* c'' := by
  induction h₁ with
  | refl        => exact h₂
  | step s _ ih => exact .step s (ih h₂)

-- ============================================================
-- § 7. Termination (big-step view)
-- ============================================================

/-- `p` started at `pc` with store `σ` haltsWithResult producing `σ'`. -/
def haltsWithResult (p : Prog) (pc : Nat) (σ σ' : Store) : Prop :=
  p ⊩ Cfg.run pc σ ⟶* Cfg.halt σ'

-- ============================================================
-- § 8. Metatheory
-- ============================================================

/-- The small-step relation is **deterministic**. -/
theorem Step.deterministic {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶ c₁) (h₂ : p ⊩ c ⟶ c₂) : c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> simp_all [Value.int.injEq, Value.typeOf] <;>
    (first | rfl | contradiction)

/-- A halted configuration admits no further steps. -/
theorem Step.no_step_from_halt {p : Prog} {σ : Store} {c : Cfg} :
    ¬ (p ⊩ Cfg.halt σ ⟶ c) :=
  fun h => by cases h

/-- An error configuration admits no further steps. -/
theorem Step.no_step_from_error {p : Prog} {σ : Store} {c : Cfg} :
    ¬ (p ⊩ Cfg.error σ ⟶ c) :=
  fun h => by cases h

/-- A type-error configuration admits no further steps. -/
theorem Step.no_step_from_typeError {p : Prog} {σ : Store} {c : Cfg} :
    ¬ (p ⊩ Cfg.typeError σ ⟶ c) :=
  fun h => by cases h

/-- Determinism of ⟶*: two sequences from the same config that both reach
    a stuck configuration must reach the same one. -/
private theorem steps_det {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶* c₁) (h₂ : p ⊩ c ⟶* c₂)
    (hn₁ : ∀ d, ¬ p ⊩ c₁ ⟶ d) (hn₂ : ∀ d, ¬ p ⊩ c₂ ⟶ d) : c₁ = c₂ := by
  induction h₁ generalizing c₂ with
  | refl =>
    cases h₂ with
    | refl   => rfl
    | step s _ => exact absurd s (hn₁ _)
  | step s rest ih =>
    cases h₂ with
    | refl    => exact absurd s (hn₂ _)
    | step s' rest' =>
      have heq := Step.deterministic s s'
      subst heq; exact ih rest' hn₁ hn₂

/-- Termination produces a **unique** final store. -/
theorem haltsWithResult_unique {p : Prog} {pc : Nat} {σ σ₁ σ₂ : Store}
    (h₁ : haltsWithResult p pc σ σ₁) (h₂ : haltsWithResult p pc σ σ₂) : σ₁ = σ₂ := by
  simp only [haltsWithResult] at h₁ h₂
  have stuck : ∀ τ d, ¬ (p ⊩ Cfg.halt τ ⟶ d) := fun _ _ h => by cases h
  have := steps_det h₁ h₂ (stuck σ₁) (stuck σ₂)
  exact Cfg.halt.inj this

/-- If two stores agree on all variables, any step from one can be
    matched by a step from the other. -/
theorem Step.store_congr {p : Prog} {pc : Nat} {σ τ : Store} {c : Cfg}
    (hσ : p ⊩ Cfg.run pc σ ⟶ c)
    (hagree : ∀ y, σ y = τ y) :
    ∃ c', p ⊩ Cfg.run pc τ ⟶ c' := by
  cases hσ with
  | const  h => exact ⟨_, .const h⟩
  | copy   h => exact ⟨_, .copy h⟩
  | binop h hy hz hs =>
    refine ⟨_, .binop h ?_ ?_ hs⟩
    · rw [← hagree]; exact hy
    · rw [← hagree]; exact hz
  | boolop h => exact ⟨_, .boolop h⟩
  | goto   h => exact ⟨_, .goto h⟩
  | iftrue h hne => exact ⟨_, .iftrue h (BoolExpr.eval_congr _ σ τ hagree ▸ hne)⟩
  | iffall h heq => exact ⟨_, .iffall h (BoolExpr.eval_congr _ σ τ hagree ▸ heq)⟩
  | halt   h => exact ⟨_, .halt h⟩
  | error h hy hz hs =>
    refine ⟨_, .error h ?_ ?_ hs⟩
    · rw [← hagree]; exact hy
    · rw [← hagree]; exact hz
  | binop_typeError h hne =>
    refine ⟨_, .binop_typeError h ?_⟩
    cases hne with
    | inl hl => left; simp [Value.typeOf] at hl ⊢; rwa [← hagree]
    | inr hr => right; simp [Value.typeOf] at hr ⊢; rwa [← hagree]

-- ============================================================
-- § 9. Progress and successor lemmas
-- ============================================================

/-- Helper: extract instruction identity from array lookup. -/
private theorem instr_eq_of_lookup {p : Prog} {pc : Nat} {instr : TAC}
    (hpc : pc < p.size) (h : p[pc]? = some instr) : p[pc] = instr :=
  Option.some.inj ((Prog.getElem?_eq_getElem hpc).symm.trans h)

/-- **Progress**: if the instruction at `pc` exists, the program is
    well-typed, and the store is well-typed, then a step is always possible.
    Unsafe division produces a `Cfg.error` transition rather than getting stuck. -/
theorem Step.progress (p : Prog) (pc : Nat) (σ : Store) (Γ : TyCtx)
    (hinb : pc < p.size)
    (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ) :
    ∃ c', Step p (Cfg.run pc σ) c' := by
  have hinstr : p[pc]? = some p[pc] := Prog.getElem?_eq_getElem hinb
  have hwti := hwtp pc hinb
  match hp : p[pc] with
  | .const x v     => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y      => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z =>
    rw [hp] at hwti; cases hwti with
    | binop _ hy hz =>
      obtain ⟨a, ha⟩ : ∃ n, σ y = .int n := Value.int_of_typeOf_int (by rw [hts y]; exact hy)
      obtain ⟨b, hb⟩ : ∃ n, σ z = .int n := Value.int_of_typeOf_int (by rw [hts z]; exact hz)
      by_cases hs : op.safe a b
      · exact ⟨_, .binop (hp ▸ hinstr) ha hb hs⟩
      · exact ⟨_, .error (hp ▸ hinstr) ha hb hs⟩
  | .boolop x be   => exact ⟨_, .boolop (hp ▸ hinstr)⟩
  | .goto l        => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l    =>
    by_cases hb : b.eval σ = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt          => exact ⟨_, .halt (hp ▸ hinstr)⟩

/-- **Type safety (single step)**: a well-typed program with a well-typed store
    never steps to a type-error configuration. -/
theorem Step.no_typeError_of_wellTyped {p : Prog} {pc : Nat} {σ τ : Store} {Γ : TyCtx}
    (hpc : pc < p.size) (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ) :
    ¬ (p ⊩ Cfg.run pc σ ⟶ Cfg.typeError τ) := by
  intro hstep
  cases hstep with
  | binop_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | binop _ hy hz =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hy)
      | inr hr => exact hr (by rw [hts]; exact hz)

/-- **Progress (untyped)**: an in-bounds PC always admits a step,
    regardless of type safety. For ill-typed binop operands, the step
    is `binop_typeError`. -/
theorem Step.progress_untyped (p : Prog) (pc : Nat) (σ : Store)
    (hinb : pc < p.size) :
    ∃ c', Step p (Cfg.run pc σ) c' := by
  have hinstr : p[pc]? = some p[pc] := Prog.getElem?_eq_getElem hinb
  match hp : p[pc] with
  | .const x v     => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y      => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z =>
    by_cases hy : (σ y).typeOf = .int
    · by_cases hz : (σ z).typeOf = .int
      · obtain ⟨a, ha⟩ := Value.int_of_typeOf_int hy
        obtain ⟨b, hb⟩ := Value.int_of_typeOf_int hz
        by_cases hs : op.safe a b
        · exact ⟨_, .binop (hp ▸ hinstr) ha hb hs⟩
        · exact ⟨_, .error (hp ▸ hinstr) ha hb hs⟩
      · exact ⟨_, .binop_typeError (hp ▸ hinstr) (.inr hz)⟩
    · exact ⟨_, .binop_typeError (hp ▸ hinstr) (.inl hy)⟩
  | .boolop x be   => exact ⟨_, .boolop (hp ▸ hinstr)⟩
  | .goto l        => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l    =>
    by_cases hb : b.eval σ = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt          => exact ⟨_, .halt (hp ▸ hinstr)⟩

-- ============================================================
-- § 10. Observable output at a configuration
-- ============================================================

/-- An observation at a configuration: either the program halted (with
    observable variable–value pairs), an error occurred (e.g. div-by-zero),
    or nothing observable happened yet. -/
inductive Observation where
  | halt      : List (Var × Value) → Observation
  | error     : Observation
  | typeError : Observation
  | nothing   : Observation
  deriving Repr, DecidableEq

/-- Observe a configuration against a program and list of observable variables. -/
def observe (p : Prog) (obs : List Var) (c : Cfg) : Observation :=
  match c with
  | .halt σ      => Observation.halt (obs.map fun v => (v, σ v))
  | .error _     => Observation.error
  | .typeError _ => Observation.typeError
  | .run pc σ =>
    match p[pc]? with
    | some .halt => Observation.halt (obs.map fun v => (v, σ v))
    | some _     => Observation.nothing
    | none       => Observation.error

-- ============================================================
-- § 11. Decidable type checking
-- ============================================================

def checkWellTypedBoolExpr (Γ : TyCtx) : BoolExpr → Bool
  | .lit _        => true
  | .bvar x       => decide (Γ x = .bool)
  | .cmp _ x y    => decide (Γ x = .int) && decide (Γ y = .int)
  | .cmpLit _ x n => decide (Γ x = .int) && decide (n.toNat < (2 ^ 64 : Nat))
  | .not e        => checkWellTypedBoolExpr Γ e

def checkWellTypedInstr (Γ : TyCtx) : TAC → Bool
  | .const x v     => decide (v.typeOf = Γ x) && match v with
    | .int n => decide (n.toNat < (2 ^ 64 : Nat))
    | .bool _ => true
  | .copy x y      => decide (Γ x = Γ y)
  | .binop x _ y z => decide (Γ x = .int) && decide (Γ y = .int) && decide (Γ z = .int)
  | .boolop x be   => decide (Γ x = .bool) && checkWellTypedBoolExpr Γ be
  | .goto _        => true
  | .ifgoto b _    => checkWellTypedBoolExpr Γ b
  | .halt          => true

theorem checkWellTypedBoolExpr_sound {Γ : TyCtx} {b : BoolExpr}
    (h : checkWellTypedBoolExpr Γ b = true) : WellTypedBoolExpr Γ b := by
  induction b with
  | lit _ => exact .lit
  | bvar x =>
    simp [checkWellTypedBoolExpr, decide_eq_true_eq] at h
    exact .bvar h
  | cmp op x y =>
    simp [checkWellTypedBoolExpr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cmp h.1 h.2
  | cmpLit op x n =>
    simp only [checkWellTypedBoolExpr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cmpLit h.1 h.2
  | not e ih =>
    simp [checkWellTypedBoolExpr] at h; exact .not (ih h)

theorem checkWellTypedInstr_sound {Γ : TyCtx} {instr : TAC}
    (h : checkWellTypedInstr Γ instr = true) : WellTypedInstr Γ instr := by
  cases instr with
  | const x v =>
    cases v with
    | int n =>
      simp only [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .const h.1 (fun m hm => by cases hm; exact h.2)
    | bool b =>
      simp only [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .const h.1 (fun _ hm => by cases hm)
  | copy x y =>
    simp [checkWellTypedInstr, decide_eq_true_eq] at h; exact .copy h
  | binop x op y z =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .binop h.1.1 h.1.2 h.2
  | boolop x be =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .boolop h.1 (checkWellTypedBoolExpr_sound h.2)
  | goto l => exact .goto
  | ifgoto b l =>
    simp [checkWellTypedInstr] at h
    exact .ifgoto (checkWellTypedBoolExpr_sound h)
  | halt => exact .halt

/-- Check that every instruction in a program is well-typed. -/
def checkWellTypedProg (Γ : TyCtx) (p : Prog) : Bool :=
  (List.range p.size).all fun i =>
    match p[i]? with
    | some instr => checkWellTypedInstr Γ instr
    | none => true

theorem checkWellTypedProg_sound {Γ : TyCtx} {p : Prog}
    (h : checkWellTypedProg Γ p = true) : WellTypedProg Γ p := by
  intro i hi
  have hmem : i ∈ List.range p.size := List.mem_range.mpr hi
  have hcheck := (List.all_eq_true.mp h) i hmem
  have hsome : p[i]? = some p[i] := Prog.getElem?_eq_getElem hi
  rw [hsome] at hcheck
  exact checkWellTypedInstr_sound hcheck

-- ============================================================
-- § 11a. Type preservation
-- ============================================================

/-- **Type preservation**: a well-typed program with a well-typed store
    preserves the typed-store invariant after any step to a run config. -/
theorem type_preservation {Γ : TyCtx} {p : Prog} {pc pc' : Nat} {σ σ' : Store}
    (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ)
    (hpc : pc < p.size)
    (hstep : p ⊩ Cfg.run pc σ ⟶ Cfg.run pc' σ') :
    TypedStore Γ σ' := by
  have hwti := hwtp pc hpc
  cases hstep with
  | const h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .const hv _ => exact TypedStore.update_typed hts hv
  | copy h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .copy hxy => exact TypedStore.update_typed hts (by rw [hts]; exact hxy.symm)
  | binop h _ _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .binop hx _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | boolop h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .boolop hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | goto _ => exact hts
  | iftrue _ _ => exact hts
  | iffall _ _ => exact hts


/-- **Type safety (multi-step)**: a well-typed, step-closed program never
    reaches a type-error configuration from a well-typed initial store. -/
theorem type_safety {p : Prog} {σ₀ σ' : Store} {Γ : TyCtx}
    (hwtp : WellTypedProg Γ p) (hts₀ : TypedStore Γ σ₀)
    (hclosed : StepClosedInBounds p) :
    ¬ (p ⊩ Cfg.run 0 σ₀ ⟶* Cfg.typeError σ') := by
  intro hsteps
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ, c = Cfg.run pc σ → c' = Cfg.typeError σ' →
      pc < p.size → TypedStore Γ σ → False from
    this _ _ hsteps 0 σ₀ rfl rfl hclosed.1 hts₀
  intro c c' hss
  induction hss with
  | refl => intro _ _ hc hc' _ _; rw [hc] at hc'; exact Cfg.noConfusion hc'
  | step hstep rest ih =>
    intro pc σ hc hc' hpc hts; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_halt s
    | error h _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_error s
    | binop_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped hpc hwtp hts
                  (.binop_typeError hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | const h =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.const h)
      · exact type_preservation hwtp hts hpc (Step.const h)
    | copy h =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.copy h)
      · exact type_preservation hwtp hts hpc (Step.copy h)
    | binop h hy hz hs =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.binop h hy hz hs)
      · exact type_preservation hwtp hts hpc (Step.binop h hy hz hs)
    | boolop h =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.boolop h)
      · exact type_preservation hwtp hts hpc (Step.boolop h)
    | goto h =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.goto h)
      · exact type_preservation hwtp hts hpc (Step.goto h)
    | iftrue h hne =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.iftrue h hne)
      · exact type_preservation hwtp hts hpc (Step.iftrue h hne)
    | iffall h heq =>
      apply ih _ _ rfl hc'
      · exact hclosed.2 pc _ σ _ hpc (Step.iffall h heq)
      · exact type_preservation hwtp hts hpc (Step.iffall h heq)

-- ============================================================
-- § 12. Example program:  acc := 1 + 2 + … + n
-- ============================================================
--
--  Variables:  "n"   – loop counter (counts down to 0)
--              "acc" – accumulator
--              "one" – constant 1 stored in a register
--
--  0:  if n != 0 goto 2  -- branch if n ≠ 0
--  1:  halt               -- n = 0  ⟹  acc = Σ 1..N
--  2:  acc := acc + n     -- accumulate current n
--  3:  n   := n - one     -- decrement
--  4:  goto 0             -- loop back

def sumProg : Prog := .ofCode #[
  TAC.ifgoto (.cmpLit .ne "n" 0) 2,       -- 0
  TAC.halt,                               -- 1
  TAC.binop  "acc" .add "acc" "n",        -- 2
  TAC.binop  "n"   .sub "n"   "one",      -- 3
  TAC.goto   0                            -- 4
]

def sumStore (n : Int) : Store :=
  Store.init |>.update "n"   (.int n)
             |>.update "acc" (.int 0)
             |>.update "one" (.int 1)

-- ▸ One step from pc=0 with n=3: the conditional is taken, jump to pc=2.
example : sumProg ⊩ Cfg.run 0 (sumStore 3) ⟶ Cfg.run 2 (sumStore 3) :=
  .iftrue rfl (by native_decide)

-- ▸ Step from pc=2: acc := acc + n fires; the updated store exists.
example : ∃ σ', sumProg ⊩ Cfg.run 2 (sumStore 3) ⟶ Cfg.run 3 σ' :=
  ⟨_, .binop rfl rfl rfl trivial⟩
