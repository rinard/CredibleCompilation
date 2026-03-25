/-!
# Operational Semantics for Three-Address Code

Following Winskel, "The Formal Semantics of Programming Languages."

We define a simple imperative language in three-address code (TAC) form,
with scalar (integer) variables, and give it a small-step structural
operational semantics.  Big-step termination and basic metatheory follow.

Note: Lean reserves `⊢`, so we use `⊩` as the program-turnstile.
-/

-- ============================================================
-- § 1. Basic domains
-- ============================================================

abbrev Var   := String
abbrev Val   := Int
abbrev Label := Nat        -- program counter / jump target

/-- A store (state) maps every variable to an integer value. -/
def Store := Var → Val

namespace Store

def init : Store := fun _ => 0

/-- Functional update  σ[x ↦ v] -/
def update (σ : Store) (x : Var) (v : Val) : Store :=
  fun y => if y == x then v else σ y

theorem update_self (σ : Store) (x : Var) (v : Val) :
    σ.update x v x = v := by simp [update]

theorem update_other (σ : Store) (x y : Var) (v : Val) (h : y ≠ x) :
    σ.update x v y = σ y := by simp only [update, beq_iff_eq, if_neg h]

theorem update_shadow (σ : Store) (x : Var) (u v : Val) :
    (σ.update x u).update x v = σ.update x v := by
  funext y; simp [update]; split <;> simp_all

theorem update_comm (σ : Store) (x y : Var) (u v : Val) (h : x ≠ y) :
    (σ.update x u).update y v = (σ.update y v).update x u := by
  funext z; simp [update]; split <;> split <;> simp_all [Ne.symm]

end Store

-- Notation  σ[x ↦ v]
notation:max σ "[" x " ↦ " v "]" => Store.update σ x v

-- ============================================================
-- § 2. Binary operators
-- ============================================================

inductive BinOp | add | sub | mul deriving Repr, DecidableEq

def BinOp.eval : BinOp → Val → Val → Val
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

-- ============================================================
-- § 2b. Comparison operators and boolean expressions
-- ============================================================

inductive CmpOp | eq | ne | lt | le deriving Repr, DecidableEq

def CmpOp.eval : CmpOp → Val → Val → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)

/-- Boolean expressions for conditional branches. -/
inductive BoolExpr where
  | var : Var → BoolExpr                    -- x ≠ 0 (backward compatible)
  | cmp : CmpOp → Var → Var → BoolExpr     -- x op y
  | not : BoolExpr → BoolExpr
  | and : BoolExpr → BoolExpr → BoolExpr
  | or  : BoolExpr → BoolExpr → BoolExpr
  deriving Repr, DecidableEq

def BoolExpr.eval (σ : Store) : BoolExpr → Bool
  | .var x     => σ x != 0
  | .cmp op x y => op.eval (σ x) (σ y)
  | .not e     => !e.eval σ
  | .and a b   => a.eval σ && b.eval σ
  | .or a b    => a.eval σ || b.eval σ

theorem BoolExpr.eval_congr (cond : BoolExpr) (σ τ : Store)
    (hagree : ∀ y, σ y = τ y) : cond.eval σ = cond.eval τ := by
  induction cond with
  | var x => simp [BoolExpr.eval, hagree]
  | cmp op x y => simp [BoolExpr.eval, hagree]
  | not e ih => simp [BoolExpr.eval, ih]
  | and a b iha ihb => simp [BoolExpr.eval, iha, ihb]
  | or a b iha ihb => simp [BoolExpr.eval, iha, ihb]

/-- Collect all variable names from a boolean expression. -/
def BoolExpr.vars : BoolExpr → List Var
  | .var x     => [x]
  | .cmp _ x y => [x, y]
  | .not e     => e.vars
  | .and a b   => a.vars ++ b.vars
  | .or a b    => a.vars ++ b.vars

/-- Extract the single variable from a `BoolExpr.var`, if applicable. -/
def BoolExpr.asVar : BoolExpr → Option Var
  | .var x => some x
  | _      => none

theorem BoolExpr.asVar_eq {b : BoolExpr} {x : Var} (h : b.asVar = some x) :
    b = .var x := by
  cases b with
  | var v => simp [asVar] at h; subst h; rfl
  | _ => simp [asVar] at h

theorem BoolExpr.var_eval_true {σ : Store} {x : Var}
    (h : BoolExpr.eval σ (.var x) = true) : σ x ≠ 0 := by
  intro heq; simp [BoolExpr.eval, heq] at h

theorem BoolExpr.var_eval_false {σ : Store} {x : Var}
    (h : BoolExpr.eval σ (.var x) = false) : σ x = 0 := by
  simp only [BoolExpr.eval] at h
  -- h : (σ x != 0) = false, i.e. !(σ x == 0) = false
  have h2 : (σ x == 0) = true := by
    cases hb : (σ x == 0) <;> simp_all [bne]
  exact beq_iff_eq.mp h2

-- ============================================================
-- § 3. Syntax – Three-Address Code instructions
-- ============================================================

/--
TAC instructions.  A **program** is an `Array TAC`; the program counter
is a `Nat` index into that array.

```
x := n          -- assign constant
x := y          -- copy
x := y ⊕ z     -- binary operation  (⊕ ∈ {+, -, *})
goto l          -- unconditional jump
if cond goto l  -- conditional jump (branch if cond is true, else fall through)
halt            -- normal termination
```
-/
inductive TAC where
  | const  : Var → Val → TAC                  -- x := n
  | copy   : Var → Var → TAC                  -- x := y
  | binop  : Var → BinOp → Var → Var → TAC   -- x := y ⊕ z
  | goto   : Label → TAC                      -- goto l
  | ifgoto : BoolExpr → Label → TAC           -- if cond then goto l
  | halt   : TAC
  deriving Repr, DecidableEq

abbrev Prog := Array TAC

-- ============================================================
-- § 4. Machine configurations
-- ============================================================

/--
A **configuration** is either:
- `Cfg.run pc σ`  — about to execute instruction `pc` in store `σ`
- `Cfg.halt σ`    — terminated with final store `σ`
-/
inductive Cfg where
  | run  : Nat → Store → Cfg
  | halt : Store → Cfg

-- ============================================================
-- § 5. Small-step operational semantics   ⟶
-- ============================================================

/--
`Step p c c'`  (written  `p ⊩ c ⟶ c'`)

One execution step of program `p`.  Each constructor reads the instruction
at the current program counter and produces the next configuration.
-/
inductive Step (p : Prog) : Cfg → Cfg → Prop where

  | const  : p[pc]? = some (.const x n) →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ n]))

  | copy   : p[pc]? = some (.copy x y) →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ σ y]))

  | binop  : p[pc]? = some (.binop x op y z) →
      Step p (.run pc σ) (.run (pc + 1) (σ[x ↦ op.eval (σ y) (σ z)]))

  | goto   : p[pc]? = some (.goto l) →
      Step p (.run pc σ) (.run l σ)

  | iftrue : p[pc]? = some (.ifgoto b l) → b.eval σ = true →
      Step p (.run pc σ) (.run l σ)

  | iffall : p[pc]? = some (.ifgoto b l) → b.eval σ = false →
      Step p (.run pc σ) (.run (pc + 1) σ)

  | halt   : p[pc]? = some .halt →
      Step p (.run pc σ) (.halt σ)

-- p ⊩ c ⟶ c'   (⊩ avoids conflict with Lean's reserved ⊢)
notation:50 p " ⊩ " c " ⟶ " c' => Step p c c'

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
  cases h₁ <;> cases h₂ <;> simp_all

/-- A halted configuration admits no further steps. -/
theorem Step.no_step_from_halt {p : Prog} {σ : Store} {c : Cfg} :
    ¬ (p ⊩ Cfg.halt σ ⟶ c) :=
  fun h => by cases h

/-- Determinism of ⟶*: two sequences from the same config that both reach
    a stuck configuration must reach the same one. -/
private theorem steps_det {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶* c₁) (h₂ : p ⊩ c ⟶* c₂)
    (hn₁ : ∀ d, ¬ p ⊩ c₁ ⟶ d) (hn₂ : ∀ d, ¬ p ⊩ c₂ ⟶ d) : c₁ = c₂ := by
  -- Both endpoints are free variables, so induction is valid.
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
  | binop  h => exact ⟨_, .binop h⟩
  | goto   h => exact ⟨_, .goto h⟩
  | iftrue h hne => exact ⟨_, .iftrue h (BoolExpr.eval_congr _ σ τ hagree ▸ hne)⟩
  | iffall h heq => exact ⟨_, .iffall h (BoolExpr.eval_congr _ σ τ hagree ▸ heq)⟩
  | halt   h => exact ⟨_, .halt h⟩

-- ============================================================
-- § 9. Progress and successor lemmas
-- ============================================================

/-- **Progress**: if the instruction at `pc` exists, a step is always possible.
    This means the only way to get stuck is if `pc` is out of bounds. -/
theorem Step.progress (p : Prog) (pc : Nat) (σ : Store)
    (hinb : pc < p.size) :
    ∃ c', Step p (Cfg.run pc σ) c' := by
  have hinstr : p[pc]? = some p[pc] := Array.getElem?_eq_getElem hinb
  match hp : p[pc] with
  | .const x n      => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y       => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z => exact ⟨_, .binop (hp ▸ hinstr)⟩
  | .goto l         => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l     =>
    by_cases hb : b.eval σ = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt           => exact ⟨_, .halt (hp ▸ hinstr)⟩

-- ============================================================
-- § 10. Example program:  acc := 1 + 2 + … + n
-- ============================================================
--
--  Variables:  "n"   – loop counter (counts down to 0)
--              "acc" – accumulator
--              "one" – constant 1 stored in a register
--
--  0:  if n goto 2        -- branch if n ≠ 0
--  1:  halt               -- n = 0  ⟹  acc = Σ 1..N
--  2:  acc := acc + n     -- accumulate current n
--  3:  n   := n - one     -- decrement
--  4:  goto 0             -- loop back

def sumProg : Prog := #[
  .ifgoto (.var "n") 2,                -- 0
  .halt,                               -- 1
  .binop  "acc" .add "acc" "n",        -- 2
  .binop  "n"   .sub "n"   "one",      -- 3
  .goto   0                            -- 4
]

def sumStore (n : Val) : Store :=
  Store.init |>.update "n"   n
             |>.update "acc" 0
             |>.update "one" 1

-- ▸ One step from pc=0 with n=3: the conditional is taken, jump to pc=2.
example : sumProg ⊩ Cfg.run 0 (sumStore 3) ⟶ Cfg.run 2 (sumStore 3) :=
  .iftrue rfl (by simp [BoolExpr.eval, sumStore, Store.update])

-- ▸ Step from pc=2: acc := acc + n fires; the updated store exists.
example : ∃ σ', sumProg ⊩ Cfg.run 2 (sumStore 3) ⟶ Cfg.run 3 σ' :=
  ⟨_, .binop rfl⟩
