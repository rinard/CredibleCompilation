import CredibleCompilation.Core

/-!
# Three-Address Code: Syntax, Semantics, and Metatheory

TAC instructions, programs, configurations, small-step operational semantics,
multi-step closure, haltsWithResult, determinism, and observable output.

Split from `Semantics.lean`.
-/

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
x := arr[idx]   -- array load
arr[idx] := val  -- array store
```
-/
inductive TAC where
  | const    : Var → Value → TAC                 -- x := v
  | copy     : Var → Var → TAC                   -- x := y
  | binop    : Var → BinOp → Var → Var → TAC    -- x := y ⊕ z
  | boolop   : Var → BoolExpr → TAC              -- x := bexpr
  | goto     : Label → TAC                       -- goto l
  | ifgoto   : BoolExpr → Label → TAC            -- if cond then goto l
  | halt     : TAC
  | arrLoad  : Var → ArrayName → Var → VarTy → TAC       -- x := arr[idx] (ty = element type)
  | arrStore : ArrayName → Var → Var → VarTy → TAC       -- arr[idx] := val (ty = element type)
  deriving Repr, DecidableEq

/-- A scalar instruction is one that does not touch ArrayMem. -/
def TAC.isScalar : TAC → Bool
  | .const .. | .copy .. | .binop .. | .boolop .. | .goto .. | .ifgoto .. | .halt => true
  | .arrLoad .. | .arrStore .. => false

/-- A program: TAC code together with its type context and observable variables. -/
structure Prog where
  code       : Array TAC
  tyCtx      : TyCtx
  observable : List Var
  arrayDecls : List (ArrayName × Nat × VarTy) := []

instance : Repr Prog where
  reprPrec p n := reprPrec p.code n

instance : GetElem Prog Nat TAC (fun p i => i < p.code.size) where
  getElem p i h := p.code[i]

def Prog.size (p : Prog) : Nat := p.code.size

/-- Look up the declared size of an array in this program. -/
nonrec def Prog.arraySize (p : Prog) (arr : ArrayName) : Nat :=
  arraySize p.arrayDecls arr

/-- Array size as `BitVec 64` for direct comparison with bitvec indices. -/
nonrec def Prog.arraySizeBv (p : Prog) (arr : ArrayName) : BitVec 64 :=
  arraySizeBv p.arrayDecls arr

/-- Look up the declared element type of an array in this program. -/
nonrec def Prog.arrayElemTy (p : Prog) (arr : ArrayName) : VarTy :=
  arrayElemTy p.arrayDecls arr

/-- A program has no array instructions. -/
def NoArrayInstrs (p : Prog) : Prop :=
  ∀ (i : Nat) (hi : i < p.code.size), p.code[i].isScalar = true

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

theorem NoArrayInstrs.isScalar_of_getElem? {p : Prog} {pc : Nat} {instr : TAC}
    (hNoArr : NoArrayInstrs p) (h : p[pc]? = some instr) : instr.isScalar = true := by
  have hpc : pc < p.size := by
    rw [getElem?_eq_some_iff] at h; exact h.1
  have heq : p[pc] = instr :=
    Option.some.inj ((Prog.getElem?_eq_getElem hpc).symm.trans h)
  show instr.isScalar = true
  rw [← heq, Prog.getElem_eq]; exact hNoArr pc hpc

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
  ⟨code, fun _ => .int, [], []⟩

-- ============================================================
-- § 4. Machine configurations
-- ============================================================

/--
A **configuration** is either:
- `Cfg.run pc σ am`    — about to execute instruction `pc` in store `σ` with array memory `am`
- `Cfg.halt σ am`      — terminated with final store `σ` and array memory `am`
- `Cfg.error σ am`     — runtime error (e.g. division by zero) with store `σ`
- `Cfg.typeError σ am` — type error (e.g. binop on non-integer operands)
-/
inductive Cfg where
  | run       : Nat → Store → ArrayMem → Cfg
  | halt      : Store → ArrayMem → Cfg
  | error     : Store → ArrayMem → Cfg
  | typeError : Store → ArrayMem → Cfg

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
      Step p (.run pc σ am) (.run (pc + 1) (σ[x ↦ v]) am)

  | copy   : p[pc]? = some (.copy x y) →
      Step p (.run pc σ am) (.run (pc + 1) (σ[x ↦ σ y]) am)

  | binop  {a b : BitVec 64} : p[pc]? = some (.binop x op y z) →
      σ y = .int a → σ z = .int b → op.safe a b →
      Step p (.run pc σ am) (.run (pc + 1) (σ[x ↦ .int (op.eval a b)]) am)

  | boolop : p[pc]? = some (.boolop x be) →
      Step p (.run pc σ am) (.run (pc + 1) (σ[x ↦ .bool (be.eval σ)]) am)

  | goto   : p[pc]? = some (.goto l) →
      Step p (.run pc σ am) (.run l σ am)

  | iftrue : p[pc]? = some (.ifgoto b l) → b.eval σ = true →
      Step p (.run pc σ am) (.run l σ am)

  | iffall : p[pc]? = some (.ifgoto b l) → b.eval σ = false →
      Step p (.run pc σ am) (.run (pc + 1) σ am)

  | halt   : p[pc]? = some .halt →
      Step p (.run pc σ am) (.halt σ am)

  | error  {a b : BitVec 64} : p[pc]? = some (.binop x op y z) →
      σ y = .int a → σ z = .int b → ¬ op.safe a b →
      Step p (.run pc σ am) (.error σ am)

  | binop_typeError : p[pc]? = some (.binop x op y z) →
      (σ y).typeOf ≠ .int ∨ (σ z).typeOf ≠ .int →
      Step p (.run pc σ am) (.typeError σ am)

  | arrLoad : p[pc]? = some (.arrLoad x arr idx ty) →
      σ idx = .int idxVal → idxVal < p.arraySizeBv arr →
      Step p (.run pc σ am) (.run (pc + 1) (σ[x ↦ Value.ofBitVec ty (am.read arr idxVal)]) am)

  | arrStore : p[pc]? = some (.arrStore arr idx val ty) →
      σ idx = .int idxVal → (σ val).typeOf = ty → idxVal < p.arraySizeBv arr →
      Step p (.run pc σ am) (.run (pc + 1) σ (am.write arr idxVal (σ val).toBits))

  | arrLoad_boundsError : p[pc]? = some (.arrLoad x arr idx ty) →
      σ idx = .int idxVal → ¬ (idxVal < p.arraySizeBv arr) →
      Step p (.run pc σ am) (.error σ am)

  | arrStore_boundsError : p[pc]? = some (.arrStore arr idx val ty) →
      σ idx = .int idxVal → (σ val).typeOf = ty → ¬ (idxVal < p.arraySizeBv arr) →
      Step p (.run pc σ am) (.error σ am)

  | arrLoad_typeError : p[pc]? = some (.arrLoad x arr idx ty) →
      (σ idx).typeOf ≠ .int →
      Step p (.run pc σ am) (.typeError σ am)

  | arrStore_typeError : p[pc]? = some (.arrStore arr idx val ty) →
      (σ idx).typeOf ≠ .int ∨ (σ val).typeOf ≠ ty →
      Step p (.run pc σ am) (.typeError σ am)


-- p ⊩ c ⟶ c'   (⊩ avoids conflict with Lean's reserved ⊢)
notation:50 p " ⊩ " c " ⟶ " c' => Step p c c'

/-- Successor PCs of a TAC instruction (for bounds checking). -/
def TAC.successors (instr : TAC) (pc : Label) : List Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _ => [pc + 1]
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _ => [pc + 1]
  | .goto l        => [l]
  | .ifgoto _ l    => [l, pc + 1]
  | .halt          => []

/-- A step from `Cfg.run pc σ am` to `Cfg.run pc' σ' am'` implies `pc'` is
    a successor of the instruction at `pc`. -/
theorem Step.mem_successors {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hstep : p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am') :
    ∃ instr, p[pc]? = some instr ∧ pc' ∈ instr.successors pc := by
  cases hstep with
  | const h        => exact ⟨_, h, by simp [TAC.successors]⟩
  | copy h         => exact ⟨_, h, by simp [TAC.successors]⟩
  | binop h _ _ _  => exact ⟨_, h, by simp [TAC.successors]⟩
  | boolop h       => exact ⟨_, h, by simp [TAC.successors]⟩
  | goto h         => exact ⟨_, h, by simp [TAC.successors]⟩
  | iftrue h _     => exact ⟨_, h, by simp [TAC.successors]⟩
  | iffall h _     => exact ⟨_, h, by simp [TAC.successors]⟩
  | arrLoad h _ _    => exact ⟨_, h, by simp [TAC.successors]⟩
  | arrStore h _ _ _ => exact ⟨_, h, by simp [TAC.successors]⟩

/-- A step from an in-bounds PC to a run-config stays in-bounds.
    This is the Prop-level condition for totality. -/
def StepClosedInBounds (p : Prog) : Prop :=
  p.size > 0 ∧
  ∀ pc pc' : Nat, ∀ σ σ' : Store, ∀ am am' : ArrayMem,
    pc < p.size → (p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am') → pc' < p.size

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
  · intro pc pc' σ σ' am am' hpc hstep
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

/-- `p` started at `pc` with store `σ` and array memory `am` haltsWithResult
    producing `σ'` and `am'`. -/
def haltsWithResult (p : Prog) (pc : Nat) (σ σ' : Store) (am am' : ArrayMem) : Prop :=
  p ⊩ Cfg.run pc σ am ⟶* Cfg.halt σ' am'

-- ============================================================
-- § 8. Metatheory
-- ============================================================

/-- The small-step relation is **deterministic**. -/
theorem Step.deterministic {p : Prog} {c c₁ c₂ : Cfg}
    (h₁ : p ⊩ c ⟶ c₁) (h₂ : p ⊩ c ⟶ c₂) : c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> simp_all [Value.int.injEq, Value.typeOf] <;>
    (first | rfl | contradiction | omega | bv_omega)

/-- A halted configuration admits no further steps. -/
theorem Step.no_step_from_halt {p : Prog} {σ : Store} {am : ArrayMem} {c : Cfg} :
    ¬ (p ⊩ Cfg.halt σ am ⟶ c) :=
  fun h => by cases h

/-- An error configuration admits no further steps. -/
theorem Step.no_step_from_error {p : Prog} {σ : Store} {am : ArrayMem} {c : Cfg} :
    ¬ (p ⊩ Cfg.error σ am ⟶ c) :=
  fun h => by cases h

/-- A type-error configuration admits no further steps. -/
theorem Step.no_step_from_typeError {p : Prog} {σ : Store} {am : ArrayMem} {c : Cfg} :
    ¬ (p ⊩ Cfg.typeError σ am ⟶ c) :=
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
theorem haltsWithResult_unique {p : Prog} {pc : Nat} {σ σ₁ σ₂ : Store} {am am₁ am₂ : ArrayMem}
    (h₁ : haltsWithResult p pc σ σ₁ am am₁) (h₂ : haltsWithResult p pc σ σ₂ am am₂) : σ₁ = σ₂ := by
  simp only [haltsWithResult] at h₁ h₂
  have stuck : ∀ τ am' d, ¬ (p ⊩ Cfg.halt τ am' ⟶ d) := fun _ _ _ h => by cases h
  have := steps_det h₁ h₂ (stuck σ₁ am₁) (stuck σ₂ am₂)
  exact (Cfg.halt.inj this).1

/-- If two stores agree on all variables, any step from one can be
    matched by a step from the other. -/
theorem Step.store_congr {p : Prog} {pc : Nat} {σ τ : Store} {am : ArrayMem} {c : Cfg}
    (hσ : p ⊩ Cfg.run pc σ am ⟶ c)
    (hagree : ∀ y, σ y = τ y) :
    ∃ c', p ⊩ Cfg.run pc τ am ⟶ c' := by
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
  | arrLoad h hidx hb =>
    exact ⟨_, .arrLoad h (by rw [← hagree]; exact hidx) hb⟩
  | arrStore h hidx hty hb =>
    exact ⟨_, .arrStore h (by rw [← hagree]; exact hidx) (by simp [Value.typeOf, ← hagree]; exact hty) hb⟩
  | arrLoad_boundsError h hidx hb =>
    exact ⟨_, .arrLoad_boundsError h (by rw [← hagree]; exact hidx) hb⟩
  | arrStore_boundsError h hidx hty hb =>
    exact ⟨_, .arrStore_boundsError h (by rw [← hagree]; exact hidx) (by simp [Value.typeOf, ← hagree]; exact hty) hb⟩
  | arrLoad_typeError h hne =>
    exact ⟨_, .arrLoad_typeError h (by simp [Value.typeOf] at hne ⊢; rwa [← hagree])⟩
  | arrStore_typeError h hne =>
    refine ⟨_, .arrStore_typeError h ?_⟩
    cases hne with
    | inl hl => left; simp [Value.typeOf] at hl ⊢; rwa [← hagree]
    | inr hr => right; simp [Value.typeOf] at hr ⊢; rwa [← hagree]

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
  | .halt σ _      => Observation.halt (obs.map fun v => (v, σ v))
  | .error _ _     => Observation.error
  | .typeError _ _ => Observation.typeError
  | .run pc σ _ =>
    match p[pc]? with
    | some .halt => Observation.halt (obs.map fun v => (v, σ v))
    | some _     => Observation.nothing
    | none       => Observation.error

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

def sumStore (n : BitVec 64) : Store :=
  Store.init |>.update "n"   (.int n)
             |>.update "acc" (.int 0)
             |>.update "one" (.int 1)

-- ▸ One step from pc=0 with n=3: the conditional is taken, jump to pc=2.
example : sumProg ⊩ Cfg.run 0 (sumStore 3) ArrayMem.init ⟶ Cfg.run 2 (sumStore 3) ArrayMem.init :=
  .iftrue rfl (by native_decide)

-- ▸ Step from pc=2: acc := acc + n fires; the updated store exists.
example : ∃ σ', sumProg ⊩ Cfg.run 2 (sumStore 3) ArrayMem.init ⟶ Cfg.run 3 σ' ArrayMem.init :=
  ⟨_, .binop rfl rfl rfl trivial⟩
