import CredibleCompilation.Semantics

/-!
# ARM64 Subset Semantics

Formal model of the ARM64 instruction subset used by the code generator.
Only models the ~18 instructions actually emitted by `CodeGen.lean`.

## Design

- Registers are modeled as a finite enumeration (only those used by codegen).
- Stack memory is a total map from byte offsets to 64-bit signed integers.
- Condition flags (NZCV) are modeled explicitly for `cmp`/`cset`.
- 32-bit (W) and 64-bit (X) register views are unified: W operations
  zero-extend the result to 64 bits, which for 0/1 boolean values is
  the identity.
-/

-- ============================================================
-- § 1. Registers
-- ============================================================

/-- ARM64 registers used by the code generator. -/
inductive ArmReg where
  | x0 | x1 | x2 | x8 | x9
  deriving Repr, DecidableEq

-- sp is implicit (stack is addressed by offset)
-- x29/x30 are only used in prologue/epilogue (not modeled)

-- ============================================================
-- § 2. Condition codes and flags
-- ============================================================

/-- ARM64 condition codes used by the code generator. -/
inductive Cond where
  | eq | ne | lt | le
  deriving Repr, DecidableEq

/-- Condition flags set by `cmp`. We model only what's needed:
    the result of a signed 64-bit comparison. -/
structure Flags where
  /-- The result of the last `cmp a b` is stored as `a - b`. -/
  diff : Int
  deriving Repr

/-- Evaluate a condition against the flags. -/
instance : DecidableEq Flags := fun a b =>
  if h : a.diff = b.diff then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro heq; cases heq; exact h rfl)

def Flags.condHolds (f : Flags) : Cond → Bool
  | .eq => f.diff == 0
  | .ne => f.diff != 0
  | .lt => decide (f.diff < 0)
  | .le => decide (f.diff ≤ 0)

-- ============================================================
-- § 3. Machine state
-- ============================================================

/-- ARM64 machine state (restricted to the codegen subset). -/
structure ArmState where
  /-- Register file. -/
  regs  : ArmReg → Int
  /-- Stack memory: maps byte offset from sp to 64-bit value. -/
  stack : Nat → Int
  /-- Program counter (index into instruction array). -/
  pc    : Nat
  /-- Condition flags from the last `cmp`. -/
  flags : Flags

/-- Update a register. -/
def ArmState.setReg (s : ArmState) (r : ArmReg) (v : Int) : ArmState :=
  { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Update a stack slot. -/
def ArmState.setStack (s : ArmState) (off : Nat) (v : Int) : ArmState :=
  { s with stack := fun o => if o == off then v else s.stack o }

/-- Advance PC by 1. -/
def ArmState.nextPC (s : ArmState) : ArmState :=
  { s with pc := s.pc + 1 }

-- ============================================================
-- § 4. ARM64 instructions
-- ============================================================

/-- ARM64 instructions used by the code generator. -/
inductive ArmInstr where
  /-- `mov Xd, #imm` — load immediate (small, fits in 16 bits). -/
  | mov      : ArmReg → Int → ArmInstr
  /-- `movz Xd, #imm16, lsl #shift` — move wide with zero. -/
  | movz     : ArmReg → UInt64 → Nat → ArmInstr
  /-- `movk Xd, #imm16, lsl #shift` — move wide with keep. -/
  | movk     : ArmReg → UInt64 → Nat → ArmInstr
  /-- `ldr Xd, [sp, #off]` — load from stack. -/
  | ldr      : ArmReg → Nat → ArmInstr
  /-- `str Xs, [sp, #off]` — store to stack. -/
  | str      : ArmReg → Nat → ArmInstr
  /-- `add Xd, Xn, Xm` — 64-bit addition. -/
  | addR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `sub Xd, Xn, Xm` — 64-bit subtraction. -/
  | subR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `mul Xd, Xn, Xm` — 64-bit multiplication. -/
  | mulR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `sdiv Xd, Xn, Xm` — signed 64-bit division. -/
  | sdivR    : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `cmp Xn, Xm` — compare two registers (sets flags). -/
  | cmp      : ArmReg → ArmReg → ArmInstr
  /-- `cset Wd, cond` — set register to 0 or 1 based on flags. -/
  | cset     : ArmReg → Cond → ArmInstr
  /-- `cbz Xn, label` — branch if zero. -/
  | cbz      : ArmReg → Nat → ArmInstr
  /-- `cbnz Wn, label` — branch if nonzero. -/
  | cbnz     : ArmReg → Nat → ArmInstr
  /-- `and Wd, Wn, #imm` — bitwise AND with immediate. -/
  | andImm   : ArmReg → ArmReg → Int → ArmInstr
  /-- `and Wd, Wn, Wm` — bitwise AND registers. -/
  | andR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `eor Wd, Wn, #imm` — exclusive OR with immediate. -/
  | eorImm   : ArmReg → ArmReg → Int → ArmInstr
  /-- `orr Wd, Wn, Wm` — bitwise OR registers. -/
  | orrR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `b label` — unconditional branch. -/
  | b        : Nat → ArmInstr
  deriving Repr, DecidableEq

/-- An ARM64 program is an array of instructions. -/
abbrev ArmProg := Array ArmInstr

-- ============================================================
-- § 5. Small-step semantics
-- ============================================================

/-- Truncate to low 32 bits (for W-register operations on booleans). -/
def truncW (n : Int) : Int := n % (2 ^ 32)

/-- Insert a 16-bit value at a given shift position, keeping other bits. -/
def insertBits (val : Int) (imm16 : UInt64) (shift : Nat) : Int :=
  let shiftU : UInt64 := shift.toUInt64
  let valU : UInt64 := val.toNat.toUInt64
  let mask : UInt64 := (0xFFFF : UInt64) <<< shiftU
  let cleared := valU &&& (~~~ mask)
  let inserted := cleared ||| (imm16 <<< shiftU)
  Int.ofNat inserted.toNat

/-- Small-step semantics for the ARM64 subset. -/
inductive ArmStep (prog : ArmProg) : ArmState → ArmState → Prop where

  | mov (rd : ArmReg) (imm : Int) :
    prog[s.pc]? = some (.mov rd imm) →
    ArmStep prog s (s.setReg rd imm |>.nextPC)

  | movz (rd : ArmReg) (imm16 : UInt64) (shift : Nat) :
    prog[s.pc]? = some (.movz rd imm16 shift) →
    ArmStep prog s (s.setReg rd (Int.ofNat (imm16 <<< shift.toUInt64).toNat) |>.nextPC)

  | movk (rd : ArmReg) (imm16 : UInt64) (shift : Nat) :
    prog[s.pc]? = some (.movk rd imm16 shift) →
    ArmStep prog s (s.setReg rd (insertBits (s.regs rd) imm16 shift) |>.nextPC)

  | ldr (rd : ArmReg) (off : Nat) :
    prog[s.pc]? = some (.ldr rd off) →
    ArmStep prog s (s.setReg rd (s.stack off) |>.nextPC)

  | str (rs : ArmReg) (off : Nat) :
    prog[s.pc]? = some (.str rs off) →
    ArmStep prog s (s.setStack off (s.regs rs) |>.nextPC)

  | addR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.addR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)

  | subR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.subR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn - s.regs rm) |>.nextPC)

  | mulR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.mulR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn * s.regs rm) |>.nextPC)

  | sdivR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.sdivR rd rn rm) →
    s.regs rm ≠ 0 →
    ArmStep prog s (s.setReg rd (s.regs rn / s.regs rm) |>.nextPC)

  | cmpRR (rn rm : ArmReg) :
    prog[s.pc]? = some (.cmp rn rm) →
    ArmStep prog s ({ s with flags := ⟨s.regs rn - s.regs rm⟩, pc := s.pc + 1 })

  | cset (rd : ArmReg) (c : Cond) :
    prog[s.pc]? = some (.cset rd c) →
    ArmStep prog s (s.setReg rd (if s.flags.condHolds c then 1 else 0) |>.nextPC)

  | cbz_taken (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbz rn lbl) →
    s.regs rn = 0 →
    ArmStep prog s { s with pc := lbl }

  | cbz_fall (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbz rn lbl) →
    s.regs rn ≠ 0 →
    ArmStep prog s s.nextPC

  | cbnz_taken (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbnz rn lbl) →
    s.regs rn ≠ 0 →
    ArmStep prog s { s with pc := lbl }

  | cbnz_fall (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbnz rn lbl) →
    s.regs rn = 0 →
    ArmStep prog s s.nextPC

  | andImm (rd rn : ArmReg) (imm : Int) :
    prog[s.pc]? = some (.andImm rd rn imm) →
    ArmStep prog s (s.setReg rd (Int.ofNat (s.regs rn |>.toNat.land imm.toNat)) |>.nextPC)

  | andR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.andR rd rn rm) →
    ArmStep prog s (s.setReg rd (Int.ofNat (s.regs rn |>.toNat.land (s.regs rm).toNat)) |>.nextPC)

  | eorImm (rd rn : ArmReg) (imm : Int) :
    prog[s.pc]? = some (.eorImm rd rn imm) →
    ArmStep prog s (s.setReg rd (Int.ofNat (s.regs rn |>.toNat.xor imm.toNat)) |>.nextPC)

  | orrR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.orrR rd rn rm) →
    ArmStep prog s (s.setReg rd (Int.ofNat (s.regs rn |>.toNat.lor (s.regs rm).toNat)) |>.nextPC)

  | branch (lbl : Nat) :
    prog[s.pc]? = some (.b lbl) →
    ArmStep prog s { s with pc := lbl }

/-- Multi-step closure. -/
inductive ArmSteps (prog : ArmProg) : ArmState → ArmState → Prop where
  | refl : ArmSteps prog s s
  | step : ArmStep prog s s' → ArmSteps prog s' s'' → ArmSteps prog s s''

theorem ArmSteps.single {prog : ArmProg} {s s' : ArmState}
    (h : ArmStep prog s s') : ArmSteps prog s s' :=
  .step h .refl

theorem ArmSteps.trans {prog : ArmProg} {s s' s'' : ArmState}
    (h1 : ArmSteps prog s s') (h2 : ArmSteps prog s' s'') :
    ArmSteps prog s s'' := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

-- ============================================================
-- § 6. Value encoding
-- ============================================================

/-- Encode a TAC `Value` as a 64-bit integer for the ARM64 representation.
    Integers are stored directly; booleans as 0/1. -/
def Value.encode : Value → Int
  | .int n  => n
  | .bool b => if b then 1 else 0

/-- Decode a 64-bit integer back to a `Value` given its type. -/
def Value.decode (ty : VarTy) (n : Int) : Value :=
  match ty with
  | .int  => .int n
  | .bool => .bool (n != 0)

/-- For integer values, encode equals toInt. -/
theorem Value.encode_eq_toInt_of_int {v : Value} (h : ∃ n, v = .int n) :
    v.encode = v.toInt := by
  obtain ⟨n, rfl⟩ := h; rfl

/-- For any value, encode equals toInt when the value is an integer. -/
@[simp] theorem Value.encode_int (n : Int) : (Value.int n).encode = n := rfl
theorem Value.encode_decode_int (n : Int) :
    Value.decode .int (Value.encode (.int n)) = .int n := by
  simp [encode, decode]

theorem Value.encode_decode_bool (b : Bool) :
    Value.decode .bool (Value.encode (.bool b)) = .bool b := by
  simp [encode, decode]; cases b <;> simp

-- ============================================================
-- § 7. State relation
-- ============================================================

/-- A variable-to-stack-offset map. -/
abbrev VarMap := List (Var × Nat)

/-- Look up a variable's stack offset. -/
def VarMap.lookup (vm : VarMap) (v : Var) : Option Nat :=
  vm.find? (fun (x, _) => x == v) |>.map Prod.snd

/-- The ARM64 stack correctly represents the TAC store:
    for every mapped variable, the stack slot holds the encoded value. -/
def StateRel (vm : VarMap) (σ : Store) (arm : ArmState) : Prop :=
  ∀ v off, vm.lookup v = some off → arm.stack off = (σ v).encode

/-- The scratch slot at offset 0 does not alias any variable slot. -/
def ScratchSafe (vm : VarMap) : Prop :=
  ∀ v off, vm.lookup v = some off → off ≠ 0

/-- The VarMap is injective: distinct variables have distinct offsets. -/
def VarMapInjective (vm : VarMap) : Prop :=
  ∀ v1 v2 off, vm.lookup v1 = some off → vm.lookup v2 = some off → v1 = v2

/-- PC correspondence: TAC PC maps to ARM PC. -/
def PcRel (pcMap : Nat → Nat) (tac_pc : Nat) (arm_pc : Nat) : Prop :=
  arm_pc = pcMap tac_pc

/-- Full simulation invariant. -/
def SimRel (vm : VarMap) (pcMap : Nat → Nat) (tac_cfg : Cfg) (arm : ArmState) : Prop :=
  match tac_cfg with
  | .run pc σ     => StateRel vm σ arm ∧ PcRel pcMap pc arm.pc
  | .halt σ       => StateRel vm σ arm
  | .error _      => True
  | .typeError _  => False

-- ============================================================
-- § 8. Formal instruction generation
-- ============================================================

/-- Generate formal ARM64 instructions for loading an immediate.
    Mirrors `loadImm64` in CodeGen.lean. -/
def formalLoadImm64 (rd : ArmReg) (n : Int) : List ArmInstr :=
  if n < 0 || (-65536 < n && n < 65536) then
    -- Small or negative: single mov (ARM assembler handles movn for negatives)
    [.mov rd n]
  else
    -- Large positive: movz/movk sequence
    let bits : UInt64 := n.toNat.toUInt64
    let w0 := bits &&& 0xFFFF
    let w1 := (bits >>> 16) &&& 0xFFFF
    let w2 := (bits >>> 32) &&& 0xFFFF
    let w3 := (bits >>> 48) &&& 0xFFFF
    let base := [.movz rd w0 0]
    let k1 := if w1 != 0 then [.movk rd w1 16] else []
    let k2 := if w2 != 0 then [.movk rd w2 32] else []
    let k3 := if w3 != 0 then [.movk rd w3 48] else []
    base ++ k1 ++ k2 ++ k3

/-- Generate formal ARM64 instructions for a boolean expression.
    Result is left in x0 (0 or 1). Mirrors `genBoolExpr` in CodeGen.lean. -/
def formalGenBoolExpr (vm : VarMap) (be : BoolExpr) : List ArmInstr :=
  match be with
  | .bvar v =>
    match vm.lookup v with
    | some off => [.ldr .x0 off, .andImm .x0 .x0 1]
    | none => []
  | .cmp op lv rv =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    match vm.lookup lv, vm.lookup rv with
    | some offL, some offR =>
      [.ldr .x1 offL, .ldr .x2 offR, .cmp .x1 .x2, .cset .x0 cond]
    | _, _ => []
  | .cmpLit op v n =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    match vm.lookup v with
    | some off =>
      [.ldr .x1 off] ++ formalLoadImm64 .x2 n ++ [.cmp .x1 .x2, .cset .x0 cond]
    | none => []
  | .not e =>
    formalGenBoolExpr vm e ++ [.eorImm .x0 .x0 1]

/-- Generate formal ARM64 instructions for a TAC instruction.
    Mirrors `genInstr` in CodeGen.lean (without the label string).
    `pcMap` maps TAC labels to ARM PCs for branch targets. -/
def formalGenInstr (vm : VarMap) (pcMap : Nat → Nat) (instr : TAC)
    (haltLabel : Nat) (divLabel : Nat) : List ArmInstr :=
  match instr with
  | .const v (.int n) =>
    match vm.lookup v with
    | some off => formalLoadImm64 .x0 n ++ [.str .x0 off]
    | none => []
  | .const v (.bool b) =>
    match vm.lookup v with
    | some off => [.mov .x0 (if b then 1 else 0), .str .x0 off]
    | none => []
  | .copy dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD => [.ldr .x0 offS, .str .x0 offD]
    | _, _ => []
  | .binop dst op lv rv =>
    match vm.lookup lv, vm.lookup rv, vm.lookup dst with
    | some offL, some offR, some offD =>
      let opInstr := match op with
        | .add => ArmInstr.addR .x0 .x1 .x2
        | .sub => .subR .x0 .x1 .x2
        | .mul => .mulR .x0 .x1 .x2
        | .div => .sdivR .x0 .x1 .x2
      if op == .div then
        [.ldr .x2 offR, .cbz .x2 divLabel,
         .ldr .x1 offL, .ldr .x2 offR, opInstr, .str .x0 offD]
      else
        [.ldr .x1 offL, .ldr .x2 offR, opInstr, .str .x0 offD]
    | _, _, _ => []
  | .boolop dst be =>
    match vm.lookup dst with
    | some offD => formalGenBoolExpr vm be ++ [.str .x0 offD]
    | none => []
  | .goto l => [.b (pcMap l)]
  | .ifgoto be l =>
    formalGenBoolExpr vm be ++ [.cbnz .x0 (pcMap l)]
  | .halt => [.b haltLabel]

-- ============================================================
-- § 9. Correctness lemmas (stubs)
-- ============================================================

/-- A code segment is embedded in the program starting at a given PC. -/
def CodeAt (prog : ArmProg) (startPC : Nat) (instrs : List ArmInstr) : Prop :=
  ∀ i, (h : i < instrs.length) →
    prog[startPC + i]? = some instrs[i]

-- Helper: CodeAt for a single instruction
theorem CodeAt.head {prog : ArmProg} {startPC : Nat} {instr : ArmInstr} {rest : List ArmInstr}
    (h : CodeAt prog startPC (instr :: rest)) :
    prog[startPC]? = some instr := by
  have := h 0 (by simp)
  simp at this; exact this

-- Helper: CodeAt for the tail
theorem CodeAt.tail {prog : ArmProg} {startPC : Nat} {instr : ArmInstr} {rest : List ArmInstr}
    (h : CodeAt prog startPC (instr :: rest)) :
    CodeAt prog (startPC + 1) rest := by
  intro i hi
  have := h (i + 1) (by simp; omega)
  rw [show startPC + (i + 1) = startPC + 1 + i from by omega] at this
  exact this

-- Helper: execute one instruction and advance
theorem ArmSteps.one_then {prog : ArmProg} {s s' s'' : ArmState}
    (h1 : ArmStep prog s s') (h2 : ArmSteps prog s' s'') :
    ArmSteps prog s s'' :=
  .step h1 h2

-- setReg preserves stack
@[simp] theorem ArmState.setReg_stack (s : ArmState) (r : ArmReg) (v : Int) :
    (s.setReg r v).stack = s.stack := rfl

-- nextPC preserves stack and regs
@[simp] theorem ArmState.nextPC_stack (s : ArmState) :
    s.nextPC.stack = s.stack := rfl

@[simp] theorem ArmState.nextPC_regs (s : ArmState) :
    s.nextPC.regs = s.regs := rfl

@[simp] theorem ArmState.nextPC_pc (s : ArmState) :
    s.nextPC.pc = s.pc + 1 := rfl

-- setReg reads
@[simp] theorem ArmState.setReg_regs_same (s : ArmState) (r : ArmReg) (v : Int) :
    (s.setReg r v).regs r = v := by
  simp [setReg]

@[simp] theorem ArmState.setReg_regs_other (s : ArmState) (r r' : ArmReg) (v : Int) (h : r' ≠ r) :
    (s.setReg r v).regs r' = s.regs r' := by
  simp [setReg, h]

@[simp] theorem ArmState.setReg_pc (s : ArmState) (r : ArmReg) (v : Int) :
    (s.setReg r v).pc = s.pc := rfl

@[simp] theorem ArmState.setReg_flags (s : ArmState) (r : ArmReg) (v : Int) :
    (s.setReg r v).flags = s.flags := rfl

@[simp] theorem ArmState.nextPC_flags (s : ArmState) :
    s.nextPC.flags = s.flags := rfl

-- Register inequality facts for simp
@[simp] theorem ArmReg.x0_ne_x1 : (ArmReg.x0 == ArmReg.x1) = false := by native_decide
@[simp] theorem ArmReg.x0_ne_x2 : (ArmReg.x0 == ArmReg.x2) = false := by native_decide
@[simp] theorem ArmReg.x1_ne_x0 : (ArmReg.x1 == ArmReg.x0) = false := by native_decide
@[simp] theorem ArmReg.x1_ne_x2 : (ArmReg.x1 == ArmReg.x2) = false := by native_decide
@[simp] theorem ArmReg.x2_ne_x0 : (ArmReg.x2 == ArmReg.x0) = false := by native_decide
@[simp] theorem ArmReg.x2_ne_x1 : (ArmReg.x2 == ArmReg.x1) = false := by native_decide
@[simp] theorem ArmReg.beq_self (r : ArmReg) : (r == r) = true := by cases r <;> native_decide

-- Helper: split CodeAt for appended lists
theorem CodeAt.append_left {prog : ArmProg} {startPC : Nat} {l1 l2 : List ArmInstr}
    (h : CodeAt prog startPC (l1 ++ l2)) :
    CodeAt prog startPC l1 := by
  intro i hi
  have := h i (by simp; omega)
  simp [List.getElem_append_left hi] at this
  exact this

theorem CodeAt.append_right {prog : ArmProg} {startPC : Nat} {l1 l2 : List ArmInstr}
    (h : CodeAt prog startPC (l1 ++ l2)) :
    CodeAt prog (startPC + l1.length) l2 := by
  intro i hi
  have hlt : l1.length + i < (l1 ++ l2).length := by simp; omega
  have := h (l1.length + i) hlt
  have hge : l1.length ≤ l1.length + i := Nat.le_add_right _ _
  rw [List.getElem_append_right hge] at this
  simp at this
  rw [show startPC + l1.length + i = startPC + (l1.length + i) from by omega]
  exact this

theorem loadImm64_correct (prog : ArmProg) (rd : ArmReg) (n : Int)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs rd = n ∧
      s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length := by
  by_cases hsmall : n < 0 || (-65536 < n && n < 65536)
  · -- Small or negative: single `mov rd, #n`
    have hformal : formalLoadImm64 rd n = [.mov rd n] := by
      simp [formalLoadImm64, hsmall]
    rw [hformal] at hCode ⊢
    refine ⟨s.setReg rd n |>.nextPC, ?_, ?_, ?_, ?_⟩
    · exact .single (.mov rd n (by subst hPC; exact hCode.head))
    · simp
    · simp
    · simp; subst hPC; rfl
  · -- Large non-negative: movz/movk sequence
    -- hsmall : ¬(n < 0 || small range) so n ≥ 0 and n ≥ 65536
    -- The movz/movk sequence reconstructs n from its UInt64 16-bit chunks.
    -- This requires proving the bitwise decomposition/reassembly identity.
    sorry

/-- Helper: Flags.condHolds matches CmpOp.eval for signed integer comparison. -/
theorem Flags.condHolds_correct (op : CmpOp) (a b : Int) :
    (Flags.mk (a - b)).condHolds (match op with | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le)
    = op.eval a b := by
  cases op <;> simp [Flags.condHolds, CmpOp.eval]
  · -- eq: (a - b == 0) = (a == b)
    show (a - b == 0) = (a == b)
    cases h : (a == b) <;> simp_all [beq_iff_eq] <;> omega
  · -- ne: (a - b != 0) = (a != b)
    show (a - b != 0) = (a != b)
    unfold bne
    cases h : (a - b == 0) <;> cases h' : (a == b) <;> simp_all [beq_iff_eq] <;> omega
  · -- lt
    omega
  · -- le
    omega

/-- Helper: executing ldr/ldr/cmp/cset for a `.cmp` boolean expression. -/
private theorem genBoolExpr_cmp_correct (prog : ArmProg) (vm : VarMap)
    (op : CmpOp) (lv rv : Var) (σ : Store) (s : ArmState) (startPC : Nat)
    (offL offR : Nat)
    (hL : vm.lookup lv = some offL) (hR : vm.lookup rv = some offR)
    (hRel : StateRel vm σ s)
    (hIntL : ∃ n, σ lv = .int n) (hIntR : ∃ n, σ rv = .int n)
    (hCode : CodeAt prog startPC
      (.ldr .x1 offL :: .ldr .x2 offR :: .cmp .x1 .x2 ::
       .cset .x0 (match op with | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le) :: List.nil))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs .x0 = (if op.eval (σ lv).toInt (σ rv).toInt then (1 : Int) else 0) ∧
      (∀ v off, vm.lookup v = some off → s'.stack off = s.stack off) ∧
      s'.pc = startPC + 4 := by
  subst hPC
  have h0 := hCode.head
  have h1 := hCode.tail.head
  have h2 := hCode.tail.tail.head
  have h3 := hCode.tail.tail.tail.head
  -- Build the 4-step execution explicitly
  -- After ldr x1: x1 = stack[offL] = (σ lv).encode
  -- After ldr x2: x2 = stack[offR] = (σ rv).encode
  -- After cmp: flags.diff = x1 - x2
  -- After cset: x0 = condHolds flags cond ? 1 : 0
  have hvalL := hRel lv offL hL
  have hvalR := hRel rv offR hR
  -- We need to show the result for each op case
  obtain ⟨nL, hnL⟩ := hIntL; obtain ⟨nR, hnR⟩ := hIntR
  -- Helper: build the 4-step execution and close value/stack/pc goals
  suffices ∀ (c : Cond),
      prog[s.pc + 1 + 1 + 1]? = some (.cset .x0 c) →
      (if (Flags.mk (nL - nR)).condHolds c then (1:Int) else 0) =
        (if op.eval nL nR then 1 else 0) →
      ∃ s', ArmSteps prog s s' ∧
        (s'.regs .x0 = if op.eval (σ lv).toInt (σ rv).toInt then (1:Int) else 0) ∧
        (∀ v off, vm.lookup v = some off → s'.stack off = s.stack off) ∧
        s'.pc = s.pc + 4 from by
    cases op <;> simp only [] at h3 <;> exact this _ h3 (by
      simp [Flags.condHolds, CmpOp.eval]; split <;> split <;> omega)
  intro c h3c hval
  exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
    (.step (.cmpRR .x1 .x2 h2) (.single (.cset .x0 c h3c)))),
    by simp only [ArmState.setReg, ArmState.nextPC,
          ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
          ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, Bool.false_eq_true, ite_false]
       rw [hvalL, hvalR, hnL, hnR]; simp only [Value.encode, Value.toInt]; exact hval,
    ⟨fun _ _ _ => rfl, by simp [ArmState.setReg, ArmState.nextPC]⟩⟩

/-- `genBoolExpr` correctly evaluates a boolean expression into x0.
    Requires that compared variables are integers (guaranteed by well-typedness). -/
theorem genBoolExpr_correct (prog : ArmProg) (vm : VarMap)
    (be : BoolExpr) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : StateRel vm σ s)
    (hScratch : ScratchSafe vm)
    (hCode : CodeAt prog startPC (formalGenBoolExpr vm be))
    (hPC : s.pc = startPC)
    (hVarMap : ∀ v, ∃ off, vm.lookup v = some off)
    (Γ : TyCtx) (hTS : TypedStore Γ σ)
    (hWTBE : WellTypedBoolExpr Γ be) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs .x0 = (if be.eval σ then (1 : Int) else 0) ∧
      (∀ v off, vm.lookup v = some off → s'.stack off = s.stack off) ∧
      s'.pc = startPC + (formalGenBoolExpr vm be).length := by
  cases be with
  | cmp op lv rv =>
    simp only [formalGenBoolExpr] at hCode ⊢
    cases hlv : vm.lookup lv with
    | none => exact absurd hlv (by obtain ⟨_, h⟩ := hVarMap lv; simp [h])
    | some offL =>
    cases hrv : vm.lookup rv with
    | none => exact absurd hrv (by obtain ⟨_, h⟩ := hVarMap rv; simp [h])
    | some offR =>
    simp only [hlv, hrv] at hCode ⊢
    -- Extract int witnesses from well-typedness
    have hIntL : ∃ n, σ lv = .int n := by
      cases hWTBE with | cmp hx hy => exact Value.int_of_typeOf_int (by rw [hTS]; exact hx)
    have hIntR : ∃ n, σ rv = .int n := by
      cases hWTBE with | cmp hx hy => exact Value.int_of_typeOf_int (by rw [hTS]; exact hy)
    exact genBoolExpr_cmp_correct prog vm op lv rv σ s startPC offL offR
      hlv hrv hRel hIntL hIntR hCode hPC
  | not e =>
    simp only [formalGenBoolExpr] at hCode ⊢
    -- Code = formalGenBoolExpr vm e ++ [eorImm x0 x0 1]
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    have hWTe : WellTypedBoolExpr Γ e := by cases hWTBE with | not h => exact h
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1⟩ :=
      genBoolExpr_correct prog vm e σ s startPC hRel hScratch hCodeE hPC hVarMap Γ hTS hWTe
    have hEor := hCodeEor.head
    rw [← hPC1] at hEor
    -- After eor: x0 = 1 - x0 (flips 0↔1)
    refine ⟨s1.setReg .x0 (Int.ofNat (s1.regs .x0 |>.toNat.xor 1)) |>.nextPC,
      hSteps1.trans (.single (.eorImm .x0 .x0 1 hEor)), ?_, ?_, ?_⟩
    · -- value: !(eval e σ)
      simp only [ArmState.setReg_regs_same, ArmState.nextPC_regs]
      rw [hx0]; simp only [BoolExpr.eval, Bool.not_eq_true']
      match h : BoolExpr.eval σ e with
      | true => simp [Int.toNat, Nat.xor, Nat.bitwise]
      | false => simp [Int.toNat, Nat.xor, Nat.bitwise]
    · intro v off hv
      simp only [ArmState.setReg, ArmState.nextPC]
      exact hStack1 v off hv
    · simp only [ArmState.setReg, ArmState.nextPC, hPC1, List.length_append, List.length_cons,
                  List.length_nil]
      omega
  | bvar v =>
    simp only [formalGenBoolExpr] at hCode ⊢
    obtain ⟨off, hOff⟩ := hVarMap v
    simp only [hOff] at hCode ⊢
    have h0 := hCode.head; have h1 := hCode.tail.head
    rw [← hPC] at h0 h1
    refine ⟨s.setReg .x0 (s.stack off) |>.nextPC
            |>.setReg .x0 (Int.ofNat (s.setReg .x0 (s.stack off) |>.nextPC |>.regs .x0 |>.toNat.land 1))
            |>.nextPC,
      .step (.ldr .x0 off h0) (.single (.andImm .x0 .x0 1 h1)), ?_, ?_, ?_⟩
    · -- value
      simp only [ArmState.setReg, ArmState.nextPC, ArmReg.beq_self, ite_true,
                  BoolExpr.eval, hRel v off hOff]
      -- σ v is a bool by well-typedness
      have hbool : ∃ b, σ v = .bool b := by
        cases hWTBE with | bvar hty =>
        have := hTS v; rw [hty] at this
        exact Value.bool_of_typeOf_bool this
      obtain ⟨bv, hbv⟩ := hbool
      simp only [hbv, Value.encode, Value.toBool]
      cases bv <;> simp [Int.toNat, Nat.land, Nat.bitwise]
    · intro w woff hv; simp [ArmState.setReg, ArmState.nextPC]
    · simp only [ArmState.setReg, ArmState.nextPC, List.length_cons, List.length_nil]; subst hPC; omega
  | cmpLit op v n =>
    simp only [formalGenBoolExpr] at hCode ⊢
    obtain ⟨off, hOff⟩ := hVarMap v
    simp only [hOff] at hCode ⊢
    -- Code = [ldr x1 off] ++ loadImm64 x2 n ++ [cmp x1 x2, cset x0 cond]
    -- Needs loadImm64_correct for x2 (which has sorry for large case),
    -- then follows the same pattern as genBoolExpr_cmp_correct.
    sorry

/-- StateRel is preserved when store is updated at `x ↦ w` and stack at `off ↦ w.encode`,
    provided `vm.lookup x = some off` and the VarMap is injective. -/
theorem StateRel.update {vm : VarMap} {σ : Store} {arm : ArmState}
    (hRel : StateRel vm σ arm)
    (hInj : VarMapInjective vm)
    (x : Var) (w : Value) (off : Nat) (hOff : vm.lookup x = some off) :
    StateRel vm (Store.update σ x w) (arm.setStack off w.encode) := by
  intro v voff hv
  simp only [ArmState.setStack, Store.update]
  by_cases hvo : voff = off
  · -- v maps to the same offset as x → v = x (by injectivity)
    subst hvo
    have := hInj v x voff hv hOff; subst this
    simp
  · -- different offset → v ≠ x (otherwise offsets would match)
    have hne : v ≠ x := fun h => hvo (by subst h; exact Option.some.inj (hv.symm.trans hOff))
    simp [hvo, hne]
    exact hRel v voff hv


/-- Single TAC instruction backward simulation. -/
theorem genInstr_correct (prog : ArmProg) (vm : VarMap) (pcMap : Nat → Nat)
    (p : Prog) (pc : Nat) (σ : Store) (s : ArmState)
    (haltLabel divLabel : Nat)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hRel : SimRel vm pcMap (.run pc σ) s)
    (hScratch : ScratchSafe vm)
    (hInjective : VarMapInjective vm)
    (hWT : WellTypedProg p.tyCtx p)
    (hTS : TypedStore p.tyCtx σ)
    (hPC_bound : pc < p.size)
    (cfg' : Cfg) (hStep : p ⊩ Cfg.run pc σ ⟶ cfg')
    (hVarMap : ∀ v, ∃ off, vm.lookup v = some off)
    (hCodeInstr : CodeAt prog (pcMap pc) (formalGenInstr vm pcMap instr haltLabel divLabel))
    (hPcNext : ∀ pc' σ', cfg' = .run pc' σ' →
      pcMap pc' = pcMap pc + (formalGenInstr vm pcMap instr haltLabel divLabel).length) :
    ∃ s', ArmSteps prog s s' ∧ SimRel vm pcMap cfg' s' := by
  obtain ⟨hStateRel, hPcRel⟩ := hRel
  cases hStep with
  | goto hinstr =>
    -- TAC: goto l → ARM: b (pcMap l)
    have heq : instr = .goto _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hCodeInstr; simp only [formalGenInstr] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    exact ⟨{ s with pc := pcMap _ }, .single (.branch _ hb),
      ⟨hStateRel, rfl⟩⟩
  | halt hinstr =>
    -- TAC: halt → ARM: b haltLabel
    -- formalGenInstr for .halt = [.b haltLabel]
    have hformal : formalGenInstr vm pcMap .halt haltLabel divLabel = [.b haltLabel] := rfl
    rw [show instr = .halt from by
      have := Option.some.inj (hInstr.symm.trans hinstr); exact this] at hCodeInstr
    rw [hformal] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    exact ⟨{ s with pc := haltLabel },
      .single (.branch haltLabel hb),
      hStateRel⟩
  | const hinstr =>
    -- TAC: x := v → ARM: loadImm64 + str (int) or mov + str (bool)
    rename_i x v
    obtain ⟨offD, hD⟩ := hVarMap x
    have heq : instr = .const x v := Option.some.inj (hInstr.symm.trans hinstr)
    cases v with
    | int n =>
      -- formalGenInstr = formalLoadImm64 x0 n ++ [str x0 offD]
      have hformal : formalGenInstr vm pcMap (.const x (.int n)) haltLabel divLabel =
          formalLoadImm64 .x0 n ++ (.str .x0 offD :: List.nil) := by
        show (match vm.lookup x with | some off => _ | none => _) = _
        rw [hD]
      rw [heq, hformal] at hCodeInstr
      -- Split CodeAt into loadImm64 part and str part
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hStr := hCodeR.head
      -- Use loadImm64_correct to load n into x0
      obtain ⟨s1, hSteps1, hx0, hStack1, hPC1⟩ :=
        loadImm64_correct prog .x0 n s (pcMap pc) hCodeL hPcRel
      -- Then str x0, [sp, #offD]
      rw [← hPC1] at hStr
      let s2 := s1.setStack offD (s1.regs .x0) |>.nextPC
      refine ⟨s2, hSteps1.trans (.single (.str .x0 offD hStr)), ⟨?_, ?_⟩⟩
      · -- StateRel
        intro w off hv
        simp only [s2, ArmState.setStack, ArmState.nextPC]
        by_cases hoff : off = offD
        · subst hoff; simp
          have := hInjective w x off hv hD; subst this
          rw [Store.update_self, hx0]; simp [Value.encode]
        · simp [hoff]
          have hne : w ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD))
          rw [Store.update_other _ _ _ _ hne]
          rw [show s1.stack off = s.stack off from by rw [hStack1]]
          exact hStateRel w off hv
      · -- PcRel
        show s1.pc + 1 = pcMap (pc + 1)
        rw [heq, hformal] at hPcNext
        have := hPcNext _ _ rfl; simp at this
        rw [this, hPC1]; omega
    | bool b =>
      have hformal : formalGenInstr vm pcMap (.const x (.bool b)) haltLabel divLabel =
          (.mov .x0 (if b then 1 else 0) :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup x with | some off => _ | none => _) = _
        rw [hD]
      rw [heq, hformal] at hCodeInstr
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      rw [← hPcRel] at h0 h1
      refine ⟨(s.setReg .x0 (if b then 1 else 0) |>.nextPC |>.setStack offD
                (s.setReg .x0 (if b then 1 else 0) |>.nextPC |>.regs .x0) |>.nextPC),
        .step (.mov .x0 _ h0) (.single (.str .x0 offD h1)), ⟨?_, ?_⟩⟩
      · -- StateRel
        intro w off hv
        simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                    ArmReg.beq_self, ite_true]
        by_cases hoff : off = offD
        · subst hoff; simp
          have := hInjective w x off hv hD; subst this
          rw [Store.update_self]; simp [Value.encode]
        · simp [hoff]
          have hne : w ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD))
          rw [Store.update_other _ _ _ _ hne]; exact hStateRel w off hv
      · -- PcRel
        show s.pc + 1 + 1 = pcMap (pc + 1)
        rw [heq, hformal] at hPcNext
        have := hPcNext _ _ rfl; simp at this
        rw [this, hPcRel]
  | copy hinstr =>
    -- TAC: copy x y → ARM: ldr x0 offS; str x0 offD
    rename_i x y
    have heq : instr = .copy x y := Option.some.inj (hInstr.symm.trans hinstr)
    obtain ⟨offS, hS⟩ := hVarMap y
    obtain ⟨offD, hD⟩ := hVarMap x
    have hformal : formalGenInstr vm pcMap (.copy x y) haltLabel divLabel =
        (.ldr .x0 offS :: .str .x0 offD :: List.nil) := by
      show (match vm.lookup y, vm.lookup x with
        | some offS, some offD => _ | _, _ => _) = _
      rw [hS, hD]
    rw [heq, hformal] at hCodeInstr
    have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
    rw [← hPcRel] at h0 h1
    -- Execute: ldr x0, [sp, #offS]; str x0, [sp, #offD]
    refine ⟨(s.setReg .x0 (s.stack offS) |>.nextPC |>.setStack offD
              (s.setReg .x0 (s.stack offS) |>.nextPC |>.regs .x0) |>.nextPC),
      .step (.ldr .x0 offS h0) (.single (.str .x0 offD h1)),
      ⟨?_, ?_⟩⟩
    · -- StateRel for σ[x ↦ σ y]
      intro v off hv
      simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                  ArmReg.beq_self, ite_true]
      by_cases hoff : off = offD
      · subst hoff
        simp
        have := hInjective v _ off hv hD; subst this
        rw [Store.update_self]; exact hStateRel y offS hS
      · simp [hoff]
        have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD))
        show s.stack off = (σ[x ↦ σ y] v).encode
        rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv
    · -- PcRel
      show s.pc + 1 + 1 = pcMap (pc + 1)
      rw [heq, hformal] at hPcNext
      have := hPcNext _ _ rfl; simp at this
      rw [this, hPcRel]
  | binop hinstr hy hz hs =>
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    rename_i x bop y z a b
    obtain ⟨offL, hL⟩ := hVarMap y
    obtain ⟨offR, hR⟩ := hVarMap z
    obtain ⟨offD, hD'⟩ := hVarMap x
    -- Case split on BinOp first, then compute formalGenInstr for each
    cases bop with
    | div =>
      -- formalGenInstr for div = [ldr x2 offR, cbz x2 divLabel, ldr x1 offL, ldr x2 offR, sdiv x0 x1 x2, str x0 offD]
      have hformal : formalGenInstr vm pcMap (.binop x .div y z) haltLabel divLabel =
          (.ldr .x2 offR :: .cbz .x2 divLabel :: .ldr .x1 offL :: .ldr .x2 offR ::
           .sdivR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head
      have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head
      have h3 := hCodeInstr.tail.tail.tail.head
      have h4 := hCodeInstr.tail.tail.tail.tail.head
      have h5 := hCodeInstr.tail.tail.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3 h4 h5
      -- hs : BinOp.div.safe a b means b ≠ 0
      -- After ldr x2 offR: x2 = stack[offR] = (σ z).encode = b
      -- cbz x2 divLabel: since b ≠ 0, falls through
      -- Then ldr x1, ldr x2, sdiv, str — same as add/sub/mul
      have hb_ne : (s.stack offR : Int) ≠ 0 := by
        rw [hStateRel z offR hR, hz]; simp [Value.encode]; exact hs
      exact ⟨_, .step (.ldr .x2 offR h0)
              (.step (.cbz_fall .x2 divLabel h1 (by simp [ArmState.setReg, ArmState.nextPC]; exact hb_ne))
              (.step (.ldr .x1 offL h2)
              (.step (.ldr .x2 offR h3)
              (.step (.sdivR .x0 .x1 .x2 h4 (by
                simp [ArmState.setReg, ArmState.nextPC]
                rw [hStateRel z offR hR, hz]; simp [Value.encode]; exact hs))
              (.single (.str .x0 offD h5)))))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x0, ArmReg.x2_ne_x1,
                       ite_true, ite_false, Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp
             have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 6 = pcMap (pc + 1)
           have := hPcNext _ _ rfl; simp at this; rw [this, hPcRel]⟩
    | add =>
      -- formalGenInstr for add = [ldr x1 offL, ldr x2 offR, addR x0 x1 x2, str x0 offD]
      have hformal : formalGenInstr vm pcMap (.binop x .add y z) haltLabel divLabel =
          (.ldr .x1 offL :: .ldr .x2 offR :: .addR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head; have h3 := hCodeInstr.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3
      exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
          (.step (.addR .x0 .x1 .x2 h2) (.single (.str .x0 offD h3)))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, ite_false,
                       Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp; have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 4 = pcMap (pc + 1)
           have := hPcNext _ _ rfl; simp at this; rw [this, hPcRel]⟩
    | sub =>
      have hformal : formalGenInstr vm pcMap (.binop x .sub y z) haltLabel divLabel =
          (.ldr .x1 offL :: .ldr .x2 offR :: .subR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head; have h3 := hCodeInstr.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3
      exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
          (.step (.subR .x0 .x1 .x2 h2) (.single (.str .x0 offD h3)))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, ite_false,
                       Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp; have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 4 = pcMap (pc + 1)
           have := hPcNext _ _ rfl; simp at this; rw [this, hPcRel]⟩
    | mul =>
      have hformal : formalGenInstr vm pcMap (.binop x .mul y z) haltLabel divLabel =
          (.ldr .x1 offL :: .ldr .x2 offR :: .mulR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head; have h3 := hCodeInstr.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3
      exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
          (.step (.mulR .x0 .x1 .x2 h2) (.single (.str .x0 offD h3)))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, ite_false,
                       Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp; have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 4 = pcMap (pc + 1)
           have := hPcNext _ _ rfl; simp at this; rw [this, hPcRel]⟩
  | boolop hinstr =>
    -- TAC: x := bexpr → ARM: genBoolExpr ++ [str x0 offD]
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    rename_i x be
    obtain ⟨offD, hD'⟩ := hVarMap x
    -- formalGenInstr = formalGenBoolExpr ++ [str x0 offD]
    have hformal : formalGenInstr vm pcMap (.boolop x be) haltLabel divLabel =
        formalGenBoolExpr vm be ++ (.str .x0 offD :: List.nil) := by
      show (match vm.lookup x with | some offD => _ | none => _) = _
      rw [hD']
    rw [hformal] at hCodeInstr hPcNext
    have hCodeBE := hCodeInstr.append_left
    have hCodeStr := hCodeInstr.append_right
    -- Extract WellTypedBoolExpr from instruction well-typedness
    have hWTbe : WellTypedBoolExpr p.tyCtx be := by
      have hwti := hWT pc hPC_bound
      have heq := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq; rw [← Option.some.inj heq] at hwti
      cases hwti with | boolop _ hbe => exact hbe
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1⟩ :=
      genBoolExpr_correct prog vm be σ s (pcMap pc) hStateRel hScratch hCodeBE hPcRel hVarMap
        p.tyCtx hTS hWTbe
    -- Then str x0, [sp, #offD]
    have hStr := hCodeStr.head; rw [← hPC1] at hStr
    refine ⟨s1.setStack offD (s1.regs .x0) |>.nextPC,
      hSteps1.trans (.single (.str .x0 offD hStr)), ⟨?_, ?_⟩⟩
    · -- StateRel for σ[x ↦ .bool (be.eval σ)]
      intro v off hv
      simp only [ArmState.setStack, ArmState.nextPC]
      by_cases hoff : off = offD
      · subst hoff; simp
        have := hInjective v x off hv hD'; subst this
        rw [Store.update_self, hx0]
        simp [Value.encode]
      · simp [hoff]
        have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
        rw [Store.update_other _ _ _ _ hne]
        exact (hStack1 v off hv).trans (hStateRel v off hv)
    · -- PcRel
      simp only [ArmState.setStack, ArmState.nextPC]
      show s1.pc + 1 = pcMap (pc + 1)
      have := hPcNext _ _ rfl
      simp [List.length_append] at this
      rw [this, hPC1]; omega
  | iftrue hinstr hcond =>
    -- Extract WellTypedBoolExpr before subst (while instr is still accessible)
    have hWTi := hWT pc hPC_bound
    have heq_instr := Prog.getElem?_eq_getElem hPC_bound
    rw [hinstr] at heq_instr
    have hinstr_eq := Option.some.inj heq_instr
    rw [← hinstr_eq] at hWTi
    have hWTbe := match hWTi with | .ifgoto hbe => hbe
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    simp only [formalGenInstr] at hCodeInstr
    have hCodeBE := hCodeInstr.append_left
    have hCodeCbnz := hCodeInstr.append_right
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1⟩ :=
      genBoolExpr_correct prog vm _ σ s (pcMap pc) hStateRel hScratch hCodeBE hPcRel hVarMap
        p.tyCtx hTS hWTbe
    have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
    have hx0_ne : s1.regs .x0 ≠ 0 := by rw [hx0, hcond]; simp
    exact ⟨{ s1 with pc := pcMap _ },
      hSteps1.trans (.single (.cbnz_taken .x0 _ hCbnz hx0_ne)),
      ⟨fun v off hv => (hStack1 v off hv).trans (hStateRel v off hv), rfl⟩⟩
  | iffall hinstr hcond =>
    -- TAC: if cond goto l (not taken) → ARM: genBoolExpr ++ [cbnz x0 (pcMap l)]
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    simp only [formalGenInstr] at hCodeInstr hPcNext
    have hCodeBE := hCodeInstr.append_left
    have hCodeCbnz := hCodeInstr.append_right
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1⟩ :=
      genBoolExpr_correct prog vm _ σ s (pcMap pc) hStateRel hScratch hCodeBE hPcRel hVarMap
        p.tyCtx hTS sorry
    have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
    have hx0_eq : s1.regs .x0 = 0 := by rw [hx0]; simp [hcond]
    refine ⟨s1.nextPC,
      hSteps1.trans (.single (.cbnz_fall .x0 _ hCbnz hx0_eq)),
      ⟨fun v off hv => (hStack1 v off hv).trans (hStateRel v off hv), ?_⟩⟩
    · show s1.pc + 1 = pcMap (pc + 1)
      have := hPcNext _ _ rfl
      simp [List.length_append] at this
      rw [this, hPC1]; omega
  | error hinstr hy hz hs =>
    exact ⟨s, .refl, trivial⟩
  | binop_typeError hinstr hne =>
    exact absurd (.binop_typeError hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)

/-- Main backward simulation: every TAC step is matched by ARM64 steps.
    Directly delegates to `genInstr_correct`. -/
theorem backward_simulation (p : Prog) (armProg : ArmProg)
    (vm : VarMap) (pcMap : Nat → Nat)
    (hWT : WellTypedProg p.tyCtx p)
    (hInjective : VarMapInjective vm)
    (hVarMap : ∀ v, ∃ off, vm.lookup v = some off)
    (hScratch : ScratchSafe vm)
    {pc : Nat} {σ : Store} {cfg' : Cfg} {s : ArmState}
    (hStep : p ⊩ Cfg.run pc σ ⟶ cfg')
    (hRel : SimRel vm pcMap (.run pc σ) s)
    (hTS : TypedStore p.tyCtx σ)
    (hPC : pc < p.size)
    (haltLabel divLabel : Nat)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hCode : CodeAt armProg (pcMap pc) (formalGenInstr vm pcMap instr haltLabel divLabel))
    (hPcNext : ∀ pc' σ', cfg' = .run pc' σ' →
      pcMap pc' = pcMap pc + (formalGenInstr vm pcMap instr haltLabel divLabel).length) :
    ∃ s', ArmSteps armProg s s' ∧ SimRel vm pcMap cfg' s' :=
  genInstr_correct armProg vm pcMap p pc σ s haltLabel divLabel
    instr hInstr hRel hScratch hInjective hWT hTS hPC cfg' hStep hVarMap
    hCode hPcNext
