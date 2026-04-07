import CredibleCompilation.Core

/-!
# ARM64 Subset Definitions

ARM64 register, instruction, condition, flags, and state definitions
for the code generator subset. Only models the ~18 instructions
actually emitted by `CodeGen.lean`.

Split from `AsmSemantics.lean`.
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
  diff : BitVec 64
  deriving Repr

/-- Evaluate a condition against the flags. -/
instance : DecidableEq Flags := fun a b =>
  if h : a.diff = b.diff then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro heq; cases heq; exact h rfl)

def Flags.condHolds (f : Flags) : Cond → Bool
  | .eq => f.diff == 0
  | .ne => f.diff != 0
  | .lt => f.diff.msb
  | .le => f.diff.msb || f.diff == 0

-- ============================================================
-- § 3. Machine state
-- ============================================================

/-- ARM64 machine state (restricted to the codegen subset). -/
structure ArmState where
  /-- Register file. -/
  regs  : ArmReg → BitVec 64
  /-- Stack memory: maps byte offset from sp to 64-bit value. -/
  stack : Nat → BitVec 64
  /-- Program counter (index into instruction array). -/
  pc    : Nat
  /-- Condition flags from the last `cmp`. -/
  flags : Flags
  /-- Array memory (global, separate from scalar stack). -/
  arrayMem : ArrayMem := fun _ _ => 0

/-- Update a register. -/
def ArmState.setReg (s : ArmState) (r : ArmReg) (v : BitVec 64) : ArmState :=
  { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Update a stack slot. -/
def ArmState.setStack (s : ArmState) (off : Nat) (v : BitVec 64) : ArmState :=
  { s with stack := fun o => if o == off then v else s.stack o }

/-- Update an array memory slot. -/
def ArmState.setArrayMem (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) : ArmState :=
  { s with arrayMem := fun a i => if a == arr && i == idx then v else s.arrayMem a i }

/-- Advance PC by 1. -/
def ArmState.nextPC (s : ArmState) : ArmState :=
  { s with pc := s.pc + 1 }

-- ============================================================
-- § 4. ARM64 instructions
-- ============================================================

/-- ARM64 instructions used by the code generator. -/
inductive ArmInstr where
  /-- `mov Xd, #imm` — load immediate (small, fits in 16 bits). -/
  | mov      : ArmReg → BitVec 64 → ArmInstr
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
  | andImm   : ArmReg → ArmReg → BitVec 64 → ArmInstr
  /-- `and Wd, Wn, Wm` — bitwise AND registers. -/
  | andR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `eor Wd, Wn, #imm` — exclusive OR with immediate. -/
  | eorImm   : ArmReg → ArmReg → BitVec 64 → ArmInstr
  /-- `orr Wd, Wn, Wm` — bitwise OR registers. -/
  | orrR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `b label` — unconditional branch. -/
  | b        : Nat → ArmInstr
  /-- Load from global array: `dst ← arrayMem[arr][idxReg]`. -/
  | arrLd    : ArmReg → ArrayName → ArmReg → ArmInstr
  /-- Store to global array: `arrayMem[arr][idxReg] ← valReg`. -/
  | arrSt    : ArrayName → ArmReg → ArmReg → ArmInstr
  deriving Repr, DecidableEq

/-- An ARM64 program is an array of instructions. -/
abbrev ArmProg := Array ArmInstr
