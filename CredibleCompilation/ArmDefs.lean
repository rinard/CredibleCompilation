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

/-- ARM64 integer registers used by the code generator.
    x0-x2: scratch, x8: array address scratch, x3-x7/x9-x18: allocatable. -/
inductive ArmReg where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18
  deriving Repr, DecidableEq

-- sp is implicit (stack is addressed by offset)
-- x29/x30 are only used in prologue/epilogue (not modeled)

/-- ARM64 floating-point registers used by the code generator.
    d0-d1: scratch, d2-d15: allocatable. -/
inductive ArmFReg where
  | d0  | d1  | d2  | d3  | d4  | d5  | d6  | d7
  | d8  | d9  | d10 | d11 | d12 | d13 | d14 | d15
  deriving Repr, DecidableEq

-- ============================================================
-- § 2. Condition codes and flags
-- ============================================================

/-- ARM64 condition codes used by the code generator. -/
inductive Cond where
  | eq | ne | lt | le
  deriving Repr, DecidableEq

/-- Condition flags set by `cmp`. We store both operands so that
    signed comparison (`slt`/`sle`) is exact for all 64-bit values. -/
structure Flags where
  lhs : BitVec 64
  rhs : BitVec 64
  deriving Repr

/-- Evaluate a condition against the flags. -/
instance : DecidableEq Flags := fun a b =>
  if h1 : a.lhs = b.lhs then
    if h2 : a.rhs = b.rhs then isTrue (by cases a; cases b; simp_all)
    else isFalse (by intro heq; cases heq; exact h2 rfl)
  else isFalse (by intro heq; cases heq; exact h1 rfl)

def Flags.condHolds (f : Flags) : Cond → Bool
  | .eq => f.lhs == f.rhs
  | .ne => f.lhs != f.rhs
  | .lt => BitVec.slt f.lhs f.rhs
  | .le => BitVec.sle f.lhs f.rhs

-- ============================================================
-- § 3. Machine state
-- ============================================================

/-- ARM64 machine state (restricted to the codegen subset). -/
structure ArmState where
  /-- Register file. -/
  regs  : ArmReg → BitVec 64
  /-- Floating-point register file. -/
  fregs : ArmFReg → BitVec 64 := fun _ => 0
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

/-- Update a floating-point register. -/
def ArmState.setFReg (s : ArmState) (r : ArmFReg) (v : BitVec 64) : ArmState :=
  { s with fregs := fun r' => if r' == r then v else s.fregs r' }

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
  /-- `mov Xd, Xn` — register-to-register move. -/
  | movR     : ArmReg → ArmReg → ArmInstr
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
  /-- `cmp Xn, #imm` — compare register with immediate (sets flags). -/
  | cmpImm   : ArmReg → BitVec 64 → ArmInstr
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
  -- Floating-point instructions
  /-- `fmov Dd, Xn` — move integer register to FP register. -/
  | fmovToFP : ArmFReg → ArmReg → ArmInstr
  /-- `ldr Dd, [sp, #off]` — load FP from stack. -/
  | fldr     : ArmFReg → Nat → ArmInstr
  /-- `str Dd, [sp, #off]` — store FP to stack. -/
  | fstr     : ArmFReg → Nat → ArmInstr
  /-- `fadd Dd, Dn, Dm` — FP addition. -/
  | faddR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fsub Dd, Dn, Dm` — FP subtraction. -/
  | fsubR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fmul Dd, Dn, Dm` — FP multiplication. -/
  | fmulR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fdiv Dd, Dn, Dm` — FP division. -/
  | fdivR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fcmp Dn, Dm` — FP compare (sets flags). -/
  | fcmpR    : ArmFReg → ArmFReg → ArmInstr
  /-- `scvtf Dd, Xn` — signed int → FP conversion. -/
  | scvtf    : ArmFReg → ArmReg → ArmInstr
  /-- `fcvtzs Xd, Dn` — FP → signed int conversion. -/
  | fcvtzs   : ArmReg → ArmFReg → ArmInstr
  /-- Load from FP array: `dst ← arrayMem[arr][idxReg]`. -/
  | farrLd   : ArmFReg → ArrayName → ArmReg → ArmInstr
  /-- Store to FP array: `arrayMem[arr][idxReg] ← valFReg`. -/
  | farrSt   : ArrayName → ArmReg → ArmFReg → ArmInstr
  /-- `stp x29, x30, [sp, #-16]!; bl _exp; ldp x29, x30, [sp], #16`
      Abstract: `d0 ← floatExpBv(d0)`, preserves everything else. -/
  | callExp  : ArmInstr
  deriving Repr, DecidableEq

/-- An ARM64 program is an array of instructions. -/
abbrev ArmProg := Array ArmInstr
