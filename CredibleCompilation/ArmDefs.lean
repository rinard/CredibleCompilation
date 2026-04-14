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
    x0-x2: scratch, x8: array address scratch, x3-x7/x9-x15: caller-saved allocatable,
    x16-x17: linker scratch (IP0/IP1), x18: platform-reserved,
    x19-x28: callee-saved allocatable (must be saved/restored in prologue/epilogue). -/
inductive ArmReg where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18
  | x19 | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28
  deriving Repr, DecidableEq

-- sp is implicit (stack is addressed by offset)
-- x29/x30 are only used in prologue/epilogue (not modeled)

/-- Convert a register number to an ArmReg. -/
def ArmReg.fromRegNum : Nat → ArmReg
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3
  | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7
  | 8 => .x8 | 9 => .x9 | 10 => .x10 | 11 => .x11
  | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15
  | 16 => .x16 | 17 => .x17 | 18 => .x18
  | 19 => .x19 | 20 => .x20 | 21 => .x21 | 22 => .x22
  | 23 => .x23 | 24 => .x24 | 25 => .x25 | 26 => .x26
  | 27 => .x27 | 28 => .x28
  | _ => .x0  -- fallback

/-- Convert an ArmReg to its register number. -/
def ArmReg.toNat : ArmReg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3
  | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18
  | .x19 => 19 | .x20 => 20 | .x21 => 21 | .x22 => 22
  | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26
  | .x27 => 27 | .x28 => 28

/-- ARM64 floating-point registers used by the code generator.
    d0-d1: scratch, d2-d15: allocatable. -/
inductive ArmFReg where
  | d0  | d1  | d2  | d3  | d4  | d5  | d6  | d7
  | d8  | d9  | d10 | d11 | d12 | d13 | d14 | d15
  deriving Repr, DecidableEq

/-- Convert a register number to an ArmFReg. -/
def ArmFReg.fromRegNum : Nat → ArmFReg
  | 0 => .d0 | 1 => .d1 | 2 => .d2 | 3 => .d3
  | 4 => .d4 | 5 => .d5 | 6 => .d6 | 7 => .d7
  | 8 => .d8 | 9 => .d9 | 10 => .d10 | 11 => .d11
  | 12 => .d12 | 13 => .d13 | 14 => .d14 | 15 => .d15
  | _ => .d0  -- fallback

/-- Convert an ArmFReg to its register number. -/
def ArmFReg.toNat : ArmFReg → Nat
  | .d0 => 0 | .d1 => 1 | .d2 => 2 | .d3 => 3
  | .d4 => 4 | .d5 => 5 | .d6 => 6 | .d7 => 7
  | .d8 => 8 | .d9 => 9 | .d10 => 10 | .d11 => 11
  | .d12 => 12 | .d13 => 13 | .d14 => 14 | .d15 => 15

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

/-- True for caller-saved integer registers: x0-x15, x18 (platform).
    Callee-saved: x19-x28.  Linker scratch x16-x17 are also caller-saved. -/
def ArmReg.isCallerSaved : ArmReg → Bool
  | .x0 | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7
  | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15
  | .x16 | .x17 | .x18 => true
  | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28 => false

/-- True for caller-saved FP registers: d0-d7.
    Callee-saved: d8-d15. -/
def ArmFReg.isCallerSaved : ArmFReg → Bool
  | .d0 | .d1 | .d2 | .d3 | .d4 | .d5 | .d6 | .d7 => true
  | .d8 | .d9 | .d10 | .d11 | .d12 | .d13 | .d14 | .d15 => false

/-- Havoc all caller-saved registers (set to 0).
    Models the effect of a library call on registers not preserved by the callee. -/
def ArmState.havocCallerSaved (s : ArmState) : ArmState :=
  { s with
    regs := fun r => if r.isCallerSaved then 0 else s.regs r
    fregs := fun r => if r.isCallerSaved then 0 else s.fregs r }

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
  /-- `eor Xd, Xn, Xm` — bitwise XOR registers. -/
  | eorR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `lsl Xd, Xn, Xm` — logical shift left (register). -/
  | lslR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `asr Xd, Xn, Xm` — arithmetic shift right (register). -/
  | asrR     : ArmReg → ArmReg → ArmReg → ArmInstr
  /-- `b label` — unconditional branch. -/
  | b        : Nat → ArmInstr
  /-- Load from global array: `dst ← arrayMem[arr][idxReg]`. -/
  | arrLd    : ArmReg → ArrayName → ArmReg → ArmInstr
  /-- Store to global array: `arrayMem[arr][idxReg] ← valReg`. -/
  | arrSt    : ArrayName → ArmReg → ArmReg → ArmInstr
  -- Floating-point instructions
  /-- `fmov Dd, Xn` — move integer register to FP register. -/
  | fmovToFP : ArmFReg → ArmReg → ArmInstr
  /-- `fmov Dd, Dn` — move FP register to FP register. -/
  | fmovRR   : ArmFReg → ArmFReg → ArmInstr
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
  /-- `fminnm Dd, Dn, Dm` — FP minimum (IEEE 754-2008). -/
  | fminR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- `fmaxnm Dd, Dn, Dm` — FP maximum (IEEE 754-2008). -/
  | fmaxR    : ArmFReg → ArmFReg → ArmFReg → ArmInstr
  /-- Binary FP library call: `d0 ← op(d0, d1)`. For pow, etc. -/
  | callBinF : FloatBinOp → ArmFReg → ArmFReg → ArmFReg → ArmInstr
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
  /-- Float unary intrinsic: library call or native instruction.
      Abstract: `fd ← op.eval(fn)`, preserves everything else. -/
  | floatUnaryInstr : FloatUnaryOp → ArmFReg → ArmFReg → ArmInstr
  deriving Repr, DecidableEq

/-- An ARM64 program is an array of instructions. -/
abbrev ArmProg := Array ArmInstr
