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
  if -65536 < n && n < 65536 then
    [.mov rd n]
  else
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
partial def formalGenBoolExpr (vm : VarMap) (be : BoolExpr) : List ArmInstr :=
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
  | .and a b =>
    formalGenBoolExpr vm a ++ [.str .x0 0] ++
    formalGenBoolExpr vm b ++ [.ldr .x1 0, .andR .x0 .x0 .x1]
  | .or a b =>
    formalGenBoolExpr vm a ++ [.str .x0 0] ++
    formalGenBoolExpr vm b ++ [.ldr .x1 0, .orrR .x0 .x0 .x1]

/-- Generate formal ARM64 instructions for a TAC instruction.
    Mirrors `genInstr` in CodeGen.lean (without the label string). -/
def formalGenInstr (vm : VarMap) (instr : TAC) (haltLabel : Nat) (divLabel : Nat)
    : List ArmInstr :=
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
  | .goto l => [.b l]
  | .ifgoto be l =>
    formalGenBoolExpr vm be ++ [.cbnz .x0 l]
  | .halt => [.b haltLabel]

-- ============================================================
-- § 9. Correctness lemmas (stubs)
-- ============================================================

/-- A code segment is embedded in the program starting at a given PC. -/
def CodeAt (prog : ArmProg) (startPC : Nat) (instrs : List ArmInstr) : Prop :=
  ∀ i, (h : i < instrs.length) →
    prog[startPC + i]? = some instrs[i]

theorem loadImm64_correct (prog : ArmProg) (rd : ArmReg) (n : Int)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs rd = n ∧
      s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length := by
  sorry

/-- `genBoolExpr` correctly evaluates a boolean expression into x0. -/
theorem genBoolExpr_correct (prog : ArmProg) (vm : VarMap)
    (be : BoolExpr) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : StateRel vm σ s)
    (hScratch : ScratchSafe vm)
    (hCode : CodeAt prog startPC (formalGenBoolExpr vm be))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs .x0 = (if be.eval σ then (1 : Int) else 0) ∧
      (∀ v off, vm.lookup v = some off → s'.stack off = s.stack off) ∧
      s'.pc = startPC + (formalGenBoolExpr vm be).length := by
  sorry

/-- Single TAC instruction backward simulation. -/
theorem genInstr_correct (prog : ArmProg) (vm : VarMap) (pcMap : Nat → Nat)
    (p : Prog) (pc : Nat) (σ : Store) (s : ArmState)
    (haltLabel divLabel : Nat)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hRel : SimRel vm pcMap (.run pc σ) s)
    (hScratch : ScratchSafe vm)
    (cfg' : Cfg) (hStep : p ⊩ Cfg.run pc σ ⟶ cfg') :
    ∃ s', ArmSteps prog s s' ∧ SimRel vm pcMap cfg' s' := by
  sorry

/-- Main backward simulation: every TAC step is matched by ARM64 steps. -/
theorem backward_simulation (p : Prog) (armProg : ArmProg)
    (vm : VarMap) (pcMap : Nat → Nat) (Γ : TyCtx)
    (hWT : WellTypedProg Γ p)
    (cfg cfg' : Cfg) (s : ArmState)
    (hStep : p ⊩ cfg ⟶ cfg')
    (hRel : SimRel vm pcMap cfg s)
    (hScratch : ScratchSafe vm) :
    ∃ s', ArmSteps armProg s s' ∧ SimRel vm pcMap cfg' s' := by
  sorry
