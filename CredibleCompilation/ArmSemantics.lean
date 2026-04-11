import CredibleCompilation.Semantics
import CredibleCompilation.ArmDefs

/-!
# ARM64 Subset Semantics

Small-step semantics, value encoding/decoding, state relation,
formal instruction generation, CodeAt and simp lemmas.

Split from `AsmSemantics.lean`.
-/

-- ============================================================
-- § 5. Small-step semantics
-- ============================================================

/-- Insert a 16-bit value at a given shift position, keeping other bits. -/
def insertBits (val : BitVec 64) (imm16 : UInt64) (shift : Nat) : BitVec 64 :=
  let imm16bv : BitVec 64 := BitVec.ofNat 64 imm16.toNat
  let mask : BitVec 64 := 0xFFFF#64 <<< shift
  let imm : BitVec 64 := imm16bv <<< shift
  (val &&& ~~~mask) ||| imm

/-- Small-step semantics for the ARM64 subset. -/
inductive ArmStep (prog : ArmProg) : ArmState → ArmState → Prop where

  | mov (rd : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.mov rd imm) →
    ArmStep prog s (s.setReg rd imm |>.nextPC)

  | movz (rd : ArmReg) (imm16 : UInt64) (shift : Nat) :
    prog[s.pc]? = some (.movz rd imm16 shift) →
    ArmStep prog s (s.setReg rd (BitVec.ofNat 64 (imm16 <<< shift.toUInt64).toNat) |>.nextPC)

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
    ArmStep prog s (s.setReg rd (BitVec.sdiv (s.regs rn) (s.regs rm)) |>.nextPC)

  | cmpRR (rn rm : ArmReg) :
    prog[s.pc]? = some (.cmp rn rm) →
    ArmStep prog s ({ s with flags := Flags.mk (s.regs rn) (s.regs rm), pc := s.pc + 1 })

  | cmpRI (rn : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.cmpImm rn imm) →
    ArmStep prog s ({ s with flags := Flags.mk (s.regs rn) imm, pc := s.pc + 1 })

  | cset (rd : ArmReg) (c : Cond) :
    prog[s.pc]? = some (.cset rd c) →
    ArmStep prog s (s.setReg rd (if s.flags.condHolds c then (1 : BitVec 64) else 0) |>.nextPC)

  | cbz_taken (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbz rn lbl) →
    s.regs rn = (0 : BitVec 64) →
    ArmStep prog s { s with pc := lbl }

  | cbz_fall (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbz rn lbl) →
    s.regs rn ≠ (0 : BitVec 64) →
    ArmStep prog s s.nextPC

  | cbnz_taken (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbnz rn lbl) →
    s.regs rn ≠ (0 : BitVec 64) →
    ArmStep prog s { s with pc := lbl }

  | cbnz_fall (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbnz rn lbl) →
    s.regs rn = (0 : BitVec 64) →
    ArmStep prog s s.nextPC

  | andImm (rd rn : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.andImm rd rn imm) →
    ArmStep prog s (s.setReg rd (s.regs rn &&& imm) |>.nextPC)

  | andR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.andR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn &&& s.regs rm) |>.nextPC)

  | eorImm (rd rn : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.eorImm rd rn imm) →
    ArmStep prog s (s.setReg rd (s.regs rn ^^^ imm) |>.nextPC)

  | orrR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.orrR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn ||| s.regs rm) |>.nextPC)

  | branch (lbl : Nat) :
    prog[s.pc]? = some (.b lbl) →
    ArmStep prog s { s with pc := lbl }

  | arrLd (dst : ArmReg) (arr : ArrayName) (idxReg : ArmReg) :
    prog[s.pc]? = some (.arrLd dst arr idxReg) →
    ArmStep prog s (s.setReg dst (s.arrayMem arr (s.regs idxReg)) |>.nextPC)

  | arrSt (arr : ArrayName) (idxReg valReg : ArmReg) :
    prog[s.pc]? = some (.arrSt arr idxReg valReg) →
    ArmStep prog s (s.setArrayMem arr (s.regs idxReg) (s.regs valReg) |>.nextPC)

  -- Floating-point instructions

  | fmovToFP (fd : ArmFReg) (rn : ArmReg) :
    prog[s.pc]? = some (.fmovToFP fd rn) →
    ArmStep prog s (s.setFReg fd (s.regs rn) |>.nextPC)

  | fldr (fd : ArmFReg) (off : Nat) :
    prog[s.pc]? = some (.fldr fd off) →
    ArmStep prog s (s.setFReg fd (s.stack off) |>.nextPC)

  | fstr (fs : ArmFReg) (off : Nat) :
    prog[s.pc]? = some (.fstr fs off) →
    ArmStep prog s (s.setStack off (s.fregs fs) |>.nextPC)

  | faddR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.faddR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fsubR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fsubR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fmulR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fmulR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fdivR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fdivR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fdiv (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fcmpRR (fn fm : ArmFReg) :
    prog[s.pc]? = some (.fcmpR fn fm) →
    ArmStep prog s ({ s with flags := Flags.mk (s.fregs fn) (s.fregs fm), pc := s.pc + 1 })

  | scvtf (fd : ArmFReg) (rn : ArmReg) :
    prog[s.pc]? = some (.scvtf fd rn) →
    ArmStep prog s (s.setFReg fd (intToFloatBv (s.regs rn)) |>.nextPC)

  | fcvtzs (rd : ArmReg) (fn : ArmFReg) :
    prog[s.pc]? = some (.fcvtzs rd fn) →
    ArmStep prog s (s.setReg rd (floatToIntBv (s.fregs fn)) |>.nextPC)

  | farrLd (fd : ArmFReg) (arr : ArrayName) (idxReg : ArmReg) :
    prog[s.pc]? = some (.farrLd fd arr idxReg) →
    ArmStep prog s (s.setFReg fd (s.arrayMem arr (s.regs idxReg)) |>.nextPC)

  | farrSt (arr : ArrayName) (idxReg : ArmReg) (valFReg : ArmFReg) :
    prog[s.pc]? = some (.farrSt arr idxReg valFReg) →
    ArmStep prog s (s.setArrayMem arr (s.regs idxReg) (s.fregs valFReg) |>.nextPC)

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

/-- Encode a TAC `Value` as a 64-bit bitvector for the ARM64 representation.
    Since `Value.int` now carries `BitVec 64`, encoding is the identity for ints. -/
def Value.encode : Value → BitVec 64
  | .int n  => n
  | .bool b => if b then 1 else 0
  | .float f => f

/-- Decode a 64-bit bitvector back to a `Value` given its type. -/
def Value.decode (ty : VarTy) (bv : BitVec 64) : Value :=
  match ty with
  | .int  => .int bv
  | .bool => .bool (bv != 0)
  | .float => .float bv

/-- For integer values, encode produces toInt. -/
theorem Value.encode_eq_toInt_of_int {v : Value} (h : ∃ n, v = .int n) :
    v.encode = v.toInt := by
  obtain ⟨n, rfl⟩ := h; rfl

/-- For any value, encode of an integer. -/
@[simp] theorem Value.encode_int (n : BitVec 64) : (Value.int n).encode = n := rfl

theorem Value.encode_decode_int (n : BitVec 64) :
    Value.decode .int (Value.encode (.int n)) = .int n := rfl

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


/-- If a BitVec 64 is nonzero as a BitVec, it is nonzero. (Trivial but useful for readability.) -/
theorem BitVec_ne_zero {b : BitVec 64} (hb : b ≠ 0) : b ≠ 0 := hb

/-- The VarMap is injective: distinct variables have distinct offsets. -/
def VarMapInjective (vm : VarMap) : Prop :=
  ∀ v1 v2 off, vm.lookup v1 = some off → vm.lookup v2 = some off → v1 = v2

/-- PC correspondence: TAC PC maps to ARM PC. -/
def PcRel (pcMap : Nat → Nat) (tac_pc : Nat) (arm_pc : Nat) : Prop :=
  arm_pc = pcMap tac_pc

/-- Full simulation invariant. -/
def SimRel (vm : VarMap) (pcMap : Nat → Nat) (tac_cfg : Cfg) (arm : ArmState) : Prop :=
  match tac_cfg with
  | .run pc σ am    => StateRel vm σ arm ∧ PcRel pcMap pc arm.pc ∧ arm.arrayMem = am
  | .halt σ am      => StateRel vm σ arm ∧ arm.arrayMem = am
  | .error _ _      => True
  | .typeError _ _  => False

-- ============================================================
-- § 8. Formal instruction generation
-- ============================================================

/-- Generate formal ARM64 instructions for loading an immediate.
    Mirrors `loadImm64` in CodeGen.lean. -/
def formalLoadImm64 (rd : ArmReg) (n : BitVec 64) : List ArmInstr :=
  if n.toNat < 65536 then
    -- Small: single mov
    [.mov rd n]
  else
    -- Large: movz/movk sequence
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
  | .lit b =>
    [.mov .x0 (if b then (1 : BitVec 64) else 0)]
  | .bvar v =>
    match vm.lookup v with
    | some off => [.ldr .x0 off, .andImm .x0 .x0 (1 : BitVec 64)]
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
    formalGenBoolExpr vm e ++ [.eorImm .x0 .x0 (1 : BitVec 64)]
  | .fcmp fop lv rv =>
    let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
    match vm.lookup lv, vm.lookup rv with
    | some offL, some offR =>
      [.fldr .d1 offL, .fldr .d2 offR, .fcmpR .d1 .d2, .cset .x0 cond]
    | _, _ => []

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
    | some off => [.mov .x0 (if b then (1 : BitVec 64) else 0), .str .x0 off]
    | none => []
  | .const v (.float f) =>
    match vm.lookup v with
    | some off => formalLoadImm64 .x0 f ++ [.str .x0 off]
    | none => []
  | .copy dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD => [.ldr .x0 offS, .str .x0 offD]
    | _, _ => []
  | .binop dst op lv rv =>
    match vm.lookup lv, vm.lookup rv, vm.lookup dst with
    | some offL, some offR, some offD =>
      let opInstr := match op with
        | .add => [ArmInstr.addR .x0 .x1 .x2]
        | .sub => [.subR .x0 .x1 .x2]
        | .mul => [.mulR .x0 .x1 .x2]
        | .div => [.sdivR .x0 .x1 .x2]
        | .mod => [.sdivR .x0 .x1 .x2, .mulR .x0 .x0 .x2, .subR .x0 .x1 .x0]
      if op == .div || op == .mod then
        [.ldr .x2 offR, .cbz .x2 divLabel,
         .ldr .x1 offL, .ldr .x2 offR] ++ opInstr ++ [.str .x0 offD]
      else
        [.ldr .x1 offL, .ldr .x2 offR] ++ opInstr ++ [.str .x0 offD]
    | _, _, _ => []
  | .boolop dst be =>
    match vm.lookup dst with
    | some offD => formalGenBoolExpr vm be ++ [.str .x0 offD]
    | none => []
  | .goto l => [.b (pcMap l)]
  | .ifgoto be l =>
    formalGenBoolExpr vm be ++ [.cbnz .x0 (pcMap l)]
  | .halt => [.b haltLabel]
  | .arrLoad x arr idx ty =>
    match vm.lookup idx, vm.lookup x with
    | some offIdx, some offX =>
      match ty with
      | .float => [.ldr .x1 offIdx, .farrLd .d0 arr .x1, .fstr .d0 offX]
      | .bool  => [.ldr .x1 offIdx, .arrLd .x0 arr .x1, .cmpImm .x0 0, .cset .x0 .ne, .str .x0 offX]
      | .int   => [.ldr .x1 offIdx, .arrLd .x0 arr .x1, .str .x0 offX]
    | _, _ => []
  | .arrStore arr idx val ty =>
    match vm.lookup idx, vm.lookup val with
    | some offIdx, some offVal =>
      if ty == .float then
        [.ldr .x1 offIdx, .fldr .d0 offVal, .farrSt arr .x1 .d0]
      else
        [.ldr .x1 offIdx, .ldr .x2 offVal, .arrSt arr .x1 .x2]
    | _, _ => []
  | .fbinop dst fop lv rv =>
    let fpInstr := match fop with
      | .fadd => ArmInstr.faddR .d0 .d1 .d2
      | .fsub => .fsubR .d0 .d1 .d2
      | .fmul => .fmulR .d0 .d1 .d2
      | .fdiv => .fdivR .d0 .d1 .d2
    match vm.lookup lv, vm.lookup rv, vm.lookup dst with
    | some offL, some offR, some offD =>
      [.fldr .d1 offL, .fldr .d2 offR, fpInstr, .fstr .d0 offD]
    | _, _, _ => []
  | .intToFloat dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD =>
      [.ldr .x0 offS, .scvtf .d0 .x0, .fstr .d0 offD]
    | _, _ => []
  | .floatToInt dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD =>
      [.fldr .d0 offS, .fcvtzs .x0 .d0, .str .x0 offD]
    | _, _ => []
  | .floatExp _dst _src => []

-- ============================================================
-- § 9. CodeAt and helper lemmas
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
@[simp] theorem ArmState.setReg_stack (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).stack = s.stack := rfl

-- nextPC preserves stack and regs
@[simp] theorem ArmState.nextPC_stack (s : ArmState) :
    s.nextPC.stack = s.stack := rfl

@[simp] theorem ArmState.nextPC_regs (s : ArmState) :
    s.nextPC.regs = s.regs := rfl

@[simp] theorem ArmState.nextPC_pc (s : ArmState) :
    s.nextPC.pc = s.pc + 1 := rfl

-- setReg reads
@[simp] theorem ArmState.setReg_regs_same (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).regs r = v := by
  simp [setReg]

@[simp] theorem ArmState.setReg_regs_other (s : ArmState) (r r' : ArmReg) (v : BitVec 64) (h : r' ≠ r) :
    (s.setReg r v).regs r' = s.regs r' := by
  simp [setReg, h]

@[simp] theorem ArmState.setReg_pc (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).pc = s.pc := rfl

@[simp] theorem ArmState.setReg_flags (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).flags = s.flags := rfl

@[simp] theorem ArmState.nextPC_flags (s : ArmState) :
    s.nextPC.flags = s.flags := rfl

-- arrayMem preservation
@[simp] theorem ArmState.setReg_arrayMem (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).arrayMem = s.arrayMem := rfl

@[simp] theorem ArmState.nextPC_arrayMem (s : ArmState) :
    s.nextPC.arrayMem = s.arrayMem := rfl

@[simp] theorem ArmState.setStack_arrayMem (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).arrayMem = s.arrayMem := rfl

-- setArrayMem preserves stack, regs, pc, flags
@[simp] theorem ArmState.setArrayMem_stack (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).stack = s.stack := rfl

@[simp] theorem ArmState.setArrayMem_regs (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).regs = s.regs := rfl

@[simp] theorem ArmState.setArrayMem_pc (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).pc = s.pc := rfl

@[simp] theorem ArmState.setArrayMem_flags (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).flags = s.flags := rfl

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
