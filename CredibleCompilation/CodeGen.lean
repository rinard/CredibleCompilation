import CredibleCompilation.WhileLang
import CredibleCompilation.Parser
import CredibleCompilation.ConstPropOpt
import CredibleCompilation.CSEOpt
import CredibleCompilation.LICMOpt
import CredibleCompilation.ConstHoistOpt
import CredibleCompilation.DAEOpt
import CredibleCompilation.DCEOpt
import CredibleCompilation.PeepholeOpt
import CredibleCompilation.RegAllocOpt
import CredibleCompilation.ExecChecker
import CredibleCompilation.BoundsOpt
import CredibleCompilation.ArmSemantics
import CredibleCompilation.ArmCorrectness
import CredibleCompilation.PropChecker

/-!
# ARM64 Code Generator for TAC Programs

Translates a type-checked `Prog` to ARM64 assembly (macOS AArch64).
Rejects programs that don't type-check.

## Design

- Variables are stored on the stack, indexed by a string→offset map.
- Integers are 64-bit signed (x registers).
- Booleans are stored as 0/1 in 64-bit slots.
- Observable variables are printed at halt via `_printf`.
- Division by zero calls `_exit(1)`.
-/

-- ============================================================
-- § 1. Variable layout
-- ============================================================

/-- Assign stack offsets to all variables that appear in the program. -/
private def collectVars (p : Prog) : List Var :=
  let vars := p.code.foldl (fun acc instr =>
    match instr with
    | .const x _       => if acc.contains x then acc else acc ++ [x]
    | .copy x y        => let a := if acc.contains x then acc else acc ++ [x]
                          if a.contains y then a else a ++ [y]
    | .binop x _ y z   => let a := if acc.contains x then acc else acc ++ [x]
                          let b := if a.contains y then a else a ++ [y]
                          if b.contains z then b else b ++ [z]
    | .boolop x _      => if acc.contains x then acc else acc ++ [x]
    | .arrLoad x _ idx _ => let a := if acc.contains x then acc else acc ++ [x]
                            if a.contains idx then a else a ++ [idx]
    | .arrStore _ idx val _ => let a := if acc.contains idx then acc else acc ++ [idx]
                               if a.contains val then a else a ++ [val]
    | .fbinop x _ y z  => let a := if acc.contains x then acc else acc ++ [x]
                          let b := if a.contains y then a else a ++ [y]
                          if b.contains z then b else b ++ [z]
    | .intToFloat x y  => let a := if acc.contains x then acc else acc ++ [x]
                          if a.contains y then a else a ++ [y]
    | .floatToInt x y  => let a := if acc.contains x then acc else acc ++ [x]
                          if a.contains y then a else a ++ [y]
    | .floatExp x y    => let a := if acc.contains x then acc else acc ++ [x]
                          if a.contains y then a else a ++ [y]
    | .floatSqrt x y   => let a := if acc.contains x then acc else acc ++ [x]
                          if a.contains y then a else a ++ [y]
    | .goto _          => acc
    | .ifgoto _ _      => acc
    | .halt            => acc
  ) ([] : List Var)
  -- Also add observable variables
  p.observable.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) vars

private def buildVarMap (vars : List Var) : List (Var × Nat) :=
  (List.range vars.length).zip vars |>.map fun (i, v) => (v, (i + 1) * 8)

private def lookupVar (varMap : List (Var × Nat)) (v : Var) : Option Nat :=
  varMap.find? (fun (x, _) => x == v) |>.map Prod.snd

/-- Collect all distinct array names used in arrLoad/arrStore instructions. -/
private def collectArrays (p : Prog) : List String :=
  p.code.foldl (fun acc instr =>
    match instr with
    | .arrLoad _ arr _ _   => if acc.contains arr then acc else acc ++ [arr]
    | .arrStore arr _ _ _  => if acc.contains arr then acc else acc ++ [arr]
    | _                  => acc
  ) ([] : List String)

-- ============================================================
-- § 2. Assembly emission helpers
-- ============================================================

private def emit (lines : List String) : String :=
  String.intercalate "\n" lines

/-- Load/store a stack variable (used only in prologue/epilogue/printf code). -/
private def loadVar (varMap : List (Var × Nat)) (v : Var) (reg : String) : String :=
  match lookupVar varMap v with
  | some off => s!"  ldr {reg}, [sp, #{off}]"
  | none => s!"  // ERROR: unknown variable {v}"

private def storeVar (varMap : List (Var × Nat)) (v : Var) (reg : String) : String :=
  match lookupVar varMap v with
  | some off => s!"  str {reg}, [sp, #{off}]"
  | none => s!"  // ERROR: unknown variable {v}"

private def loadVarFP (varMap : List (Var × Nat)) (v : Var) (freg : String) : String :=
  match lookupVar varMap v with
  | some off => s!"  ldr {freg}, [sp, #{off}]"
  | none => s!"  // ERROR: unknown variable {v}"

-- ============================================================
-- § 2a. ArmInstr pretty-printer
-- ============================================================

private def ppReg : ArmReg → String
  | .x0 => "x0" | .x1 => "x1" | .x2 => "x2" | .x3 => "x3"
  | .x4 => "x4" | .x5 => "x5" | .x6 => "x6" | .x7 => "x7"
  | .x8 => "x8" | .x9 => "x9" | .x10 => "x10" | .x11 => "x11"
  | .x12 => "x12" | .x13 => "x13" | .x14 => "x14" | .x15 => "x15"
  | .x16 => "x16" | .x17 => "x17" | .x18 => "x18"

private def ppFReg : ArmFReg → String
  | .d0 => "d0" | .d1 => "d1" | .d2 => "d2" | .d3 => "d3"
  | .d4 => "d4" | .d5 => "d5" | .d6 => "d6" | .d7 => "d7"
  | .d8 => "d8" | .d9 => "d9" | .d10 => "d10" | .d11 => "d11"
  | .d12 => "d12" | .d13 => "d13" | .d14 => "d14" | .d15 => "d15"

private def ppCond : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"

/-- Map float-comparison condition codes to ARM64 mnemonics.
    After `fcmp`, ARM64 uses `mi` (minus) for less-than and `ls` (lower or same)
    for less-or-equal, unlike integer `cmp` which uses `lt`/`le`. -/
private def ppCondFloat : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "mi" | .le => "ls"

/-- Resolve a branch target (Nat) to a label string.
    Sentinel values map to special labels; others are reverse-mapped from
    ARM PC offsets back to TAC PC labels. -/
private def ppLabel (haltS divS boundsS : Nat) (tacPcOf : Nat → Option Nat)
    (target : Nat) : String :=
  if target == haltS then ".Lhalt"
  else if target == divS then ".Ldiv_by_zero"
  else if target == boundsS then ".Lbounds_err"
  else match tacPcOf target with
    | some tacPC => s!".L{tacPC}"
    | none => s!".Larm{target}"

/-- Pretty-print a single ArmInstr to one or more assembly lines.
    `afterFcmp` indicates the preceding instruction was `fcmpR`, so
    condition codes for `cset` use the float convention. -/
private def ppInstr (lbl : Nat → String) (afterFcmp : Bool) (instr : ArmInstr) : List String :=
  match instr with
  | .mov rd n =>
    [s!"  mov {ppReg rd}, #{n.toInt}"]
  | .movR rd rn =>
    if rd == rn then [] else [s!"  mov {ppReg rd}, {ppReg rn}"]
  | .movz rd imm16 shift =>
    if shift == 0 then [s!"  movz {ppReg rd}, #{imm16}"]
    else [s!"  movz {ppReg rd}, #{imm16}, lsl #{shift}"]
  | .movk rd imm16 shift =>
    [s!"  movk {ppReg rd}, #{imm16}, lsl #{shift}"]
  | .ldr rd off =>
    [s!"  ldr {ppReg rd}, [sp, #{off}]"]
  | .str rs off =>
    [s!"  str {ppReg rs}, [sp, #{off}]"]
  | .addR rd rn rm =>
    [s!"  add {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .subR rd rn rm =>
    [s!"  sub {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .mulR rd rn rm =>
    [s!"  mul {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .sdivR rd rn rm =>
    [s!"  sdiv {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .cmp rn rm =>
    [s!"  cmp {ppReg rn}, {ppReg rm}"]
  | .cmpImm rn imm =>
    if imm.toInt ≤ 4095 then
      [s!"  cmp {ppReg rn}, #{imm.toInt}"]
    else
      -- Large immediate: load into x0, then compare with register
      [s!"  mov x0, #{imm.toInt}", s!"  cmp {ppReg rn}, x0"]
  | .cset _rd c =>
    [s!"  cset w0, {if afterFcmp then ppCondFloat c else ppCond c}"]
  | .cbz rn target =>
    [s!"  cbz {ppReg rn}, {lbl target}"]
  | .cbnz _rn target =>
    [s!"  cbnz w0, {lbl target}"]
  | .andImm _rd _rn imm =>
    [s!"  and w0, w0, #{imm.toInt}"]
  | .andR rd rn rm =>
    [s!"  and {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .eorImm _rd _rn imm =>
    [s!"  eor w0, w0, #{imm.toInt}"]
  | .orrR rd rn rm =>
    [s!"  orr {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .b target =>
    [s!"  b {lbl target}"]
  | .arrLd dst arr idxReg =>
    [s!"  adrp x8, _arr_{arr}@PAGE",
     s!"  add x8, x8, _arr_{arr}@PAGEOFF",
     s!"  ldr {ppReg dst}, [x8, {ppReg idxReg}, lsl #3]"]
  | .arrSt arr idxReg valReg =>
    [s!"  adrp x8, _arr_{arr}@PAGE",
     s!"  add x8, x8, _arr_{arr}@PAGEOFF",
     s!"  str {ppReg valReg}, [x8, {ppReg idxReg}, lsl #3]"]
  | .fmovToFP fd rn =>
    [s!"  fmov {ppFReg fd}, {ppReg rn}"]
  | .fmovRR fd fn =>
    if fd == fn then [] else [s!"  fmov {ppFReg fd}, {ppFReg fn}"]
  | .fldr fd off =>
    [s!"  ldr {ppFReg fd}, [sp, #{off}]"]
  | .fstr fs off =>
    [s!"  str {ppFReg fs}, [sp, #{off}]"]
  | .faddR fd fn fm =>
    [s!"  fadd {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fsubR fd fn fm =>
    [s!"  fsub {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fmulR fd fn fm =>
    [s!"  fmul {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fdivR fd fn fm =>
    [s!"  fdiv {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fcmpR fn fm =>
    [s!"  fcmp {ppFReg fn}, {ppFReg fm}"]
  | .scvtf fd rn =>
    [s!"  scvtf {ppFReg fd}, {ppReg rn}"]
  | .fcvtzs rd fn =>
    [s!"  fcvtzs {ppReg rd}, {ppFReg fn}"]
  | .farrLd fd arr idxReg =>
    [s!"  adrp x8, _arr_{arr}@PAGE",
     s!"  add x8, x8, _arr_{arr}@PAGEOFF",
     s!"  ldr {ppFReg fd}, [x8, {ppReg idxReg}, lsl #3]"]
  | .farrSt arr idxReg fs =>
    [s!"  adrp x8, _arr_{arr}@PAGE",
     s!"  add x8, x8, _arr_{arr}@PAGEOFF",
     s!"  str {ppFReg fs}, [x8, {ppReg idxReg}, lsl #3]"]
  | .callExp fd fn =>
    let load := if fn == .d0 then [] else [s!"  fmov d0, {ppFReg fn}"]
    let store := if fd == .d0 then [] else [s!"  fmov {ppFReg fd}, d0"]
    load ++ ["  stp x29, x30, [sp, #-16]!", "  bl _exp",
             "  ldp x29, x30, [sp], #16"] ++ store
  | .fsqrt fd fn =>
    [s!"  fsqrt {ppFReg fd}, {ppFReg fn}"]

/-- Pretty-print a list of ArmInstr, tracking fcmp state for cset. -/
private def ppInstrs (lbl : Nat → String) : List ArmInstr → List String
  | [] => []
  | instr :: rest =>
    let afterFcmp := match instr with | .fcmpR .. => true | _ => false
    let lines := ppInstr lbl false instr
    let restLines := ppInstrsAux lbl afterFcmp rest
    lines ++ restLines
where
  ppInstrsAux (lbl : Nat → String) (prevWasFcmp : Bool) : List ArmInstr → List String
    | [] => []
    | instr :: rest =>
      let lines := ppInstr lbl prevWasFcmp instr
      let nextFcmp := match instr with | .fcmpR .. => true | _ => false
      lines ++ ppInstrsAux lbl nextFcmp rest

-- ============================================================
-- § 2b. VarLayout construction
-- ============================================================

private def varToArmReg (v : Var) : Option ArmReg :=
  if v.startsWith "__x" then
    match (v.drop 3).toNat? with
    | some 0 => some .x0 | some 1 => some .x1 | some 2 => some .x2
    | some 3 => some .x3 | some 4 => some .x4 | some 5 => some .x5
    | some 6 => some .x6 | some 7 => some .x7 | some 8 => some .x8
    | some 9 => some .x9 | some 10 => some .x10 | some 11 => some .x11
    | some 12 => some .x12 | some 13 => some .x13 | some 14 => some .x14
    | some 15 => some .x15 | some 16 => some .x16 | some 17 => some .x17
    | some 18 => some .x18 | _ => none
  else none

private def varToArmFReg (v : Var) : Option ArmFReg :=
  if v.startsWith "__d" then
    match (v.drop 3).toNat? with
    | some 0 => some .d0 | some 1 => some .d1 | some 2 => some .d2
    | some 3 => some .d3 | some 4 => some .d4 | some 5 => some .d5
    | some 6 => some .d6 | some 7 => some .d7 | some 8 => some .d8
    | some 9 => some .d9 | some 10 => some .d10 | some 11 => some .d11
    | some 12 => some .d12 | some 13 => some .d13 | some 14 => some .d14
    | some 15 => some .d15 | _ => none
  else none

/-- Build a VarLayout from the variable list and stack offset map.
    Register-allocated vars (named `__xN`/`__dN`) map to their register;
    all others map to their stack slot. -/
private def buildVarLayout (vars : List Var) (varMap : List (Var × Nat)) : VarLayout :=
  { entries := vars.filterMap fun v =>
      match varToArmReg v with
      | some r => some (v, .ireg r)
      | none => match varToArmFReg v with
        | some r => some (v, .freg r)
        | none => match lookupVar varMap v with
          | some off => some (v, .stack off)
          | none => none }

-- ============================================================
-- § 2c. pcMap and bounds-safe computation
-- ============================================================

/-- Compute instruction length for a TAC instruction.
    `pcMap` does not affect instruction count (only branch target values). -/
private def instrLength (layout : VarLayout) (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool) (instr : TAC)
    (haltS divS boundsS : Nat) : Nat :=
  match verifiedGenInstr layout (fun _ => 0) instr haltS divS boundsS arrayDecls boundsSafe with
  | some l => l.length
  | none => 0

/-- Build a pcMap (TAC PC → cumulative ARM instruction offset) as a prefix sum. -/
private def buildPcMap (lengths : Array Nat) : Nat → Nat :=
  let offsets := lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)
  fun tacPC => offsets.getD tacPC 0

/-- Build reverse map: ARM instruction offset → TAC PC (only defined at boundaries). -/
private def buildTacPcOf (lengths : Array Nat) : Nat → Option Nat :=
  let init : List (Nat × Nat) × Nat := ([], 0)
  let pairs := (List.range lengths.size).foldl (init := init) fun state i =>
    let acc := state.1
    let cumLen := state.2
    ((cumLen, i) :: acc, cumLen + (lengths.getD i 0))
  fun armPC => (pairs.1.find? fun p => p.1 == armPC).map Prod.snd

/-- Compute whether a bounds check can be elided for a given instruction at `pc`. -/
private def isBoundsSafe (arrayDecls : List (ArrayName × Nat × VarTy))
    (intervals : Array (Option BoundsOpt.IMap)) (pc : Nat) (instr : TAC) : Bool :=
  match instr with
  | .arrLoad _ arr idx _ | .arrStore arr idx _ _ =>
    match intervals.getD pc none with
    | some m => (BoundsOpt.imLookup m idx).inBounds (arraySize arrayDecls arr)
    | none => false
  | _ => false

-- ============================================================
-- § 3. Well-formedness checks (discharge proof hypotheses at runtime)
-- ============================================================

/-- Check WellTypedLayout: no float var in ireg, no non-float var in freg,
    and every variable referenced by the program has a layout entry.
    Corresponds to the `hWTL` hypothesis in verifiedGenInstr_correct. -/
private def checkWellTypedLayout (Γ : TyCtx) (layout : VarLayout)
    (code : Array TAC) : Option String :=
  -- Collect all variables referenced in the program
  let allVars := code.foldl (init := ([] : List Var)) fun acc instr =>
    acc ++ (TAC.vars instr).filter fun v => !acc.contains v
  -- Check type/register consistency for all layout entries
  let typeErr := layout.entries.find? fun (v, loc) =>
    match loc with
    | .freg _ => Γ v != .float  -- non-float in freg
    | .ireg _ => Γ v == .float  -- float in ireg
    | .stack _ => false
  match typeErr with
  | some (v, loc) =>
    let locStr := match loc with
      | .freg _ => "freg" | .ireg _ => "ireg" | .stack _ => "stack"
    let tyStr := match Γ v with | .int => "int" | .bool => "bool" | .float => "float"
    some s!"layout type mismatch: {v} (type {tyStr}) in {locStr}"
  | none =>
  -- Check completeness: every referenced variable must be in the layout
  match allVars.find? fun v => (layout v).isNone with
  | some v => some s!"variable {v} referenced but not in layout"
  | none => none

/-- Check that all branch targets are in bounds.
    Corresponds to the `hPC_bound` hypothesis on successor PCs. -/
private def checkBranchTargets (code : Array TAC) : Option String :=
  let n := code.size
  match (List.range n).find? fun pc =>
    match code.getD pc .halt with
    | .goto l | .ifgoto _ l => l >= n
    | _ => false
  with
  | some pc =>
    let target := match code.getD pc .halt with
      | .goto l | .ifgoto _ l => l | _ => 0
    some s!"branch at PC {pc} targets {target} (out of bounds, size = {n})"
  | none => none

-- ============================================================
-- § 5. Program codegen
-- ============================================================

/-- Result of the verified code generation core.
    Contains structured ArmInstr arrays that can be pretty-printed by the
    unverified shell, and all metadata needed for label resolution. -/
structure VerifiedAsmResult where
  /-- Variable zeroing instructions (register zeros + stack zeros). -/
  initInstrs : Array ArmInstr
  /-- Per-TAC-PC list of generated ARM instructions. -/
  bodyPerPC : Array (List ArmInstr)
  /-- Instructions to save register-allocated observable values to stack. -/
  haltSaveInstrs : Array ArmInstr
  /-- TAC PC → cumulative ARM instruction offset. -/
  pcMap : Nat → Nat
  /-- Variable layout (register/stack assignments). -/
  layout : VarLayout
  /-- Variable name → stack offset map (all vars have slots for printf). -/
  varMap : List (Var × Nat)
  /-- Number of init instructions (for label offset computation). -/
  initLen : Nat
  /-- Sentinel values for special branch targets. -/
  haltS : Nat
  divS : Nat
  boundsS : Nat
  /-- Reverse map: ARM offset → TAC PC. -/
  tacPcOf : Nat → Option Nat

/-- Generate init instructions that zero all variables.
    Register vars get register-zero moves; stack vars get str x0. -/
private def genInitCode (vars : List Var) (layout : VarLayout) : List ArmInstr :=
  vars.filterMap fun v =>
    match layout v with
    | some (.freg r) => some (.fmovToFP r .x0)   -- fmov dN, xzr  (x0 is 0)
    | some (.ireg r) => some (.mov r 0)
    | some (.stack off) => some (.str .x0 off)
    | none => none

/-- Generate instructions to save register-allocated observable values to stack. -/
private def genHaltSave (observable : List Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) : List ArmInstr :=
  observable.filterMap fun v =>
    match layout v with
    | some (.ireg r) =>
      match lookupVar varMap v with
      | some off => some (.str r off)
      | none => none
    | some (.freg r) =>
      match lookupVar varMap v with
      | some off => some (.fstr r off)
      | none => none
    | _ => none

/-- Verified core of code generation. Performs all validation and produces
    structured ArmInstr data. No string emission or platform-specific code. -/
def verifiedGenerateAsm (p : Prog) : Except String VerifiedAsmResult := do
  if !checkWellTypedProg p.tyCtx p then
    .error "program failed type check"
  else
    let vars := collectVars p
    let varMap := buildVarMap vars
    let layout := buildVarLayout vars varMap
    -- Check WellTypedLayout (hWTL hypothesis)
    match checkWellTypedLayout p.tyCtx layout p.code with
    | some err => .error s!"well-typed layout check failed: {err}"
    | none =>
    -- Check branch targets in bounds (hPC_bound on successors)
    match checkBranchTargets p.code with
    | some err => .error s!"branch target check failed: {err}"
    | none =>
    let intervals := BoundsOpt.analyzeIntervals p
    -- Sentinel values for special labels
    let haltS := p.code.size * 1000
    let divS  := p.code.size * 1000 + 1
    let boundsS := p.code.size * 1000 + 2
    -- Pass 1: compute instruction lengths (pcMap-independent)
    let lengths := (List.range p.code.size).map fun pc =>
      let instr := p.code.getD pc .halt
      let safe := isBoundsSafe p.arrayDecls intervals pc instr
      instrLength layout p.arrayDecls safe instr haltS divS boundsS
    let lengthsArr := lengths.toArray
    -- Build real pcMap and reverse map
    let pcMap := buildPcMap lengthsArr
    let tacPcOf := buildTacPcOf lengthsArr
    -- Generate init code
    let initInstrs := genInitCode vars layout
    -- Pass 2: generate instructions with real pcMap
    let bodyResult := (List.range p.code.size).foldl
        (init := some (Array.mkEmpty p.code.size)) fun acc pc =>
      match acc with
      | none => none
      | some arr =>
        let instr := p.code.getD pc .halt
        let safe := isBoundsSafe p.arrayDecls intervals pc instr
        match verifiedGenInstr layout pcMap instr haltS divS boundsS p.arrayDecls safe with
        | none => none
        | some armInstrs => some (arr.push armInstrs)
    match bodyResult with
    | none => .error "verifiedGenInstr failed (layout or type mismatch)"
    | some bodyPerPC =>
    -- Generate halt-save instructions
    let haltSaveInstrs := genHaltSave p.observable layout varMap
    .ok {
      initInstrs := initInstrs.toArray
      bodyPerPC := bodyPerPC
      haltSaveInstrs := haltSaveInstrs.toArray
      pcMap := pcMap
      layout := layout
      varMap := varMap
      initLen := initInstrs.length
      haltS := haltS
      divS := divS
      boundsS := boundsS
      tacPcOf := tacPcOf
    }

-- ============================================================
-- § 5a. Whole-program refinement
-- ============================================================

/-!
## Whole-program refinement

Lifts the per-instruction `ext_backward_simulation` from ArmCorrectness.lean
to a multi-step simulation over `verifiedGenerateAsm`.

**Theorem statement.** If `verifiedGenerateAsm p = .ok r`, then any TAC
execution `p ⊩ Cfg.run pc σ am ⟶* cfg'` starting from an ARM state satisfying
`ExtSimRel` is simulated by `ArmSteps` preserving `ExtSimRel`.

**Known sorrys that propagate:**
- 2 sorrys from `verifiedGenInstr_correct` (arrLoad, arrStore)
-/

/-- The flat ARM body: all per-PC instruction lists concatenated. -/
def VerifiedAsmResult.bodyFlat (r : VerifiedAsmResult) : ArmProg :=
  (r.bodyPerPC.toList.flatMap id).toArray

/-- Properties extracted from a successful `verifiedGenerateAsm` call.
    These are the invariants that the main code-generation function establishes
    via its runtime checks (type check, layout check, branch target check). -/
structure GenAsmSpec (p : Prog) (r : VerifiedAsmResult) : Prop where
  /-- The program is well-typed under its own TyCtx. -/
  wellTypedProg : WellTypedProg p.tyCtx p
  /-- The layout respects types: float vars in fregs, non-float in iregs/stack. -/
  wellTypedLayout : WellTypedLayout p.tyCtx r.layout
  /-- bodyPerPC has one entry per TAC instruction. -/
  bodySize : r.bodyPerPC.size = p.size
  /-- Each bodyPerPC entry was produced by verifiedGenInstr. -/
  instrGen : ∀ pc, (hpc : pc < p.size) →
    ∃ safe : Bool,
      verifiedGenInstr r.layout r.pcMap p[pc]
        r.haltS r.divS r.boundsS p.arrayDecls safe =
      some (r.bodyPerPC[pc]'(bodySize ▸ hpc))
  /-- pcMap is the prefix sum of bodyPerPC lengths. -/
  pcMapLengths : ∃ lengths : Array Nat,
    lengths.size = r.bodyPerPC.size ∧
    r.pcMap = buildPcMap lengths ∧
    ∀ (i : Nat) (hL : i < lengths.size) (hB : i < r.bodyPerPC.size),
      lengths[i] = (r.bodyPerPC[i]).length
  /-- Every variable referenced by an instruction has a layout entry. -/
  layoutComplete : ∀ pc (hpc : pc < p.size), ∀ v, v ∈ (p[pc]).vars → r.layout v ≠ none

/-- If lookup returns some, the key-value pair is in the list. -/
private theorem lookup_mem {v : String} {loc : VarLoc}
    {entries : List (String × VarLoc)}
    (h : entries.lookup v = some loc) : (v, loc) ∈ entries := by
  induction entries with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      have hv : v = hd.fst := by simpa using heq
      have hl : hd.snd = loc := by simpa using h
      subst hv; subst hl; simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- checkWellTypedLayout returning none implies WellTypedLayout (type consistency). -/
private theorem checkWellTypedLayout_wellTyped {Γ : TyCtx} {layout : VarLayout}
    {code : Array TAC}
    (h : checkWellTypedLayout Γ layout code = none) : WellTypedLayout Γ layout := by
  simp only [checkWellTypedLayout] at h
  split at h
  · simp at h
  · rename_i hTypeOk
    split at h
    · simp at h
    · constructor
      · intro v fr hNotFloat hContra
        have := (List.find?_eq_none.mp hTypeOk) ⟨v, .freg fr⟩ (lookup_mem hContra)
        simp at this; exact absurd this hNotFloat
      · intro v ir hFloat hContra
        have := (List.find?_eq_none.mp hTypeOk) ⟨v, .ireg ir⟩ (lookup_mem hContra)
        simp at this; exact absurd hFloat this

/-- Foldl that appends preserves existing elements. -/
private theorem foldl_preserves_mem {init : List Var} {instrs : List TAC} {v : Var}
    (hv : v ∈ init) :
    v ∈ instrs.foldl (fun acc i =>
      acc ++ (TAC.vars i).filter fun w => !acc.contains w) init := by
  induction instrs generalizing init with
  | nil => exact hv
  | cons _ tl ih => simp only [List.foldl]; exact ih (List.mem_append_left _ hv)

/-- The foldl in checkWellTypedLayout collects all TAC.vars from all instructions. -/
private theorem foldl_collects (instrs : List TAC) (v : Var) (instr : TAC)
    (hMem : instr ∈ instrs) (hv : v ∈ TAC.vars instr) :
    v ∈ instrs.foldl (init := ([] : List Var)) fun acc i =>
      acc ++ (TAC.vars i).filter fun w => !acc.contains w := by
  suffices ∀ (init : List Var),
      v ∈ instrs.foldl (fun acc i =>
        acc ++ (TAC.vars i).filter fun w => !acc.contains w) init from this []
  intro init
  induction instrs generalizing init with
  | nil => simp at hMem
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hMem with rfl | htl
    · apply foldl_preserves_mem
      by_cases hmem : v ∈ init
      · exact List.mem_append_left _ hmem
      · apply List.mem_append_right
        rw [List.mem_filter]
        exact ⟨hv, by simp [List.contains_iff_mem, hmem]⟩
    · exact ih htl _

/-- checkWellTypedLayout returning none implies all TAC.vars are in the layout. -/
private theorem checkWellTypedLayout_instrMapped {Γ : TyCtx} {layout : VarLayout}
    {code : Array TAC}
    (h : checkWellTypedLayout Γ layout code = none)
    {pc : Nat} (hpc : pc < code.size) {v : Var}
    (hv : v ∈ TAC.vars code[pc]) : layout v ≠ none := by
  simp only [checkWellTypedLayout] at h
  split at h
  · simp at h
  · rename_i hTypeOk
    split at h
    · simp at h
    · rename_i hComplete
      intro hNone
      have hInAll : v ∈ code.foldl (init := ([] : List Var)) fun acc instr =>
          acc ++ (TAC.vars instr).filter fun w => !acc.contains w := by
        rw [← Array.foldl_toList]
        exact foldl_collects code.toList v code[pc] (Array.getElem_mem_toList hpc) hv
      have := (List.find?_eq_none.mp hComplete) v hInAll
      simp [Option.isNone, hNone] at this

/-- The foldl body generation produces arrays of the right size and content. -/
private theorem body_foldl_spec {code : Array TAC} {layout : VarLayout} {pcMap : Nat → Nat}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {intervals : Array (Option BoundsOpt.IMap)} {bodyPerPC : Array (List ArmInstr)}
    (hFold : (List.range code.size).foldl
      (init := some (Array.mkEmpty code.size))
      (fun acc pc => match acc with
        | none => none
        | some arr =>
          let instr := code.getD pc .halt
          let safe := isBoundsSafe arrayDecls intervals pc instr
          match verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe with
          | none => none
          | some armInstrs => some (arr.push armInstrs)) = some bodyPerPC) :
    bodyPerPC.size = code.size ∧
    ∀ pc (hb : pc < bodyPerPC.size),
      verifiedGenInstr layout pcMap (code.getD pc .halt) haltS divS boundsS arrayDecls
        (isBoundsSafe arrayDecls intervals pc (code.getD pc .halt)) =
      some bodyPerPC[pc] := by
  -- Generalized lemma: for any initial array and prefix length m,
  -- if the foldl over range m succeeds, the result has the right size and content.
  have hGetD : ∀ k : Nat, code.getD k .halt = (code[k]?.getD .halt) := by
    intro k; unfold Array.getD
    cases Decidable.em (k < code.size) with
    | inl h => simp [h, getElem?_pos]
    | inr h => simp [h, getElem?_neg]
  let F := fun (acc : Option (Array (List ArmInstr))) (pc : Nat) =>
    match acc with
    | none => none
    | some arr =>
      let instr := code.getD pc .halt
      let safe := isBoundsSafe arrayDecls intervals pc instr
      match verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe with
      | none => none
      | some armInstrs => some (arr.push armInstrs)
  suffices key : ∀ (m : Nat) (initArr res : Array (List ArmInstr)),
      m ≤ code.size →
      (List.range m).foldl F (some initArr) = some res →
      res.size = initArr.size + m ∧
      (∀ (i : Nat) (hi : i < initArr.size) (hir : i < res.size),
        res[i]'hir = initArr[i]'hi) ∧
      (∀ (k : Nat), k < m →
        (hkr : initArr.size + k < res.size) →
        verifiedGenInstr layout pcMap (code.getD k .halt) haltS divS boundsS arrayDecls
          (isBoundsSafe arrayDecls intervals k (code.getD k .halt)) =
        some (res[initArr.size + k]'hkr)) by
    have ⟨hSz, _, hNew⟩ := key code.size (Array.mkEmpty code.size) bodyPerPC
      (Nat.le_refl _) hFold
    simp at hSz
    refine ⟨hSz, fun pc hb => ?_⟩
    have h := hNew pc (by omega) (by show 0 + pc < bodyPerPC.size; omega)
    simp only [show (Array.mkEmpty code.size : Array (List ArmInstr)).size = 0 from rfl,
      Nat.zero_add] at h
    exact h
  intro m
  induction m with
  | zero =>
    intro initArr res _ hEq
    simp [List.range_zero, List.foldl, F] at hEq
    subst hEq
    exact ⟨by omega, fun _ hi hir => rfl, fun _ hk => by omega⟩
  | succ n ih =>
    intro initArr res hle hEq
    simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
    -- The foldl result is F (foldl F (some initArr) (range n)) n
    -- Split on the intermediate foldl result
    generalize hMid : (List.range n).foldl F (some initArr) = midResult at hEq
    match midResult with
    | none =>
      simp [F] at hEq
    | some midArr =>
      -- Apply IH to get properties of midArr
      have hle' : n ≤ code.size := by omega
      have ⟨hMidSz, hMidOld, hMidNew⟩ := ih initArr midArr hle' hMid
      -- Now the last step processes element n
      dsimp only [F] at hEq
      -- Split on verifiedGenInstr result
      have hn_lt : n < code.size := by omega
      generalize hGen : verifiedGenInstr layout pcMap (code.getD n .halt) haltS divS boundsS
        arrayDecls (isBoundsSafe arrayDecls intervals n (code.getD n .halt)) = genR at hEq
      match genR with
      | none => simp at hEq
      | some armInstrsN =>
        simp at hEq; subst hEq
        have hResSz : (midArr.push armInstrsN).size = initArr.size + (n + 1) := by
          simp [Array.size_push, hMidSz]; omega
        refine ⟨hResSz, ?_, ?_⟩
        · -- Old elements from initArr are preserved
          intro i hi hir
          have hiMid : i < midArr.size := by rw [hMidSz]; omega
          simp [Array.getElem_push, hiMid]
          exact hMidOld i hi hiMid
        · -- Elements k in range [0, n+1): code.getD k mapped to res[initArr.size + k]
          intro k hk hkr
          by_cases hkN : k = n
          · -- k = n: this is the newly pushed element
            subst hkN
            have hIdx : initArr.size + k = midArr.size := by omega
            have : ¬ (initArr.size + k < midArr.size) := by omega
            simp [Array.getElem_push, this]
            rw [← hGetD]; exact hGen
          · -- k < n: use IH
            have hkLt : k < n := by omega
            have hIdx : initArr.size + k < midArr.size := by omega
            simp [Array.getElem_push, hIdx]
            rw [← hGetD]; exact hMidNew k hkLt (by omega)

/-- instrLength equals verifiedGenInstr result length (pcMap only affects branch target values,
    not instruction count). -/
private theorem instrLength_eq_length {layout : VarLayout} {pcMap : Nat → Nat} {instr : TAC}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {safe : Bool} {instrs : List ArmInstr}
    (h : verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe = some instrs) :
    instrLength layout arrayDecls safe instr haltS divS boundsS = instrs.length := by
  simp only [instrLength]
  have hSS : layout.scratchSafe = true := by
    cases hss : layout.scratchSafe <;> simp [verifiedGenInstr, hss] at h ⊢
  have hII : layout.isInjective = true := by
    cases hii : layout.isInjective <;> simp [verifiedGenInstr, hSS, hii] at h ⊢
  cases instr with
  | goto l => simp [verifiedGenInstr, hSS, hII] at h ⊢; subst h; simp
  | halt => simp [verifiedGenInstr, hSS, hII] at h ⊢; subst h; simp
  | ifgoto be l =>
    simp [verifiedGenInstr, hSS, hII] at h ⊢
    subst h; simp [List.length_append]
  | _ =>
    -- Non-branch: pcMap doesn't appear, so (fun _ => 0) gives identical result
    simp [verifiedGenInstr, hSS, hII] at h ⊢
    -- After simp, the goal and h have the same expression (pcMap eliminated)
    -- Split on remaining matches (layout, op, etc.) and close with simp_all
    (try split at h ⊢); (try split at h ⊢); (try split at h ⊢); (try split at h ⊢)
    all_goals (first | simp_all | (split at h <;> simp_all))


/-- A successful `verifiedGenerateAsm` call satisfies `GenAsmSpec`. -/
theorem verifiedGenerateAsm_spec {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm p = .ok r) : GenAsmSpec p r := by
  unfold verifiedGenerateAsm at hGen
  split at hGen
  · simp at hGen
  · rename_i hWT_guard
    have hWT : checkWellTypedProg p.tyCtx p = true := by simpa using hWT_guard
    dsimp only [] at hGen
    split at hGen
    · simp at hGen
    · rename_i hWTL_check
      split at hGen
      · simp at hGen
      · rename_i hBT_check
        split at hGen
        · simp at hGen
        · rename_i bodyPerPC hBodyMatch
          -- Replace r with its concrete record value
          have hr := Except.ok.inj hGen; subst hr
          -- Now all r.field references become concrete
          have ⟨hSz, hPCs⟩ := body_foldl_spec hBodyMatch
          have hgetD : ∀ pc (h : pc < p.size), p.code.getD pc .halt = p[pc] := by
            intro pc hpc; simp [Prog.size_eq] at hpc
            simp [Array.getD, dif_pos hpc, Prog.getElem_eq]
          exact {
            wellTypedProg := checkWellTypedProg_sound hWT
            wellTypedLayout := checkWellTypedLayout_wellTyped hWTL_check
            bodySize := by simp [Prog.size_eq]; exact hSz
            instrGen := fun pc hpc => by
              have hpc' : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
              have hgen := hPCs pc (hSz ▸ hpc')
              rw [hgetD pc hpc] at hgen
              exact ⟨_, hgen⟩
            pcMapLengths := by
              refine ⟨((List.range p.code.size).map fun pc =>
                instrLength (buildVarLayout (collectVars p) (buildVarMap (collectVars p)))
                  p.arrayDecls
                  (isBoundsSafe p.arrayDecls (BoundsOpt.analyzeIntervals p) pc (p.code.getD pc .halt))
                  (p.code.getD pc .halt)
                  (p.code.size * 1000) (p.code.size * 1000 + 1) (p.code.size * 1000 + 2)).toArray,
                ?_, rfl, ?_⟩
              · simp [List.length_map, List.length_range, hSz]
              · intro i hL hB
                dsimp only [] at hB ⊢
                simp at hL
                simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
                exact instrLength_eq_length (hPCs i (hSz ▸ (by omega)))
            layoutComplete := fun pc hpc v hv => by
              simp [Prog.size_eq] at hpc
              exact checkWellTypedLayout_instrMapped hWTL_check hpc hv
          }

-- ──────────────────────────────────────────────────────────────
-- buildPcMap prefix-sum lemmas
-- ──────────────────────────────────────────────────────────────

/-- The offsets array built by `buildPcMap`'s foldl. -/
private def buildOffsets (lengths : Array Nat) : Array Nat :=
  lengths.foldl (init := #[0]) fun acc len => acc.push (acc.back! + len)

/-- Core invariant: `buildOffsets` via list foldl produces a prefix-sum array
    of size `lengths.size + 1` where `offsets[0] = 0` and
    `offsets[i+1] = offsets[i] + lengths[i]`. We characterize it by a recursive
    function and then prove `buildPcMap` properties from that. -/
private def prefixSumList : List Nat → Nat → List Nat
  | [], acc => [acc]
  | l :: rest, acc => acc :: prefixSumList rest (acc + l)

private theorem prefixSumList_length : ∀ (ls : List Nat) (acc : Nat),
    (prefixSumList ls acc).length = ls.length + 1 := by
  intro ls; induction ls with
  | nil => intro acc; simp [prefixSumList]
  | cons l rest ih => intro acc; simp [prefixSumList, ih]

private theorem prefixSumList_head : ∀ (ls : List Nat) (acc : Nat),
    (prefixSumList ls acc)[0]'(by simp [prefixSumList_length]) = acc := by
  intro ls; induction ls with
  | nil => intro acc; simp [prefixSumList]
  | cons l rest _ => intro acc; simp [prefixSumList]

private theorem prefixSumList_succ (ls : List Nat) (acc : Nat) (i : Nat)
    (hi : i < ls.length) :
    (prefixSumList ls acc)[i + 1]'(by rw [prefixSumList_length]; omega) =
    (prefixSumList ls acc)[i]'(by rw [prefixSumList_length]; omega) +
    ls[i]'hi := by
  induction ls generalizing acc i with
  | nil => simp at hi
  | cons l rest ih =>
    simp only [prefixSumList]
    cases i with
    | zero =>
      simp [List.getElem_cons_zero, prefixSumList_head]
    | succ n =>
      simp only [List.getElem_cons_succ]
      exact ih (acc + l) n (by simp at hi; omega)

/-- The foldl in `buildPcMap` preserves early indices: `push` only appends. -/
private theorem foldl_push_getD_zero :
    ∀ (ls : List Nat) (init : Array Nat) (hsz : 0 < init.size),
    init[0]'hsz = 0 →
    (ls.foldl (fun acc len => acc.push (acc.back! + len)) init).getD 0 0 = 0 := by
  intro ls; induction ls with
  | nil =>
    intro init hsz h0; simp only [List.foldl]
    unfold Array.getD; split
    · exact h0
    · omega
  | cons l rest ih =>
    intro init hsz h0; simp only [List.foldl]
    have hsz' : 0 < (init.push (init.back! + l)).size := by simp [Array.size_push]
    apply ih _ hsz'
    simp [Array.getElem_push, hsz, h0]

/-- `buildPcMap` starts at 0 for the first TAC PC. -/
private theorem buildPcMap_zero (lengths : Array Nat) :
    buildPcMap lengths 0 = 0 := by
  show (lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)).getD 0 0 = 0
  rw [← Array.foldl_toList]
  exact foldl_push_getD_zero lengths.toList #[0] (by simp) (by simp)

/-- Generalized bridge: foldl-with-push on an array `(pfx ++ [acc]).toArray`
    produces `pfx ++ prefixSumList ls acc`. -/
private theorem foldl_push_toList :
    ∀ (ls : List Nat) (pfx : List Nat) (acc : Nat),
    (ls.foldl (fun a len => a.push (a.back! + len))
      ((pfx ++ [acc]).toArray)).toList =
    pfx ++ prefixSumList ls acc := by
  intro ls; induction ls with
  | nil => intro pfx acc; simp [prefixSumList, List.foldl]
  | cons l rest ih =>
    intro pfx acc; simp only [List.foldl, prefixSumList]
    have h1 : (pfx ++ [acc]).toArray.back! = acc := by
      simp
    have h2 : (pfx ++ [acc]).toArray.push (acc + l) =
        ((pfx ++ [acc]) ++ [acc + l]).toArray := by simp
    rw [h1, h2, ih (pfx ++ [acc]) (acc + l)]
    simp

/-- The offsets array built by buildPcMap's foldl equals prefixSumList. -/
private theorem buildPcMap_offsets_eq (lengths : Array Nat) :
    (lengths.foldl (init := #[0]) fun acc len =>
      acc.push (acc.back! + len)).toList = prefixSumList lengths.toList 0 := by
  rw [← Array.foldl_toList]
  exact foldl_push_toList lengths.toList ([] : List Nat) 0

/-- `buildPcMap` gives prefix sums:
    `pcMap (pc + 1) = pcMap pc + lengths[pc]`. -/
private theorem buildPcMap_succ (lengths : Array Nat) (pc : Nat)
    (hpc : pc < lengths.size) :
    buildPcMap lengths (pc + 1) =
    buildPcMap lengths pc + lengths[pc] := by
  show (lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)).getD (pc + 1) 0 =
    (lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)).getD pc 0 + lengths[pc]
  let offsets := lengths.foldl (init := #[0]) fun acc len =>
    acc.push (acc.back! + len)
  have hEq := buildPcMap_offsets_eq lengths
  -- offsets.size
  have hSz : offsets.size = lengths.size + 1 := by
    have : offsets.toList.length = (prefixSumList lengths.toList 0).length :=
      congrArg List.length hEq
    simp [prefixSumList_length] at this; exact this
  -- Both indices in bounds
  have h1 : pc + 1 < offsets.size := by omega
  have h0 : pc < offsets.size := by omega
  -- Unfold getD, both in-bounds
  show (if _ : pc + 1 < offsets.size then offsets[pc + 1] else 0) =
       (if _ : pc < offsets.size then offsets[pc] else 0) + lengths[pc]
  simp only [h1, h0, dite_true]
  -- Connect offsets[i] to prefixSumList via toList
  have hIdx : ∀ (i : Nat) (hi : i < offsets.size),
      offsets[i] = (prefixSumList lengths.toList 0)[i]'(by
        rw [prefixSumList_length]; simp; omega) := by
    intro i hi
    have : offsets.toList[i]? = (prefixSumList lengths.toList 0)[i]? := by rw [hEq]
    rw [Array.getElem?_toList] at this
    rw [Array.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by rw [prefixSumList_length]; simp; omega)] at this
    exact Option.some.inj this
  rw [hIdx _ h1, hIdx _ h0]
  have : lengths.toList[pc] = lengths[pc] := by simp
  rw [← this]
  exact prefixSumList_succ lengths.toList 0 pc (by simp; exact hpc)

-- ──────────────────────────────────────────────────────────────
-- CodeAt from the flat body
-- ──────────────────────────────────────────────────────────────

/-- Indexing into a flattened list of lists at a segment boundary:
    element `j` of segment `k` is at position `(sum of lengths of segments 0..k-1) + j`
    in the flat list. -/
private theorem flatMap_segment_getElem (lss : List (List α)) (k j : Nat)
    (hk : k < lss.length) (hj : j < lss[k].length) :
    let offset := (lss.take k).flatMap id |>.length
    ((lss.flatMap id)[offset + j]?) = some (lss[k][j]) := by
  induction lss generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
    simp only [List.flatMap_cons, id]
    cases k with
    | zero =>
      simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
                  List.getElem_cons_zero] at hj ⊢
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    | succ n =>
      have hk' : n < tl.length := by simp at hk; omega
      simp only [List.take_succ_cons, List.flatMap_cons, id, List.length_append,
                  List.getElem_cons_succ] at hj ⊢
      rw [List.getElem?_append_right (by omega)]
      conv => lhs; rw [show hd.length + ((tl.take n).flatMap id).length + j - hd.length =
             ((tl.take n).flatMap id).length + j from by omega]
      exact ih n hk' hj

/-- `buildPcMap lengths pc` equals the total length of the first `pc` segments. -/
private theorem buildPcMap_eq_take_length (bodyPerPC : Array (List ArmInstr))
    (lengths : Array Nat)
    (hSz : lengths.size = bodyPerPC.size)
    (hLen : ∀ (i : Nat) (hL : i < lengths.size) (hB : i < bodyPerPC.size),
      lengths[i] = (bodyPerPC[i]).length)
    (pc : Nat) (hpc : pc ≤ bodyPerPC.size) :
    buildPcMap lengths pc =
    ((bodyPerPC.toList.take pc).flatMap id).length := by
  induction pc with
  | zero =>
    rw [buildPcMap_zero]
    simp
  | succ n ih =>
    have hn : n < lengths.size := by omega
    rw [buildPcMap_succ lengths n hn]
    have ih' := ih (by omega)
    rw [ih']
    -- take (n+1) = take n ++ [bodyPerPC.toList[n]]
    rw [List.take_add_one]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton, id,
               List.length_append]
    congr 1
    rw [hLen n hn (by omega)]
    simp

/-- Each per-PC instruction block is embedded in the flat body at the
    offset given by `pcMap`. -/
private theorem codeAt_of_bodyFlat (bodyPerPC : Array (List ArmInstr))
    (lengths : Array Nat)
    (hSz : lengths.size = bodyPerPC.size)
    (hLen : ∀ (i : Nat) (hL : i < lengths.size) (hB : i < bodyPerPC.size),
      lengths[i] = (bodyPerPC[i]).length)
    (pc : Nat) (hpc : pc < bodyPerPC.size) :
    CodeAt (bodyPerPC.toList.flatMap id).toArray
      (buildPcMap lengths pc) bodyPerPC[pc] := by
  intro i hi
  -- Convert Array getElem? to List getElem?
  rw [List.getElem?_toArray]
  -- Rewrite buildPcMap as take-length
  rw [buildPcMap_eq_take_length bodyPerPC lengths hSz hLen pc (by omega)]
  -- Use flatMap_segment_getElem on bodyPerPC.toList
  have hpc' : pc < bodyPerPC.toList.length := by simp; exact hpc
  have hj : i < bodyPerPC.toList[pc].length := by simp; exact hi
  exact flatMap_segment_getElem bodyPerPC.toList pc i hpc' hj

-- ──────────────────────────────────────────────────────────────
-- Per-step simulation (wraps ext_backward_simulation)
-- ──────────────────────────────────────────────────────────────

/-- One-step simulation: if we can take a TAC step from a running
    configuration, there exist ARM steps preserving `ExtSimRel`.

    This wraps `ext_backward_simulation` by discharging `CodeAt` and
    `hPcNext` from the `GenAsmSpec` invariants. -/
private theorem step_simulation {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec p r)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : ExtSimRel r.layout r.pcMap (.run pc σ am) s)
    (hPC : pc < p.size)
    (hTS : TypedStore p.tyCtx σ) :
    ∃ s', ArmSteps r.bodyFlat s s' ∧
          ExtSimRel r.layout r.pcMap cfg' s' := by
  -- Extract per-PC instruction data from spec
  obtain ⟨safe, hSome⟩ := spec.instrGen pc hPC
  obtain ⟨lengths, hLenSz, hPcMapEq, hLenEq⟩ := spec.pcMapLengths
  -- Obtain CodeAt from flat body
  have hBodySz : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
  have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc)
      (r.bodyPerPC[pc]'hBodySz) := by
    show CodeAt (r.bodyPerPC.toList.flatMap id).toArray _ _
    rw [hPcMapEq]
    exact codeAt_of_bodyFlat r.bodyPerPC lengths hLenSz hLenEq pc hBodySz
  -- Lookup the instruction
  have hInstr : p[pc]? = some p[pc] := by
    simp [Prog.getElem?_eq_getElem hPC]
  -- Build hPcNext: for sequential successor pc+1, pcMap (pc+1) = pcMap pc + instrs.length
  have hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      r.pcMap (pc + 1) = r.pcMap pc +
        (r.bodyPerPC[pc]'hBodySz).length := by
    intro σ' am' _
    have hpc_len : pc < lengths.size := hLenSz ▸ hBodySz
    simp only [hPcMapEq]
    rw [buildPcMap_succ lengths pc hpc_len]
    congr 1
    exact hLenEq pc hpc_len hBodySz
  exact ext_backward_simulation p r.bodyFlat r.layout r.pcMap
    r.haltS r.divS r.boundsS p.arrayDecls safe
    hStep hRel hPC spec.wellTypedProg hTS spec.wellTypedLayout
    p[pc] hInstr
    (r.bodyPerPC[pc]'hBodySz) hSome
    hCodeAt hPcNext (spec.layoutComplete pc hPC)

-- ──────────────────────────────────────────────────────────────
-- Multi-step simulation (main theorem)
-- ──────────────────────────────────────────────────────────────

/-- Extract `pc < p.size` from any TAC step out of a running configuration.
    Every `Step` constructor requires `p[pc]? = some _`. -/
private theorem Step.pc_lt_of_step {p : Prog} {pc : Nat} {σ : Store}
    {am : ArrayMem} {cfg' : Cfg}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg') : pc < p.size := by
  if h : pc < p.size then exact h
  else have := Prog.getElem?_none h; cases hStep <;> simp_all

/-- Classify a single step result: either the successor is `.run` with
    `TypedStore` preserved, or it is terminal (no further steps). -/
private theorem step_run_or_terminal {p : Prog} {pc : Nat} {σ : Store}
    {am : ArrayMem} {c : Cfg}
    (hwtp : WellTypedProg p.tyCtx p) (hts : TypedStore p.tyCtx σ)
    (hpc : pc < p.size) (hstep : p ⊩ Cfg.run pc σ am ⟶ c) :
    (∃ pc' σ' am', c = .run pc' σ' am' ∧ TypedStore p.tyCtx σ') ∨
    (∀ c', ¬ (p ⊩ c ⟶ c')) := by
  cases hstep with
  | const h =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .const h)⟩
  | copy h =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .copy h)⟩
  | binop h h1 h2 h3 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .binop h h1 h2 h3)⟩
  | boolop h =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .boolop h)⟩
  | goto _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | iftrue _ _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | iffall _ _ => exact .inl ⟨_, _, _, rfl, hts⟩
  | arrLoad h h1 h2 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .arrLoad h h1 h2)⟩
  | arrStore h h1 h2 h3 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .arrStore h h1 h2 h3)⟩
  | fbinop h h1 h2 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .fbinop h h1 h2)⟩
  | intToFloat h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .intToFloat h h1)⟩
  | floatToInt h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .floatToInt h h1)⟩
  | floatExp h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .floatExp h h1)⟩
  | floatSqrt h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .floatSqrt h h1)⟩
  | halt _ => exact .inr fun _ h => Step.no_step_from_halt h
  | error _ _ _ _ => exact .inr fun _ h => Step.no_step_from_error h
  | binop_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | arrLoad_boundsError _ _ _ => exact .inr fun _ h => Step.no_step_from_error h
  | arrStore_boundsError _ _ _ _ => exact .inr fun _ h => Step.no_step_from_error h
  | arrLoad_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | arrStore_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | fbinop_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | intToFloat_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | floatToInt_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | floatExp_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | floatSqrt_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h

/-- Whole-program backward simulation for `verifiedGenerateAsm`.

    If the verified code generator succeeds on program `p`, then any
    multi-step TAC execution starting from a configuration whose ARM
    counterpart satisfies `ExtSimRel` is simulated by `ArmSteps`
    preserving `ExtSimRel`.

    The proof proceeds by induction on the TAC `Steps` derivation,
    applying `step_simulation` (which wraps `ext_backward_simulation`)
    at each step, using `step_run_or_terminal` to classify the
    intermediate config, and `type_preservation` for `TypedStore`.

    **Propagated sorrys:** 2 from `verifiedGenInstr_correct` (arrLoad,
    arrStore). -/
theorem tacToArm_refinement {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm p = .ok r)
    {pc : Nat} {σ : Store} {am : ArrayMem}
    (s : ArmState)
    (hRel : ExtSimRel r.layout r.pcMap (.run pc σ am) s)
    (hTS : TypedStore p.tyCtx σ)
    (cfg' : Cfg) (hSteps : p ⊩ Cfg.run pc σ am ⟶* cfg') :
    ∃ s', ArmSteps r.bodyFlat s s' ∧
          ExtSimRel r.layout r.pcMap cfg' s' := by
  have spec := verifiedGenerateAsm_spec hGen
  -- Generalize the start config for induction (pattern from type_preservation_steps)
  suffices ∀ c c_end, Steps p c c_end →
      ∀ pc σ am s,
        c = Cfg.run pc σ am →
        ExtSimRel r.layout r.pcMap (.run pc σ am) s →
        TypedStore p.tyCtx σ →
        ∃ s', ArmSteps r.bodyFlat s s' ∧
              ExtSimRel r.layout r.pcMap c_end s' from
    this _ _ hSteps pc σ am s rfl hRel hTS
  intro c c_end hSteps
  induction hSteps with
  | refl =>
    intro pc σ am s hc hRel _; subst hc; exact ⟨s, .refl, hRel⟩
  | step hStep rest ih =>
    intro pc σ am s hc hRel hTS_cur; subst hc
    have hPC := Step.pc_lt_of_step hStep
    obtain ⟨s_mid, hArm1, hRel_mid⟩ :=
      step_simulation spec hStep hRel hPC hTS_cur
    -- Classify the one-step successor
    rcases step_run_or_terminal spec.wellTypedProg hTS_cur hPC hStep with
      ⟨pc', σ', am', hEq, hTS'⟩ | hTerminal
    · -- Successor is .run: subst and apply IH
      subst hEq
      obtain ⟨s', hArm2, hRel'⟩ := ih _ _ _ s_mid rfl hRel_mid hTS'
      exact ⟨s', hArm1.trans hArm2, hRel'⟩
    · -- Successor is terminal: rest must be refl
      cases rest with
      | refl => exact ⟨s_mid, hArm1, hRel_mid⟩
      | step h _ => exact absurd h (hTerminal _)

/-- Corollary: initial ExtSimRel establishment.
    For a zero-initialized store, if the layout maps every variable and
    the ARM state's registers/stack/fregs are all zero at PC = pcMap 0,
    then `ExtSimRel` holds at the initial configuration. -/
theorem initial_extSimRel (layout : VarLayout) (pcMap : Nat → Nat)
    (σ₀ : Store) (am₀ : ArrayMem) (s₀ : ArmState)
    (hEncode : ∀ v, (σ₀ v).encode = 0)
    (hPC : s₀.pc = pcMap 0)
    (hRegs : ∀ r, s₀.regs r = 0)
    (hFregs : ∀ r, s₀.fregs r = 0)
    (hStack : ∀ off, s₀.stack off = 0)
    (hAM : s₀.arrayMem = am₀) :
    ExtSimRel layout pcMap (.run 0 σ₀ am₀) s₀ := by
  refine ⟨?_, ?_, ?_⟩
  · intro v loc hLoc
    rw [hEncode]
    match loc with
    | .stack off => exact hStack off
    | .ireg r => exact hRegs r
    | .freg r => exact hFregs r
  · exact hPC
  · exact hAM

/-- Top-level correctness: if code generation succeeds and the TAC program
    starts from a zero-initialized store, every reachable TAC configuration
    is simulated by ARM steps from a zeroed ARM state.

    This combines `tacToArm_refinement` with `initial_extSimRel` to
    eliminate all intermediate hypotheses. The only requirements are:
    1. Code generation succeeded (`verifiedGenerateAsm p = .ok r`)
    2. The TAC program reaches `cfg'` from the typed zero-initialized store

    `Store.typedInit` assigns each variable the zero value of its declared type
    (`Value.ofBitVec (Γ v) 0`), so `TypedStore` holds for any type context.

    **Propagated sorrys:** 2 from `verifiedGenInstr_correct` (arrLoad, arrStore). -/
private theorem typedInit_encode (Γ : TyCtx) (v : Var) :
    (Store.typedInit Γ v).encode = 0 := by
  simp [Store.typedInit, Value.ofBitVec, Value.encode]
  cases Γ v <;> simp [Value.ofBitVec, Value.encode]

theorem tacToArm_correctness {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm p = .ok r)
    {cfg' : Cfg}
    (hSteps : p ⊩ Cfg.run 0 (Store.typedInit p.tyCtx) (fun _ _ => 0) ⟶* cfg') :
    ∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap cfg' s' :=
  tacToArm_refinement hGen _
    (initial_extSimRel r.layout r.pcMap (Store.typedInit p.tyCtx) (fun _ _ => 0)
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ }
      (typedInit_encode p.tyCtx) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl)
    (TypedStore.typedInit p.tyCtx)
    cfg' hSteps

/-- Generate the complete assembly for a program.
    Calls `verifiedGenerateAsm` for the verified core, then wraps it with
    prologue/epilogue, printf code, error handlers, and data sections. -/
def generateAsm (p : Prog) : Except String String := do
  let r ← verifiedGenerateAsm p
  let vars := collectVars p
  -- Stack frame: 16-byte aligned
  -- Layout: [scratch 8B] [var1 8B] ... [varN 8B] [padding] [x29 8B] [x30 8B]
  let frameSize := ((vars.length + 1) * 8 + 16 + 15) / 16 * 16
  let header := [
    ".global _main",
    ".align 2",
    "",
    "_main:",
    s!"  sub sp, sp, #{frameSize}",
    s!"  str x30, [sp, #{frameSize - 8}]",
    s!"  str x29, [sp, #{frameSize - 16}]",
    s!"  add x29, sp, #{frameSize - 16}",
    "",
    "  // Initialize all variables to 0",
    "  mov x0, #0"
  ]
  let lbl := ppLabel r.haltS r.divS r.boundsS r.tacPcOf
  -- Pretty-print init instructions
  let initLines := ppInstrs lbl r.initInstrs.toList
  -- Pretty-print body with TAC PC labels
  let body := (List.range r.bodyPerPC.size).flatMap fun pc =>
    [s!".L{pc}:"] ++ ppInstrs lbl ((r.bodyPerPC[pc]!))
  -- Print observable variables at halt (loads from stack, safe after saveRegs)
  let printCode := p.observable.flatMap fun v =>
    let isFloat := p.tyCtx v == .float
    let fmtLabel := if isFloat then s!".Lfmt_float" else ".Lfmt"
    if isFloat then
      s!"  // print {v} (float)" ::
      (loadVarFP r.varMap v "d0") ::
      "  sub sp, sp, #32" ::
      s!"  adrp x8, .Lname_{v}@PAGE" ::
      s!"  add x8, x8, .Lname_{v}@PAGEOFF" ::
      "  str x8, [sp]" ::
      "  str d0, [sp, #8]" ::
      s!"  adrp x0, {fmtLabel}@PAGE" ::
      s!"  add x0, x0, {fmtLabel}@PAGEOFF" ::
      "  bl _printf" ::
      "  add sp, sp, #32" :: List.nil
    else
      s!"  // print {v}" ::
      (loadVar r.varMap v "x9") ::
      "  sub sp, sp, #16" ::
      s!"  adrp x8, .Lname_{v}@PAGE" ::
      s!"  add x8, x8, .Lname_{v}@PAGEOFF" ::
      "  str x8, [sp]" ::
      "  str x9, [sp, #8]" ::
      s!"  adrp x0, {fmtLabel}@PAGE" ::
      s!"  add x0, x0, {fmtLabel}@PAGEOFF" ::
      "  bl _printf" ::
      "  add sp, sp, #16" :: List.nil
  -- Pretty-print halt-save instructions
  let saveLines := ppInstrs lbl r.haltSaveInstrs.toList
  let footer := [
    "",
    ".Lhalt:",
    "  // Save register values to stack for printf"] ++
    saveLines ++
    ["  // Print observable variables"] ++
    printCode ++
    ["",
     "  // Exit with code 0",
     "  mov x0, #0",
     s!"  ldr x29, [sp, #{frameSize - 16}]",
     s!"  ldr x30, [sp, #{frameSize - 8}]",
     s!"  add sp, sp, #{frameSize}",
     "  ret",
     "",
     ".Ldiv_by_zero:",
     "  adrp x0, .Ldiv_msg@PAGE",
     "  add x0, x0, .Ldiv_msg@PAGEOFF",
     "  bl _printf",
     "  mov x0, #1",
     "  bl _exit",
     "",
     ".Lbounds_err:",
     "  adrp x0, .Lbounds_msg@PAGE",
     "  add x0, x0, .Lbounds_msg@PAGEOFF",
     "  bl _printf",
     "  mov x0, #1",
     "  bl _exit",
     "",
     ".section __TEXT,__cstring",
     ".Lfmt:",
     "  .asciz \"%s = %ld\\n\"",
     ".Lfmt_float:",
     "  .asciz \"%s = %f\\n\"",
     ".Ldiv_msg:",
     "  .asciz \"error: division by zero\\n\"",
     ".Lbounds_msg:",
     "  .asciz \"error: array index out of bounds\\n\""] ++
    p.observable.map fun v =>
     s!".Lname_{v}:\n  .asciz \"{v}\""
  -- Emit .data section for each array (size × 8 bytes, zero-initialized)
  let arrays := collectArrays p
  let arrayData := if arrays.isEmpty then [] else
    ["", ".section __DATA,__data"] ++
    arrays.flatMap fun arr =>
      [s!".global _arr_{arr}",
       ".align 3",
       s!"_arr_{arr}:",
       s!"  .space {(if p.arraySize arr == 0 then 1024 else p.arraySize arr) * 8}"]
  .ok (emit (header ++ [""] ++ initLines ++ [""] ++ body ++ footer ++ arrayData ++ [""]))

-- ============================================================
-- § 6. End-to-end: parse → compile → codegen
-- ============================================================

/-- Apply a single optimization pass: run it, check the certificate, return the
    optimized program. Errors if the certificate check fails. -/
def applyPass (name : String) (pass : Prog → ECertificate) (p : Prog) : Except String Prog :=
  let cert := pass p
  if cert.orig.code != p.code || cert.orig.observable != p.observable ||
     cert.orig.arrayDecls != p.arrayDecls then
    .error s!"optimization certificate orig mismatch for {name} (code={cert.orig.code == p.code} obs={cert.orig.observable == p.observable} arr={cert.orig.arrayDecls == p.arrayDecls})"
  else if checkCertificateExec cert then .ok cert.trans
  else
    let checks := checkCertificateVerboseExec cert
    let failures := checks.filter (fun (_, b) => !b)
    let failNames := failures.map (fun (n, _) => n)
    .error s!"optimization certificate check failed for {name}: {failNames}"

/-- Apply each optimization pass in sequence:
    DCE → ConstProp → DCE → DAE → CSE → LICM → ConstHoist → Peephole → DCE → RegAlloc.
    DCE at start: eliminates dead code from goto patterns in source.
    DCE after ConstProp: eliminates dead branches from constant folding.
    DCE before RegAlloc: cleans up after Peephole.
    Each pass is checked by the executable certificate checker. -/
def optimizePipeline (p : Prog) : Except String Prog := do
  let p ← applyPass "DCE" DCEOpt.optimize p
  let p ← applyPass "LICM" LICMOpt.optimize p
  let p ← applyPass "ConstProp" ConstPropOpt.optimize p
  let p ← applyPass "DCE" DCEOpt.optimize p
  let p ← applyPass "DAE" DAEOpt.optimize p
  let p ← applyPass "CSE" CSEOpt.optimize p
  let p ← applyPass "ConstHoist" ConstHoistOpt.optimize p
  let p ← applyPass "Peephole" PeepholeOpt.optimize p
  let p ← applyPass "DCE" DCEOpt.optimize p
  applyPass "RegAlloc" RegAllocOpt.optimize p

def compileToAsm (input : String) : Except String String := do
  let prog ← parseProgram input
  if !prog.typeCheck then .error "program failed type check (frontend)"
  let tac := prog.compileToTAC
  let opt ← optimizePipeline tac
  generateAsm opt

-- ============================================================
-- § 7. IO driver: write assembly, assemble, and run
-- ============================================================

/-- Write assembly to a file, assemble it, link it, and run the resulting binary. -/
def assembleAndRun (asm : String) (asmFile binFile : String := "/tmp/tac_out.s")
    : IO UInt32 := do
  let asmPath := asmFile
  let binPath := binFile.replace ".s" ""
  IO.FS.writeFile ⟨asmPath⟩ asm
  -- Assemble and link via cc (handles macOS linker details)
  let result ← IO.Process.output {
    cmd := "cc"
    args := #["-o", binPath, asmPath, "-lSystem"]
  }
  if result.exitCode != 0 then
    IO.eprintln s!"Assembly failed:\n{result.stderr}"
    return 1
  -- Run
  let run ← IO.Process.output { cmd := binPath }
  IO.print run.stdout
  if run.exitCode != 0 then
    IO.eprintln run.stderr
  return run.exitCode

-- ============================================================
-- § 8. Tests
-- ============================================================

-- Generate assembly for a simple program
#eval! compileToAsm "
  var x : int, y : int;
  x := 3;
  y := x + 4
"

-- Generate assembly for an array program
#eval! compileToAsm "
  var i : int, x : int;
  arr[0] := 42;
  i := 1;
  arr[i] := 100;
  i := 0;
  x := arr[i]
"

-- Generate assembly for sum 1..n (n initialized to 0, so sum = 0)
#eval! compileToAsm "
  var n : int, s : int, i : int;
  s := 0;
  i := 1;
  while (i <= n) {
    s := s + i;
    i := i + 1
  }
"
