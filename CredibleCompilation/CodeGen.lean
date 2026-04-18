import CredibleCompilation.WhileLang
import CredibleCompilation.Parser
import CredibleCompilation.ConstPropOpt
import CredibleCompilation.CSEOpt
import CredibleCompilation.LICMOpt
import CredibleCompilation.ConstHoistOpt
import CredibleCompilation.DAEOpt
import CredibleCompilation.FMAFusionOpt
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
    | .floatUnary x _ y => let a := if acc.contains x then acc else acc ++ [x]
                          if a.contains y then a else a ++ [y]
    | .fternop x _ a b c => let acc := if acc.contains x then acc else acc ++ [x]
                            let acc := if acc.contains a then acc else acc ++ [a]
                            let acc := if acc.contains b then acc else acc ++ [b]
                            if acc.contains c then acc else acc ++ [c]
    | .print _ vs      => vs.foldl (fun a v => if a.contains v then a else a ++ [v]) acc
    | .goto _          => acc
    | .ifgoto _ _      => acc
    | .halt            => acc
  ) ([] : List Var)
  -- Also add observable variables
  p.observable.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) vars

private def buildVarMap (vars : List Var) : List (Var × Nat) :=
  (List.range vars.length).zip vars |>.map fun (i, v) => (v, (i + 1) * 8)

private theorem mem_fst_of_mem_zip {a : α} {b : β} {l1 : List α} {l2 : List β}
    (h : (a, b) ∈ l1.zip l2) : a ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => simp at h
  | cons _ _ ih =>
    cases l2 with
    | nil => simp at h
    | cons _ tl =>
      simp [List.zip_cons_cons] at h
      exact h.elim (fun ⟨h, _⟩ => h ▸ .head _) (fun h => .tail _ (ih h))

/-- The offsets produced by `buildVarMap` are pairwise distinct.
    Offsets are (i+1)*8 for i in [0, vars.length), which are injective. -/
private theorem buildVarMap_offsets_nodup (vars : List Var) :
    ((buildVarMap vars).map Prod.snd).Nodup := by
  simp only [buildVarMap, List.map_map]
  rw [List.Nodup, List.pairwise_map]
  -- Suffices: fst components of zip are pairwise distinct
  suffices List.Pairwise (fun a b => a.1 ≠ b.1) ((List.range vars.length).zip vars) by
    exact this.imp fun {a b} h heq => h (by
      show a.1 = b.1
      have : (a.1 + 1) * 8 = (b.1 + 1) * 8 := heq
      omega)
  -- Prove: zip preserves pairwise-distinctness on first components
  have hND := List.nodup_range (n := vars.length)
  rw [List.Nodup] at hND
  generalize List.range vars.length = ns at hND
  induction hND generalizing vars with
  | nil => simp
  | cons hmem _ ih =>
    cases vars with
    | nil => simp
    | cons v tl =>
      simp only [List.zip_cons_cons, List.pairwise_cons]
      exact ⟨fun ⟨x, w⟩ hm => hmem x (mem_fst_of_mem_zip hm), ih tl⟩

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
  | .x19 => "x19" | .x20 => "x20" | .x21 => "x21" | .x22 => "x22"
  | .x23 => "x23" | .x24 => "x24" | .x25 => "x25" | .x26 => "x26"
  | .x27 => "x27" | .x28 => "x28"

private def ppFReg : ArmFReg → String
  | .d0 => "d0" | .d1 => "d1" | .d2 => "d2" | .d3 => "d3"
  | .d4 => "d4" | .d5 => "d5" | .d6 => "d6" | .d7 => "d7"
  | .d8 => "d8" | .d9 => "d9" | .d10 => "d10" | .d11 => "d11"
  | .d12 => "d12" | .d13 => "d13" | .d14 => "d14" | .d15 => "d15"

/-- Generate ARM load + store lines for one printf argument at stack offset `i*8`. -/
private def genPrintArgLoad (tyCtx : TyCtx) (layout : VarLayout)
    (varMap : List (Var × Nat)) (i : Nat) (v : Var) : List String :=
  let storeInstr := "  str " ++ (if tyCtx v == .float then "d0" else "x1") ++
    ", [sp, #" ++ toString (i * 8) ++ "]"
  if tyCtx v == .float then
    let loadLine := match layout v with
      | some (.freg reg) => s!"  fmov d0, {ppFReg reg}"
      | _ => loadVarFP varMap v "d0"
    loadLine :: storeInstr :: []
  else
    let loadLine := match layout v with
      | some (.ireg reg) => s!"  mov x1, {ppReg reg}"
      | _ => loadVar varMap v "x1"
    loadLine :: storeInstr :: []

private def ppCond : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .hs => "hs" | .lo => "lo"

/-- Map float-comparison condition codes to ARM64 mnemonics.
    After `fcmp`, ARM64 uses `mi` (minus) for less-than and `ls` (lower or same)
    for less-or-equal, unlike integer `cmp` which uses `lt`/`le`. -/
private def ppCondFloat : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "mi" | .le => "ls" | .gt => "gt" | .ge => "ge"
  | .hs => "hs" | .lo => "lo"

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
    condition codes for `cset` use the float convention.
    Save/restore of caller-saved registers around library calls is now
    handled by the verified codegen layer (genCallSaveRestore), so ppInstr
    no longer needs libSave/libRestore parameters. -/
private def ppInstr (lbl : Nat → String) (afterFcmp : Bool)
    (instr : ArmInstr) : List String :=
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
  | .eorR rd rn rm =>
    [s!"  eor {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .lslR rd rn rm =>
    [s!"  lsl {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .asrR rd rn rm =>
    [s!"  asr {ppReg rd}, {ppReg rn}, {ppReg rm}"]
  | .b target =>
    [s!"  b {lbl target}"]
  | .printCall lines => lines
  | .bCond c target =>
    [s!"  b.{if afterFcmp then ppCondFloat c else ppCond c} {lbl target}"]
  | .arrLd dst arr idxReg =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  ldr {ppReg dst}, [x0, {ppReg idxReg}, lsl #3]"]
  | .arrSt arr idxReg valReg =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  str {ppReg valReg}, [x0, {ppReg idxReg}, lsl #3]"]
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
  | .fmaddR fd fn fm fa =>
    [s!"  fmadd {ppFReg fd}, {ppFReg fn}, {ppFReg fm}, {ppFReg fa}"]
  | .fmsubR fd fn fm fa =>
    [s!"  fmsub {ppFReg fd}, {ppFReg fn}, {ppFReg fm}, {ppFReg fa}"]
  | .fminR fd fn fm =>
    [s!"  fminnm {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .fmaxR fd fn fm =>
    [s!"  fmaxnm {ppFReg fd}, {ppFReg fn}, {ppFReg fm}"]
  | .callBinF fop fd fn fm =>
    let name := match fop with
      | .fpow => "_pow" | _ => "_unknown_binop"
    let load0 := if fn == .d0 then [] else [s!"  fmov d0, {ppFReg fn}"]
    let load1 := if fm == .d1 then [] else [s!"  fmov d1, {ppFReg fm}"]
    let store := if fd == .d0 then [] else [s!"  fmov {ppFReg fd}, d0"]
    load0 ++ load1 ++ [s!"  stp x29, x30, [sp, #-16]!", s!"  bl {name}",
             "  ldp x29, x30, [sp], #16"] ++ store
  | .fcmpR fn fm =>
    [s!"  fcmp {ppFReg fn}, {ppFReg fm}"]
  | .scvtf fd rn =>
    [s!"  scvtf {ppFReg fd}, {ppReg rn}"]
  | .fcvtzs rd fn =>
    [s!"  fcvtzs {ppReg rd}, {ppFReg fn}"]
  | .farrLd fd arr idxReg =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  ldr {ppFReg fd}, [x0, {ppReg idxReg}, lsl #3]"]
  | .farrSt arr idxReg fs =>
    [s!"  adrp x0, _arr_{arr}@PAGE",
     s!"  add x0, x0, _arr_{arr}@PAGEOFF",
     s!"  str {ppFReg fs}, [x0, {ppReg idxReg}, lsl #3]"]
  | .floatUnaryInstr op fd fn =>
    match op with
    | .sqrt => [s!"  fsqrt {ppFReg fd}, {ppFReg fn}"]
    | .abs  => [s!"  fabs {ppFReg fd}, {ppFReg fn}"]
    | .neg  => [s!"  fneg {ppFReg fd}, {ppFReg fn}"]
    | _ =>  -- library call intrinsics (save/restore handled by verified codegen)
      let name := match op with
        | .exp => "_exp" | .sin => "_sin" | .cos => "_cos" | .tan => "_tan"
        | .log => "_log" | .log2 => "_log2" | .log10 => "_log10" | .round => "_round"
        | .sqrt | .abs | .neg => unreachable!
      let load := if fn == .d0 then [] else [s!"  fmov d0, {ppFReg fn}"]
      let store := if fd == .d0 then [] else [s!"  fmov {ppFReg fd}, d0"]
      load ++ [s!"  stp x29, x30, [sp, #-16]!", s!"  bl {name}",
               "  ldp x29, x30, [sp], #16"] ++ store

/-- Pretty-print a list of ArmInstr, tracking fcmp state for cset. -/
private def ppInstrs (lbl : Nat → String)
    : List ArmInstr → List String
  | [] => []
  | instr :: rest =>
    let afterFcmp := match instr with | .fcmpR .. => true | _ => false
    let lines := ppInstr lbl false instr
    let restLines := ppInstrsAux lbl afterFcmp rest
    lines ++ restLines
where
  ppInstrsAux (lbl : Nat → String)
      (prevWasFcmp : Bool) : List ArmInstr → List String
    | [] => []
    | instr :: rest =>
      let lines := ppInstr lbl prevWasFcmp instr
      let nextFcmp := match instr with | .fcmpR .. => true | _ => false
      lines ++ ppInstrsAux lbl nextFcmp rest

-- ============================================================
-- § 2b. VarLayout construction
-- ============================================================

private def varToArmReg (v : Var) : Option ArmReg :=
  -- Int registers (__ir{N}) and bool registers (__br{N}) both use ARM x-registers
  let n? := if v.startsWith "__ir" then (v.drop 4).toNat?
            else if v.startsWith "__br" then (v.drop 4).toNat?
            else none
  match n? with
  | some 0 => some .x0 | some 1 => some .x1 | some 2 => some .x2
  | some 3 => some .x3 | some 4 => some .x4 | some 5 => some .x5
  | some 6 => some .x6 | some 7 => some .x7 | some 8 => some .x8
  | some 9 => some .x9 | some 10 => some .x10 | some 11 => some .x11
  | some 12 => some .x12 | some 13 => some .x13 | some 14 => some .x14
  | some 15 => some .x15 | some 16 => some .x16 | some 17 => some .x17
  | some 18 => some .x18 | some 19 => some .x19 | some 20 => some .x20
  | some 21 => some .x21 | some 22 => some .x22 | some 23 => some .x23
  | some 24 => some .x24 | some 25 => some .x25 | some 26 => some .x26
  | some 27 => some .x27 | some 28 => some .x28 | _ => none

private def varToArmFReg (v : Var) : Option ArmFReg :=
  if v.startsWith "__fr" then
    match (v.drop 4).toNat? with
    | some 0 => some .d0 | some 1 => some .d1 | some 2 => some .d2
    | some 3 => some .d3 | some 4 => some .d4 | some 5 => some .d5
    | some 6 => some .d6 | some 7 => some .d7 | some 8 => some .d8
    | some 9 => some .d9 | some 10 => some .d10 | some 11 => some .d11
    | some 12 => some .d12 | some 13 => some .d13 | some 14 => some .d14
    | some 15 => some .d15 | _ => none
  else none

/-- Build a VarLayout from the variable list and stack offset map.
    Register-allocated vars (named `__irN`/`__brN`/`__frN`) map to their register;
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
-- § 2c. Call-site save/restore for caller-saved registers
-- ============================================================

/-- Is a TAC instruction a library call that clobbers caller-saved registers?
    This includes non-native float unary ops (exp, sin, …) and fpow. -/
private def isLibCallTAC : TAC → Bool
  | .floatUnary _ op _ => !op.isNative
  | .fbinop _ .fpow _ _ => true
  | _ => false

/-- Generate save/restore ArmInstr lists for caller-saved registers that are live
    at a library call site. Each live variable in a caller-saved register is saved
    to its existing stack slot (from varMap) before the call and restored after.
    Returns (saveInstrs, restoreInstrs). -/
def genCallSaveRestore (liveVars : List Var) (layout : VarLayout)
    (varMap : List (Var × Nat)) : List ArmInstr × List ArmInstr :=
  let callerSavedLive := liveVars.filterMap fun v =>
    match layout v with
    | some (.ireg r) =>
      if r.isCallerSaved then
        match varMap.find? (fun (x, _) => x == v) with
        | some (_, off) => some (Sum.inl (r, off))  -- int reg + stack offset
        | none => none
      else none
    | some (.freg r) =>
      if r.isCallerSaved then
        match varMap.find? (fun (x, _) => x == v) with
        | some (_, off) => some (Sum.inr (r, off))  -- float reg + stack offset
        | none => none
      else none
    | _ => none
  let saves := callerSavedLive.map fun
    | .inl (r, off) => ArmInstr.str r off
    | .inr (r, off) => ArmInstr.fstr r off
  let restores := callerSavedLive.map fun
    | .inl (r, off) => ArmInstr.ldr r off
    | .inr (r, off) => ArmInstr.fldr r off
  (saves, restores)

/-- Filter genCallerSaveAll entries to exclude the destination variable's register.
    For lib-calls, the destination's register should NOT be saved/restored because
    the base instructions write the result there and restoring would overwrite it. -/
private def callerSaveEntries (layout : VarLayout) (varMap : List (Var × Nat))
    (exclude : Option Var := none) : List CallerSaveEntry :=
  let all := genCallerSaveAll layout varMap
  match exclude with
  | none => all
  | some d => all.filter fun e =>
    match layout d, e with
    | some (.ireg r), .ireg ir _ => !(ir == r)
    | some (.freg r), .freg fr _ => !(fr == r)
    | _, _ => true

/-- Number of save/restore instructions for a call site. -/
private def callSaveRestoreLen (layout : VarLayout)
    (varMap : List (Var × Nat)) (exclude : Option Var := none) : Nat :=
  let entries := callerSaveEntries layout varMap exclude
  (entriesToSaves entries).length + (entriesToRestores entries).length

/-- Remove the destination variable of an instruction from a live-variable list.
    At a call site `x := f(...)`, x's old value is dead (being overwritten),
    so it must not be saved/restored — the call produces x's new value. -/
private def removeDest (instr : TAC) (live : List Var) : List Var :=
  match DAEOpt.instrDef instr with
  | some x => live.filter (· != x)
  | none => live

-- ============================================================
-- § 2d. pcMap and bounds-safe computation
-- ============================================================

/-- Compute instruction length for a TAC instruction.
    `pcMap` does not affect instruction count (only branch target values).
    Save/restore uses `genCallerSaveAll` (all caller-saved regs, not just live). -/
private def instrLength (layout : VarLayout) (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool) (instr : TAC)
    (haltS divS boundsS : Nat)
    (varMap : List (Var × Nat) := []) : Nat :=
  match instr with
  | .print _ _ =>
    -- saves + 1 printCall + restores
    1 + callSaveRestoreLen layout varMap
  | _ =>
  let baseLen := match verifiedGenInstr layout (fun _ => 0) instr haltS divS boundsS arrayDecls boundsSafe with
    | some l => l.length
    | none => 0
  if isLibCallTAC instr then
    baseLen + callSaveRestoreLen layout varMap (DAEOpt.instrDef instr)
  else baseLen

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

-- ============================================================
-- § 4b. Caller-save spec checker
-- ============================================================

/-- Boolean no-duplicates check for a list. -/
private def listNodupBool [BEq α] : List α → Bool
  | [] => true
  | x :: rest => !rest.any (· == x) && listNodupBool rest

private theorem listNodupBool_sound [DecidableEq α] {l : List α}
    (h : listNodupBool l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    simp only [listNodupBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hNotIn, hRest⟩ := h
    refine List.nodup_cons.mpr ⟨?_, ih hRest⟩
    intro hMem
    simp only [Bool.eq_false_iff] at hNotIn
    exact hNotIn (List.any_eq_true.mpr ⟨x, hMem, by simp⟩)

/-- Check all properties needed by `callerSave_composition` for
    the entries produced by `genCallerSaveAll layout varMap`. -/
private def checkCallerSaveSpec (layout : VarLayout) (varMap : List (Var × Nat)) : Bool :=
  let entries := genCallerSaveAll layout varMap
  -- hFresh: no save offset equals a stack layout offset
  entries.all (fun e =>
    layout.entries.all (fun (_, loc) =>
      match loc with | .stack o => !(o == e.off) | _ => true)) &&
  -- hNodup: save offsets pairwise distinct
  listNodupBool (entries.map CallerSaveEntry.off) &&
  -- hCoversIreg: every caller-saved ireg in layout has an entry
  layout.entries.all (fun (_, loc) =>
    match loc with
    | .ireg r => !r.isCallerSaved ||
        entries.any (fun e => match e with | .ireg ir _ => ir == r | _ => false)
    | _ => true) &&
  -- hCoversFreg: every caller-saved freg in layout has an entry
  layout.entries.all (fun (_, loc) =>
    match loc with
    | .freg r => !r.isCallerSaved ||
        entries.any (fun e => match e with | .freg fr _ => fr == r | _ => false)
    | _ => true) &&
  -- hUniqIreg: any two ireg entries with the same register have equal offsets
  entries.all (fun e1 => entries.all (fun e2 =>
    match e1, e2 with
    | .ireg ir1 off1, .ireg ir2 off2 => !(ir1 == ir2) || (off1 == off2)
    | _, _ => true)) &&
  -- hUniqFreg: any two freg entries with the same register have equal offsets
  entries.all (fun e1 => entries.all (fun e2 =>
    match e1, e2 with
    | .freg fr1 off1, .freg fr2 off2 => !(fr1 == fr2) || (off1 == off2)
    | _, _ => true))

/-- Soundness: if the caller-save check passes, all 6 properties hold. -/
private theorem checkCallerSaveSpec_sound {layout : VarLayout} {varMap : List (Var × Nat)}
    (h : checkCallerSaveSpec layout varMap = true) :
    let entries := genCallerSaveAll layout varMap
    -- hFresh
    (∀ e ∈ entries, ∀ v, layout v ≠ some (.stack e.off)) ∧
    -- hNodup
    (entries.map CallerSaveEntry.off).Nodup ∧
    -- hCoversIreg
    (∀ v ir, layout v = some (.ireg ir) → ir.isCallerSaved = true →
      ∃ off, CallerSaveEntry.ireg ir off ∈ entries) ∧
    -- hCoversFreg
    (∀ v fr, layout v = some (.freg fr) → fr.isCallerSaved = true →
      ∃ off, CallerSaveEntry.freg fr off ∈ entries) ∧
    -- hUniqIreg
    (∀ ir off1 off2, CallerSaveEntry.ireg ir off1 ∈ entries →
      CallerSaveEntry.ireg ir off2 ∈ entries → off1 = off2) ∧
    -- hUniqFreg
    (∀ fr off1 off2, CallerSaveEntry.freg fr off1 ∈ entries →
      CallerSaveEntry.freg fr off2 ∈ entries → off1 = off2) := by
  simp only [checkCallerSaveSpec, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hFreshB, hNodupB⟩, hCovIB⟩, hCovFB⟩, hUniqIB⟩, hUniqFB⟩ := h
  have hNodupP := listNodupBool_sound hNodupB
  refine ⟨?_, hNodupP, ?_, ?_, ?_, ?_⟩
  · -- hFresh
    intro e he v hContra
    have := (List.all_eq_true.mp hFreshB) e he
    have hAll := List.all_eq_true.mp this
    have hMem := lookup_mem hContra
    have := hAll ⟨v, .stack e.off⟩ hMem
    simp at this
  · -- hCoversIreg
    intro v ir hLoc hCS
    have hMem := lookup_mem hLoc
    have := (List.all_eq_true.mp hCovIB) ⟨v, .ireg ir⟩ hMem
    simp only [hCS, Bool.not_true, Bool.false_or] at this
    rw [List.any_eq_true] at this
    obtain ⟨e, heMem, heEq⟩ := this
    match e, heEq with
    | .ireg ir' off, heq =>
      simp at heq; exact ⟨off, heq ▸ heMem⟩
    | .freg _ _, heq => simp at heq
  · -- hCoversFreg
    intro v fr hLoc hCS
    have hMem := lookup_mem hLoc
    have := (List.all_eq_true.mp hCovFB) ⟨v, .freg fr⟩ hMem
    simp only [hCS, Bool.not_true, Bool.false_or] at this
    rw [List.any_eq_true] at this
    obtain ⟨e, heMem, heEq⟩ := this
    match e, heEq with
    | .freg fr' off, heq =>
      simp at heq; exact ⟨off, heq ▸ heMem⟩
    | .ireg _ _, heq => simp at heq
  · -- hUniqIreg: pairwise check → same reg means same offset
    intro ir off1 off2 h1 h2
    have h1' := (List.all_eq_true.mp hUniqIB) (.ireg ir off1) h1
    have h2' := (List.all_eq_true.mp h1') (.ireg ir off2) h2
    simp at h2'; exact h2'
  · -- hUniqFreg: pairwise check → same reg means same offset
    intro fr off1 off2 h1 h2
    have h1' := (List.all_eq_true.mp hUniqFB) (.freg fr off1) h1
    have h2' := (List.all_eq_true.mp h1') (.freg fr off2) h2
    simp at h2'; exact h2'

-- ============================================================
-- § 5. Program codegen
-- ============================================================

/-- Result of the verified code generation core.
    Contains structured ArmInstr arrays that can be pretty-printed by the
    unverified shell, and all metadata needed for label resolution. -/
structure VerifiedAsmResult where
  /-- Variable zeroing instructions (register zeros + stack zeros). -/
  initInstrs : Array ArmInstr
  /-- Per-TAC-PC list of generated ARM instructions.
      Library call sites include save/restore of live caller-saved registers. -/
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
  /-- Callee-saved register save instructions (prologue). -/
  calleeSavePrologue : List ArmInstr
  /-- Callee-saved register restore instructions (epilogue). -/
  calleeSaveEpilogue : List ArmInstr
  /-- Which callee-saved registers are used: (intRegs, floatRegs). -/
  calleeSaveRegs : List Nat × List Nat

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

/-- Detect callee-saved registers used in the layout. Returns (intRegNums, floatRegNums). -/
private def detectCalleeSavedLayout (layout : VarLayout) : List Nat × List Nat :=
  let intRegs := layout.entries.filterMap fun (_, loc) =>
    match loc with
    | .ireg r => if !r.isCallerSaved then some r.toNat else none
    | _ => none
  let floatRegs := layout.entries.filterMap fun (_, loc) =>
    match loc with
    | .freg r => if !r.isCallerSaved then some r.toNat else none
    | _ => none
  (intRegs.eraseDups, floatRegs.eraseDups)

/-- Generate callee-save prologue (store) and epilogue (load) ArmInstr lists.
    `baseOffset` is the stack offset where the callee-save area begins
    (typically right after variable slots). -/
private def genVerifiedCalleeSave (intRegs : List Nat) (floatRegs : List Nat)
    (baseOffset : Nat) : List ArmInstr × List ArmInstr :=
  -- Save int registers
  let (intSaves, intRestores, _) := intRegs.foldl (fun (s, r, off) n =>
    let reg := ArmReg.fromRegNum n
    (s ++ [.str reg off], r ++ [.ldr reg off], off + 8)
  ) ([], [], baseOffset)
  -- Save float registers
  let (floatSaves, floatRestores, _) := floatRegs.foldl (fun (s, r, off) n =>
    let freg := ArmFReg.fromRegNum n
    (s ++ [.fstr freg off], r ++ [.fldr freg off], off + 8)
  ) ([], [], baseOffset + intRegs.length * 8)
  (intSaves ++ floatSaves, intRestores ++ floatRestores)

/-- Build the pre-computed assembly lines for a `printCall` instruction.
    These are emitted by `ppInstr` and model the printf calling convention:
    sub sp, arg loads, adrp/add for format string, bl _printf, add sp. -/
private def genPrintCallLines (tyCtx : TyCtx) (layout : VarLayout)
    (varMap : List (Var × Nat)) (pc : Nat) (fmt : String) (vs : List Var) : List String :=
  let stackSize := max 16 (((vs.length * 8 + 15) / 16) * 16)
  let fmtComment := fmt.foldl (fun acc c => match c with
    | '\n' => acc ++ "\\n" | '\t' => acc ++ "\\t" | c => acc ++ c.toString) ""
  let loadLines := (List.range vs.length).flatMap fun i =>
    genPrintArgLoad tyCtx layout varMap i (vs.getD i "")
  let comment := "  // print " ++ "\"" ++ fmtComment ++ "\""
  let fmtLabel := ".Lfmt_print_" ++ toString pc
  let subSp := "  sub sp, sp, #" ++ toString stackSize
  let addSp := "  add sp, sp, #" ++ toString stackSize
  let adrp := "  adrp x0, " ++ fmtLabel ++ "@PAGE"
  let addX0 := "  add x0, x0, " ++ fmtLabel ++ "@PAGEOFF"
  let bl := "  bl _printf"
  comment :: subSp :: loadLines ++ [adrp, addX0, bl, addSp]

/-- Step function for pass-2 body generation. For each TAC instruction,
    generates (and possibly wraps) ARM instructions, pushing onto the accumulator.
    Returns `none` if verifiedGenInstr fails; propagates `none` from previous steps. -/
private def bodyGenStep (code : Array TAC) (layout : VarLayout) (pcMap : Nat → Nat)
    (_liveOut : Array (List Var)) (varMap : List (Var × Nat))
    (intervals : Array (Option BoundsOpt.IMap))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (haltS divS boundsS : Nat) (tyCtx : TyCtx)
    (acc : Option (Array (List ArmInstr))) (pc : Nat)
    : Option (Array (List ArmInstr)) :=
  match acc with
  | none => none
  | some arr =>
    let instr := code.getD pc .halt
    let safe := isBoundsSafe arrayDecls intervals pc instr
    let isPrint := match instr with | .print _ _ => true | _ => false
    if isPrint then
      let (fmt, vs) := match instr with | .print f v => (f, v) | _ => ("", [])
      let entries := genCallerSaveAll layout varMap
      let saves := entriesToSaves entries
      let restores := entriesToRestores entries
      let printLines := genPrintCallLines tyCtx layout varMap pc fmt vs
      some (arr.push (saves ++ [ArmInstr.printCall printLines] ++ restores))
    else
    match verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe with
    | none => none
    | some armInstrs =>
      let armInstrs' :=
        if isLibCallTAC instr then
          -- Exclude destination: restoring it would overwrite the computation result
          let entries := callerSaveEntries layout varMap (DAEOpt.instrDef instr)
          entriesToSaves entries ++ armInstrs ++ entriesToRestores entries
        else armInstrs
      some (arr.push armInstrs')

/-- Verified core of code generation. Performs all validation and produces
    structured ArmInstr data. No string emission or platform-specific code. -/
def verifiedGenerateAsm (tyCtx : TyCtx) (p : Prog) : Except String VerifiedAsmResult := do
  if !checkWellTypedProg tyCtx p then
    .error "program failed type check"
  else
    let vars := collectVars p
    let varMap := buildVarMap vars
    let layout := buildVarLayout vars varMap
    -- Check layout safety: no scratch registers, injective mapping
    if !layout.scratchSafe then
      .error "layout uses scratch register"
    else if !layout.isInjective then
      .error "layout is not injective"
    else
    -- Check WellTypedLayout (hWTL hypothesis)
    match checkWellTypedLayout tyCtx layout p.code with
    | some err => .error s!"well-typed layout check failed: {err}"
    | none =>
    -- Check caller-save spec (callerSave_composition hypotheses)
    if !checkCallerSaveSpec layout varMap then
      .error "caller-save spec check failed"
    else
    -- Check branch targets in bounds (hPC_bound on successors)
    match checkBranchTargets p.code with
    | some err => .error s!"branch target check failed: {err}"
    | none =>
    let intervals := BoundsOpt.analyzeIntervals p
    -- Liveness analysis for call-site save/restore
    let liveOut := DAEOpt.analyzeLiveness p
    -- Sentinel values for special labels
    let haltS := p.code.size * 1000
    let divS  := p.code.size * 1000 + 1
    let boundsS := p.code.size * 1000 + 2
    -- Pass 1: compute instruction lengths (pcMap-independent)
    -- Includes save/restore overhead at library call sites.
    let lengths := (List.range p.code.size).map fun pc =>
      let instr := p.code.getD pc .halt
      let safe := isBoundsSafe p.arrayDecls intervals pc instr
      instrLength layout p.arrayDecls safe instr haltS divS boundsS varMap
    let lengthsArr := lengths.toArray
    -- Build real pcMap and reverse map
    let pcMap := buildPcMap lengthsArr
    let tacPcOf := buildTacPcOf lengthsArr
    -- Generate init code
    let initInstrs := genInitCode vars layout
    -- Pass 2: generate instructions with real pcMap
    -- For library call sites, wrap with save/restore of live caller-saved registers.
    let bodyResult := (List.range p.code.size).foldl
        (bodyGenStep p.code layout pcMap liveOut varMap intervals p.arrayDecls haltS divS boundsS tyCtx)
        (some (Array.mkEmpty p.code.size))
    match bodyResult with
    | none => .error "verifiedGenInstr failed (layout or type mismatch)"
    | some bodyPerPC =>
    -- Generate halt-save instructions
    let haltSaveInstrs := genHaltSave p.observable layout varMap
    -- Callee-saved register prologue/epilogue
    let (csIntRegs, csFloatRegs) := detectCalleeSavedLayout layout
    let calleeSaveOffset := (vars.length + 1) * 8  -- right after variable slots
    let (csPrologue, csEpilogue) := genVerifiedCalleeSave csIntRegs csFloatRegs calleeSaveOffset
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
      calleeSavePrologue := csPrologue
      calleeSaveEpilogue := csEpilogue
      calleeSaveRegs := (csIntRegs, csFloatRegs)
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
- 0 sorrys from `verifiedGenInstr_correct` (arrLoad bool case closed)
-/

/-- The flat ARM body: all per-PC instruction lists concatenated. -/
def VerifiedAsmResult.bodyFlat (r : VerifiedAsmResult) : ArmProg :=
  (r.bodyPerPC.toList.flatMap id).toArray

/-- Properties extracted from a successful `verifiedGenerateAsm` call.
    These are the invariants that the main code-generation function establishes
    via its runtime checks (type check, layout check, branch target check). -/
structure GenAsmSpec (tyCtx : TyCtx) (p : Prog) (r : VerifiedAsmResult) : Prop where
  /-- The program is well-typed under the given TyCtx. -/
  wellTypedProg : WellTypedProg tyCtx p
  /-- The layout respects types: float vars in fregs, non-float in iregs/stack. -/
  wellTypedLayout : WellTypedLayout tyCtx r.layout
  /-- bodyPerPC has one entry per TAC instruction. -/
  bodySize : r.bodyPerPC.size = p.size
  /-- Each non-print, non-lib-call bodyPerPC entry was produced by verifiedGenInstr.
      Print PCs use unverified codegen; lib-call PCs are wrapped (see callSiteSaveRestore). -/
  instrGen : ∀ pc, (hpc : pc < p.size) →
    isLibCallTAC p[pc] = false →
    (∀ fmt vs, p[pc] ≠ .print fmt vs) →
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
  /-- At library call sites, bodyPerPC wraps verifiedGenInstr output with
      save/restore of caller-saved registers excluding the destination
      (via callerSaveEntries). -/
  callSiteSaveRestore : ∀ pc (hpc : pc < p.size),
    isLibCallTAC p[pc] = true →
    ∃ baseInstrs,
      verifiedGenInstr r.layout r.pcMap p[pc]
        r.haltS r.divS r.boundsS p.arrayDecls (isBoundsSafe p.arrayDecls (BoundsOpt.analyzeIntervals p) pc p[pc]) =
        some baseInstrs ∧
      r.bodyPerPC[pc]'(bodySize ▸ hpc) =
        entriesToSaves (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])) ++
        baseInstrs ++
        entriesToRestores (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]))
  /-- At print sites, bodyPerPC = entriesToSaves entries ++ [printCall _] ++ entriesToRestores entries
      where entries = genCallerSaveAll layout varMap. -/
  printSaveRestore : ∀ pc (hpc : pc < p.size),
    (∃ fmt vs, p[pc] = .print fmt vs) →
    ∃ lines,
      r.bodyPerPC[pc]'(bodySize ▸ hpc) =
        entriesToSaves (genCallerSaveAll r.layout r.varMap) ++
        [ArmInstr.printCall lines] ++
        entriesToRestores (genCallerSaveAll r.layout r.varMap)
  /-- The entries from genCallerSaveAll satisfy all callerSave_composition hypotheses. -/
  callerSaveSpec :
    let entries := genCallerSaveAll r.layout r.varMap
    (∀ e ∈ entries, ∀ v, r.layout v ≠ some (.stack e.off)) ∧
    (entries.map CallerSaveEntry.off).Nodup ∧
    (∀ v ir, r.layout v = some (.ireg ir) → ir.isCallerSaved = true →
      ∃ off, CallerSaveEntry.ireg ir off ∈ entries) ∧
    (∀ v fr, r.layout v = some (.freg fr) → fr.isCallerSaved = true →
      ∃ off, CallerSaveEntry.freg fr off ∈ entries) ∧
    (∀ ir off1 off2, CallerSaveEntry.ireg ir off1 ∈ entries →
      CallerSaveEntry.ireg ir off2 ∈ entries → off1 = off2) ∧
    (∀ fr off1 off2, CallerSaveEntry.freg fr off1 ∈ entries →
      CallerSaveEntry.freg fr off2 ∈ entries → off1 = off2)

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
        exact ⟨hv, by simp [hmem]⟩
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

private theorem Array.push_inj {a : Array α} {x y : α} (h : a.push x = a.push y) : x = y := by
  have := congrArg (·[a.size]?) h; simp at this; exact this

/-- A foldl over `List.range n` that propagates `none` and pushes exactly one
    element per successful `some` step produces an array of size `n`. -/
private theorem foldl_push_size
    {n : Nat} {res : Array α}
    {F : Option (Array α) → Nat → Option (Array α)}
    (hNone : ∀ pc, F none pc = none)
    (hPush : ∀ arr pc, F (some arr) pc = none ∨ ∃ x, F (some arr) pc = some (arr.push x))
    (hFold : (List.range n).foldl F (some #[]) = some res) :
    res.size = n := by
  suffices key : ∀ (m : Nat) (initArr res : Array α),
      (List.range m).foldl F (some initArr) = some res →
      res.size = initArr.size + m by
    have := key n #[] res hFold; simp at this; exact this
  intro m
  induction m with
  | zero =>
    intro initArr res hEq; simp at hEq; subst hEq; omega
  | succ k ih =>
    intro initArr res hEq
    simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
    generalize hMid : (List.range k).foldl F (some initArr) = midResult at hEq
    match midResult with
    | none => rw [hNone] at hEq; simp at hEq
    | some midArr =>
      have hMidSz := ih initArr midArr hMid
      rcases hPush midArr k with hFail | ⟨x, hP⟩
      · rw [hFail] at hEq; simp at hEq
      · rw [hP] at hEq; simp at hEq; subst hEq
        simp [Array.size_push, hMidSz]; omega

/-- A foldl that propagates `none` and pushes one element per step:
    for each index `pc < res.size`, there exists an intermediate array `mid`
    of size `pc` such that `F (some mid) pc = some (mid.push res[pc])`. -/
private theorem foldl_push_content
    {n : Nat} {res : Array α}
    {F : Option (Array α) → Nat → Option (Array α)}
    (hNone : ∀ pc, F none pc = none)
    (hPush : ∀ arr pc, F (some arr) pc = none ∨ ∃ x, F (some arr) pc = some (arr.push x))
    (hFold : (List.range n).foldl F (some #[]) = some res)
    (pc : Nat) (hpc : pc < res.size) :
    ∃ mid : Array α, mid.size = pc ∧
      F (some mid) pc = some (mid.push res[pc]) := by
  have hResSz : res.size = n := foldl_push_size hNone hPush hFold
  -- Generalized: for foldl over range m starting from initArr
  suffices key : ∀ (m : Nat) (initArr midRes : Array α),
      (List.range m).foldl F (some initArr) = some midRes →
      midRes.size = initArr.size + m →
      ∀ k, k < m → (hk : initArr.size + k < midRes.size) →
        ∃ mid : Array α, mid.size = initArr.size + k ∧
          F (some mid) k = some (mid.push midRes[initArr.size + k]) by
    have := key n #[] res hFold (by simp; exact hResSz) pc (by omega) (by simp; exact hpc)
    simpa using this
  intro m
  induction m with
  | zero => intro _ _ _ _ k hk; omega
  | succ j ih =>
    intro initArr midRes hEq hSz k hk hkBound
    simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
    generalize hMid : (List.range j).foldl F (some initArr) = midResult at hEq
    match midResult with
    | none => rw [hNone] at hEq; simp at hEq
    | some midArr =>
      -- Get midArr size by the same foldl_push_size argument
      have hMidSz : midArr.size = initArr.size + j := by
        clear ih hEq hSz hk hkBound
        revert initArr midArr hMid
        induction j with
        | zero => intro i r h; simp at h; subst h; omega
        | succ j' ihj =>
          intro initArr midArr hEq
          simp only [List.range_succ, List.foldl_append, List.foldl] at hEq
          generalize hM : (List.range j').foldl F (some initArr) = mr at hEq
          match mr with
          | none => rw [hNone] at hEq; simp at hEq
          | some ma =>
            rcases hPush ma j' with hF | ⟨x, hP⟩
            · rw [hF] at hEq; simp at hEq
            · rw [hP] at hEq; simp at hEq; subst hEq
              simp [Array.size_push, ihj initArr ma hM]; omega
      rcases hPush midArr j with hFail | ⟨x, hP⟩
      · rw [hFail] at hEq; simp at hEq
      · rw [hP] at hEq; simp at hEq; subst hEq
        by_cases hkj : k = j
        · -- k = j: the element just pushed
          subst hkj
          have hNotLt : ¬ (initArr.size + k < midArr.size) := by omega
          simp only [Array.getElem_push, hNotLt, dite_false]
          exact ⟨midArr, hMidSz, hP⟩
        · -- k < j: use IH, element preserved by push
          have hkLt : k < j := by omega
          have hIdxLt : initArr.size + k < midArr.size := by omega
          have hPrevSz : midArr.size = initArr.size + j := hMidSz
          have ⟨mid, hMidSz', hStep⟩ := ih initArr midArr hMid hPrevSz k hkLt (by omega)
          refine ⟨mid, hMidSz', ?_⟩
          simp only [Array.getElem_push, hIdxLt, dite_true] at hStep ⊢
          exact hStep

-- ──────────────────────────────────────────────────────────────
-- bodyGenStep properties
-- ──────────────────────────────────────────────────────────────

@[simp] theorem bodyGenStep_none (code : Array TAC) (layout : VarLayout)
    (pcMap : Nat → Nat) (liveOut : Array (List Var))
    (varMap : List (Var × Nat)) (intervals : Array (Option BoundsOpt.IMap))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (haltS divS boundsS : Nat) (tyCtx : TyCtx) (pc : Nat) :
    bodyGenStep code layout pcMap liveOut varMap intervals arrayDecls
      haltS divS boundsS tyCtx none pc = none := rfl

theorem bodyGenStep_push (code : Array TAC) (layout : VarLayout)
    (pcMap : Nat → Nat) (liveOut : Array (List Var))
    (varMap : List (Var × Nat)) (intervals : Array (Option BoundsOpt.IMap))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (haltS divS boundsS : Nat) (tyCtx : TyCtx) (arr : Array (List ArmInstr)) (pc : Nat) :
    bodyGenStep code layout pcMap liveOut varMap intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = none ∨
    ∃ instrs, bodyGenStep code layout pcMap liveOut varMap intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = some (arr.push instrs) := by
  simp only [bodyGenStep]
  split <;> split <;> simp_all
  -- print case: push (simp_all removed the Or, leaving ∃)
  · exact ⟨_, rfl⟩
  -- non-print case: split on verifiedGenInstr
  · generalize verifiedGenInstr layout pcMap _ haltS divS boundsS arrayDecls _ = r
    cases r with
    | none => exact Or.inl rfl
    | some instrs => exact Or.inr ⟨_, rfl⟩

/-- `verifiedGenInstr` output length is independent of pcMap.
    For goto/ifgoto, pcMap changes values but not list length.
    For all other instructions, pcMap is unused so `simp` normalizes to identical terms. -/
private theorem verifiedGenInstr_length_pcMap_indep {layout : VarLayout}
    {pcMap₁ pcMap₂ : Nat → Nat} {instr : TAC}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {safe : Bool} {l₁ l₂ : List ArmInstr}
    (h₁ : verifiedGenInstr layout pcMap₁ instr haltS divS boundsS arrayDecls safe = some l₁)
    (h₂ : verifiedGenInstr layout pcMap₂ instr haltS divS boundsS arrayDecls safe = some l₂) :
    l₁.length = l₂.length := by
  cases instr with
  | goto l =>
    simp [verifiedGenInstr] at h₁ h₂
    obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂; subst h₁; subst h₂; rfl
  | ifgoto be l =>
    simp only [verifiedGenInstr] at h₁ h₂
    split at h₁ <;> simp_all
    -- Lists differ only in pcMap inside one instruction; length is identical
    all_goals (split at h₁ <;> split at h₂ <;> simp_all
               <;> (try (obtain ⟨_, rfl⟩ := h₁; obtain ⟨_, rfl⟩ := h₂; simp [List.length_append]))
               <;> (try (subst_vars; obtain ⟨_, rfl⟩ := h₂; simp [List.length_append])))
  | const _ val =>
    have : some l₁ = some l₂ := by rw [← h₁, ← h₂]; cases val <;> simp [verifiedGenInstr]
    exact congrArg _ (Option.some.inj this)
  | copy _ _ | binop _ _ _ _ | boolop _ _ | halt
  | arrLoad _ _ _ _ | arrStore _ _ _ _ | fbinop _ _ _ _
  | intToFloat _ _ | floatToInt _ _ | floatUnary _ _ _ | fternop _ _ _ _ _ =>
    have : some l₁ = some l₂ := by rw [← h₁, ← h₂]; simp [verifiedGenInstr]
    exact congrArg _ (Option.some.inj this)
  | print _ _ => simp [verifiedGenInstr] at h₁

/-- instrLength equals the length of the generated instruction list (including
    save/restore wrapping at call sites). -/
private theorem instrLength_eq_length {layout : VarLayout} {pcMap : Nat → Nat} {instr : TAC}
    {haltS divS boundsS : Nat} {arrayDecls : List (ArrayName × Nat × VarTy)}
    {safe : Bool} {instrs : List ArmInstr}
    {varMap : List (Var × Nat)}
    (h : verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe = some instrs) :
    instrLength layout arrayDecls safe instr haltS divS boundsS varMap =
      (if isLibCallTAC instr then
        let entries := callerSaveEntries layout varMap (DAEOpt.instrDef instr)
        (entriesToSaves entries ++ instrs ++ entriesToRestores entries).length
      else instrs.length) := by
  -- Print case: verifiedGenInstr returns none, contradicting h
  -- Non-print: instrLength uses dummy pcMap (fun _ => 0); equate lengths via pcMap-independence
  -- Lib-call: also need callSaveRestoreLen = saves.length + restores.length (definitional)
  cases instr with
  | print => simp [verifiedGenInstr] at h
  | const v val =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    cases val <;> simp_all <;> split at h <;> simp_all
  | copy dst src =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | binop x op y z =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | boolop x be =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | goto l =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all; subst_vars; simp
  | ifgoto be l =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
    split at h <;> simp_all
    all_goals (try obtain ⟨_, h⟩ := h)
    all_goals (subst_vars; simp [List.length_append, List.length_cons])
  | halt =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | arrLoad x arr idx ty =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | arrStore arr idx val ty =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | fbinop x fop y z =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.fbinop x fop y z) haltS divS boundsS arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_pcMap_ind layout (.fbinop x fop y z) haltS divS boundsS
          arrayDecls safe _ pcMap dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      cases fop <;> simp_all [Nat.add_comm] <;> omega
  | intToFloat x y =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | floatToInt x y =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all
  | floatUnary x op y =>
    simp only [instrLength, isLibCallTAC, callSaveRestoreLen, callerSaveEntries, DAEOpt.instrDef]
    generalize hd : verifiedGenInstr layout (fun _ => 0)
      (.floatUnary x op y) haltS divS boundsS arrayDecls safe = dr
    cases dr with
    | none =>
      simp only [verifiedGenInstr] at h hd
      split at hd <;> simp_all <;> split at h <;> simp_all
    | some dl =>
      have hLen := verifiedGenInstr_length_pcMap_ind layout (.floatUnary x op y) haltS divS boundsS
          arrayDecls safe _ pcMap dl instrs hd h
      simp only [hLen, List.length_append, entriesToSaves_length, entriesToRestores_length]
      cases op.isNative <;> simp_all [Nat.add_comm] <;> omega
  | fternop x op a b c =>
    simp only [instrLength, isLibCallTAC, verifiedGenInstr] at *
    split at h <;> simp_all


/-- The list pushed by `bodyGenStep` has length equal to `instrLength`. -/
private theorem bodyGenStep_length {code : Array TAC} {layout : VarLayout}
    {pcMap : Nat → Nat} {liveOut : Array (List Var)} {varMap : List (Var × Nat)}
    {intervals : Array (Option BoundsOpt.IMap)}
    {arrayDecls : List (ArrayName × Nat × VarTy)}
    {haltS divS boundsS : Nat} {tyCtx : TyCtx}
    {arr : Array (List ArmInstr)} {pc : Nat}
    {instrs : List ArmInstr}
    (hStep : bodyGenStep code layout pcMap liveOut varMap intervals arrayDecls
      haltS divS boundsS tyCtx (some arr) pc = some (arr.push instrs))
    (hpc : pc < code.size) :
    instrs.length = instrLength layout arrayDecls
      (isBoundsSafe arrayDecls intervals pc (code.getD pc .halt))
      (code.getD pc .halt) haltS divS boundsS varMap := by
  -- Normalize getD to getElem in goal
  have hGetD : code.getD pc .halt = code[pc] := by simp [Array.getD, hpc]
  rw [hGetD]
  -- Unfold bodyGenStep in hypothesis
  simp only [bodyGenStep, Array.getD, hpc, dite_true] at hStep
  -- Case split: print vs non-print (isPrint match)
  split at hStep
  · -- .print match
    rename_i fmt vs heq
    split at hStep
    · -- isPrint = true
      have heqI : code[pc] = TAC.print fmt vs := heq
      have := Array.push_inj (Option.some.inj hStep); subst this
      simp_all [instrLength, callSaveRestoreLen, callerSaveEntries, List.length_append]; omega
    · -- isPrint = false for .print: contradiction
      rename_i h; exact absurd rfl h
  · -- non-.print match
    rename_i heqPrint
    split at hStep
    · -- isPrint = true for non-print: contradiction
      rename_i h; simp at h
    · -- isPrint = false: the real non-print case
      simp at hStep
      split at hStep
      · simp at hStep  -- verifiedGenInstr = none: contradiction
      · rename_i armInstrs hGenInstr
        -- Use instrLength_eq_length to relate instrLength to verifiedGenInstr output
        rw [instrLength_eq_length hGenInstr]
        split at hStep
        · -- lib-call case
          rename_i hLib
          have hInstrs := Array.push_inj (Option.some.inj hStep)
          simp only [hLib, ite_true]; rw [← hInstrs]
          simp [List.length_append, entriesToSaves_length, entriesToRestores_length]
        · -- non-lib-call case
          rename_i hNotLib
          have hInstrs := Array.push_inj (Option.some.inj hStep)
          have hNotLib' : isLibCallTAC code[pc] = false := by
            cases h : isLibCallTAC code[pc] <;> simp_all
          simp [hNotLib', hInstrs]

/-- A successful `verifiedGenerateAsm` call satisfies `GenAsmSpec`. -/
theorem verifiedGenerateAsm_spec {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r) : GenAsmSpec tyCtx p r := by
  -- Unfold and clear error guards
  simp only [verifiedGenerateAsm] at hGen
  split at hGen <;> simp_all                     -- checkWellTypedProg
  -- scratchSafe
  split at hGen <;> simp_all
  -- isInjective
  split at hGen <;> simp_all
  -- checkWellTypedLayout
  split at hGen
  · simp_all
  · -- none case — continue
    -- checkCallerSaveSpec
    split at hGen
    · simp_all
    · -- !checkCallerSaveSpec = false, i.e. checkCallerSaveSpec = true
      rename_i hWTL hCSS
      replace hCSS : checkCallerSaveSpec
          (buildVarLayout (collectVars p) (buildVarMap (collectVars p)))
          (buildVarMap (collectVars p)) = true := by
        revert hCSS; simp
      -- checkBranchTargets
      split at hGen
      · simp_all
      · -- none case — continue to bodyResult
        split at hGen
        · simp_all
        · -- some bodyPerPC
          -- Extract r = constructed record
          simp only [Except.ok.injEq] at hGen; subst r
          rename_i bodyPerPC heqFold
          -- Foldl properties: Lean unifies F from heqFold
          have hBSz : bodyPerPC.size = p.code.size := by
            apply foldl_push_size _ _ heqFold
            · intro; rfl
            · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ arr pc
          refine ⟨
            checkWellTypedProg_sound ‹_›,
            checkWellTypedLayout_wellTyped ‹_›,
            by simp [Prog.size_eq]; exact hBSz,
            ?instrGen, ?pcMapLengths, ?layoutComplete, ?callSiteSaveRestore,
            ?printSaveRestore, ?callerSaveSpec⟩
          case instrGen =>
            intro pc hpc hNotLib hNotPrint
            have hpcB : pc < bodyPerPC.size := by rw [hBSz]; simp [Prog.size_eq] at hpc; exact hpc
            have hpcCode : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
            -- Get foldl content
            have hContent := by
              apply foldl_push_content _ _ heqFold pc hpcB
              · intro; rfl
              · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ arr pc
            obtain ⟨mid, _, hStep⟩ := hContent
            -- Unfold bodyGenStep; simplify getD to getElem
            simp only [bodyGenStep, Array.getD, show pc < p.code.size from hpcCode,
              dite_true] at hStep
            -- Case split on isPrint match, then if isPrint
            split at hStep <;> split at hStep
            · -- print, isTrue: contradicts hNotPrint
              simp_all
            · -- print, isFalse: contradicts (isPrint was true)
              simp_all
            · -- non-print, isTrue: false=true, absurd
              simp_all
            · -- non-print, isFalse: the real case
              simp at hStep
              -- Split on verifiedGenInstr
              split at hStep
              · simp at hStep
              · -- some armInstrs
                rename_i armInstrs hGenInstr
                -- isLibCallTAC is false (via hNotLib)
                have : isLibCallTAC p.code[pc] = false := hNotLib
                rw [this] at hStep; simp at hStep
                exact ⟨_, (Array.push_inj hStep) ▸ hGenInstr⟩
          case pcMapLengths =>
            -- Witness: the inline lengthsArr from codegen; pcMap = buildPcMap _ is rfl
            refine ⟨_, ?_, rfl, ?_⟩
            · -- size: lengthsArr.size = bodyPerPC.size (both = p.code.size)
              simp [List.length_map, List.length_range, hBSz]
            · -- element equality: lengthsArr[i] = bodyPerPC[i].length
              intro i hL hB
              -- lengthsArr[i] = instrLength at pc i
              -- bodyPerPC[i].length = instrLength at pc i (by bodyGenStep_length)
              have hpcCode : i < p.code.size := by rw [← hBSz]; exact hB
              have hContent := by
                apply foldl_push_content _ _ heqFold i hB
                · intro; rfl
                · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ arr pc
              obtain ⟨mid, _, hStep⟩ := hContent
              rw [bodyGenStep_length hStep hpcCode]
              -- Now: instrLength ... = instrLength ... (should be rfl or simp)
              simp [List.getElem_toArray, List.getElem_map]
          case layoutComplete =>
            intro pc hpc v hv
            exact checkWellTypedLayout_instrMapped ‹_› (by simp [Prog.size_eq] at hpc; exact hpc) hv
          case callSiteSaveRestore =>
            intro pc hpc hLib
            have hpcB : pc < bodyPerPC.size := by rw [hBSz]; simp [Prog.size_eq] at hpc; exact hpc
            have hpcCode : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
            have hContent := by
              apply foldl_push_content _ _ heqFold pc hpcB
              · intro; rfl
              · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ arr pc
            obtain ⟨mid, _, hStep⟩ := hContent
            simp only [bodyGenStep, Array.getD, show pc < p.code.size from hpcCode,
              dite_true] at hStep
            -- Not a print (lib-call TACs are floatUnary/fpow, not print)
            split at hStep <;> split at hStep
            · -- print, isTrue: print is not a lib-call
              simp_all [isLibCallTAC]
            · simp_all  -- print, isFalse
            · simp_all  -- non-print, isTrue
            · -- non-print, isFalse: the real case
              simp at hStep
              split at hStep
              · simp at hStep  -- verifiedGenInstr = none: contradiction
              · rename_i armInstrs hGenInstr
                -- isLibCallTAC is true
                rw [show isLibCallTAC p.code[pc] = true from hLib] at hStep
                simp only [ite_true] at hStep
                have hEq := (Array.push_inj (Option.some.inj hStep)).symm
                rw [← List.append_assoc] at hEq
                exact ⟨armInstrs, hGenInstr, hEq⟩
          case printSaveRestore =>
            intro pc hpc ⟨fmt, vs, hPrint⟩
            have hpcB : pc < bodyPerPC.size := by rw [hBSz]; simp [Prog.size_eq] at hpc; exact hpc
            have hpcCode : pc < p.code.size := by simp [Prog.size_eq] at hpc; exact hpc
            have hContent := by
              apply foldl_push_content _ _ heqFold pc hpcB
              · intro; rfl
              · intro arr pc; exact bodyGenStep_push _ _ _ _ _ _ _ _ _ _ _ arr pc
            obtain ⟨mid, _, hStep⟩ := hContent
            simp only [bodyGenStep, Array.getD, show pc < p.code.size from hpcCode,
              dite_true] at hStep
            -- Print case: isPrint = true
            split at hStep <;> split at hStep
            · -- print, isTrue: extract entriesToSaves ++ [printCall] ++ entriesToRestores
              have hEq := (Array.push_inj (Option.some.inj hStep)).symm
              exact ⟨_, hEq⟩
            · -- print, isFalse: contradiction
              rename_i h; exact absurd rfl h
            · -- non-print, isTrue: contradiction (p[pc] is .print)
              rename_i heq h
              have hPE : p[pc] = TAC.print fmt vs := hPrint
              simp [Prog.getElem_eq] at hPE
              simp_all
            · -- non-print, isFalse
              rename_i heq h
              have hPE : p[pc] = TAC.print fmt vs := hPrint
              simp [Prog.getElem_eq] at hPE
              simp_all
          case callerSaveSpec =>
            exact checkCallerSaveSpec_sound hCSS


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
private theorem step_simulation {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : ExtSimRel r.layout r.pcMap (.run pc σ am) s)
    (hPC : pc < p.size)
    (hTS : TypedStore tyCtx σ) :
    ∃ s', ArmSteps r.bodyFlat s s' ∧
          ExtSimRel r.layout r.pcMap cfg' s' := by
  -- Case split: lib-call, print, or normal instruction
  by_cases hLib : isLibCallTAC p[pc] = true
  · -- Lib-call case: save/restore around computation (excludes destination)
    -- Determine cfg' early (before infrastructure, to avoid simp_all pollution)
    have hCfgRun : ∃ σ', cfg' = .run (pc + 1) σ' am := by
      have : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      cases hStep <;> simp_all [isLibCallTAC]
      -- Remaining: type-error cases — impossible under TypedStore + WellTypedProg
      -- WellTypedInstr gives Γ y = .float; TypedStore gives (σ y).typeOf = Γ y = .float
      all_goals {
        rename_i hInstr hTypeErr
        have hWTI := spec.wellTypedProg pc hPC
        rw [show p[pc] = p.code[pc] from rfl] at hWTI
        rw [hInstr] at hWTI
        cases hWTI <;> simp_all [TypedStore]
      }
    obtain ⟨σ', hCfg⟩ := hCfgRun
    -- TAC-level: lib-call only modifies the destination variable
    -- Prove before subst to avoid am-dependency issues in cases hStep
    have hDstOnly : ∀ v, DAEOpt.instrDef p[pc] ≠ some v → σ' v = σ v := by
      have : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      -- cases hStep with cfg' still abstract (avoids am = am.write unification)
      intro v hne
      cases hStep <;> simp_all [isLibCallTAC, DAEOpt.instrDef]
      all_goals (rw [← ‹_ = σ'›]; simp [Store.update]; intro h; exact absurd h.symm ‹_›)
    -- TAC result: σ' = σ[dst ↦ result] (before subst, to avoid am-dependency)
    have hLibStep : ∀ x op y, p.code[pc] = .floatUnary x op y →
        ∃ f, σ y = .float f ∧ σ' x = .float (op.eval f) := by
      have hpc : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      intro x' op' y' hI
      have hI' : p[pc]? = some (.floatUnary x' op' y') := by
        simp [Prog.getElem?_code, Array.getElem?_eq_getElem hpc, hI]
      cases hStep with
      | floatUnary hinstr hy =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl⟩
        exact ⟨_, hy, by cases hCfg; simp [Store.update_self]⟩
      | floatUnary_typeError hinstr hne =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl⟩
        have hWTI := spec.wellTypedProg pc hPC
        rw [show p[pc] = p.code[pc] from rfl, hI] at hWTI
        cases hWTI <;> simp_all [TypedStore]
      | _ => exfalso; simp_all
    have hLibStepBin : ∀ x y z, p.code[pc] = .fbinop x .fpow y z →
        ∃ fy fz, σ y = .float fy ∧ σ z = .float fz ∧
          σ' x = .float (FloatBinOp.eval .fpow fy fz) := by
      have hpc : pc < p.code.size := by simp [Prog.size_eq] at hPC; exact hPC
      intro x' y' z' hI
      have hI' : p[pc]? = some (.fbinop x' .fpow y' z') := by
        simp [Prog.getElem?_code, Array.getElem?_eq_getElem hpc, hI]
      cases hStep with
      | fbinop hinstr hy hz =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨_, _, hy, hz, by cases hCfg; simp [Store.update_self]⟩
      | fbinop_typeError hinstr hne =>
        have := Option.some.inj (hI'.symm.trans hinstr)
        rcases this with ⟨rfl, rfl, rfl, rfl⟩
        have hWTI := spec.wellTypedProg pc hPC
        rw [show p[pc] = p.code[pc] from rfl, hI] at hWTI
        cases hWTI <;> simp_all [TypedStore]
      | _ => exfalso; simp_all
    subst hCfg
    -- Get bodyPerPC = saves ++ baseInstrs ++ restores
    obtain ⟨baseInstrs, hGenInstr, hBody⟩ :=
      spec.callSiteSaveRestore pc hPC hLib
    -- Infrastructure
    obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
    have hpcB : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
    have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc) (r.bodyPerPC[pc]'hpcB) := by
      rw [hPcMap]; exact codeAt_of_bodyFlat r.bodyPerPC lengths hLSz hLenEq pc hpcB
    rw [hBody] at hCodeAt
    -- Abbreviate entries
    let entries := callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
    -- Split CodeAt: saves ++ baseInstrs ++ restores
    have hCodeSB := hCodeAt.append_left (l2 := entriesToRestores entries)
    have hCodeRestores := hCodeAt.append_right
      (l1 := entriesToSaves entries ++ baseInstrs)
    have hCodeSaves := hCodeSB.append_left (l2 := baseInstrs)
    have hCodeBase := hCodeSB.append_right (l1 := entriesToSaves entries)
    -- Extract ExtStateRel components
    obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
    have hSPC : s.pc = r.pcMap pc := hPcRel
    -- hPcNext
    have hPcNext : r.pcMap (pc + 1) = r.pcMap pc + (r.bodyPerPC[pc]'hpcB).length := by
      rw [hPcMap, buildPcMap_succ lengths pc (by rw [hLSz]; exact hpcB)]
      congr 1; exact hLenEq pc (by rw [hLSz]; exact hpcB) hpcB
    -- Step 1: saves
    have hStepSaves := armSteps_saves r.bodyFlat entries s (hSPC ▸ hCodeSaves)
    let s_saved := {applyCallerSaves entries s with pc := s.pc + entries.length}
    have hSavedPC : s_saved.pc = r.pcMap pc + (entriesToSaves entries).length := by
      simp [s_saved, entriesToSaves_length, hSPC]
    -- Entry vars (non-dst caller-saved) are unchanged by the TAC step.
    -- An entry var's register is in callerSaveEntries, which excludes the dst.
    -- So the var ≠ dst, and hDstOnly gives σ'(v) = σ(v).
    have hEIU : ∀ v ir, r.layout v = some (.ireg ir) →
        (∃ off, CallerSaveEntry.ireg ir off ∈ entries) → σ' v = σ v := by
      intro v ir hLoc ⟨off, hMem⟩
      apply hDstOnly; intro hContra
      -- hContra : DAEOpt.instrDef p[pc] = some v
      -- hMem : .ireg ir off ∈ callerSaveEntries ... (some v)
      -- callerSaveEntries filters out entries matching layout v's register
      -- Since layout v = .ireg ir, the filter removes .ireg ir entries
      show False
      simp only [show entries = callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) from rfl,
        callerSaveEntries, hContra] at hMem
      rw [List.mem_filter] at hMem
      simp [hLoc] at hMem
    have hEFU : ∀ v fr, r.layout v = some (.freg fr) →
        (∃ off, CallerSaveEntry.freg fr off ∈ entries) → σ' v = σ v := by
      intro v fr hLoc ⟨off, hMem⟩
      apply hDstOnly; intro hContra
      show False
      simp only [show entries = callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) from rfl,
        callerSaveEntries, hContra] at hMem
      rw [List.mem_filter] at hMem
      simp [hLoc] at hMem
    -- ARM-level: base instruction stepping + state properties
    have hBaseExists : ∃ s_mid : ArmState,
        ArmSteps r.bodyFlat s_saved s_mid ∧
        s_mid.pc = s_saved.pc + baseInstrs.length ∧
        s_mid.arrayMem = am ∧
        (∀ e ∈ entries, s_mid.stack e.off = (applyCallerSaves entries s).stack e.off) ∧
        (∀ v ir, r.layout v = some (.ireg ir) →
          (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s_mid.regs ir = (σ' v).encode) ∧
        (∀ v fr, r.layout v = some (.freg fr) →
          (∀ off, CallerSaveEntry.freg fr off ∉ entries) → s_mid.fregs fr = (σ' v).encode) ∧
        (∀ v off, r.layout v = some (.stack off) → s_mid.stack off = (σ' v).encode) := by
      -- Step 0: ExtStateRel for s_saved
      have hEntriesSub' : entries.Sublist (genCallerSaveAll r.layout r.varMap) := by
        show (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])).Sublist _
        unfold callerSaveEntries
        cases DAEOpt.instrDef p[pc] with
        | none => exact List.Sublist.refl _
        | some _ => exact List.filter_sublist
      have hRelSaved : ExtStateRel r.layout σ s_saved := by
        show ExtStateRel r.layout σ {applyCallerSaves entries s with pc := s.pc + entries.length}
        intro v loc hv
        exact ExtStateRel.applyCallerSaves_preserved hStateRel entries
          (fun e he v' => spec.callerSaveSpec.1 e (hEntriesSub'.subset he) v') v loc hv
      -- Step 1: case-split on p[pc]
      cases hInstr : p.code[pc] with
      | floatUnary x op y =>
        -- Step 2: unfold verifiedGenInstr for floatUnary
        rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
        have hSS : r.layout.scratchSafe = true := by
          cases h : r.layout.scratchSafe
          · simp [verifiedGenInstr, h] at hGenInstr
          · rfl
        have hII : r.layout.isInjective = true := by
          cases h : r.layout.isInjective
          · simp [verifiedGenInstr, hSS, h] at hGenInstr
          · rfl
        have hScratch : ExtScratchSafe r.layout := VarLayout.scratchSafe_spec r.layout hSS
        have hInjective : VarLayoutInjective r.layout := VarLayout.isInjective_spec r.layout hII
        have hNotIregY : ∀ ir, r.layout y ≠ some (.ireg ir) := by
          intro ir h; have := hGenInstr; simp [verifiedGenInstr, hSS, hII, h] at this
        have hNotIregX : ∀ ir, r.layout x ≠ some (.ireg ir) := by
          intro ir h; have := hGenInstr
          simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or, h] at this
          split at this <;> simp_all
        let src_reg := match r.layout y with | some (.freg r) => r | _ => ArmFReg.d0
        let dst_reg := match r.layout x with | some (.freg r) => r | _ => ArmFReg.d0
        have hInstrs : baseInstrs =
            vLoadVarFP r.layout y src_reg ++ [.floatUnaryInstr op dst_reg src_reg] ++
            vStoreVarFP r.layout x dst_reg := by
          simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or] at hGenInstr
          split at hGenInstr
          · simp_all
          · exact (Option.some.inj hGenInstr).symm
        -- Phase A: load y into src_reg
        rw [hInstrs] at hCodeBase
        have hCodeLoad := hCodeBase.append_left.append_left
          (l2 := [.floatUnaryInstr op dst_reg src_reg])
        have hMappedY : r.layout y ≠ none := by
          have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) y
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
          exact this (by simp [TAC.vars])
        obtain ⟨s1, hSteps1, hSR1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
          vLoadVarFP_eff_exec r.bodyFlat r.layout y σ s_saved
            (r.pcMap pc + (entriesToSaves entries).length) .d0
            hRelSaved hScratch hSavedPC hNotIregY (Or.inl rfl) hMappedY hCodeLoad
        -- Phase B: havoc (floatUnaryLibCall)
        have hCodeMid := hCodeBase.append_left.append_right
          (l1 := vLoadVarFP r.layout y src_reg)
        have hCall : r.bodyFlat[s1.pc]? = some (.floatUnaryInstr op dst_reg src_reg) := by
          rw [hPC1]; exact hCodeMid.head
        have hNotNat : op.isNative = false := by
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at hLib
          cases op <;> simp [isLibCallTAC, FloatUnaryOp.isNative] at hLib ⊢
        let newRegs : ArmReg → BitVec 64 := fun _ => 0
        let newFregs : ArmFReg → BitVec 64 := fun _ => 0
        let s2 := s1.havocCallerSaved newRegs newFregs |>.setFReg dst_reg (op.eval (s1.fregs src_reg)) |>.nextPC
        have hSteps2 : ArmSteps r.bodyFlat s1 s2 :=
          .single (.floatUnaryLibCall op dst_reg src_reg newRegs newFregs hCall hNotNat)
        -- Phase C: store dst_reg into x (manual, ExtStateRel broken)
        have hPC2 : s2.pc = s1.pc + 1 := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
        have hCodeStore : CodeAt r.bodyFlat s2.pc (vStoreVarFP r.layout x dst_reg) := by
          have h := hCodeBase.append_right
            (l1 := vLoadVarFP r.layout y src_reg ++ [.floatUnaryInstr op dst_reg src_reg])
          rw [hPC2, hPC1]; simp [List.length_append] at h ⊢; exact h
        -- Step through vStoreVarFP and compose
        -- Shared facts for all sub-cases
        have hPC1' : s1.pc = r.pcMap pc + (entriesToSaves entries).length +
            (vLoadVarFP r.layout y src_reg).length := hPC1
        have hAM2 : s2.arrayMem = s1.arrayMem := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
        have hAMChain : s2.arrayMem = am := by
          rw [hAM2, hAM1]; simp [s_saved, applyCallerSaves_arrayMem, hArrayMem]
        -- Non-entry ireg: shared across all sub-cases (store doesn't touch iregs)
        have hNEI_shared : ∀ v ir, r.layout v = some (.ireg ir) →
            (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s2.regs ir = (σ' v).encode := by
          intro v ir hLoc hNE
          -- s2.regs ir = (havocCallerSaved ...).regs ir (setFReg/nextPC don't touch regs)
          have : s2.regs ir = (s1.havocCallerSaved newRegs newFregs).regs ir := by
            simp [s2, ArmState.nextPC, ArmState.setFReg]
          rw [this]
          -- ir must be callee-saved (otherwise genCallerSaveAll has an entry, which
          -- passes the callerSaveEntries filter since layout x isn't ireg)
          have hCS : ir.isCallerSaved = false := by
            cases hcs : ir.isCallerSaved with
            | false => rfl
            | true =>
            obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
            obtain ⟨coff, hMem⟩ := hCoversIreg v ir hLoc hcs
            -- hMem : .ireg ir coff ∈ genCallerSaveAll
            -- Show it passes the callerSaveEntries filter (layout x isn't ireg)
            have hInE : CallerSaveEntry.ireg ir coff ∈ entries := by
              show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
              rw [show p[pc] = p.code[pc] from rfl, hInstr]
              simp only [callerSaveEntries, DAEOpt.instrDef]
              rw [List.mem_filter]
              refine ⟨hMem, ?_⟩
              rcases hlx2 : r.layout x with _ | ⟨off2 | ir2 | fr2⟩ <;> simp [hlx2]
              exact absurd hlx2 (hNotIregX ir2)
            exact absurd hInE (hNE coff)
          -- Callee-saved: havocCallerSaved preserves ir
          show (fun r => if r.isCallerSaved then newRegs r else s1.regs r) ir = _
          simp [hCS]
          -- s1.regs = s_saved.regs = s.regs (load doesn't touch iregs)
          rw [hRegs1]; simp [s_saved, applyCallerSaves_regs]
          -- s.regs ir = (σ v).encode by hStateRel
          have hVal := hStateRel v (.ireg ir) hLoc; simp at hVal; rw [hVal]
          -- σ' v = σ v since dst (x) is not v (x is freg/stack, v is ireg)
          have hne : DAEOpt.instrDef p[pc] ≠ some v := by
            rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
            intro h; rw [← h] at hLoc; exact absurd hLoc (hNotIregX ir)
          rw [hDstOnly v hne]
        -- Save slots: s2.stack = (applyCallerSaves entries s).stack
        have hStack2 : s2.stack = (applyCallerSaves entries s).stack := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved_stack, hStack1, s_saved]
        -- TAC result: extract σ' x and connect to ARM
        obtain ⟨f, hfy, hσx⟩ := hLibStep x op y hInstr
        -- ARM result: s2.fregs dst_reg = op.eval f = (σ' x).encode
        have hSR1' : s1.fregs src_reg = (σ y).encode := hSR1
        have hArmResult : s2.fregs dst_reg = (σ' x).encode := by
          simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
          rw [hSR1', hfy, hσx]; simp [Value.encode]
        rcases hlx : r.layout x with _ | ⟨off | ir | fr⟩
        · -- none: vStoreVarFP = [], s_mid = s2
          have hSS2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
            fun e _ => by rw [hStack2]
          refine ⟨s2, hSteps1.trans hSteps2, ?_, hAMChain, hSS2, hNEI_shared, ?_, ?_⟩
          · -- PC
            rw [hPC2, hPC1', hSavedPC, hInstrs]; simp [vStoreVarFP, hlx, List.length_append]; omega
          · -- non-entry freg
            intro v fr hLoc hNE
            -- dst_reg = .d0 (layout x = none), so fr ≠ .d0 by scratchSafe
            have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
            have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hScratch.not_d0 v)
            -- s2.fregs fr = (havocCallerSaved ...).fregs fr (setFReg only changed .d0)
            have : s2.fregs fr = (s1.havocCallerSaved newRegs newFregs).fregs fr := by
              simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
            rw [this]
            -- fr callee-saved (same argument as ireg)
            have hCS : fr.isCallerSaved = false := by
              cases hcs : fr.isCallerSaved with
              | false => rfl
              | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
              have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                rw [show p[pc] = p.code[pc] from rfl, hInstr]
                simp only [callerSaveEntries, DAEOpt.instrDef]
                rw [List.mem_filter]
                exact ⟨hMem, by simp [hlx]⟩
              exact absurd hInE (hNE coff)
            show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr = _
            simp [hCS]
            -- s1.fregs fr preserved from load (fr ≠ src_reg or fr = src_reg)
            -- Use hRel1 (ExtStateRel for s1) since load preserves it
            have hVal := hRel1 v (.freg fr) hLoc; simp at hVal; rw [hVal]
            -- σ' v = σ v (v ≠ x since layout x = none)
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; rw [← h] at hLoc; simp [hlx] at hLoc
            rw [hDstOnly v hne]
          · -- stack vars
            intro v off' hLoc
            rw [hStack2]
            have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; rw [← h] at hLoc; simp [hlx] at hLoc
            rw [hDstOnly v hne]
        · -- stack off: vStoreVarFP = [.fstr dst_reg off]
          simp [vStoreVarFP, hlx] at hCodeStore
          have hFstr : r.bodyFlat[s2.pc]? = some (.fstr dst_reg off) := hCodeStore.head
          let s3 := (s2.setStack off (s2.fregs dst_reg)).nextPC
          have hSteps3 : ArmSteps r.bodyFlat s2 s3 :=
            .single (.fstr dst_reg off hFstr)
          have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setStack]
          have hNEI3 : ∀ v ir, r.layout v = some (.ireg ir) →
              (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s3.regs ir = (σ' v).encode :=
            fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
          have hSS3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off := by
            intro e he
            simp [s3, ArmState.nextPC, ArmState.setStack]
            -- e.off ≠ off because off is a layout offset for x, and save slots are fresh
            have hne : e.off ≠ off := by
              intro heq
              exact spec.callerSaveSpec.1 e (hEntriesSub'.subset he) x (heq ▸ hlx)
            simp [hne, hStack2]
          refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ?_, ?_, hSS3, hNEI3, ?_, ?_⟩
          · -- PC
            simp [s3, ArmState.nextPC, ArmState.setStack]
            rw [hPC2, hPC1', hSavedPC, hInstrs]; simp [vStoreVarFP, hlx, List.length_append]; omega
          · -- arrayMem
            simp [s3, ArmState.nextPC, ArmState.setStack, hAMChain]
          · -- non-entry freg (s3.fregs = s2.fregs since setStack doesn't touch fregs)
            intro v fr hLoc hNE
            have hFregs3 : s3.fregs = s2.fregs := by simp [s3, ArmState.nextPC, ArmState.setStack]
            rw [hFregs3]
            -- dst_reg = .d0 (layout x = stack, not freg)
            have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
            have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hScratch.not_d0 v)
            have : s2.fregs fr = (s1.havocCallerSaved newRegs newFregs).fregs fr := by
              simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
            rw [this]
            have hCS : fr.isCallerSaved = false := by
              cases hcs : fr.isCallerSaved with
              | false => rfl
              | true =>
              obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
              have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                rw [show p[pc] = p.code[pc] from rfl, hInstr]
                simp only [callerSaveEntries, DAEOpt.instrDef]
                rw [List.mem_filter]
                exact ⟨hMem, by simp [hlx]⟩
              exact absurd hInE (hNE coff)
            show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr = _
            simp [hCS]
            have hVal := hRel1 v (.freg fr) hLoc; simp at hVal; rw [hVal]
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; subst h; rw [hlx] at hLoc; cases hLoc
            rw [hDstOnly v hne]
          · -- stack vars
            intro v off' hLoc
            simp [s3, ArmState.nextPC, ArmState.setStack]
            by_cases hvo : off' = off
            · -- v maps to same offset as x → v = x by injectivity
              have hvx : v = x := hInjective v x (.stack off) (hvo ▸ hLoc) hlx
              subst hvx
              simp [hvo]; exact hArmResult
            · -- different offset → use s2.stack
              simp [hvo, hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hvx : v ≠ x := by
                intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hvo rfl
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]; exact hvx.symm
              rw [hDstOnly v hne]
        · -- ireg: impossible
          exact absurd hlx (hNotIregX ir)
        · -- freg r: vStoreVarFP = fmovRR or []
          by_cases hEq : fr == dst_reg
          · -- fr = dst_reg: vStoreVarFP = [], s_mid = s2
            simp [vStoreVarFP, hlx, hEq] at hCodeStore
            have hSS2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
              fun e _ => by rw [hStack2]
            refine ⟨s2, hSteps1.trans hSteps2, ?_, hAMChain, hSS2, hNEI_shared, ?_, ?_⟩
            · -- PC
              rw [hPC2, hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
            · -- non-entry freg (s_mid = s2, dst_reg = fr)
              intro v fr' hLoc hNE
              have hDR : dst_reg = fr := by simp [dst_reg, hlx]
              by_cases hff : fr' = fr
              · -- fr' = fr = dst_reg → v = x by injectivity
                subst hff; have := hInjective v x _ hLoc hlx; subst this
                rw [hDR] at hArmResult; exact hArmResult
              · -- fr' ≠ fr → setFReg didn't touch fr'
                have : s2.fregs fr' = (s1.havocCallerSaved newRegs newFregs).fregs fr' := by
                  simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                rw [this]
                have hCS : fr'.isCallerSaved = false := by
                  cases hcs : fr'.isCallerSaved with
                  | false => rfl
                  | true =>
                  obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                  obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                  have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                    show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]
                    simp only [callerSaveEntries, DAEOpt.instrDef]
                    rw [List.mem_filter]
                    refine ⟨hMem, ?_⟩; simp [hlx, hff]
                  exact absurd hInE (hNE coff)
                show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr' = _
                simp [hCS]
                have hVal := hRel1 v (.freg fr') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc; rw [hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; rw [hlx] at hLoc; cases hLoc
              rw [hDstOnly v hne]
          · -- fr ≠ dst_reg: vStoreVarFP = [.fmovRR fr dst_reg]
            simp [vStoreVarFP, hlx, hEq] at hCodeStore
            have hFmov : r.bodyFlat[s2.pc]? = some (.fmovRR fr dst_reg) := hCodeStore.head
            let s3 := (s2.setFReg fr (s2.fregs dst_reg)).nextPC
            have hSteps3 : ArmSteps r.bodyFlat s2 s3 :=
              .single (.fmovRR fr dst_reg hFmov)
            have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setFReg]
            have hNEI3 : ∀ v ir, r.layout v = some (.ireg ir) →
                (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s3.regs ir = (σ' v).encode :=
              fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
            have hStack3 : s3.stack = s2.stack := by simp [s3, ArmState.nextPC, ArmState.setFReg]
            have hSS3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off :=
              fun e _ => by rw [hStack3, hStack2]
            refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ?_, ?_, hSS3, hNEI3, ?_, ?_⟩
            · -- PC
              simp [s3, ArmState.nextPC, ArmState.setFReg]
              rw [hPC2, hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
            · -- arrayMem
              simp [s3, ArmState.nextPC, ArmState.setFReg, hAMChain]
            · -- non-entry freg (s3 = setFReg fr ... of s2)
              intro v fr' hLoc hNE
              have hDR : dst_reg = fr := by simp [dst_reg, hlx]
              by_cases hff : fr' = fr
              · -- fr' = fr → v = x, s3.fregs fr = s2.fregs dst_reg = (σ' x).encode
                have hvx := hInjective v x _ (hff ▸ hLoc) hlx; subst hvx
                simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                exact hArmResult
              · -- fr' ≠ fr → s3.fregs fr' = s2.fregs fr'
                have : s3.fregs fr' = s2.fregs fr' := by
                  simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                rw [this]
                have : s2.fregs fr' = (s1.havocCallerSaved newRegs newFregs).fregs fr' := by
                  simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                rw [this]
                have hCS : fr'.isCallerSaved = false := by
                  cases hcs : fr'.isCallerSaved with
                  | false => rfl
                  | true =>
                  obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                  obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                  have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                    show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]
                    simp only [callerSaveEntries, DAEOpt.instrDef]
                    rw [List.mem_filter]
                    refine ⟨hMem, ?_⟩; simp [hlx, hff]
                  exact absurd hInE (hNE coff)
                show (fun r => if r.isCallerSaved then newFregs r else s1.fregs r) fr' = _
                simp [hCS]
                have hVal := hRel1 v (.freg fr') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc; rw [hStack3, hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; rw [hlx] at hLoc; cases hLoc
              rw [hDstOnly v hne]
      | fbinop x fop y z =>
        cases fop with
        | fpow =>
          -- Step 2: unfold verifiedGenInstr for fbinop fpow
          rw [show p[pc] = p.code[pc] from rfl, hInstr] at hGenInstr
          have hSS : r.layout.scratchSafe = true := by
            cases h : r.layout.scratchSafe
            · simp [verifiedGenInstr, h] at hGenInstr
            · rfl
          have hII : r.layout.isInjective = true := by
            cases h : r.layout.isInjective
            · simp [verifiedGenInstr, hSS, h] at hGenInstr
            · rfl
          have hScratch : ExtScratchSafe r.layout := VarLayout.scratchSafe_spec r.layout hSS
          have hInjective : VarLayoutInjective r.layout := VarLayout.isInjective_spec r.layout hII
          have hNotIregY : ∀ ir, r.layout y ≠ some (.ireg ir) := by
            intro ir h; have := hGenInstr; simp [verifiedGenInstr, hSS, hII, h] at this
          have hNotIregZ : ∀ ir, r.layout z ≠ some (.ireg ir) := by
            intro ir h; have := hGenInstr; simp [verifiedGenInstr, hSS, hII, h] at this
          have hNotIregX : ∀ ir, r.layout x ≠ some (.ireg ir) := by
            intro ir h; have := hGenInstr; simp [verifiedGenInstr, hSS, hII, h] at this
          let lv_reg := match r.layout y with | some (.freg r) => r | _ => ArmFReg.d1
          let rv_reg := match r.layout z with | some (.freg r) => r | _ => ArmFReg.d2
          let dst_reg := match r.layout x with | some (.freg r) => r | _ => ArmFReg.d0
          have hInstrs : baseInstrs =
              vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg ++
              [.callBinF .fpow dst_reg lv_reg rv_reg] ++
              vStoreVarFP r.layout x dst_reg := by
            have h := hGenInstr
            simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or] at h
            -- Eliminate ireg branches by case-splitting each layout
            rcases hly : r.layout y with _ | ⟨ir | fr | off⟩
            all_goals rcases hlz : r.layout z with _ | ⟨ir | fr | off⟩
            all_goals rcases hlx : r.layout x with _ | ⟨ir | fr | off⟩
            all_goals (try { exact absurd hly (hNotIregY _) })
            all_goals (try { exact absurd hlz (hNotIregZ _) })
            all_goals (try { exact absurd hlx (hNotIregX _) })
            all_goals (simp [hly, hlz, hlx, lv_reg, rv_reg, dst_reg] at h ⊢; exact h.symm)
          -- Phase A: load y into lv_reg, then z into rv_reg
          rw [hInstrs] at hCodeBase
          have hCodeLoad1 := hCodeBase.append_left.append_left.append_left
            (l2 := vLoadVarFP r.layout z rv_reg)
          have hMappedY : r.layout y ≠ none := by
            have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) y
            rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
            exact this (by simp [TAC.vars])
          obtain ⟨s1, hSteps1, hSR1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
            vLoadVarFP_eff_exec r.bodyFlat r.layout y σ s_saved
              (r.pcMap pc + (entriesToSaves entries).length) .d1
              hRelSaved hScratch hSavedPC hNotIregY (Or.inr (Or.inl rfl)) hMappedY hCodeLoad1
          -- Second load: z into rv_reg
          have hCodeLoad2 : CodeAt r.bodyFlat s1.pc (vLoadVarFP r.layout z rv_reg) := by
            rw [hPC1]
            exact hCodeBase.append_left.append_left.append_right
              (l1 := vLoadVarFP r.layout y lv_reg)
          have hMappedZ : r.layout z ≠ none := by
            have := spec.layoutComplete pc (by simp [Prog.size_eq] at hPC; exact hPC) z
            rw [show p[pc] = p.code[pc] from rfl, hInstr] at this
            exact this (by simp [TAC.vars])
          obtain ⟨s1b, hSteps1b, hSR1b, hRel1b, hRegs1b, hPC1b, hAM1b, hFregs1b, hStack1b⟩ :=
            vLoadVarFP_eff_exec r.bodyFlat r.layout z σ s1
              s1.pc .d2
              hRel1 hScratch rfl hNotIregZ (Or.inr (Or.inr rfl)) hMappedZ hCodeLoad2
          -- Phase B: havoc (callBinF)
          have hCodeMid := hCodeBase.append_left.append_right
            (l1 := vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg)
          have hPC1' : s1.pc = r.pcMap pc + (entriesToSaves entries).length +
              (vLoadVarFP r.layout y lv_reg).length := hPC1
          have hPC1b' : s1b.pc = s1.pc + (vLoadVarFP r.layout z rv_reg).length := hPC1b
          have hCall : r.bodyFlat[s1b.pc]? = some (.callBinF .fpow dst_reg lv_reg rv_reg) := by
            rw [hPC1b', hPC1']
            have hIdx : r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg).length + (vLoadVarFP r.layout z rv_reg).length =
              r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg).length := by
              simp [List.length_append]; omega
            rw [hIdx]; exact hCodeMid.head
          let newRegs : ArmReg → BitVec 64 := fun _ => 0
          let newFregs : ArmFReg → BitVec 64 := fun _ => 0
          let s2 := s1b.havocCallerSaved newRegs newFregs |>.setFReg dst_reg
            (FloatBinOp.eval .fpow (s1b.fregs lv_reg) (s1b.fregs rv_reg)) |>.nextPC
          have hSteps2 : ArmSteps r.bodyFlat s1b s2 :=
            .single (.callBinF .fpow dst_reg lv_reg rv_reg newRegs newFregs hCall)
          -- Phase C setup: shared facts
          have hPC2 : s2.pc = s1b.pc + 1 := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
          have hAM2 : s2.arrayMem = s1b.arrayMem := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
          have hAMChain : s2.arrayMem = am := by
            rw [hAM2, hAM1b, hAM1]; simp [s_saved, applyCallerSaves_arrayMem, hArrayMem]
          have hStack2 : s2.stack = (applyCallerSaves entries s).stack := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved_stack,
              hStack1b, hStack1, s_saved]
          -- TAC result
          obtain ⟨fy, fz, hfy, hfz, hσx⟩ := hLibStepBin x y z hInstr
          have hSR1' : s1.fregs lv_reg = (σ y).encode := hSR1
          have hSR1b' : s1b.fregs rv_reg = (σ z).encode := hSR1b
          -- s1b.fregs lv_reg = (σ y).encode (preserved across second load)
          have hLvPreserved : s1b.fregs lv_reg = (σ y).encode := by
            rcases hly : r.layout y with _ | ⟨offy | iry | fry⟩
            · exact absurd hly hMappedY
            · -- y in stack: lv_reg = .d1, second load didn't touch .d1
              simp [lv_reg, hly]
              have : (ArmFReg.d1 : ArmFReg) ≠ rv_reg := by
                rcases hlz : r.layout z with _ | ⟨_ | _ | frz⟩ <;>
                  simp [rv_reg, hlz]
                exact fun h => absurd (h ▸ hlz) (hScratch.not_d1 z)
              rw [hFregs1b _ this]
              have := hSR1'; simp [lv_reg, hly] at this; exact this
            · exact absurd hly (hNotIregY iry)
            · -- y in freg: use hRel1b (ExtStateRel preserved)
              have : lv_reg = fry := by simp [lv_reg, hly]
              rw [this]; exact hRel1b y (.freg fry) hly
          have hArmResult : s2.fregs dst_reg = (σ' x).encode := by
            simp [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved]
            rw [hLvPreserved, hSR1b', hfy, hfz, hσx]; simp [Value.encode]
          -- Non-entry ireg: shared (store doesn't touch iregs)
          have hNEI_shared : ∀ v ir, r.layout v = some (.ireg ir) →
              (∀ off, CallerSaveEntry.ireg ir off ∉ entries) → s2.regs ir = (σ' v).encode := by
            intro v ir hLoc hNE
            have : s2.regs ir = (s1b.havocCallerSaved newRegs newFregs).regs ir := by
              simp [s2, ArmState.nextPC, ArmState.setFReg]
            rw [this]
            have hCS : ir.isCallerSaved = false := by
              cases hcs : ir.isCallerSaved with
              | false => rfl
              | true =>
              obtain ⟨_, _, hCoversIreg, _⟩ := spec.callerSaveSpec
              obtain ⟨coff, hMem⟩ := hCoversIreg v ir hLoc hcs
              have hInE : CallerSaveEntry.ireg ir coff ∈ entries := by
                show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                rw [show p[pc] = p.code[pc] from rfl, hInstr]
                simp only [callerSaveEntries, DAEOpt.instrDef]
                rw [List.mem_filter]
                refine ⟨hMem, ?_⟩
                rcases hlx2 : r.layout x with _ | ⟨off2 | ir2 | fr2⟩ <;> simp [hlx2]
                exact absurd hlx2 (hNotIregX ir2)
              exact absurd hInE (hNE coff)
            show (fun r => if r.isCallerSaved then newRegs r else s1b.regs r) ir = _
            simp [hCS]
            rw [hRegs1b, hRegs1]; simp [s_saved, applyCallerSaves_regs]
            have hVal := hStateRel v (.ireg ir) hLoc; simp at hVal; rw [hVal]
            have hne : DAEOpt.instrDef p[pc] ≠ some v := by
              rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
              intro h; rw [← h] at hLoc; exact absurd hLoc (hNotIregX ir)
            rw [hDstOnly v hne]
          -- Phase C: store + CodeAt
          have hCodeStore : CodeAt r.bodyFlat s2.pc (vStoreVarFP r.layout x dst_reg) := by
            have h := hCodeBase.append_right
              (l1 := vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg ++
                [.callBinF .fpow dst_reg lv_reg rv_reg])
            rw [hPC2, hPC1b', hPC1']
            have hIdx : r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg).length +
                (vLoadVarFP r.layout z rv_reg).length + 1 =
              r.pcMap pc + (entriesToSaves entries).length +
                (vLoadVarFP r.layout y lv_reg ++ vLoadVarFP r.layout z rv_reg ++
                  [ArmInstr.callBinF .fpow dst_reg lv_reg rv_reg]).length := by
              simp [List.length_append]; omega
            rw [hIdx]; exact h
          -- rcases on layout x
          rcases hlx : r.layout x with _ | ⟨off | ir | fr⟩
          · -- none
            have hSS2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
              fun e _ => by rw [hStack2]
            refine ⟨s2, (hSteps1.trans hSteps1b).trans hSteps2, ?_, hAMChain, hSS2, hNEI_shared, ?_, ?_⟩
            · rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, List.length_append]; omega
            · -- non-entry freg
              intro v fr hLoc hNE
              have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
              have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hScratch.not_d0 v)
              have : s2.fregs fr = (s1b.havocCallerSaved newRegs newFregs).fregs fr := by
                simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
              rw [this]
              have hCS : fr.isCallerSaved = false := by
                cases hcs : fr.isCallerSaved with
                | false => rfl
                | true =>
                obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
                have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                  show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]
                  simp only [callerSaveEntries, DAEOpt.instrDef]
                  rw [List.mem_filter]
                  exact ⟨hMem, by simp [hlx]⟩
                exact absurd hInE (hNE coff)
              show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr = _
              simp [hCS]
              have hVal := hRel1b v (.freg fr) hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; simp [hlx] at hLoc
              rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc
              rw [hStack2]
              have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; simp [hlx] at hLoc
              rw [hDstOnly v hne]
          · -- stack off
            simp [vStoreVarFP, hlx] at hCodeStore
            have hFstr : r.bodyFlat[s2.pc]? = some (.fstr dst_reg off) := hCodeStore.head
            let s3 := (s2.setStack off (s2.fregs dst_reg)).nextPC
            have hSteps3 : ArmSteps r.bodyFlat s2 s3 := .single (.fstr dst_reg off hFstr)
            have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setStack]
            have hNEI3 := fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
            have hSS3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off := by
              intro e he; simp [s3, ArmState.nextPC, ArmState.setStack]
              have hne : e.off ≠ off := by
                intro heq; exact spec.callerSaveSpec.1 e (hEntriesSub'.subset he) x (heq ▸ hlx)
              simp [hne, hStack2]
            refine ⟨s3, (hSteps1.trans hSteps1b).trans (hSteps2.trans hSteps3), ?_, ?_, hSS3, hNEI3, ?_, ?_⟩
            · simp [s3, ArmState.nextPC, ArmState.setStack]
              rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
              simp [vStoreVarFP, hlx, List.length_append]; omega
            · simp [s3, ArmState.nextPC, ArmState.setStack, hAMChain]
            · -- non-entry freg
              intro v fr hLoc hNE
              have hFregs3 : s3.fregs = s2.fregs := by simp [s3, ArmState.nextPC, ArmState.setStack]
              rw [hFregs3]
              have hDR : dst_reg = .d0 := by simp [dst_reg, hlx]
              have hfrne : fr ≠ ArmFReg.d0 := fun h => absurd (h ▸ hLoc) (hScratch.not_d0 v)
              have : s2.fregs fr = (s1b.havocCallerSaved newRegs newFregs).fregs fr := by
                simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hfrne]
              rw [this]
              have hCS : fr.isCallerSaved = false := by
                cases hcs : fr.isCallerSaved with
                | false => rfl
                | true =>
                obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                obtain ⟨coff, hMem⟩ := hCoversFreg v fr hLoc hcs
                have hInE : CallerSaveEntry.freg fr coff ∈ entries := by
                  show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]
                  simp only [callerSaveEntries, DAEOpt.instrDef]
                  rw [List.mem_filter]; exact ⟨hMem, by simp [hlx]⟩
                exact absurd hInE (hNE coff)
              show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr = _
              simp [hCS]
              have hVal := hRel1b v (.freg fr) hLoc; simp at hVal; rw [hVal]
              have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                intro h; subst h; rw [hlx] at hLoc; cases hLoc
              rw [hDstOnly v hne]
            · -- stack vars
              intro v off' hLoc
              simp [s3, ArmState.nextPC, ArmState.setStack]
              by_cases hvo : off' = off
              · have hvx := hInjective v x (.stack off) (hvo ▸ hLoc) hlx; subst hvx
                simp [hvo]; exact hArmResult
              · simp [hvo, hStack2]
                have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
                have hvx : v ≠ x := by
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hvo rfl
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]; exact hvx.symm
                rw [hDstOnly v hne]
          · exact absurd hlx (hNotIregX ir)
          · -- freg fr
            by_cases hEq : fr == dst_reg
            · -- fr = dst_reg
              simp [vStoreVarFP, hlx, hEq] at hCodeStore
              have hSS2 : ∀ e ∈ entries, s2.stack e.off = (applyCallerSaves entries s).stack e.off :=
                fun e _ => by rw [hStack2]
              refine ⟨s2, (hSteps1.trans hSteps1b).trans hSteps2, ?_, hAMChain, hSS2, hNEI_shared, ?_, ?_⟩
              · rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
                simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
              · -- non-entry freg
                intro v fr' hLoc hNE
                have hDR : dst_reg = fr := by simp [dst_reg, hlx]
                by_cases hff : fr' = fr
                · subst hff; have := hInjective v x _ hLoc hlx; subst this
                  rw [hDR] at hArmResult; exact hArmResult
                · have : s2.fregs fr' = (s1b.havocCallerSaved newRegs newFregs).fregs fr' := by
                    simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                  rw [this]
                  have hCS : fr'.isCallerSaved = false := by
                    cases hcs : fr'.isCallerSaved with
                    | false => rfl
                    | true =>
                    obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                    obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                    have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                      show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                      rw [show p[pc] = p.code[pc] from rfl, hInstr]
                      simp only [callerSaveEntries, DAEOpt.instrDef]
                      rw [List.mem_filter]; refine ⟨hMem, ?_⟩; simp [hlx, hff]
                    exact absurd hInE (hNE coff)
                  show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr' = _
                  simp [hCS]
                  have hVal := hRel1b v (.freg fr') hLoc; simp at hVal; rw [hVal]
                  have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                    intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                  rw [hDstOnly v hne]
              · -- stack vars
                intro v off' hLoc; rw [hStack2]
                have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc
                rw [hDstOnly v hne]
            · -- fr ≠ dst_reg
              simp [vStoreVarFP, hlx, hEq] at hCodeStore
              have hFmov : r.bodyFlat[s2.pc]? = some (.fmovRR fr dst_reg) := hCodeStore.head
              let s3 := (s2.setFReg fr (s2.fregs dst_reg)).nextPC
              have hSteps3 : ArmSteps r.bodyFlat s2 s3 := .single (.fmovRR fr dst_reg hFmov)
              have hRegs3 : s3.regs = s2.regs := by simp [s3, ArmState.nextPC, ArmState.setFReg]
              have hNEI3 := fun v ir hLoc hNE => hRegs3 ▸ hNEI_shared v ir hLoc hNE
              have hStack3 : s3.stack = s2.stack := by simp [s3, ArmState.nextPC, ArmState.setFReg]
              have hSS3 : ∀ e ∈ entries, s3.stack e.off = (applyCallerSaves entries s).stack e.off :=
                fun e _ => by rw [hStack3, hStack2]
              refine ⟨s3, (hSteps1.trans hSteps1b).trans (hSteps2.trans hSteps3), ?_, ?_, hSS3, hNEI3, ?_, ?_⟩
              · simp [s3, ArmState.nextPC, ArmState.setFReg]
                rw [hPC2, hPC1b', hPC1', hSavedPC, hInstrs]
                simp [vStoreVarFP, hlx, hEq, List.length_append]; omega
              · simp [s3, ArmState.nextPC, ArmState.setFReg, hAMChain]
              · -- non-entry freg
                intro v fr' hLoc hNE
                have hDR : dst_reg = fr := by simp [dst_reg, hlx]
                by_cases hff : fr' = fr
                · have hvx := hInjective v x _ (hff ▸ hLoc) hlx; subst hvx
                  simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                  exact hArmResult
                · have : s3.fregs fr' = s2.fregs fr' := by
                    simp [s3, ArmState.nextPC, ArmState.setFReg, hff]
                  rw [this]
                  have : s2.fregs fr' = (s1b.havocCallerSaved newRegs newFregs).fregs fr' := by
                    simp [s2, ArmState.nextPC, ArmState.setFReg, hDR, hff]
                  rw [this]
                  have hCS : fr'.isCallerSaved = false := by
                    cases hcs : fr'.isCallerSaved with
                    | false => rfl
                    | true =>
                    obtain ⟨_, _, _, hCoversFreg, _⟩ := spec.callerSaveSpec
                    obtain ⟨coff, hMem⟩ := hCoversFreg v fr' hLoc hcs
                    have hInE : CallerSaveEntry.freg fr' coff ∈ entries := by
                      show _ ∈ callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])
                      rw [show p[pc] = p.code[pc] from rfl, hInstr]
                      simp only [callerSaveEntries, DAEOpt.instrDef]
                      rw [List.mem_filter]; refine ⟨hMem, ?_⟩; simp [hlx, hff]
                    exact absurd hInE (hNE coff)
                  show (fun r => if r.isCallerSaved then newFregs r else s1b.fregs r) fr' = _
                  simp [hCS]
                  have hVal := hRel1b v (.freg fr') hLoc; simp at hVal; rw [hVal]
                  have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                    rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                    intro h; subst h; rw [hlx] at hLoc; cases hLoc; exact hff rfl
                  rw [hDstOnly v hne]
              · -- stack vars
                intro v off' hLoc; rw [hStack3, hStack2]
                have hVal := hRelSaved v (.stack off') hLoc; simp at hVal; rw [hVal]
                have hne : DAEOpt.instrDef p[pc] ≠ some v := by
                  rw [show p[pc] = p.code[pc] from rfl, hInstr]; simp [DAEOpt.instrDef]
                  intro h; subst h; rw [hlx] at hLoc; cases hLoc
                rw [hDstOnly v hne]
        | _ => simp [isLibCallTAC, show p[pc] = p.code[pc] from rfl, hInstr] at hLib
      | _ => simp [isLibCallTAC, show p[pc] = p.code[pc] from rfl, hInstr] at hLib
    obtain ⟨s_mid, hBaseSteps, hMidPC, hMidAM, hSaveSlots, hNEI, hNEF, hSV⟩ :=
      hBaseExists
    -- Step 3: restores
    have hRestorePC : s_mid.pc =
        r.pcMap pc + (entriesToSaves entries ++ baseInstrs).length := by
      rw [hMidPC, hSavedPC]; simp [List.length_append]; omega
    have hRestoreCode : CodeAt r.bodyFlat s_mid.pc (entriesToRestores entries) := by
      rw [hRestorePC]; exact hCodeRestores
    have hStepRestores := armSteps_restores r.bodyFlat entries s_mid hRestoreCode
    -- Compose all three
    let s_final := {applyCallerRestores entries s_mid with
      pc := s_mid.pc + entries.length}
    have hAllSteps : ArmSteps r.bodyFlat s s_final :=
      hStepSaves.trans (hBaseSteps.trans hStepRestores)
    -- Prove ExtSimRel for the final state
    obtain ⟨hFresh, hNodup, hCoversIreg, hCoversFreg, hUniqIreg, hUniqFreg⟩ :=
      spec.callerSaveSpec
    refine ⟨s_final, hAllSteps, ?_, ?_, ?_⟩
    · -- ExtStateRel via callerSave_composition_excluding
      -- entries ⊆ genCallerSaveAll (callerSaveEntries filters genCallerSaveAll)
      have hEntriesSub : entries.Sublist (genCallerSaveAll r.layout r.varMap) := by
        show (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])).Sublist _
        unfold callerSaveEntries
        cases DAEOpt.instrDef p[pc] with
        | none => exact List.Sublist.refl _
        | some _ => exact List.filter_sublist
      have hSubset : ∀ e, e ∈ entries → e ∈ genCallerSaveAll r.layout r.varMap :=
        fun e he => hEntriesSub.subset he
      -- Nodup on entries (sublist of nodup list)
      have hNodupE : (entries.map CallerSaveEntry.off).Nodup :=
        hNodup.sublist (hEntriesSub.map _)
      have hCSCE := ExtStateRel.callerSave_composition_excluding
        hStateRel entries s_mid
        (fun e he v hv => hFresh e (hSubset e he) v hv)
        hNodupE
        (fun r o1 o2 h1 h2 => hUniqIreg r o1 o2 (hSubset _ h1) (hSubset _ h2))
        (fun r o1 o2 h1 h2 => hUniqFreg r o1 o2 (hSubset _ h1) (hSubset _ h2))
        (fun ir off h => genCallerSaveAll_allCS_ireg (hSubset _ h))
        (fun fr off h => genCallerSaveAll_allCS_freg (hSubset _ h))
        hSaveSlots hNEI hNEF hSV hEIU hEFU
      -- hCSCE : ExtStateRel layout σ' (applyCallerRestores entries s_mid)
      -- s_final = {applyCallerRestores entries s_mid with pc := ...}
      show ExtStateRel r.layout σ' s_final
      exact hCSCE.withPC _
    · -- PcRel: s_final.pc = pcMap (pc + 1)
      show s_mid.pc + entries.length = r.pcMap (pc + 1)
      rw [hBody] at hPcNext
      rw [hMidPC, hSavedPC, hPcNext]
      simp only [List.length_append, entriesToSaves_length, entriesToRestores_length,
        show entries = callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc]) from rfl]
      omega
    · -- ArrayMem preserved
      show (applyCallerRestores entries s_mid).arrayMem = am
      rw [applyCallerRestores_arrayMem]
      exact hMidAM
  · by_cases hPrint : ∃ fmt vs, p[pc] = .print fmt vs
    · -- Print case: save/restore around printCall (havoc)
      obtain ⟨fmt, vs, hPrintEq⟩ := hPrint
      -- Get bodyPerPC structure from GenAsmSpec
      obtain ⟨lines, hBody⟩ :=
        spec.printSaveRestore pc hPC ⟨fmt, vs, hPrintEq⟩
      -- Get pcMap/lengths infrastructure
      obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
      have hpcB : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
      -- CodeAt for the full bodyPerPC[pc] block
      have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc) (r.bodyPerPC[pc]'hpcB) := by
        rw [hPcMap]; exact codeAt_of_bodyFlat r.bodyPerPC lengths hLSz hLenEq pc hpcB
      rw [hBody] at hCodeAt
      -- Abbreviate entries
      let entries := genCallerSaveAll r.layout r.varMap
      -- Split CodeAt into three parts: (saves ++ [printCall]) ++ restores
      have hCodeSP := hCodeAt.append_left
        (l2 := entriesToRestores entries)
      have hCodeRestores := hCodeAt.append_right
        (l1 := entriesToSaves entries ++ [ArmInstr.printCall lines])
      have hCodeSaves := hCodeSP.append_left (l2 := [ArmInstr.printCall lines])
      have hCodePrint := hCodeSP.append_right (l1 := entriesToSaves entries)
      -- Extract ExtStateRel components
      obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
      -- Print step: cfg' = .run (pc+1) σ am
      have hCfg : cfg' = .run (pc + 1) σ am := by
        have hInstr : p[pc]? = some (.print fmt vs) :=
          Prog.getElem?_eq_getElem hPC ▸ congrArg some hPrintEq
        cases hStep <;> simp_all
      subst hCfg
      -- hPcNext: pcMap(pc+1) = pcMap(pc) + bodyPerPC[pc].length
      have hPcNext : r.pcMap (pc + 1) = r.pcMap pc + (r.bodyPerPC[pc]'hpcB).length := by
        rw [hPcMap, buildPcMap_succ lengths pc (by rw [hLSz]; exact hpcB)]
        congr 1; exact hLenEq pc (by rw [hLSz]; exact hpcB) hpcB
      -- Rewrite s.pc to r.pcMap pc using PcRel
      have hSPC : s.pc = r.pcMap pc := hPcRel
      -- Step 1: saves
      have hStepSaves := armSteps_saves r.bodyFlat entries s
        (hSPC ▸ hCodeSaves)
      -- Step 2: printCall
      have hPrintCode : r.bodyFlat[s.pc + entries.length]? =
          some (ArmInstr.printCall lines) := by
        have := hCodePrint 0 (by simp)
        simp only [List.getElem_cons_zero, entriesToSaves_length] at this
        rw [hSPC]; exact this
      -- Pick arbitrary havoc values (callerSave_composition handles any)
      let newRegs : ArmReg → BitVec 64 := fun _ => 0
      let newFregs : ArmFReg → BitVec 64 := fun _ => 0
      have hStepPrint1 : ArmStep r.bodyFlat
          {applyCallerSaves entries s with pc := s.pc + entries.length}
          ({applyCallerSaves entries s with pc := s.pc + entries.length}.havocCallerSaved newRegs newFregs |>.nextPC) :=
        .printCall lines newRegs newFregs hPrintCode
      -- Step 3: restores
      have hRestorePC : s.pc + (entriesToSaves entries).length + 1 =
          r.pcMap pc + (entriesToSaves entries ++ [ArmInstr.printCall lines]).length := by
        simp [entriesToSaves_length, hSPC]; omega
      have hRestoreCode : CodeAt r.bodyFlat
          (s.pc + entries.length + 1) (entriesToRestores entries) := by
        rw [show s.pc + entries.length + 1 =
            s.pc + (entriesToSaves entries).length + 1 by simp [entriesToSaves_length]]
        rw [hRestorePC]; exact hCodeRestores
      -- The state after printCall
      let s_mid := {applyCallerSaves entries s with pc := s.pc + entries.length}.havocCallerSaved newRegs newFregs |>.nextPC
      have hMidPC : s_mid.pc = s.pc + entries.length + 1 := by
        simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved]
      have hStepRestores := armSteps_restores r.bodyFlat entries s_mid
        (hMidPC ▸ hRestoreCode)
      -- Compose all three: saves → printCall → restores
      let s_final := {applyCallerRestores entries s_mid with
        pc := s_mid.pc + entries.length}
      have hAllSteps : ArmSteps r.bodyFlat s s_final :=
        hStepSaves.trans ((ArmSteps.single hStepPrint1).trans hStepRestores)
      -- Prove ExtSimRel for the final state
      refine ⟨s_final, hAllSteps, ?_, ?_, ?_⟩
      · -- ExtStateRel: callerSave_composition on the logical state, then
        -- transfer to s_final via pc-independence.
        -- First, get the logical result
        let s_havoc := (applyCallerSaves entries s).havocCallerSaved newRegs newFregs
        -- Destructure callerSaveSpec
        obtain ⟨hFresh, hNodup, hCoversIreg, hCoversFreg, hUniqIreg, hUniqFreg⟩ :=
          spec.callerSaveSpec
        have hCSC := @ExtStateRel.callerSave_composition _ _ _
          hStateRel entries newRegs newFregs
          hFresh hNodup hCoversIreg hCoversFreg hUniqIreg hUniqFreg
          (fun ir off h => genCallerSaveAll_allCS_ireg h)
          (fun fr off h => genCallerSaveAll_allCS_freg h)
        -- hCSC : ExtStateRel layout σ (applyCallerRestores entries s_havoc)
        -- s_final = {applyCallerRestores entries s_mid with pc := ...}
        -- s_mid = {s_havoc with pc := ...}
        -- Use pc-irrelevance to relate
        have : applyCallerRestores entries s_mid =
            {applyCallerRestores entries s_havoc with
             pc := s_mid.pc} := by
          rw [show s_mid = {s_havoc with pc := s_mid.pc} from by
            simp [s_mid, s_havoc, ArmState.nextPC, ArmState.havocCallerSaved]]
          exact applyCallerRestores_pc_irrelevant entries s_havoc s_mid.pc
        show ExtStateRel r.layout σ s_final
        rw [show s_final = {applyCallerRestores entries s_mid with
            pc := s_mid.pc + entries.length} from rfl]
        rw [this]
        exact hCSC.withPC _
      · -- PcRel: s_final.pc = pcMap (pc + 1)
        show s_mid.pc + entries.length = r.pcMap (pc + 1)
        rw [hBody] at hPcNext
        rw [hMidPC, hPcNext, hSPC]
        simp only [List.length_append, entriesToSaves_length, entriesToRestores_length,
                   List.length_cons, List.length_nil]
        simp only [show entries = genCallerSaveAll r.layout r.varMap from rfl]
        omega
      · -- ArrayMem preserved (saves/havoc/restores don't touch arrayMem)
        show (applyCallerRestores entries s_mid).arrayMem = am
        rw [applyCallerRestores_arrayMem]
        simp [s_mid, ArmState.nextPC, ArmState.havocCallerSaved,
              applyCallerSaves_arrayMem]
        exact hArrayMem
    · -- Normal case: delegate to ext_backward_simulation
      have hNotPrint : ∀ fmt vs, p[pc] ≠ .print fmt vs := by
        intro fmt vs h; exact hPrint ⟨fmt, vs, h⟩
      have hNotLib : isLibCallTAC p[pc] = false := by
        cases h : isLibCallTAC p[pc] <;> simp_all
      -- Get instrs from instrGen
      obtain ⟨safe, hSome⟩ := spec.instrGen pc hPC hNotLib hNotPrint
      -- Get pcMap = buildPcMap lengths with element-wise equality
      obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
      have hpcB : pc < r.bodyPerPC.size := spec.bodySize ▸ hPC
      -- CodeAt from codeAt_of_bodyFlat
      have hCodeAt : CodeAt r.bodyFlat (r.pcMap pc) (r.bodyPerPC[pc]'hpcB) := by
        rw [hPcMap]; exact codeAt_of_bodyFlat r.bodyPerPC lengths hLSz hLenEq pc hpcB
      -- hPcNext from buildPcMap_succ
      have hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
          r.pcMap (pc + 1) = r.pcMap pc + (r.bodyPerPC[pc]'hpcB).length := by
        intro _ _ _
        rw [hPcMap, buildPcMap_succ lengths pc (by rw [hLSz]; exact hpcB)]
        congr 1; exact hLenEq pc (by rw [hLSz]; exact hpcB) hpcB
      -- hNCSL/hNCSLBin: vacuously true (not a lib-call)
      have hNCSL : ∀ x op y, p[pc] = .floatUnary x op y →
          op.isNative = false → NoCallerSavedLayout r.layout := by
        intro x op y heq hNN
        simp [isLibCallTAC, heq, hNN] at hNotLib
      have hNCSLBin : ∀ x y z, p[pc] = .fbinop x .fpow y z →
          NoCallerSavedLayout r.layout := by
        intro x y z heq
        simp [isLibCallTAC, heq] at hNotLib
      exact ext_backward_simulation p r.bodyFlat r.layout r.pcMap
        r.haltS r.divS r.boundsS p.arrayDecls safe
        hStep hRel hPC tyCtx spec.wellTypedProg hTS spec.wellTypedLayout
        p[pc] (Prog.getElem?_eq_getElem hPC)
        (r.bodyPerPC[pc]'hpcB) hSome hCodeAt hPcNext
        (spec.layoutComplete pc hPC) rfl hNCSL hNCSLBin

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
private theorem step_run_or_terminal {tyCtx : TyCtx} {p : Prog} {pc : Nat} {σ : Store}
    {am : ArrayMem} {c : Cfg}
    (hwtp : WellTypedProg tyCtx p) (hts : TypedStore tyCtx σ)
    (hpc : pc < p.size) (hstep : p ⊩ Cfg.run pc σ am ⟶ c) :
    (∃ pc' σ' am', c = .run pc' σ' am' ∧ TypedStore tyCtx σ') ∨
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
  | floatUnary h h1 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .floatUnary h h1)⟩
  | fternop h h1 h2 h3 =>
    exact .inl ⟨_, _, _, rfl, type_preservation hwtp hts hpc
      (show Step p (.run pc σ am) _ from .fternop h h1 h2 h3)⟩
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
  | floatUnary_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | fternop_typeError _ _ => exact .inr fun _ h => Step.no_step_from_typeError h
  | print _ => exact .inl ⟨_, _, _, rfl, hts⟩

/-- Whole-program backward simulation for `verifiedGenerateAsm`.

    If the verified code generator succeeds on program `p`, then any
    multi-step TAC execution starting from a configuration whose ARM
    counterpart satisfies `ExtSimRel` is simulated by `ArmSteps`
    preserving `ExtSimRel`.

    The proof proceeds by induction on the TAC `Steps` derivation,
    applying `step_simulation` (which wraps `ext_backward_simulation`)
    at each step, using `step_run_or_terminal` to classify the
    intermediate config, and `type_preservation` for `TypedStore`.

    **Propagated sorrys:** 0 from `verifiedGenInstr_correct`. -/
theorem tacToArm_refinement {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r)
    {pc : Nat} {σ : Store} {am : ArrayMem}
    (s : ArmState)
    (hRel : ExtSimRel r.layout r.pcMap (.run pc σ am) s)
    (hTS : TypedStore tyCtx σ)
    (cfg' : Cfg) (hSteps : p ⊩ Cfg.run pc σ am ⟶* cfg') :
    ∃ s', ArmSteps r.bodyFlat s s' ∧
          ExtSimRel r.layout r.pcMap cfg' s' := by
  have spec := verifiedGenerateAsm_spec hGen
  -- Generalize the start config for induction (pattern from type_preservation_steps)
  suffices ∀ c c_end, Steps p c c_end →
      ∀ pc σ am s,
        c = Cfg.run pc σ am →
        ExtSimRel r.layout r.pcMap (.run pc σ am) s →
        TypedStore tyCtx σ →
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

    **Propagated sorrys:** 0 from `verifiedGenInstr_correct`. -/
private theorem typedInit_encode (Γ : TyCtx) (v : Var) :
    (Store.typedInit Γ v).encode = 0 := by
  simp [Store.typedInit, Value.ofBitVec, Value.encode]
  cases Γ v <;> simp

theorem tacToArm_correctness {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r)
    {cfg' : Cfg}
    (hSteps : p ⊩ Cfg.run 0 (Store.typedInit tyCtx) (fun _ _ => 0) ⟶* cfg') :
    ∃ s', ArmSteps r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s' ∧
      ExtSimRel r.layout r.pcMap cfg' s' :=
  tacToArm_refinement hGen _
    (initial_extSimRel r.layout r.pcMap (Store.typedInit tyCtx) (fun _ _ => 0)
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ }
      (typedInit_encode tyCtx) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl)
    (TypedStore.typedInit tyCtx)
    cfg' hSteps

/-- Reserved integer register numbers that must never appear in register allocation.
    x16-x17: linker scratch (IP0/IP1), x18: platform-reserved. -/
private def reservedIntRegs : List Nat := [16, 17, 18]

/-- Caller-saved integer register numbers (x3-x8, x9-x15). -/
private def callerSavedIntRegs : List Nat := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Caller-saved float register numbers (d0-d7). d0 is the call arg/return. -/
private def callerSavedFloatRegs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Callee-saved integer register numbers. If any are used, the prologue/epilogue
    must save and restore them. -/
private def calleeSavedIntRegs : List Nat := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

/-- Callee-saved float register numbers (d8-d15). -/
private def calleeSavedFloatRegs : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]

/-- Check that no variable in the TAC program maps to a reserved register.
    Returns an error if a reserved register is found. -/
private def checkRegConvention (vars : List Var) : Except String Unit := do
  for v in vars do
    let n? := if v.startsWith "__ir" then (v.drop 4).toNat?
              else if v.startsWith "__br" then (v.drop 4).toNat?
              else none
    match n? with
    | some n =>
      if reservedIntRegs.contains n then
        throw s!"register allocator bug: variable '{v}' uses reserved register x{n}"
    | none => pure ()

-- detectCalleeSaved, detectCallerSaved, pairUpSameClass, libcallSaveRestore,
-- calleeSavePrologue, calleeSaveEpilogue: removed.
-- Callee-save prologue/epilogue and caller-save save/restore are now
-- generated as verified ArmInstr in verifiedGenerateAsm.

/-- Generate the complete assembly for a program.
    Calls `verifiedGenerateAsm` for the verified core, then wraps it with
    prologue/epilogue, printf code, error handlers, and data sections. -/
def generateAsm (tyCtx : TyCtx) (p : Prog) : Except String String := do
  let r ← verifiedGenerateAsm tyCtx p
  let vars := collectVars p
  -- Check register convention before generating assembly
  checkRegConvention vars
  -- Defense-in-depth: verify every callee-saved register in the layout is in calleeSaveRegs
  let layoutCallee := detectCalleeSavedLayout r.layout
  let (csIntRegs, csFloatRegs) := r.calleeSaveRegs
  if !layoutCallee.1.all csIntRegs.contains then
    .error "callee-saved int register used in layout but not saved in prologue"
  if !layoutCallee.2.all csFloatRegs.contains then
    .error "callee-saved float register used in layout but not saved in prologue"
  -- Stack frame: 16-byte aligned
  -- Layout: [scratch 8B] [var1 8B] ... [varN 8B] [callee-saved slots] [padding] [x29 8B] [x30 8B]
  let calleeSaveBytes := (csIntRegs.length + csFloatRegs.length) * 8
  let frameSize := ((vars.length + 1) * 8 + calleeSaveBytes + 16 + 15) / 16 * 16
  -- Pretty-print callee-save prologue/epilogue from verified ArmInstr
  let lbl := ppLabel r.haltS r.divS r.boundsS r.tacPcOf
  let csProlog := ppInstrs lbl r.calleeSavePrologue
  let csEpilog := ppInstrs lbl r.calleeSaveEpilogue
  let header := [
    ".global _main",
    ".align 2",
    "",
    "_main:",
    s!"  sub sp, sp, #{frameSize}",
    s!"  str x30, [sp, #{frameSize - 8}]",
    s!"  str x29, [sp, #{frameSize - 16}]",
    s!"  add x29, sp, #{frameSize - 16}"] ++
    (if csProlog.isEmpty then [] else
      ["  // Save callee-saved registers"] ++ csProlog) ++
    ["",
    "  // Initialize all variables to 0",
    "  mov x0, #0"
  ]
  -- Pretty-print init instructions
  let initLines := ppInstrs lbl r.initInstrs.toList
  -- Pretty-print body with TAC PC labels (uniform for all instructions,
  -- including print — printCall in bodyPerPC carries pre-computed printf lines)
  let body := (List.range r.bodyPerPC.size).flatMap fun pc =>
    [s!".L{pc}:"] ++ ppInstrs lbl ((r.bodyPerPC[pc]!))
  -- Print observable variables at halt (loads from stack, safe after saveRegs)
  let printCode := p.observable.flatMap fun v =>
    let isFloat := tyCtx v == .float
    let fmtLabel := if isFloat then s!".Lfmt_float" else ".Lfmt"
    if isFloat then
      s!"  // print {v} (float)" ::
      (loadVarFP r.varMap v "d0") ::
      "  sub sp, sp, #32" ::
      s!"  adrp x1, .Lname_{v}@PAGE" ::
      s!"  add x1, x1, .Lname_{v}@PAGEOFF" ::
      "  str x1, [sp]" ::
      "  str d0, [sp, #8]" ::
      s!"  adrp x0, {fmtLabel}@PAGE" ::
      s!"  add x0, x0, {fmtLabel}@PAGEOFF" ::
      "  bl _printf" ::
      "  add sp, sp, #32" :: List.nil
    else
      s!"  // print {v}" ::
      (loadVar r.varMap v "x9") ::
      "  sub sp, sp, #16" ::
      s!"  adrp x1, .Lname_{v}@PAGE" ::
      s!"  add x1, x1, .Lname_{v}@PAGEOFF" ::
      "  str x1, [sp]" ::
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
     "  mov x0, #0"] ++
    (if csEpilog.isEmpty then [] else
      ["  // Restore callee-saved registers"] ++ csEpilog) ++
    [s!"  ldr x29, [sp, #{frameSize - 16}]",
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
     "  .asciz \"error: array index out of bounds\\n\"",
     ""] ++
    -- Per-instruction format strings for print statements
    (List.range p.code.size).filterMap (fun pc =>
      match p.code.getD pc .halt with
      | .print fmt _ =>
        -- Re-escape special characters for .asciz directive
        let escaped := fmt.foldl (fun acc c =>
          match c with
          | '\n' => acc ++ "\\n"
          | '\t' => acc ++ "\\t"
          | '\\' => acc ++ "\\\\"
          | '"'  => acc ++ "\\\""
          | c    => acc ++ c.toString) ""
        some s!".Lfmt_print_{pc}:\n  .asciz \"{escaped}\""
      | _ => none) ++
    [""] ++
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

/-- Apply a single optimization pass: run it, override the certificate's tyCtx
    with the expected one, check the certificate, return the optimized program.
    Overriding tyCtx ensures the certificate is validated under the correct
    type context regardless of what the pass produced. -/
def applyPass (name : String) (tyCtx : TyCtx) (pass : Prog → ECertificate) (p : Prog) : Except String Prog :=
  let cert := { pass p with tyCtx := tyCtx }
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
def optimizePipeline (tyCtx : TyCtx) (p : Prog) : Except String Prog := do
  let p ← applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) p
  let p ← applyPass "LICM" tyCtx (LICMOpt.optimize tyCtx) p
  let p ← applyPass "ConstProp" tyCtx (ConstPropOpt.optimize tyCtx) p
  let p ← applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) p
  let p ← applyPass "DAE" tyCtx (DAEOpt.optimize tyCtx) p
  let p ← applyPass "FMAFusion" tyCtx (FMAFusionOpt.optimize tyCtx) p
  let p ← applyPass "CSE" tyCtx (CSEOpt.optimize tyCtx) p
  let p ← applyPass "ConstHoist" tyCtx (ConstHoistOpt.optimize tyCtx) p
  let p ← applyPass "Peephole" tyCtx (PeepholeOpt.optimize tyCtx) p
  let p ← applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) p
  applyPass "RegAlloc" tyCtx (RegAllocOpt.optimize tyCtx) p


/-- Try to apply a single optimization pass. If the certificate check fails,
    print a warning and return the input program unchanged. -/
def tryPass (name : String) (tyCtx : TyCtx) (pass : Prog → ECertificate) (p : Prog) : IO Prog := do
  match applyPass name tyCtx pass p with
  | .ok p' => return p'
  | .error msg =>
    IO.eprintln s!"warning: skipping {name} optimization ({msg})"
    return p

/-- Apply a list of certificate-checked optimization passes resiliently.
    Each pass is checked by the executable certificate checker; if a check
    fails, that pass is skipped and the pipeline continues with the
    unoptimized program. Always succeeds. -/
def applyPassesPure (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) → Prog → Prog
  | [], p => p
  | (name, pass) :: rest, p =>
    let p' := match applyPass name tyCtx pass p with
      | .ok p' => p'
      | .error _ => p
    applyPassesPure tyCtx rest p'

/-- The standard optimization pass list. -/
def standardPasses (tyCtx : TyCtx) : List (String × (Prog → ECertificate)) :=
  [ ("DCE", DCEOpt.optimize tyCtx),
    ("LICM", LICMOpt.optimize tyCtx),
    ("ConstProp", ConstPropOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("DAE", DAEOpt.optimize tyCtx),
    ("FMAFusion", FMAFusionOpt.optimize tyCtx),
    ("CSE", CSEOpt.optimize tyCtx),
    ("ConstHoist", ConstHoistOpt.optimize tyCtx),
    ("Peephole", PeepholeOpt.optimize tyCtx),
    ("DCE", DCEOpt.optimize tyCtx),
    ("RegAlloc", RegAllocOpt.optimize tyCtx) ]

/-- IO version of applyPassesPure with warning messages on failures. -/
def applyPassesIO (tyCtx : TyCtx) (passes : List (String × (Prog → ECertificate))) (p : Prog) : IO Prog :=
  passes.foldlM (fun p (name, pass) => tryPass name tyCtx pass p) p

def compileToAsm (input : String) : Except String String := do
  let prog ← parseProgram input
  if !prog.typeCheckStrict then .error "program failed type check (frontend)"
  let tac := prog.compileToTAC
  let tyCtx := prog.tyCtx
  let opt := applyPassesPure tyCtx (standardPasses tyCtx) tac
  generateAsm tyCtx opt

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
