import CredibleCompilation.WhileLang
import CredibleCompilation.Parser
import CredibleCompilation.ConstPropOpt
import CredibleCompilation.CSEOpt
import CredibleCompilation.LICMOpt
import CredibleCompilation.DAEOpt
import CredibleCompilation.DCEOpt
import CredibleCompilation.PeepholeOpt
import CredibleCompilation.RegAllocOpt
import CredibleCompilation.ExecChecker

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

private def storeVarFP (varMap : List (Var × Nat)) (v : Var) (freg : String) : String :=
  match lookupVar varMap v with
  | some off => s!"  str {freg}, [sp, #{off}]"
  | none => s!"  // ERROR: unknown variable {v}"

-- ============================================================
-- § 2a. Register-aware load/store helpers
-- ============================================================

/-- Detect register allocation by variable name prefix.
    `__xN` → integer register xN, `__dN` → float register dN. -/
private def lookupReg (v : Var) : Option String :=
  if v.startsWith "__x" then some (v.drop 2).toString  -- "__x3" → "x3"
  else if v.startsWith "__d" then some (v.drop 2).toString  -- "__d5" → "d5"
  else none

/-- Is this register name a float register (dN)? -/
private def isFloatReg (reg : String) : Bool := reg.startsWith "d"

/-- Load an integer variable into a scratch register. If the variable is in a
    register, emit `mov`; otherwise load from stack. -/
private def smartLoadVar (varMap : List (Var × Nat))
    (v : Var) (reg : String) : String :=
  match lookupReg v with
  | some r => if r == reg then s!"  // {v} already in {reg}" else s!"  mov {reg}, {r}"
  | none => loadVar varMap v reg

/-- Store a value from a scratch register into an integer variable. If the
    variable is register-allocated, emit `mov`; otherwise store to stack. -/
private def smartStoreVar (varMap : List (Var × Nat))
    (v : Var) (reg : String) : String :=
  match lookupReg v with
  | some r => if r == reg then s!"  // {v} already in {reg}" else s!"  mov {r}, {reg}"
  | none => storeVar varMap v reg

/-- Load a float variable into a scratch FP register. -/
private def smartLoadVarFP (varMap : List (Var × Nat))
    (v : Var) (freg : String) : String :=
  match lookupReg v with
  | some r => if r == freg then s!"  // {v} already in {freg}" else s!"  fmov {freg}, {r}"
  | none => loadVarFP varMap v freg

/-- Store a value from a scratch FP register into a float variable. -/
private def smartStoreVarFP (varMap : List (Var × Nat))
    (v : Var) (freg : String) : String :=
  match lookupReg v with
  | some r => if r == freg then s!"  // {v} already in {freg}" else s!"  fmov {r}, {freg}"
  | none => storeVarFP varMap v freg

/-- Load an arbitrary 64-bit integer into a register.
    Uses `mov` for small values, `movz`/`movk` sequence for large ones. -/
private def loadImm64 (reg : String) (n : BitVec 64) : List String :=
  if n.toInt.natAbs < 65536 then
    s!"  mov {reg}, #{n.toInt}" :: List.nil
  else
    let bits : UInt64 := n.toNat.toUInt64
    let w0 := bits &&& 0xFFFF
    let w1 := (bits >>> 16) &&& 0xFFFF
    let w2 := (bits >>> 32) &&& 0xFFFF
    let w3 := (bits >>> 48) &&& 0xFFFF
    let base := s!"  movz {reg}, #{w0}" :: List.nil
    let k1 := if w1 != 0 then s!"  movk {reg}, #{w1}, lsl #16" :: List.nil else List.nil
    let k2 := if w2 != 0 then s!"  movk {reg}, #{w2}, lsl #32" :: List.nil else List.nil
    let k3 := if w3 != 0 then s!"  movk {reg}, #{w3}, lsl #48" :: List.nil else List.nil
    base ++ k1 ++ k2 ++ k3

-- ============================================================
-- § 3. Boolean expression codegen
-- ============================================================

/-- Generate code for a BoolExpr, result in w0 (0 or 1). Clobbers x0-x2, d1-d2. -/
private partial def genBoolExpr (varMap : List (Var × Nat))
    (be : BoolExpr) : List String :=
  match be with
  | .lit b =>
    s!"  mov x0, #{if b then 1 else 0}" :: List.nil
  | .bvar v =>
    (smartLoadVar varMap v "x0") :: "  and w0, w0, #1" :: List.nil
  | .cmp op lv rv =>
    let cond := match op with | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"
    match lookupReg lv, lookupReg rv with
    | some rl, some rr =>
      s!"  cmp {rl}, {rr}" :: s!"  cset w0, {cond}" :: List.nil
    | _, _ =>
      (smartLoadVar varMap lv "x1") :: (smartLoadVar varMap rv "x2") ::
      "  cmp x1, x2" :: s!"  cset w0, {cond}" :: List.nil
  | .cmpLit op v n =>
    let cond := match op with | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"
    (smartLoadVar varMap v "x1") :: List.nil ++
    loadImm64 "x2" n ++
    ("  cmp x1, x2" :: s!"  cset w0, {cond}" :: List.nil)
  | .not e =>
    genBoolExpr varMap e ++ ("  eor w0, w0, #1" :: List.nil)
  | .fcmp op lv rv =>
    let cond := match op with | .feq => "eq" | .fne => "ne" | .flt => "mi" | .fle => "ls"
    match lookupReg lv, lookupReg rv with
    | some rl, some rr =>
      s!"  fcmp {rl}, {rr}" :: s!"  cset w0, {cond}" :: List.nil
    | _, _ =>
      (smartLoadVarFP varMap lv "d1") :: (smartLoadVarFP varMap rv "d2") ::
      "  fcmp d1, d2" :: s!"  cset w0, {cond}" :: List.nil

-- ============================================================
-- § 4. Instruction codegen
-- ============================================================

private def genInstr (varMap : List (Var × Nat))
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (pc : Nat) (instr : TAC) : List String :=
  (s!".L{pc}:" :: List.nil) ++
  match instr with
  | .const v (.int n) =>
    match lookupReg v with
    | some r => loadImm64 r n
    | none => loadImm64 "x0" n ++ [storeVar varMap v "x0"]
  | .const v (.bool b) =>
    match lookupReg v with
    | some r => [s!"  mov {r}, #{if b then 1 else 0}"]
    | none => [s!"  mov x0, #{if b then 1 else 0}", storeVar varMap v "x0"]
  | .const v (.float n) =>
    match lookupReg v with
    | some r => loadImm64 "x0" n ++ [s!"  fmov {r}, x0"]
    | none => loadImm64 "x0" n ++ [storeVar varMap v "x0"]
  | .copy dst src =>
    let srcReg := lookupReg src
    let dstReg := lookupReg dst
    let isFloat := srcReg.any isFloatReg || dstReg.any isFloatReg
    if isFloat then
      match srcReg, dstReg with
      | some rs, some rd => if rs == rd then [] else [s!"  fmov {rd}, {rs}"]
      | some rs, none => [storeVarFP varMap dst rs]
      | none, some rd => [loadVarFP varMap src rd]
      | none, none => [loadVarFP varMap src "d0", storeVarFP varMap dst "d0"]
    else
      match srcReg, dstReg with
      | some rs, some rd => if rs == rd then [] else [s!"  mov {rd}, {rs}"]
      | some rs, none => [storeVar varMap dst rs]
      | none, some rd => [loadVar varMap src rd]
      | none, none => [loadVar varMap src "x0", storeVar varMap dst "x0"]
  | .binop dst op lv rv =>
    match lookupReg dst, lookupReg lv, lookupReg rv with
    | some rd, some rl, some rr =>
      if op == .div || op == .mod then
        if op == .div then
          [s!"  cbz {rr}, .Ldiv_by_zero", s!"  sdiv {rd}, {rl}, {rr}"]
        else
          [s!"  cbz {rr}, .Ldiv_by_zero", s!"  sdiv {rd}, {rl}, {rr}",
           s!"  msub {rd}, {rd}, {rr}, {rl}"]
      else match op with
        | .add => [s!"  add {rd}, {rl}, {rr}"]
        | .sub => [s!"  sub {rd}, {rl}, {rr}"]
        | .mul => [s!"  mul {rd}, {rl}, {rr}"]
        | _ => [s!"  add {rd}, {rl}, {rr}"]
    | _, _, _ =>
      let opInstr := match op with
        | .add => ["  add x0, x1, x2"]
        | .sub => ["  sub x0, x1, x2"]
        | .mul => ["  mul x0, x1, x2"]
        | .div => ["  sdiv x0, x1, x2"]
        | .mod => ["  sdiv x0, x1, x2", "  msub x0, x0, x2, x1"]
      if op == .div || op == .mod then
        [smartLoadVar varMap rv "x2", "  cbz x2, .Ldiv_by_zero",
         smartLoadVar varMap lv "x1", smartLoadVar varMap rv "x2"] ++
        opInstr ++ [smartStoreVar varMap dst "x0"]
      else
        [smartLoadVar varMap lv "x1", smartLoadVar varMap rv "x2"] ++
        opInstr ++ [smartStoreVar varMap dst "x0"]
  | .boolop dst be =>
    genBoolExpr varMap be ++ [smartStoreVar varMap dst "x0"]
  | .goto l =>
    s!"  b .L{l}" :: List.nil
  | .ifgoto be l =>
    genBoolExpr varMap be ++ (s!"  cbnz w0, .L{l}" :: List.nil)
  | .halt =>
    "  b .Lhalt" :: List.nil
  | .arrLoad x _arr idx _ =>
    let arrSize := arraySize arrayDecls _arr
    let isFloatDest := (lookupReg x).any isFloatReg
    let storeResult := if isFloatDest then
        ["  fmov d0, x0", smartStoreVarFP varMap x "d0"]
      else [smartStoreVar varMap x "x0"]
    (smartLoadVar varMap idx "x1") ::
    s!"  cmp x1, #{arrSize}" ::
    "  b.hs .Lbounds_err" ::
    s!"  adrp x8, _arr_{_arr}@PAGE" ::
    s!"  add x8, x8, _arr_{_arr}@PAGEOFF" ::
    "  ldr x0, [x8, x1, lsl #3]" ::
    storeResult
  | .arrStore _arr idx val _ =>
    let arrSize := arraySize arrayDecls _arr
    let isFloatVal := (lookupReg val).any isFloatReg
    let loadVal := if isFloatVal then
        [smartLoadVarFP varMap val "d0", "  fmov x2, d0"]
      else [smartLoadVar varMap val "x2"]
    (smartLoadVar varMap idx "x1") ::
    s!"  cmp x1, #{arrSize}" ::
    "  b.hs .Lbounds_err" ::
    loadVal ++
    s!"  adrp x8, _arr_{_arr}@PAGE" ::
    s!"  add x8, x8, _arr_{_arr}@PAGEOFF" ::
    "  str x2, [x8, x1, lsl #3]" :: List.nil
  | .fbinop dst op lv rv =>
    let opName := match op with
      | .fadd => "fadd" | .fsub => "fsub" | .fmul => "fmul" | .fdiv => "fdiv"
    match lookupReg dst, lookupReg lv, lookupReg rv with
    | some rd, some rl, some rr =>
      [s!"  {opName} {rd}, {rl}, {rr}"]
    | _, _, _ =>
      (smartLoadVarFP varMap lv "d1") ::
      (smartLoadVarFP varMap rv "d2") ::
      s!"  {opName} d0, d1, d2" :: (smartStoreVarFP varMap dst "d0") :: List.nil
  | .intToFloat dst src =>
    match lookupReg dst, lookupReg src with
    | some rd, some rs => [s!"  scvtf {rd}, {rs}"]
    | _, _ =>
      (smartLoadVar varMap src "x0") ::
      "  scvtf d0, x0" ::
      (smartStoreVarFP varMap dst "d0") :: List.nil
  | .floatToInt dst src =>
    match lookupReg dst, lookupReg src with
    | some rd, some rs => [s!"  fcvtzs {rd}, {rs}"]
    | _, _ =>
      (smartLoadVarFP varMap src "d0") ::
      "  fcvtzs x0, d0" ::
      (smartStoreVar varMap dst "x0") :: List.nil
  | .floatExp dst src =>
    match lookupReg dst, lookupReg src with
    | some rd, some rs =>
      let load := if rs == "d0" then [] else [s!"  fmov d0, {rs}"]
      let store := if rd == "d0" then [] else [s!"  fmov {rd}, d0"]
      load ++ ["  stp x29, x30, [sp, #-16]!", "  bl _exp",
               "  ldp x29, x30, [sp], #16"] ++ store
    | _, _ =>
      (smartLoadVarFP varMap src "d0") ::
      "  stp x29, x30, [sp, #-16]!" ::
      "  bl _exp" ::
      "  ldp x29, x30, [sp], #16" ::
      (smartStoreVarFP varMap dst "d0") :: List.nil

-- ============================================================
-- § 5. Program codegen
-- ============================================================

/-- Generate the complete assembly for a program. Returns none if type check fails. -/
def generateAsm (p : Prog) : Option String :=
  if !checkWellTypedProg p.tyCtx p then none
  else
    let vars := collectVars p
    let varMap := buildVarMap vars
    -- Stack frame: 16-byte aligned
    -- Layout: [scratch 8B] [var1 8B] ... [varN 8B] [padding] [x29 8B] [x30 8B]
    -- All variables get stack slots (needed for halt save of register values)
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
    -- Initialize: register vars get register zero, stack vars get stack zero
    let initVars := vars.flatMap fun v =>
      match lookupReg v with
      | some r =>
        if isFloatReg r then [s!"  fmov {r}, xzr"]
        else [s!"  mov {r}, #0"]
      | none => [storeVar varMap v "x0"]
    let body := (List.range p.code.size).flatMap fun pc =>
      genInstr varMap p.arrayDecls pc (p.code.getD pc .halt)
    -- At halt: save register-allocated observable values to stack for printf
    let saveRegs := p.observable.filterMap fun v =>
      match lookupReg v with
      | some r =>
        match lookupVar varMap v with
        | some off => some s!"  str {r}, [sp, #{off}]"
        | none => none
      | none => none
    -- Print observable variables at halt (loads from stack, safe after saveRegs)
    let printCode := p.observable.flatMap fun v =>
      let isFloat := p.tyCtx v == .float
      let fmtLabel := if isFloat then s!".Lfmt_float" else ".Lfmt"
      if isFloat then
        s!"  // print {v} (float)" ::
        (loadVarFP varMap v "d0") ::
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
        (loadVar varMap v "x9") ::
        "  sub sp, sp, #16" ::
        s!"  adrp x8, .Lname_{v}@PAGE" ::
        s!"  add x8, x8, .Lname_{v}@PAGEOFF" ::
        "  str x8, [sp]" ::
        "  str x9, [sp, #8]" ::
        s!"  adrp x0, {fmtLabel}@PAGE" ::
        s!"  add x0, x0, {fmtLabel}@PAGEOFF" ::
        "  bl _printf" ::
        "  add sp, sp, #16" :: List.nil
    let footer := [
      "",
      ".Lhalt:",
      "  // Save register values to stack for printf"] ++
      saveRegs ++
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
    some (emit (header ++ [""] ++ initVars ++ [""] ++ body ++ footer ++ arrayData ++ [""]))

-- ============================================================
-- § 6. End-to-end: parse → compile → codegen
-- ============================================================

/-- Apply a single optimization pass: run it, check the certificate, return the
    optimized program. Errors if the certificate check fails. -/
def applyPass (name : String) (pass : Prog → ECertificate) (p : Prog) : Except String Prog :=
  let cert := pass p
  if checkCertificateExec cert then .ok cert.trans
  else .error s!"optimization certificate check failed for {name}"

/-- Apply each optimization pass in sequence:
    ConstProp → DCE → DAE → CSE → LICM → RegAlloc → Peephole.
    Each pass is checked by the executable certificate checker. -/
def optimizePipeline (p : Prog) : Except String Prog := do
  let p ← applyPass "ConstProp" ConstPropOpt.optimize p
  let p ← applyPass "DCE" DCEOpt.optimize p
  let p ← applyPass "DAE" DAEOpt.optimize p
  let p ← applyPass "CSE" CSEOpt.optimize p
  let p ← applyPass "LICM" LICMOpt.optimize p
  let p ← applyPass "Peephole" PeepholeOpt.optimize p
  .ok p

def compileToAsm (input : String) : Except String String := do
  let prog ← parseProgram input
  let tac := prog.compile
  let opt ← do
    let p ← optimizePipeline tac
    let p ← optimizePipeline p
    applyPass "RegAlloc" RegAllocOpt.optimize p
  match generateAsm opt with
  | some asm => .ok asm
  | none => .error "program failed type check"

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
