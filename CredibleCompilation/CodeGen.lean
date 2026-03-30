import CredibleCompilation.WhileLang
import CredibleCompilation.Parser

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

/-- Load an arbitrary 64-bit integer into a register.
    Uses `mov` for small values, `movz`/`movk` sequence for large ones. -/
private def loadImm64 (reg : String) (n : Int) : List String :=
  if -65536 < n && n < 65536 then
    s!"  mov {reg}, #{n}" :: List.nil
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

/-- Generate code for a BoolExpr, result in w0 (0 or 1). Clobbers x0-x3. -/
private partial def genBoolExpr (varMap : List (Var × Nat)) (be : BoolExpr) : List String :=
  match be with
  | .bvar v =>
    (loadVar varMap v "x0") :: "  and w0, w0, #1" :: List.nil
  | .cmp op lv rv =>
    let cond := match op with | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"
    (loadVar varMap lv "x1") :: (loadVar varMap rv "x2") ::
    "  cmp x1, x2" :: s!"  cset w0, {cond}" :: List.nil
  | .cmpLit op v n =>
    let cond := match op with | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le"
    (loadVar varMap v "x1") :: List.nil ++
    loadImm64 "x2" n ++
    ("  cmp x1, x2" :: s!"  cset w0, {cond}" :: List.nil)
  | .not e =>
    genBoolExpr varMap e ++ ("  eor w0, w0, #1" :: List.nil)

-- ============================================================
-- § 4. Instruction codegen
-- ============================================================

private def genInstr (varMap : List (Var × Nat)) (pc : Nat) (instr : TAC) : List String :=
  (s!".L{pc}:" :: List.nil) ++
  match instr with
  | .const v (.int n) =>
    loadImm64 "x0" n ++ (storeVar varMap v "x0" :: List.nil)
  | .const v (.bool b) =>
    s!"  mov x0, #{if b then 1 else 0}" :: storeVar varMap v "x0" :: List.nil
  | .copy dst src =>
    (loadVar varMap src "x0") :: (storeVar varMap dst "x0") :: List.nil
  | .binop dst op lv rv =>
    let opInstr := match op with
      | .add => "  add x0, x1, x2"
      | .sub => "  sub x0, x1, x2"
      | .mul => "  mul x0, x1, x2"
      | .div => "  sdiv x0, x1, x2"
    if op == .div then
      (loadVar varMap rv "x2") :: "  cbz x2, .Ldiv_by_zero" ::
      (loadVar varMap lv "x1") :: (loadVar varMap rv "x2") ::
      opInstr :: (storeVar varMap dst "x0") :: List.nil
    else
      (loadVar varMap lv "x1") :: (loadVar varMap rv "x2") ::
      opInstr :: (storeVar varMap dst "x0") :: List.nil
  | .boolop dst be =>
    genBoolExpr varMap be ++ ((storeVar varMap dst "x0") :: List.nil)
  | .goto l =>
    s!"  b .L{l}" :: List.nil
  | .ifgoto be l =>
    genBoolExpr varMap be ++ (s!"  cbnz w0, .L{l}" :: List.nil)
  | .halt =>
    "  b .Lhalt" :: List.nil

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
    -- Need (1 + N) * 8 bytes for scratch+vars, plus 16 for saved regs
    let frameSize := ((vars.length + 1) * 8 + 16 + 15) / 16 * 16
    let header := [
      ".global _main",
      ".align 2",
      "",
      "_main:",
      s!"  sub sp, sp, #{frameSize}",
      s!"  stp x29, x30, [sp, #{frameSize - 16}]",
      s!"  add x29, sp, #{frameSize - 16}",
      "",
      "  // Initialize all variables to 0",
      "  mov x0, #0"
    ]
    let initVars := vars.map fun v => storeVar varMap v "x0"
    let body := (List.range p.code.size).flatMap fun pc =>
      genInstr varMap pc (p.code.getD pc .halt)
    -- Print observable variables at halt
    -- ARM64 Darwin variadic convention: args after format go on the stack
    let printCode := p.observable.flatMap fun v =>
      s!"  // print {v}" ::
      (loadVar varMap v "x9") ::       -- load value before adjusting sp
      "  sub sp, sp, #16" ::
      s!"  adrp x8, .Lname_{v}@PAGE" ::
      s!"  add x8, x8, .Lname_{v}@PAGEOFF" ::
      "  str x8, [sp]" ::
      "  str x9, [sp, #8]" ::
      "  adrp x0, .Lfmt@PAGE" ::
      "  add x0, x0, .Lfmt@PAGEOFF" ::
      "  bl _printf" ::
      "  add sp, sp, #16" :: List.nil
    let footer := [
      "",
      ".Lhalt:",
      "  // Print observable variables"] ++
      printCode ++
      ["",
       "  // Exit with code 0",
       "  mov x0, #0",
       s!"  ldp x29, x30, [sp, #{frameSize - 16}]",
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
       ".section __TEXT,__cstring",
       ".Lfmt:",
       "  .asciz \"%s = %ld\\n\"",
       ".Ldiv_msg:",
       "  .asciz \"error: division by zero\\n\""] ++
      p.observable.map fun v =>
       s!".Lname_{v}:\n  .asciz \"{v}\""
    some (emit (header ++ [""] ++ initVars ++ [""] ++ body ++ footer ++ [""]))

-- ============================================================
-- § 6. End-to-end: parse → compile → codegen
-- ============================================================

/-- Parse a While program string, compile to TAC, generate ARM64 assembly. -/
def compileToAsm (input : String) : Except String String := do
  let prog ← parseProgram input
  let tac := prog.compile
  match generateAsm tac with
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
