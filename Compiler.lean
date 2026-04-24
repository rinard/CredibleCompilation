import CredibleCompilation.CodeGen

/-- Embedded C runtime stubs for typed-print library calls (printInt, printBool,
    printFloat, printString). Written to a temp file at link time. -/
def runtimeSrc : String := include_str "Compiler/runtime.c"

/-- Materialize `runtimeSrc` to a temp file and return its path. -/
def writeRuntime : IO String := do
  let path := "/tmp/credible_runtime.c"
  IO.FS.writeFile ⟨path⟩ runtimeSrc
  return path

/-- **Structured driver: compile a source file to an assembly text file.**

    Each step's name and order matches the corresponding stage in the verified
    pipeline (see `compilePipeline` in CodeGen.lean and the top-level theorems
    in PipelineCorrectness.lean).  Stages are logged to stderr so the structure
    is observable from the command line. -/
def compileFileToFile (inputFile outputFile : String) (noOpt : Bool) : IO UInt32 := do
  IO.eprintln s!"[1/6] Reading source file: {inputFile}"
  let src ← IO.FS.readFile ⟨inputFile⟩
  -- Stage 1: parse (unverified)
  IO.eprintln s!"[2/6] Parsing (unverified)..."
  let prog ← match parseProgram src with
    | .ok p => pure p
    | .error e => IO.eprintln s!"  parse error: {e}"; return 1
  -- Stage 2: well-formedness
  IO.eprintln s!"[3/6] Well-formedness check..."
  if !prog.wellFormed then
    IO.eprintln s!"  program is not well-formed (typecheck/noGoto/noReservedNames failed)"
    return 1
  let tyCtx := prog.tyCtx
  -- Stage 3: AST → TAC (verified)
  IO.eprintln s!"[4/6] AST → TAC (verified by compileToTAC_*) ..."
  let tac := prog.compileToTAC
  IO.eprintln s!"  TAC size: {tac.size}"
  -- Stage 4: optimizations (verified, certificate-checked)
  IO.eprintln s!"[5/6] Applying {if noOpt then 0 else (standardPasses tyCtx).length} \
    certificate-checked optimization passes..."
  let optPasses := if noOpt then [] else standardPasses tyCtx
  let opt := applyPasses tyCtx optPasses tac
  IO.eprintln s!"  Optimized TAC size: {opt.size}"
  -- Stage 5: TAC → verified ASM core (verified)
  IO.eprintln s!"[6/6] TAC → verified ASM (verifiedGenerateAsm) + format & write..."
  let r ← match verifiedGenerateAsm tyCtx opt with
    | .ok r => pure r
    | .error e => IO.eprintln s!"  verifiedGenerateAsm error: {e}"; return 1
  IO.eprintln s!"  Verified ASM core: {r.bodyFlat.size} ARM instructions"
  -- Stage 6: format (unverified pretty-print + boilerplate) → write
  let asm ← match formatVerifiedAsm r opt with
    | .ok s => pure s
    | .error e => IO.eprintln s!"  format error: {e}"; return 1
  IO.FS.writeFile ⟨outputFile⟩ asm
  IO.eprintln s!"  Written: {outputFile}"
  return 0

def main (args : List String) : IO UInt32 := do
  -- Parse -O0 flag from anywhere in args
  let noOpt := args.contains "-O0"
  let args := args.filter (· != "-O0")
  match args with
  | [inputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compilePipeline src noOpt with
    | .ok asm => IO.print asm; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | [inputFile, "-S", outputFile] =>
    -- Structured pipeline: compile to assembly text file with stage logging.
    compileFileToFile inputFile outputFile noOpt
  | [inputFile, "-o", outputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compilePipeline src noOpt with
    | .ok asm =>
      let asmFile := outputFile ++ ".s"
      IO.FS.writeFile ⟨asmFile⟩ asm
      let runtimePath ← writeRuntime
      let cc ← IO.Process.output { cmd := "cc", args := #["-o", outputFile, asmFile, runtimePath] }
      if cc.exitCode != 0 then IO.eprintln cc.stderr; return 1
      IO.eprintln s!"compiled: {outputFile}"; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | [inputFile, "-r"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compilePipeline src noOpt with
    | .ok asm =>
      let asmFile := "/tmp/while_out.s"
      let binFile := "/tmp/while_out"
      IO.FS.writeFile ⟨asmFile⟩ asm
      let runtimePath ← writeRuntime
      let cc ← IO.Process.output { cmd := "cc", args := #["-o", binFile, asmFile, runtimePath] }
      if cc.exitCode != 0 then IO.eprintln cc.stderr; return 1
      let run ← IO.Process.spawn { cmd := binFile, stdin := .inherit, stdout := .inherit, stderr := .inherit }
      let exit ← run.wait; return exit
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | [inputFile, "-debug"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "well-formedness check failed"; return 1
      let tac := prog.compileToTAC
      let tyCtx := prog.tyCtx
      IO.println s!"TAC size: {tac.size}"
      IO.println s!"LICM hoistable: {LICMOpt.numHoistable tac}"
      let cert := { RegAllocOpt.optimize tyCtx tac with tyCtx := tyCtx }
      IO.println s!"Trans size: {cert.trans.size}"
      for (name, result) in checkCertificateVerboseExec cert do
        IO.println s!"  {name}: {if result then "ok" else "FAIL"}"
      return 0
  | [inputFile, "-licm"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.wellFormed then IO.eprintln "well-formedness check failed"; return 1
      let tac := prog.compileToTAC
      let tyCtx := prog.tyCtx
      let tac ← match applyPass "DCE" tyCtx (DCEOpt.optimize tyCtx) tac with
        | .ok p => pure p | .error e => IO.eprintln e; return 1
      let cert := { LICMOpt.optimize tyCtx tac with tyCtx := tyCtx }
      IO.println s!"=== LICM Certificate ==="
      IO.println s!"orig size: {cert.orig.size}  trans size: {cert.trans.size}"
      let inLoop := LICMOpt.findLoopPCs tac
      let hoistable := LICMOpt.findHoistable tac inLoop
      IO.println s!"hoistable: {hoistable.length}"
      for (pc, loopHead, x, v) in hoistable do
        IO.println s!"  pc={pc} loopHead={loopHead} {x} := {repr v}"
      IO.println s!"\n=== Verbose Check ==="
      for (name, result) in checkCertificateVerboseExec cert do
        IO.println s!"  {name}: {if result then "ok" else "FAIL"}"
      return 0
  | _ =>
    IO.eprintln "Usage: compiler <file.w>               -- print assembly to stdout"
    IO.eprintln "       compiler <file.w> -S <file.s>   -- structured pipeline (logs stages, writes .s)"
    IO.eprintln "       compiler <file.w> -o <out>      -- compile to binary"
    IO.eprintln "       compiler <file.w> -r            -- compile and run"
    return 1
