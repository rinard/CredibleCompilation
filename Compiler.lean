import CredibleCompilation.CodeGen

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compileToAsm src with
    | .ok asm =>
      IO.print asm
      return 0
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 1
  | [inputFile, "-o", outputFile] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compileToAsm src with
    | .ok asm =>
      let asmFile := outputFile ++ ".s"
      IO.FS.writeFile ⟨asmFile⟩ asm
      let cc ← IO.Process.output { cmd := "cc", args := #["-o", outputFile, asmFile] }
      if cc.exitCode != 0 then
        IO.eprintln cc.stderr
        return 1
      IO.eprintln s!"compiled: {outputFile}"
      return 0
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 1
  | [inputFile, "-r"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match compileToAsm src with
    | .ok asm =>
      let asmFile := "/tmp/while_out.s"
      let binFile := "/tmp/while_out"
      IO.FS.writeFile ⟨asmFile⟩ asm
      let cc ← IO.Process.output { cmd := "cc", args := #["-o", binFile, asmFile] }
      if cc.exitCode != 0 then
        IO.eprintln cc.stderr
        return 1
      let run ← IO.Process.spawn { cmd := binFile, stdin := .inherit, stdout := .inherit, stderr := .inherit }
      let exit ← run.wait
      return exit
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 1
  | _ =>
    IO.eprintln "Usage: compiler <file.w>          -- print assembly to stdout"
    IO.eprintln "       compiler <file.w> -o <out>  -- compile to binary"
    IO.eprintln "       compiler <file.w> -r        -- compile and run"
    return 1
