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
  | [inputFile, "-debug"] =>
    let src ← IO.FS.readFile ⟨inputFile⟩
    match parseProgram src with
    | .error e => IO.eprintln s!"parse error: {e}"; return 1
    | .ok prog =>
      if !prog.typeCheck then IO.eprintln "type check failed"; return 1
      let tac := prog.compileToTAC
      IO.println s!"TAC size: {tac.size}"
      let cert := RegAllocOpt.optimize tac
      IO.println s!"Trans size: {cert.trans.size}"
      for (name, result) in checkCertificateVerboseExec cert do
        IO.println s!"  {name}: {if result then "ok" else "FAIL"}"
      -- Find which PCs fail invariant preservation
      let checkInvProg (label : String) (prog : Prog) (inv : Array EInv) : IO Unit := do
        for pc in List.range prog.size do
          match prog[pc]? with
          | some instr =>
            for pc' in successors instr pc do
              let inv_pre := inv.getD pc ([] : EInv)
              let inv_post := inv.getD pc' ([] : EInv)
              for atom in inv_post do
                if !checkInvAtom inv_pre instr atom then
                  IO.println s!"  inv_fail {label}: PC {pc} ({repr instr}) -> PC {pc'}, atom {repr atom}"
                  IO.println s!"    inv_pre: {repr inv_pre}"
          | none => pure ()
      checkInvProg "orig" cert.orig cert.inv_orig
      checkInvProg "trans" cert.trans cert.inv_trans
      return 0
  | _ =>
    IO.eprintln "Usage: compiler <file.w>          -- print assembly to stdout"
    IO.eprintln "       compiler <file.w> -o <out>  -- compile to binary"
    IO.eprintln "       compiler <file.w> -r        -- compile and run"
    return 1
