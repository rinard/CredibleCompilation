import CredibleCompilation.CodeGen
import CredibleCompilation.ExecChecker

-- Parse and compile the array program
def diagArray : Except String Unit := do
  let input := "
  var i : int, x : int;
  arr[0] := 42;
  i := 1;
  arr[i] := 100;
  i := 0;
  x := arr[i]
"
  let prog ← CodeGen.parseProgram input
  let tac := prog.compileToTAC
  -- First pipeline
  let p1 ← CodeGen.optimizePipeline tac
  -- Get the RegAlloc certificate
  let cert := RegAllocOpt.optimize p1
  -- Run verbose check
  let results := checkCertificateVerboseExec cert
  for (name, result) in results do
    IO.println s!"{name}: {result}"
  pure ()

#eval diagArray
