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
      IO.println s!"LICM hoistable: {LICMOpt.numHoistable tac}"
      -- Quick LICM cert check
      let licm := LICMOpt.optimize tac
      for (n, r) in checkCertificateVerboseExec licm do
        if !r then IO.println s!"  LICM {n}: FAIL"
      -- Find first failing trans PC
      for tpc in List.range licm.trans.size do
        match licm.trans[tpc]?, licm.instrCerts[tpc]? with
        | some instr, some ic =>
          if instr != .halt then
            for pc_t' in successors instr tpc do
              let ic' := licm.instrCerts.getD pc_t' default
              let branchInfo := match instr with
                | .ifgoto b l => match b.mapVarsRel ic.rel with
                  | some oc => if !(l == tpc + 1) then some (oc, pc_t' == l) else none
                  | none => none
                | _ => none
              let ok := ic.transitions.any fun tc =>
                tc.rel == ic.rel && tc.rel_next == ic'.rel &&
                checkOrigPath licm.orig ([] : SymStore) ([] : SymArrayMem)
                  (licm.inv_orig.getD ic.pc_orig ([] : EInv))
                  ic.pc_orig tc.origLabels ic'.pc_orig branchInfo &&
                checkRelConsistency licm.orig ic.pc_orig tc.origLabels instr
                  (licm.inv_orig.getD ic.pc_orig ([] : EInv)) tc.rel tc.rel_next
              if !ok then
                let r := ic.transitions.headD default
                let relOk := r.rel == ic.rel && r.rel_next == ic'.rel
                let pathOk := checkOrigPath licm.orig ([] : SymStore) ([] : SymArrayMem)
                  (licm.inv_orig.getD ic.pc_orig ([] : EInv))
                  ic.pc_orig r.origLabels ic'.pc_orig branchInfo
                let rcOk := checkRelConsistency licm.orig ic.pc_orig r.origLabels instr
                  (licm.inv_orig.getD ic.pc_orig ([] : EInv)) r.rel r.rel_next
                IO.println s!"  T{tpc}→T{pc_t'} o={ic.pc_orig}→{ic'.pc_orig} rel={relOk} path={pathOk} rc={rcOk} labels={r.origLabels}"
                -- Find failing pair
                if !rcOk then
                  let (origSS, origSAM) := execPath licm.orig ([] : SymStore) ([] : SymArrayMem) ic.pc_orig r.origLabels
                  let (transSS, transSAM) := execSymbolic ([] : SymStore) ([] : SymArrayMem) instr
                  let preSubst := buildSubstMap r.rel
                  let inv := licm.inv_orig.getD ic.pc_orig ([] : EInv)
                  -- Check amCheck
                  let amOk := origSAM.length == transSAM.length
                  IO.println s!"    amLen: orig={origSAM.length} trans={transSAM.length} ok={amOk}"
                  for (eo, et) in r.rel_next do
                    let origVal := eo.substSym origSS |>.simplify inv
                    let transVal := (et.substSym transSS).substSym preSubst |>.simplify inv
                    if origVal != transVal then
                      IO.println s!"    pair fail: ({repr eo}, {repr et}) → orig={repr origVal} trans={repr transVal}"
                      break
                break
        | _, _ => pure ()
      -- Show hoisted detection
      let licmInLoop := LICMOpt.findLoopPCs tac
      let licmH := LICMOpt.findHoistable tac licmInLoop
      IO.println s!"  hoistable: {licmH.map fun (h, p, x, _) => (h, p, x)}"
      let licmPCMap := LICMOpt.computePCMap tac.size licmH
      let licmOPM := LICMOpt.buildOrigPCMap tac.size licmPCMap licm.trans.size licmH
      for tpc in List.range licm.trans.size do
        if LICMOpt.isHoisted licm.trans licmOPM tpc then
          IO.println s!"  hoisted T{tpc}: opm={licmOPM.getD tpc 999}"
      let cert := RegAllocOpt.optimize tac
      IO.println s!"Trans size: {cert.trans.size}"
      for (name, result) in checkCertificateVerboseExec cert do
        IO.println s!"  {name}: {if result then "ok" else "FAIL"}"
      return 0
  | _ =>
    IO.eprintln "Usage: compiler <file.w>          -- print assembly to stdout"
    IO.eprintln "       compiler <file.w> -o <out>  -- compile to binary"
    IO.eprintln "       compiler <file.w> -r        -- compile and run"
    return 1
