import CredibleCompilation.ExecExamples

def main : IO Unit := do
  IO.println "=== Credible Compilation Certificate Checker ==="
  IO.println ""
  let examples : List (String × Bool) := [
    ("Constant Propagation", checkCertificateExec ConstProp.cert),
    ("Copy Propagation", checkCertificateExec CopyProp.cert),
    ("Common Subexpression Elimination", checkCertificateExec CSE.cert),
    ("Dead Code Elimination", checkCertificateExec DCE.cert),
    ("Loop-Invariant Code Motion", checkCertificateExec LICM.cert),
    ("Induction Variable Elimination", checkCertificateExec IVE.cert),
    ("Bad Example (buggy transform)", checkCertificateExec BadExample.cert)
  ]
  for (name, result) in examples do
    let status := if result then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Verbose: Bad Example ---"
  for (name, result) in checkCertificateVerboseExec BadExample.cert do
    let mark := if result then "ok" else "FAIL"
    IO.println s!"  {name}: {mark}"
