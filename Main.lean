import CredibleCompilation.DecidableChecker

def main : IO Unit := do
  IO.println "=== Credible Compilation Certificate Checker ==="
  IO.println ""
  let examples : List (String × Bool) := [
    ("Example 1 (simple const prop)", checkCertificate DExample1.cert),
    ("Example 2 (binop const prop)", checkCertificate DExample2.cert),
    ("Example 3 (loop optimization)", checkCertificate DExample3.cert),
    ("Bad Example (buggy y:=3≠5)", checkCertificate DBadExample.cert)
  ]
  for (name, result) in examples do
    let status := if result then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Verbose: Bad Example ---"
  for (name, result) in checkCertificateVerbose DBadExample.cert do
    let mark := if result then "ok" else "FAIL"
    IO.println s!"  {name}: {mark}"
