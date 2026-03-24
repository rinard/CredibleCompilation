import CredibleCompilation.ExecChecker

def main : IO Unit := do
  IO.println "=== Credible Compilation Certificate Checker ==="
  IO.println ""
  let examples : List (String × Bool) := [
    ("Example 1 (simple const prop)", checkCertificate EExample1.cert),
    ("Example 2 (binop const prop)", checkCertificate EExample2.cert),
    ("Example 3 (loop optimization)", checkCertificate EExample3.cert),
    ("Bad Example (buggy y:=3≠5)", checkCertificate EBadExample.cert)
  ]
  for (name, result) in examples do
    let status := if result then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Verbose: Bad Example ---"
  for (name, result) in checkCertificateVerbose EBadExample.cert do
    let mark := if result then "ok" else "FAIL"
    IO.println s!"  {name}: {mark}"
