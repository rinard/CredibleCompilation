import CredibleCompilation.ExecExamples

def main : IO Unit := do
  IO.println "=== Credible Compilation Certificate Checker ==="
  IO.println ""
  let examples : List (String × Bool) := [
    ("Example 1 (simple const prop)", checkCertificateExec EExample1.cert),
    ("Example 2 (binop const prop)", checkCertificateExec EExample2.cert),
    ("Example 3 (loop optimization)", checkCertificateExec EExample3.cert),
    ("Example 4 (simple CSE)", checkCertificateExec EExample4.cert),
    ("Example 5 (CSE chain)", checkCertificateExec EExample5.cert),
    ("Example 6 (CSE in loop)", checkCertificateExec EExample6.cert),
    ("Example 7 (const prop+CSE+DCE)", checkCertificateExec EExample7.cert),
    ("Example 8 (goto elimination)", checkCertificateExec EExample8.cert),
    ("Example 9 (IV elimination)", checkCertificateExec EExample9.cert),
    ("Bad Example (buggy y:=3≠5)", checkCertificateExec EBadExample.cert)
  ]
  for (name, result) in examples do
    let status := if result then "PASS" else "FAIL"
    IO.println s!"  {name}: {status}"
  IO.println ""
  IO.println "--- Verbose: Bad Example ---"
  for (name, result) in checkCertificateVerboseExec EBadExample.cert do
    let mark := if result then "ok" else "FAIL"
    IO.println s!"  {name}: {mark}"
