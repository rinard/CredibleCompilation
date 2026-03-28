import CredibleCompilation.CSEOpt

/-!
# CSE Optimizer — Examples

Tests the optimizer on several programs and verifies that the generated
certificates pass `checkCertificateExec`.
-/

open CSEOpt

namespace CSEOptExamples

-- ============================================================
-- § 1. Simple CSE: reuse a computed expression
-- ============================================================

/-! Original:
    0: a := x + y
    1: b := x + y   ← same expression, reuse a
    2: halt

  Expected:
    0: a := x + y
    1: b := a        ← copy
    2: halt
-/

def simpleProg : Prog := #[
  .binop "a" .add "x" "y",
  .binop "b" .add "x" "y",
  .halt
]

def simpleCert := optimize simpleProg ("b" :: [])

#eval! simpleCert.trans
#eval! checkCertificateExec simpleCert
#eval! checkCertificateVerboseExec simpleCert

-- ============================================================
-- § 2. Chained CSE: second expression uses first's result
-- ============================================================

/-! Original:
    0: a := x + y
    1: b := a + z
    2: c := x + y   ← reuse a
    3: d := a + z    ← reuse b
    4: halt

  Expected:
    0: a := x + y
    1: b := a + z
    2: c := a        ← copy
    3: d := b        ← copy
    4: halt
-/

def chainProg : Prog := #[
  .binop "a" .add "x" "y",
  .binop "b" .add "a" "z",
  .binop "c" .add "x" "y",
  .binop "d" .add "a" "z",
  .halt
]

def chainCert := optimize chainProg ("c" :: "d" :: [])

#eval! chainCert.trans
#eval! checkCertificateExec chainCert
#eval! checkCertificateVerboseExec chainCert

-- ============================================================
-- § 3. Kill: reassigning an operand invalidates the expression
-- ============================================================

/-! Original:
    0: a := x + y
    1: x := 42       ← kills x+y
    2: b := x + y    ← NOT the same as a (x changed)
    3: halt

  Expected: no optimization (expression killed)
-/

def killProg : Prog := #[
  .binop "a" .add "x" "y",
  .const "x" (.int 42),
  .binop "b" .add "x" "y",
  .halt
]

def killCert := optimize killProg ("b" :: [])

#eval! killCert.trans   -- should be unchanged
#eval! checkCertificateExec killCert
#eval! checkCertificateVerboseExec killCert

-- ============================================================
-- § 4. Multiple distinct expressions
-- ============================================================

/-! Original:
    0: a := x + y
    1: b := x * y
    2: c := x + y   ← reuse a
    3: d := x * y   ← reuse b
    4: halt
-/

def multiProg : Prog := #[
  .binop "a" .add "x" "y",
  .binop "b" .mul "x" "y",
  .binop "c" .add "x" "y",
  .binop "d" .mul "x" "y",
  .halt
]

def multiCert := optimize multiProg ("c" :: "d" :: [])

#eval! multiCert.trans
#eval! checkCertificateExec multiCert
#eval! checkCertificateVerboseExec multiCert

-- ============================================================
-- § 5. CSE with constants (setup then compute)
-- ============================================================

/-! Original:
    0: x := 5
    1: y := 3
    2: a := x + y
    3: b := x * y
    4: c := x + y   ← reuse a
    5: halt

  Expected: pc 4 becomes copy c a
-/

def constProg : Prog := #[
  .const "x" (.int 5),
  .const "y" (.int 3),
  .binop "a" .add "x" "y",
  .binop "b" .mul "x" "y",
  .binop "c" .add "x" "y",
  .halt
]

def constCert := optimize constProg ("c" :: [])

#eval! constCert.trans
#eval! checkCertificateExec constCert
#eval! checkCertificateVerboseExec constCert

-- ============================================================
-- § 6. CSE in a loop (expression survives the back-edge)
-- ============================================================

/-! Original:
    0: a := x + y        ← compute once
    1: if a < 100 goto 3
    2: halt
    3: b := x + y        ← reuse a (x, y, a unchanged in loop)
    4: goto 1

  Since x, y, and a are never modified, the expression x+y remains
  available through the loop back-edge.
-/

def loopProg : Prog := #[
  .binop "a" .add "x" "y",
  .ifgoto (.cmpLit .lt "a" 100) 3,
  .halt,
  .binop "b" .add "x" "y",
  .goto 1
]

def loopCert := optimize loopProg ("b" :: [])

#eval! loopCert.trans
#eval! checkCertificateExec loopCert
#eval! checkCertificateVerboseExec loopCert

-- ============================================================
-- § 7. No CSE when result aliases an operand
-- ============================================================

/-! Original:
    0: x := x + y     ← x is both result and operand
    1: a := x + y     ← NOT the same (x changed)
    2: halt

  Expected: no optimization (x was overwritten)
-/

def aliasProg : Prog := #[
  .binop "x" .add "x" "y",
  .binop "a" .add "x" "y",
  .halt
]

def aliasCert := optimize aliasProg ("a" :: [])

#eval! aliasCert.trans   -- should be unchanged
#eval! checkCertificateExec aliasCert
#eval! checkCertificateVerboseExec aliasCert

end CSEOptExamples
