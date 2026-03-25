import CredibleCompilation.LICMOpt

/-!
# LICM Optimizer — Examples

Tests the optimizer on several programs and verifies that the generated
certificates pass `checkCertificateExec`.
-/

open LICMOpt

namespace LICMOptExamples

-- ============================================================
-- § 1. Classic LICM: pre-loop computation makes loop body copy redundant
-- ============================================================

/-! Original:
    0: one := 1
    1: t := a * b          ← pre-loop computation
    2: if n ≠ 0 goto 4
    3: halt
    4: s := s + t
    5: t := a * b          ← REDUNDANT (t already = a*b)
    6: n := n - one
    7: goto 2

  Expected: pc 5 becomes `goto 6`
-/

def classicProg : Prog := #[
  .const "one" 1,
  .binop "t" .mul "a" "b",
  .ifgoto (.cmpLit .ne "n" 0) 4,
  .halt,
  .binop "s" .add "s" "t",
  .binop "t" .mul "a" "b",
  .binop "n" .sub "n" "one",
  .goto 2
]

def classicCert := optimize classicProg ("s" :: [])

#eval! classicCert.trans
#eval! checkCertificateExec classicCert
#eval! checkCertificateVerboseExec classicCert

-- ============================================================
-- § 2. Not redundant: operand modified inside loop
-- ============================================================

/-! Original:
    0: t := a * b
    1: a := a + t          ← modifies a, kills available a*b
    2: t := a * b          ← NOT redundant (a changed)
    3: halt

  Expected: no change
-/

def notRedundantProg : Prog := #[
  .binop "t" .mul "a" "b",
  .binop "a" .add "a" "t",
  .binop "t" .mul "a" "b",
  .halt
]

def notRedundantCert := optimize notRedundantProg ("t" :: [])

#eval! notRedundantCert.trans
#eval! checkCertificateExec notRedundantCert
#eval! checkCertificateVerboseExec notRedundantCert

-- ============================================================
-- § 3. Multiple redundant recomputations in one loop
-- ============================================================

/-! Original:
    0: t1 := a + b         ← pre-loop
    1: t2 := c * d         ← pre-loop
    2: if n ≠ 0 goto 4
    3: halt
    4: s := s + t1
    5: t1 := a + b         ← REDUNDANT
    6: r := r + t2
    7: t2 := c * d         ← REDUNDANT
    8: n := n - t1
    9: goto 2

  Expected: pcs 5 and 7 become goto
-/

def multiProg : Prog := #[
  .binop "t1" .add "a" "b",
  .binop "t2" .mul "c" "d",
  .ifgoto (.cmpLit .ne "n" 0) 4,
  .halt,
  .binop "s" .add "s" "t1",
  .binop "t1" .add "a" "b",
  .binop "r" .add "r" "t2",
  .binop "t2" .mul "c" "d",
  .binop "n" .sub "n" "t1",
  .goto 2
]

def multiCert := optimize multiProg ("s" :: "r" :: [])

#eval! multiCert.trans
#eval! checkCertificateExec multiCert
#eval! checkCertificateVerboseExec multiCert

-- ============================================================
-- § 4. Redundant in straight-line code (not a loop)
-- ============================================================

/-! Original:
    0: t := x + y
    1: a := t + z
    2: t := x + y          ← REDUNDANT (t still = x+y)
    3: halt

  Expected: pc 2 becomes goto 3
-/

def straightProg : Prog := #[
  .binop "t" .add "x" "y",
  .binop "a" .add "t" "z",
  .binop "t" .add "x" "y",
  .halt
]

def straightCert := optimize straightProg ("a" :: [])

#eval! straightCert.trans
#eval! checkCertificateExec straightCert
#eval! checkCertificateVerboseExec straightCert

-- ============================================================
-- § 5. No optimization (all unique computations)
-- ============================================================

/-! Original:
    0: a := x + y
    1: b := x * y
    2: c := a + b
    3: halt

  Expected: no change
-/

def uniqueProg : Prog := #[
  .binop "a" .add "x" "y",
  .binop "b" .mul "x" "y",
  .binop "c" .add "a" "b",
  .halt
]

def uniqueCert := optimize uniqueProg ("c" :: [])

#eval! uniqueCert.trans
#eval! checkCertificateExec uniqueCert
#eval! checkCertificateVerboseExec uniqueCert

-- ============================================================
-- § 6. Conservative: t is operand in another available expression
-- ============================================================

/-! Original:
    0: t := a + b
    1: s := t + c          ← t is operand here
    2: t := a + b          ← WOULD be redundant, but t is an operand
                              in another available entry — conservative skip
    3: halt

  Expected: no change (conservative)
-/

def conservativeProg : Prog := #[
  .binop "t" .add "a" "b",
  .binop "s" .add "t" "c",
  .binop "t" .add "a" "b",
  .halt
]

def conservativeCert := optimize conservativeProg ("s" :: [])

#eval! conservativeCert.trans
#eval! checkCertificateExec conservativeCert
#eval! checkCertificateVerboseExec conservativeCert

end LICMOptExamples
