import CredibleCompilation.ExecChecker

/-!
# Executable Certificate Examples

Example certificates for the executable checker.
-/

-- Helper: build an ETransCorr with empty relation
private abbrev tc (labels : List Label) : ETransCorr := { origLabels := labels }
-- Helper: build identity pairs from a list of observable variables
private def obsRel (obs : List Var) : EExprRel :=
  obs.map fun v => (.var v, .var v)
-- Helper: build an ETransCorr whose target has observable identity pairs
private abbrev tcObs (labels : List Label) (obs : EExprRel) : ETransCorr :=
  { origLabels := labels, rel_next := obs }
-- Helper: build an EInstrCert with empty relation
private abbrev ic (pc : Label) (trans : List ETransCorr) : EInstrCert :=
  { pc_orig := pc, transitions := trans }
-- Helper: build an EInstrCert for a halt label with observable identity pairs
private abbrev icObs (pc : Label) (obs : EExprRel) : EInstrCert :=
  { pc_orig := pc, rel := obs, transitions := [] }
-- Helper: build an EHaltCert with empty relation
private abbrev hc (pc : Label) : EHaltCert := { pc_orig := pc }

-- ============================================================
-- § 1. Example certificates
-- ============================================================

/-! ### Example 1: Simple constant propagation (copy → const)
  Original:  `0: x:=5; 1: y:=x; 2: halt`
  Transformed: `0: x:=5; 1: y:=5; 2: halt`
-/
namespace EExample1

def cert : ECertificate :=
  { orig  := #[.const "x" 5, .copy "y" "x", .halt]
    trans := #[.const "x" 5, .const "y" 5, .halt]
    inv_orig  := #[[], [("x", .lit 5)], [("x", .lit 5)]]
    inv_trans := #[[], [("x", .lit 5)], [("x", .lit 5)]]
    observable := ["y"]
    instrCerts := #[
      ic 0 ([tc [1]]),                          -- trans 0→1 maps to orig 0→1
      ic 1 ([(tcObs [2] (obsRel ["y"]))]),                 -- trans 1→2 maps to orig 1→2
      icObs 2 (obsRel ["y"]) ]                              -- halt
    haltCerts := #[hc 0, hc 0, hc 2]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample1

/-! ### Example 2: Constant propagation into binop operand
  Original:  `0: a:=10; 1: b:=a; 2: c:=b+y; 3: halt`
  Transformed: `0: a:=10; 1: b:=10; 2: c:=b+y; 3: halt`
-/
namespace EExample2

def cert : ECertificate :=
  { orig  := #[.const "a" 10, .copy "b" "a", .binop "c" .add "b" "y", .halt]
    trans := #[.const "a" 10, .const "b" 10, .binop "c" .add "b" "y", .halt]
    inv_orig  := #[[], [("a", .lit 10)], [("a", .lit 10), ("b", .lit 10)], [("a", .lit 10), ("b", .lit 10)]]
    inv_trans := #[[], [("a", .lit 10)], [("a", .lit 10), ("b", .lit 10)], [("a", .lit 10), ("b", .lit 10)]]
    observable := ["c"]
    instrCerts := #[
      ic 0 ([tc [1]]),
      ic 1 ([tc [2]]),
      ic 2 ([tcObs [3] (obsRel ["c"])]),
      icObs 3 (obsRel ["c"]) ]
    haltCerts := #[hc 0, hc 0, hc 0, hc 3]
    measure := #[0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample2

/-! ### Example 3: Redundant assignment removal in a loop
  Original (7 instr): includes redundant `step:=2` at pc 4
  Transformed (6 instr): redundant assignment removed
  Trans 3→4 maps to orig 3→4→5 (two original steps)
-/
namespace EExample3

def cert : ECertificate :=
  { orig := #[
      .const "step" 2,                -- 0
      .ifgoto "n" 3,                  -- 1
      .halt,                          -- 2
      .binop "acc" .add "acc" "n",    -- 3
      .const "step" 2,               -- 4 (redundant)
      .binop "n" .sub "n" "step",    -- 5
      .goto 1 ]                       -- 6
    trans := #[
      .const "step" 2,                -- 0
      .ifgoto "n" 3,                  -- 1
      .halt,                          -- 2
      .binop "acc" .add "acc" "n",    -- 3
      .binop "n" .sub "n" "step",    -- 4
      .goto 1 ]                       -- 5
    inv_orig  := #[[], [("step", .lit 2)], [("step", .lit 2)], [("step", .lit 2)],
                    [("step", .lit 2)], [("step", .lit 2)], [("step", .lit 2)]]
    inv_trans := #[[], [("step", .lit 2)], [("step", .lit 2)],
                    [("step", .lit 2)], [("step", .lit 2)], [("step", .lit 2)]]
    observable := ["acc"]
    instrCerts := #[
      ic 0 ([tc [1]]),                                        -- trans 0→1 : orig 0→1
      ic 1 ([tc [3], tcObs [2] (obsRel ["acc"])]),                      -- trans 1→3 or 1→2
      icObs 2 (obsRel ["acc"]),                                          -- halt
      ic 3 ([tc [4, 5]]),                                     -- trans 3→4 : orig 3→4→5 (two steps)
      ic 5 ([tc [6]]),                                        -- trans 4→5 : orig 5→6
      ic 6 ([tc [1]]) ]                                       -- trans 5→1 : orig 6→1
    haltCerts := #[hc 0, hc 0, hc 2, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample3

/-! ### Bad Example: Buggy transformation (y:=x → y:=3, should be y:=5)
  The checker rejects this because the symbolic effects don't match:
  orig `copy "y" "x"` under invariant `x=5` produces `y=5`,
  but trans `const "y" 3` produces `y=3`.
-/
namespace EBadExample

def cert : ECertificate :=
  { orig  := #[.const "x" 5, .copy "y" "x", .halt]
    trans := #[.const "x" 5, .const "y" 3, .halt]
    inv_orig  := #[[], [("x", .lit 5)], [("x", .lit 5)]]
    inv_trans := #[[], [("x", .lit 5)], [("x", .lit 5)]]
    observable := ["y"]
    instrCerts := #[
      ic 0 ([tc [1]]),
      ic 1 ([tcObs [2] (obsRel ["y"])]),
      icObs 2 (obsRel ["y"]) ]
    haltCerts := #[hc 0, hc 0, hc 2]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- false
#eval! checkCertificateVerboseExec cert       -- all_transitions fails

end EBadExample

/-! ### Example 4: Simple common subexpression elimination
  Original:  `0: a := x+y; 1: b := x+y; 2: halt`
  Transformed: `0: a := x+y; 1: b := a; 2: halt`
  The second `x+y` is replaced by a copy from `a`.
  Invariant: after pc 0, `a = x+y`.
-/
namespace EExample4

def cert : ECertificate :=
  { orig  := #[.binop "a" .add "x" "y",
               .binop "b" .add "x" "y",
               .halt]
    trans := #[.binop "a" .add "x" "y",
               .copy "b" "a",
               .halt]
    inv_orig  := #[[], [("a", .bin .add (.var "x") (.var "y"))],
                      [("a", .bin .add (.var "x") (.var "y"))]]
    inv_trans := #[[], [("a", .bin .add (.var "x") (.var "y"))],
                      [("a", .bin .add (.var "x") (.var "y"))]]
    observable := ["a", "b"]
    instrCerts := #[
      ic 0 ([tc [1]]),          -- trans 0→1 : orig 0→1
      ic 1 ([tcObs [2] (obsRel ["a", "b"])]),  -- trans 1→2 : orig 1→2
      icObs 2 (obsRel ["a", "b"]) ]            -- halt
    haltCerts := #[hc 0, hc 0, hc 2]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample4

/-! ### Example 5: CSE with a chain of dependent subexpressions
  Original:
    0: t := a * b;  1: u := a * b;  2: v := t + u;  3: halt
  Transformed:
    0: t := a * b;  1: u := t;      2: v := t + u;  3: halt
  After pc 0 both programs know `t = a*b`.
  The binop `v := t + u` is identical in both, so no invariant
  beyond `t = a*b` is needed for the CSE step.
-/
namespace EExample5

def cert : ECertificate :=
  { orig  := #[.binop "t" .mul "a" "b",
               .binop "u" .mul "a" "b",
               .binop "v" .add "t" "u",
               .halt]
    trans := #[.binop "t" .mul "a" "b",
               .copy "u" "t",
               .binop "v" .add "t" "u",
               .halt]
    inv_orig  := #[[], [("t", .bin .mul (.var "a") (.var "b"))],
                      [("t", .bin .mul (.var "a") (.var "b"))],
                      [("t", .bin .mul (.var "a") (.var "b"))]]
    inv_trans := #[[], [("t", .bin .mul (.var "a") (.var "b"))],
                      [("t", .bin .mul (.var "a") (.var "b"))],
                      [("t", .bin .mul (.var "a") (.var "b"))]]
    observable := ["v"]
    instrCerts := #[
      ic 0 ([tc [1]]),
      ic 1 ([tc [2]]),
      ic 2 ([tcObs [3] (obsRel ["v"])]),
      icObs 3 (obsRel ["v"]) ]
    haltCerts := #[hc 0, hc 0, hc 0, hc 3]
    measure := #[0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample5

/-! ### Example 6: CSE inside a loop
  Original (loop body recomputes `k := a * b` each iteration):
    0: k := a * b;  1: if n goto 3;  2: halt
    3: acc := acc + k;  4: k := a * b;  5: n := n - one;  6: goto 1
  Transformed (redundant recomputation removed):
    0: k := a * b;  1: if n goto 3;  2: halt
    3: acc := acc + k;  4: n := n - one;  5: goto 1
  Invariant `k = a*b` holds throughout the loop in both programs.
  Trans 3→4 maps to orig 3→4→5 (skipping the redundant `k := a*b`
  because `k` already equals `a*b`).
-/
namespace EExample6

def cert : ECertificate :=
  { orig := #[
      .binop "k" .mul "a" "b",         -- 0
      .ifgoto "n" 3,                    -- 1
      .halt,                            -- 2
      .binop "acc" .add "acc" "k",      -- 3
      .binop "k" .mul "a" "b",         -- 4 (redundant)
      .binop "n" .sub "n" "one",       -- 5
      .goto 1 ]                         -- 6
    trans := #[
      .binop "k" .mul "a" "b",         -- 0
      .ifgoto "n" 3,                    -- 1
      .halt,                            -- 2
      .binop "acc" .add "acc" "k",      -- 3
      .binop "n" .sub "n" "one",       -- 4
      .goto 1 ]                         -- 5
    inv_orig  := #[[], [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))]]
    inv_trans := #[[], [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))],
                      [("k", .bin .mul (.var "a") (.var "b"))]]
    observable := ["acc"]
    instrCerts := #[
      ic 0 ([tc [1]]),                    -- trans 0→1 : orig 0→1
      ic 1 ([tc [3], tcObs [2] (obsRel ["acc"])]),  -- trans 1→3 or 1→2
      icObs 2 (obsRel ["acc"]),                      -- halt
      ic 3 ([tc [4, 5]]),                 -- trans 3→4 : orig 3→4→5 (two steps)
      ic 5 ([tc [6]]),                    -- trans 4→5 : orig 5→6
      ic 6 ([tc [1]]) ]                   -- trans 5→1 : orig 6→1
    haltCerts := #[hc 0, hc 0, hc 2, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample6

/-! ### Example 7: Combined constant propagation + CSE + dead code elimination

  Original (9 instructions):
    0: n := 10
    1: m := 10
    2: t := n + m            -- computable at compile time
    3: if t goto 5           -- always taken (t=20≠0)
    4: halt                  -- dead code (unreachable)
    5: x := a * b
    6: y := a * b            -- CSE target (same as x)
    7: z := x + y
    8: halt

  Transformed (7 instructions) — three optimizations applied:
    0: n := 10
    1: m := 10
    2: t := 20               -- constant propagation + folding (10+10=20)
    3: x := a * b            -- dead code elimination (always-taken branch + dead halt removed)
    4: y := x                -- CSE (reuse x = a*b)
    5: z := x + y
    6: halt

  The certificate bridges three original steps (2→3→5) for transformed step 2→3,
  using symbolic execution to resolve the always-taken branch at original pc 3.
-/
namespace EExample7

private def inv_n : EInv := [("n", .lit 10)]
private def inv_nm : EInv := [("n", .lit 10), ("m", .lit 10)]
private def inv_nmt : EInv := [("n", .lit 10), ("m", .lit 10), ("t", .lit 20)]
private def ab : Expr := .bin .mul (.var "a") (.var "b")
private def inv_nmt_x : EInv := inv_nmt ++ [("x", ab)]
private def inv_nmt_xy : EInv := inv_nmt ++ [("x", ab), ("y", ab)]

def cert : ECertificate :=
  { orig := #[
      .const "n" 10,                -- 0
      .const "m" 10,                -- 1
      .binop "t" .add "n" "m",     -- 2: t := n+m (= 20)
      .ifgoto "t" 5,               -- 3: always taken
      .halt,                        -- 4: dead (unreachable)
      .binop "x" .mul "a" "b",     -- 5
      .binop "y" .mul "a" "b",     -- 6: CSE target
      .binop "z" .add "x" "y",     -- 7
      .halt ]                       -- 8
    trans := #[
      .const "n" 10,                -- 0
      .const "m" 10,                -- 1
      .const "t" 20,               -- 2: constant folded
      .binop "x" .mul "a" "b",     -- 3: dead code eliminated
      .copy "y" "x",               -- 4: CSE
      .binop "z" .add "x" "y",     -- 5
      .halt ]                       -- 6
    inv_orig := #[
      [],                           -- 0
      inv_n,                        -- 1
      inv_nm,                       -- 2
      inv_nmt,                      -- 3
      inv_nmt,                      -- 4 (unreachable but preserved)
      inv_nmt,                      -- 5
      inv_nmt_x,                    -- 6
      inv_nmt_xy,                   -- 7
      inv_nmt_xy ]                  -- 8
    inv_trans := #[
      [],                           -- 0
      inv_n,                        -- 1
      inv_nm,                       -- 2
      inv_nmt,                      -- 3
      inv_nmt_x,                    -- 4
      inv_nmt_xy,                   -- 5
      inv_nmt_xy ]                  -- 6
    observable := ["z"]
    instrCerts := #[
      ic 0 ([tc [1]]),              -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),              -- trans 1→2 : orig 1→2
      ic 2 ([tc [3, 5]]),           -- trans 2→3 : orig 2→3→5 (const prop + dead code elim)
      ic 5 ([tc [6]]),              -- trans 3→4 : orig 5→6
      ic 6 ([tc [7]]),              -- trans 4→5 : orig 6→7 (CSE)
      ic 7 ([tcObs [8] (obsRel ["z"])]),      -- trans 5→6 : orig 7→8
      icObs 8 (obsRel ["z"]) ]                 -- halt
    haltCerts := #[hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 8]
    measure := #[0, 0, 0, 0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample7

/-! ### Example 8: Goto elimination (basic block reordering)

  Based on: `n = 500; k = 500; while (n) { n = n - 1; } k = 0;`

  The loop counts `n` down to zero; the only post-loop effect is `k := 0`.
  The original uses a `goto` to jump from the loop exit to the post-loop
  cleanup.  The transformed version reorders the basic blocks so the cleanup
  follows the conditional branch's fall-through directly, eliminating the
  `goto` and saving one instruction.

  Original (9 instructions):
    0: n := 500;  1: k := 500;  2: one := 1
    3: if n goto 5;  4: goto 7
    5: n := n - one;  6: goto 3
    7: k := 0;  8: halt

  Transformed (8 instructions — goto eliminated, blocks reordered):
    0: n := 500;  1: k := 500;  2: one := 1
    3: if n goto 6
    4: k := 0;  5: halt
    6: n := n - one;  7: goto 3

  The certificate bridges trans 3→4 to orig 3→4→7 (fall-through, then
  skip the goto), proving the reordered blocks produce identical effects.
-/
namespace EExample8

-- Invariant building blocks
private def inv_n : EInv := [("n", .lit 500)]
private def inv_nk : EInv := [("n", .lit 500), ("k", .lit 500)]
private def inv_loop : EInv := [("one", .lit 1), ("k", .lit 500)]
private def inv_post : EInv := [("one", .lit 1), ("k", .lit 0)]

def cert : ECertificate :=
  { orig := #[
      .const "n" 500,              -- 0
      .const "k" 500,              -- 1
      .const "one" 1,              -- 2
      .ifgoto "n" 5,               -- 3: while n ≠ 0
      .goto 7,                     -- 4: exit loop
      .binop "n" .sub "n" "one",   -- 5: n -= 1
      .goto 3,                     -- 6: loop back
      .const "k" 0,               -- 7: post-loop cleanup
      .halt ]                      -- 8
    trans := #[
      .const "n" 500,              -- 0
      .const "k" 500,              -- 1
      .const "one" 1,              -- 2
      .ifgoto "n" 6,               -- 3: while n ≠ 0
      .const "k" 0,               -- 4: post-loop cleanup (inlined)
      .halt,                       -- 5
      .binop "n" .sub "n" "one",   -- 6: n -= 1
      .goto 3 ]                    -- 7: loop back
    inv_orig := #[
      [],                           -- 0
      inv_n,                        -- 1
      inv_nk,                       -- 2
      inv_loop,                     -- 3: loop head
      inv_loop,                     -- 4
      inv_loop,                     -- 5
      inv_loop,                     -- 6
      inv_loop,                     -- 7: post-loop
      inv_post ]                    -- 8: after k := 0
    inv_trans := #[
      [],                           -- 0
      inv_n,                        -- 1
      inv_nk,                       -- 2
      inv_loop,                     -- 3: loop head
      inv_loop,                     -- 4: fall-through exit
      inv_post,                     -- 5: after k := 0
      inv_loop,                     -- 6: loop body
      inv_loop ]                    -- 7
    observable := ["n", "k"]
    instrCerts := #[
      ic 0 ([tc [1]]),                -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                -- trans 1→2 : orig 1→2
      ic 2 ([tc [3]]),                -- trans 2→3 : orig 2→3
      ic 3 ([tc [5], tc [4, 7]]),     -- trans 3→6 : orig 3→5 (taken)
                                       -- trans 3→4 : orig 3→4→7 (fall + skip goto)
      ic 7 ([tcObs [8] (obsRel ["n", "k"])]),  -- trans 4→5 : orig 7→8
      icObs 8 (obsRel ["n", "k"]),              -- halt
      ic 5 ([tc [6]]),                -- trans 6→7 : orig 5→6
      ic 6 ([tc [3]]) ]               -- trans 7→3 : orig 6→3 (loop back)
    haltCerts := #[hc 0, hc 0, hc 0, hc 0, hc 0, hc 8, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample8

/-! ### Example 9: Induction variable elimination

  Based on: `i = 0; n = 1; k = 500; while (i < k) { n = n + k; i = i + 1; } i = 10`

  The original program recomputes the loop condition `rem := k - i` every
  iteration.  The transformed program replaces this with a countdown
  `rem := rem - one`, using the algebraic identity `(k - i_old) - 1 = k - i`
  (where `i = i_old + 1`).

  Original (10 instructions):
    0: one := 1;  1: i := 0;  2: n := 1;  3: k := 500
    4: rem := k - i      ← loop head: recompute condition from i
    5: if rem goto 7;  6: goto 10
    7: n := n + k;  8: i := i + one;  9: goto 4
    10: i := 10;  11: halt

  Transformed (13 instructions — pc 9 differs, extra goto at pc 10):
    0: one := 1;  1: i := 0;  2: n := 1;  3: k := 500
    4: rem := k - i      ← initial computation (same as orig, used once)
    5: if rem goto 7;  6: goto 11
    7: n := n + k;  8: i := i + one
    9: rem := rem - one  ← IVE: decrement countdown
    10: goto 5           ← skip rem recomputation
    11: i := 10;  12: halt

  The relational invariant **`rem = 501 - i`** at pc 9 (after `i` is
  incremented but before `rem` is updated) is the key: both
  `(501 - i) - 1` and `500 - i` simplify to `.bin .sub (.lit 500) (.var "i")`
  via the reassociation rule `(lit − x) − lit → (lit − lit) − x`.
-/
namespace EExample9

-- Invariant building blocks
private def inv_1 : EInv := [("one", .lit 1)]
private def inv_1k : EInv := [("one", .lit 1), ("k", .lit 500)]
/-- At the loop head (pc 5) and body (pcs 7–8): rem = 500 - i. -/
private def inv_loop : EInv :=
  [("one", .lit 1), ("k", .lit 500),
   ("rem", .bin .sub (.lit 500) (.var "i"))]
/-- After i := i + one (pc 9): rem is stale, rem = 501 - i. -/
private def inv_post_inc : EInv :=
  [("one", .lit 1), ("k", .lit 500),
   ("rem", .bin .sub (.lit 501) (.var "i"))]

def cert : ECertificate :=
  { orig := #[
      .const "one" 1,                -- 0
      .const "i" 0,                  -- 1
      .const "n" 1,                  -- 2
      .const "k" 500,               -- 3
      .binop "rem" .sub "k" "i",    -- 4: loop head — recompute rem
      .ifgoto "rem" 7,              -- 5: enter body if i < k
      .goto 10,                      -- 6: exit loop
      .binop "n" .add "n" "k",      -- 7: body
      .binop "i" .add "i" "one",   -- 8: i++
      .goto 4,                       -- 9: back to recomputation
      .const "i" 10,                -- 10: post-loop
      .halt ]                        -- 11
    trans := #[
      .const "one" 1,                -- 0
      .const "i" 0,                  -- 1
      .const "n" 1,                  -- 2
      .const "k" 500,               -- 3
      .binop "rem" .sub "k" "i",    -- 4: initial rem = 500 (computed once)
      .ifgoto "rem" 7,              -- 5: loop head
      .goto 11,                      -- 6: exit loop
      .binop "n" .add "n" "k",      -- 7: body (same)
      .binop "i" .add "i" "one",   -- 8: i++ (same)
      .binop "rem" .sub "rem" "one",-- 9: IVE — countdown
      .goto 5,                       -- 10: skip rem recomputation
      .const "i" 10,                -- 11: post-loop
      .halt ]                        -- 12
    inv_orig := #[
      [],                            -- 0
      inv_1,                         -- 1
      inv_1,                         -- 2
      inv_1,                         -- 3
      inv_1k,                        -- 4: before rem computed
      inv_loop,                      -- 5: rem = 500 - i
      inv_loop,                      -- 6
      inv_loop,                      -- 7
      inv_loop,                      -- 8
      inv_post_inc,                  -- 9: after i++, rem = 501 - i
      inv_1k,                        -- 10: post-loop
      inv_1k ]                       -- 11
    inv_trans := #[
      [],                            -- 0
      inv_1,                         -- 1
      inv_1,                         -- 2
      inv_1,                         -- 3
      inv_1k,                        -- 4
      inv_loop,                      -- 5: rem = 500 - i
      inv_loop,                      -- 6
      inv_loop,                      -- 7
      inv_loop,                      -- 8
      inv_post_inc,                  -- 9: rem = 501 - i (before countdown)
      inv_loop,                      -- 10: rem = 500 - i (after countdown)
      inv_1k,                        -- 11
      inv_1k ]                       -- 12
    observable := ["n", "i"]
    instrCerts := #[
      ic 0 ([tc [1]]),                -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                -- trans 1→2 : orig 1→2
      ic 2 ([tc [3]]),                -- trans 2→3 : orig 2→3
      ic 3 ([tc [4]]),                -- trans 3→4 : orig 3→4
      ic 4 ([tc [5]]),                -- trans 4→5 : orig 4→5
      ic 5 ([tc [7], tc [6]]),        -- trans 5→7 or 5→6 : orig 5→7 or 5→6
      ic 6 ([tc [10]]),               -- trans 6→11 : orig 6→10
      ic 7 ([tc [8]]),                -- trans 7→8 : orig 7→8
      ic 8 ([tc [9]]),                -- trans 8→9 : orig 8→9
      ic 9 ([tc [4, 5]]),             -- trans 9→10 : orig 9→4→5 (the IVE step!)
      ic 5 ([tc []]),                 -- trans 10→5 : orig 5→5 (zero-step)
      ic 10 ([tcObs [11] (obsRel ["n", "i"])]),  -- trans 11→12 : orig 10→11
      icObs 11 (obsRel ["n", "i"]) ]              -- halt
    haltCerts := #[hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample9

/-! ### Example 10: CSE with temporary variable mapped to an expression

  Original:
    0: a := x + y
    1: b := x + y
    2: halt

  Transformed (CSE into temporary):
    0: t := x + y    -- extract common subexpression into temp
    1: a := t
    2: b := t
    3: halt

  The temporary `t` in the transformed program does not exist in the original.
  The expression relation `(x+y, t)` maps transformed variable `t` to the
  *expression* `x+y` in the original — something the old variable-map framework
  could not express.

  At halt, only `a` and `b` are observable; `t` is not.
  Trans step 0 is a zero-step original transition (orig stays at pc 0)
  that establishes the `t = x+y` relation, with a decreasing measure to
  guarantee termination.
-/
namespace EExample10

-- The key relation: transformed variable `t` equals original expression `x+y`
private def tRel : EExprRel := [(.bin .add (.var "x") (.var "y"), .var "t")]
-- At halt: observable identity + temp mapping (temp not observable)
private def haltRel : EExprRel := obsRel ["a", "b"] ++ tRel

def cert : ECertificate :=
  { orig  := #[.binop "a" .add "x" "y",
               .binop "b" .add "x" "y",
               .halt]
    trans := #[.binop "t" .add "x" "y",    -- 0: extract CSE into temp
               .copy "a" "t",               -- 1: a gets temp
               .copy "b" "t",               -- 2: b gets temp
               .halt]                        -- 3
    inv_orig  := #[[], [], []]
    inv_trans := #[[], [], [], []]
    observable := ["a", "b"]
    instrCerts := #[
      -- Trans 0→1: orig stays at 0 (zero-step), establishes t = x+y
      { pc_orig := 0, rel := [],
        transitions := [{ origLabels := [], rel_next := tRel }] },
      -- Trans 1→2: orig 0→1 (a := x+y), t = x+y carries through
      { pc_orig := 0, rel := tRel,
        transitions := [{ origLabels := [1], rel := tRel, rel_next := tRel }] },
      -- Trans 2→3: orig 1→2 (b := x+y), post-rel adds observable identity
      { pc_orig := 1, rel := tRel,
        transitions := [{ origLabels := [2], rel := tRel, rel_next := haltRel }] },
      -- Halt: orig pc 2 is also halt
      { pc_orig := 2, rel := haltRel, transitions := [] } ]
    haltCerts := #[hc 0, hc 0, hc 0, hc 2]
    measure := #[1, 0, 0, 0] }   -- measure decreases at the zero-step

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample10

/-! ### Example 11: Induction variable elimination (variable removed from transformed program)

  Computes `j = 0 + 1 + 2 + … + 99` using a loop counter `rem` counting down
  from 100.  The original program recomputes `k := hundred − rem` (counting up
  from 0) each iteration; the transformed replaces this with an incremental
  `k := k + one`.

  Original (10 instructions):
    0: one := 1;  1: hundred := 100;  2: rem := hundred
    3: k := hundred − rem             ← initial k (= 0); also recomputes each iter
    4: if rem goto 6;  5: halt        ← j observable
    6: j := j + k
    7: rem := rem − one
    8: k := hundred − rem             ← recompute k for next iteration
    9: goto 4

  Transformed (10 instructions):
    0: one := 1;  1: hundred := 100;  2: rem := hundred
    3: k := 0                         ← same initial value, different instruction
    4: if rem goto 6;  5: halt
    6: j := j + k
    7: k := k + one                   ← IVE: increment instead of recompute
    8: rem := rem − one
    9: goto 4

  The expression relation at the loop head maps transformed `k` to original
  expression `hundred − rem`:
    `(hundred − rem, k)` — meaning `k_trans = (hundred − rem).eval(σ_orig)`

  After `rem--` but before `k` is updated, `k` is "stale": the relation shifts
  to `(99 − rem, k)` (i.e., `k = (hundred − rem) − 1` with hundred=100).
  The new reassoc rules verify that `(100 − rem) + 1 = 101 − rem = 100 − (rem − 1)`.

  The original invariant `k = hundred − rem` (at pcs where it holds) lets the
  checker equate orig-side `.var "k"` with `hundred − rem`, matching the
  trans-side relation substitution.
-/
namespace EExample11

-- Loop-head relation: k_trans = (hundred - rem)_orig
private def loopRel : EExprRel :=
  [(.bin .sub (.var "hundred") (.var "rem"), .var "k")]
-- Mid-loop relation (after k++, before rem--): k = 101 - rem
private def midRel : EExprRel :=
  [(.bin .sub (.lit 101) (.var "rem"), .var "k")]

-- Invariants
private def inv_init : EInv := [("one", .lit 1)]
private def inv_setup : EInv := [("one", .lit 1), ("hundred", .lit 100)]
-- At init pc 3 only: rem is known to be 100
private def inv_init_rem : EInv :=
  [("one", .lit 1), ("hundred", .lit 100), ("rem", .lit 100)]
-- Loop invariant: one=1, hundred=100
private def inv_loop : EInv := [("one", .lit 1), ("hundred", .lit 100)]
-- Loop invariant where k = hundred - rem is also known
-- Note: use `.lit 100` not `.var "hundred"` because `simplify` does not
-- recursively resolve variables returned by invariant lookup.
private def inv_loop_k : EInv :=
  [("one", .lit 1), ("hundred", .lit 100),
   ("k", .bin .sub (.lit 100) (.var "rem"))]

def cert : ECertificate :=
  { orig := #[
      .const "one" 1,                 -- 0
      .const "hundred" 100,           -- 1
      .copy "rem" "hundred",          -- 2: rem := 100
      .binop "k" .sub "hundred" "rem",-- 3: k := 100 - rem = 0 (init)
      .ifgoto "rem" 6,                -- 4: loop head
      .halt,                          -- 5
      .binop "j" .add "j" "k",        -- 6: j += k
      .binop "rem" .sub "rem" "one",  -- 7: rem--
      .binop "k" .sub "hundred" "rem",-- 8: k := 100 - rem (recompute)
      .goto 4 ]                        -- 9
    trans := #[
      .const "one" 1,                 -- 0
      .const "hundred" 100,           -- 1
      .copy "rem" "hundred",          -- 2: rem := 100
      .const "k" 0,                   -- 3: k := 0
      .ifgoto "rem" 6,                -- 4: loop head
      .halt,                          -- 5
      .binop "j" .add "j" "k",        -- 6: j += k
      .binop "k" .add "k" "one",     -- 7: k++ (IVE)
      .binop "rem" .sub "rem" "one",  -- 8: rem--
      .goto 4 ]                        -- 9
    inv_orig := #[
      [],                              -- 0
      inv_init,                        -- 1
      inv_setup,                       -- 2
      inv_init_rem,                    -- 3: rem=100 known (init only)
      inv_loop_k,                      -- 4: loop head, k = hundred - rem
      inv_loop_k,                      -- 5: halt
      inv_loop_k,                      -- 6: j := j + k
      inv_loop_k,                      -- 7: rem--, k still valid
      inv_loop,                        -- 8: k stale (rem decremented)
      inv_loop_k ]                     -- 9: k recomputed
    inv_trans := #[
      [],                              -- 0
      inv_init,                        -- 1
      inv_setup,                       -- 2
      inv_setup,                       -- 3
      inv_loop,                        -- 4: loop head
      inv_loop,                        -- 5: halt
      inv_loop,                        -- 6
      inv_loop,                        -- 7
      inv_loop,                        -- 8
      inv_loop ]                       -- 9
    observable := ["j"]
    instrCerts := #[
      -- Init (trans 0–2 same as orig 0–2)
      ic 0 ([tc [1]]),                              -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                              -- trans 1→2 : orig 1→2
      ic 2 ([tc [3]]),                              -- trans 2→3 : orig 2→3
      -- Trans 3 (k:=0): orig 3 (k:=hundred-rem) → 4.  Establishes loopRel.
      { pc_orig := 3, rel := [],
        transitions := [{ origLabels := [4], rel_next := loopRel }] },
      -- Loop head (trans 4, ifgoto): orig 4
      { pc_orig := 4, rel := loopRel,
        transitions := [
          -- Taken → 6: orig 4→6
          { origLabels := [6], rel := loopRel, rel_next := loopRel },
          -- Fallthrough → 5: orig 4→5
          { origLabels := [5], rel := loopRel, rel_next := loopRel }
        ] },
      -- Halt (trans 5, orig 5)
      { pc_orig := 5, rel := loopRel, transitions := [] },
      -- Trans 6 (j:=j+k): orig 6 (j:=j+k) → 7.  Same instruction.
      { pc_orig := 6, rel := loopRel,
        transitions := [{ origLabels := [7], rel := loopRel, rel_next := loopRel }] },
      -- Trans 7 (k:=k+one): zero-step at orig 7.  IVE: advances k proactively.
      -- Pre: loopRel (k = hundred-rem).  Post: midRel (k = 101-rem).
      { pc_orig := 7, rel := loopRel,
        transitions := [{ origLabels := [], rel := loopRel, rel_next := midRel }] },
      -- Trans 8 (rem:=rem-one): orig 7→8→9→4 (rem--, k:=hundred-rem, goto, loop head).
      -- Pre: midRel (k = 101-rem).  Post: loopRel (k = hundred-rem with new rem).
      { pc_orig := 7, rel := midRel,
        transitions := [{ origLabels := [8, 9, 4], rel := midRel, rel_next := loopRel }] },
      -- Trans 9 (goto 4): zero-step at orig 4 (loop head).
      { pc_orig := 4, rel := loopRel,
        transitions := [{ origLabels := [], rel := loopRel, rel_next := loopRel }] }
    ]
    haltCerts := #[hc 0, hc 0, hc 0, hc 0, hc 0, hc 5, hc 0, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0, 0, 2, 1, 1] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end EExample11
