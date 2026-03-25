import CredibleCompilation.ExecChecker

/-!
# Executable Certificate Examples

Each example demonstrates a specific compiler optimization verified by the
executable certificate checker.  The checker returns `true` for correct
transformations and `false` for buggy ones.

## Optimizations covered

1. **Constant propagation** — propagate known constants through copies
2. **Copy propagation** — replace uses of a copied variable with the original
3. **Common subexpression elimination (CSE)** — reuse already-computed values
4. **Dead code elimination** — remove unreachable code after always-taken branches
5. **Loop-invariant code motion (LICM)** — remove redundant loop-invariant
   recomputation from loop bodies
6. **Induction variable elimination (IVE)** — replace recomputation with
   incremental update using reassociation
-/

-- ============================================================
-- Helpers
-- ============================================================

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
-- § 1. Constant propagation (chain)
-- ============================================================

/-! ### Example 1: Constant propagation through a chain of copies

  Original:
    0: x := 7
    1: y := x          — copy (x is 7)
    2: z := y          — copy (y is 7)
    3: halt

  Transformed:
    0: x := 7
    1: y := 7          — propagated
    2: z := 7          — propagated
    3: halt

  Invariants: `x = 7` at labels ≥ 1, `y = 7` at labels ≥ 2.
-/
namespace ConstProp

def cert : ECertificate :=
  { orig  := #[.const "x" 7, .copy "y" "x", .copy "z" "y", .halt]
    trans := #[.const "x" 7, .const "y" 7, .const "z" 7, .halt]
    inv_orig  := #[[], [("x", .lit 7)], [("x", .lit 7), ("y", .lit 7)],
                       [("x", .lit 7), ("y", .lit 7)]]
    inv_trans := #[[], [("x", .lit 7)], [("x", .lit 7), ("y", .lit 7)],
                       [("x", .lit 7), ("y", .lit 7)]]
    observable := ["z"]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                            -- trans 1→2 : orig 1→2
      ic 2 ([tcObs [3] (obsRel ["z"])]),          -- trans 2→3 : orig 2→3
      icObs 3 (obsRel ["z"]) ]                    -- halt
    haltCerts := #[hc 0, hc 0, hc 0, hc 3]
    measure := #[0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end ConstProp

-- ============================================================
-- § 2. Copy propagation
-- ============================================================

/-! ### Example 2: Copy propagation — replace copied variable with original

  Original:
    0: a := b          — copy
    1: c := a + d      — uses a (= b)
    2: halt

  Transformed:
    0: a := b          — same copy
    1: c := b + d      — replaced a with b
    2: halt

  Invariant: `a = b` at labels ≥ 1.
  Under this invariant, `a + d` simplifies to the same value as `b + d`.
-/
namespace CopyProp

def cert : ECertificate :=
  { orig  := #[.copy "a" "b", .binop "c" .add "a" "d", .halt]
    trans := #[.copy "a" "b", .binop "c" .add "b" "d", .halt]
    inv_orig  := #[[], [("a", .var "b")], [("a", .var "b")]]
    inv_trans := #[[], [("a", .var "b")], [("a", .var "b")]]
    observable := ["c"]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tcObs [2] (obsRel ["c"])]),          -- trans 1→2 : orig 1→2
      icObs 2 (obsRel ["c"]) ]                    -- halt
    haltCerts := #[hc 0, hc 0, hc 2]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end CopyProp

-- ============================================================
-- § 3. Common subexpression elimination
-- ============================================================

/-! ### Example 3: CSE — reuse an already-computed expression

  Original:
    0: a := x + y
    1: b := x + y      — same as a
    2: c := a + b
    3: halt

  Transformed:
    0: a := x + y
    1: b := a           — CSE: reuse a
    2: c := a + b
    3: halt

  Invariant: `a = x + y` at labels ≥ 1.
-/
namespace CSE

def cert : ECertificate :=
  { orig  := #[.binop "a" .add "x" "y",
               .binop "b" .add "x" "y",
               .binop "c" .add "a" "b",
               .halt]
    trans := #[.binop "a" .add "x" "y",
               .copy "b" "a",
               .binop "c" .add "a" "b",
               .halt]
    inv_orig  := #[[], [("a", .bin .add (.var "x") (.var "y"))],
                      [("a", .bin .add (.var "x") (.var "y"))],
                      [("a", .bin .add (.var "x") (.var "y"))]]
    inv_trans := #[[], [("a", .bin .add (.var "x") (.var "y"))],
                      [("a", .bin .add (.var "x") (.var "y"))],
                      [("a", .bin .add (.var "x") (.var "y"))]]
    observable := ["c"]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                            -- trans 1→2 : orig 1→2
      ic 2 ([tcObs [3] (obsRel ["c"])]),          -- trans 2→3 : orig 2→3
      icObs 3 (obsRel ["c"]) ]                    -- halt
    haltCerts := #[hc 0, hc 0, hc 0, hc 3]
    measure := #[0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end CSE

-- ============================================================
-- § 4. Bad example (buggy transformation)
-- ============================================================

/-! ### Bad Example: Incorrect constant propagation

  Original:
    0: x := 5
    1: y := x          — y gets 5
    2: halt

  Transformed (BUGGY):
    0: x := 5
    1: y := 3          — WRONG: should be 5
    2: halt

  Observable variable: y.  The checker rejects this because the symbolic
  effects don't match: orig produces y = 5 but trans produces y = 3.
-/
namespace BadExample

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

end BadExample

-- ============================================================
-- § 5. Dead code elimination
-- ============================================================

/-! ### Example 4: Dead code elimination — remove unreachable code

  Original:
    0: x := 1
    1: if x goto 3      — always taken (x = 1 ≠ 0)
    2: halt              — DEAD (unreachable)
    3: y := 5
    4: halt

  Transformed:
    0: x := 1
    1: y := 5            — branch + dead code removed
    2: halt

  Invariant: `x = 1` at labels ≥ 1.
  The checker's symbolic analysis resolves `computeNextPC` for the ifgoto:
  under invariant `x = 1`, the branch is always taken.
  Trans 1→2 maps to orig 1→3→4 (take branch, y := 5, reach halt).
-/
namespace DCE

def cert : ECertificate :=
  { orig  := #[.const "x" 1,            -- 0
               .ifgoto (.var "x") 3,     -- 1: always taken
               .halt,                    -- 2: dead
               .const "y" 5,            -- 3
               .halt]                    -- 4
    trans := #[.const "x" 1,            -- 0
               .const "y" 5,            -- 1: branch + dead code removed
               .halt]                    -- 2
    inv_orig  := #[[], [("x", .lit 1)], [("x", .lit 1)],
                      [("x", .lit 1)], [("x", .lit 1)]]
    inv_trans := #[[], [("x", .lit 1)], [("x", .lit 1)]]
    observable := ["y"]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tcObs [3, 4] (obsRel ["y"])]),       -- trans 1→2 : orig 1→3→4
      icObs 4 (obsRel ["y"]) ]                    -- halt
    haltCerts := #[hc 0, hc 0, hc 4]
    measure := #[0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end DCE

-- ============================================================
-- § 6. Loop-invariant code motion (LICM)
-- ============================================================

/-! ### Example 5: LICM — remove redundant loop-invariant recomputation

  Original (8 instructions):
    0: one := 1
    1: t := a * b                  — initial computation
    2: if n goto 4
    3: halt
    4: s := s + t
    5: t := a * b                  — REDUNDANT: a, b unchanged in loop
    6: n := n - one
    7: goto 2

  Transformed (7 instructions — redundant recomputation removed):
    0: one := 1
    1: t := a * b
    2: if n goto 4
    3: halt
    4: s := s + t
    5: n := n - one
    6: goto 2

  Invariant: `t = a * b` throughout both programs (since a, b are never
  modified).  Trans 4→5 maps to orig 4→5→6 — the redundant `t := a * b`
  at orig 5 is a no-op under the invariant, so both paths produce the
  same effect.
-/
namespace LICM

private def inv_loop : EInv :=
  [("one", .lit 1), ("t", .bin .mul (.var "a") (.var "b"))]

def cert : ECertificate :=
  { orig := #[
      .const "one" 1,              -- 0
      .binop "t" .mul "a" "b",    -- 1: t := a * b
      .ifgoto (.var "n") 4,       -- 2: loop head
      .halt,                       -- 3
      .binop "s" .add "s" "t",    -- 4: loop body
      .binop "t" .mul "a" "b",    -- 5: redundant recomputation
      .binop "n" .sub "n" "one",  -- 6: n--
      .goto 2 ]                    -- 7
    trans := #[
      .const "one" 1,              -- 0
      .binop "t" .mul "a" "b",    -- 1: t := a * b
      .ifgoto (.var "n") 4,       -- 2: loop head
      .halt,                       -- 3
      .binop "s" .add "s" "t",    -- 4: loop body
      .binop "n" .sub "n" "one",  -- 5: n--  (redundant t:=a*b removed)
      .goto 2 ]                    -- 6
    inv_orig := #[
      [],                          -- 0
      [("one", .lit 1)],          -- 1
      inv_loop,                    -- 2
      inv_loop,                    -- 3
      inv_loop,                    -- 4
      inv_loop,                    -- 5
      inv_loop,                    -- 6
      inv_loop ]                   -- 7
    inv_trans := #[
      [],                          -- 0
      [("one", .lit 1)],          -- 1
      inv_loop,                    -- 2
      inv_loop,                    -- 3
      inv_loop,                    -- 4
      inv_loop,                    -- 5
      inv_loop ]                   -- 6
    observable := ["s"]
    instrCerts := #[
      ic 0 ([tc [1]]),                                    -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                                    -- trans 1→2 : orig 1→2
      ic 2 ([tc [4], tcObs [3] (obsRel ["s"])]),          -- trans 2→4/3 : orig 2→4/3
      icObs 3 (obsRel ["s"]),                             -- halt
      ic 4 ([tc [5, 6]]),                                 -- trans 4→5 : orig 4→5→6 (skip redundant t:=a*b)
      ic 6 ([tc [7]]),                                    -- trans 5→6 : orig 6→7
      ic 7 ([tc [2]]) ]                                   -- trans 6→2 : orig 7→2
    haltCerts := #[hc 0, hc 0, hc 0, hc 3, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0, 0] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end LICM

-- ============================================================
-- § 7. Induction variable elimination (IVE)
-- ============================================================

/-! ### Example 6: IVE — replace recomputation with incremental update

  Original (7 instructions):
    0: one := 1
    1: k := 100
    2: rem := k - i             — loop head: recompute rem = 100 - i
    3: if rem goto 5
    4: halt
    5: i := i + one
    6: goto 2

  Transformed (8 instructions):
    0: one := 1
    1: k := 100
    2: rem := k - i             — initial computation (same)
    3: if rem goto 5
    4: halt
    5: i := i + one
    6: rem := rem - one         — IVE: decrement instead of recompute
    7: goto 3                   — skip recomputation, jump to loop head

  After `i := i + one` (pc 5), the invariant `rem = 100 - i` becomes
  stale: `rem = 101 - i` (using the new `i`).  The IVE step
  `rem := rem - one` restores it: `(101 - i) - 1` simplifies to
  `100 - i` via the reassociation rule `(lit - var) - lit → (lit-lit) - var`.

  Trans 6→7 maps to orig 6→2→3 (goto, recompute rem, loop head).
  Trans 7→3 is a zero-step (orig already at the loop head) with a
  decreasing measure.
-/
namespace IVE

private def inv_1k : EInv := [("one", .lit 1), ("k", .lit 100)]
private def inv_loop : EInv :=
  [("one", .lit 1), ("k", .lit 100),
   ("rem", .bin .sub (.lit 100) (.var "i"))]
private def inv_post_inc : EInv :=
  [("one", .lit 1), ("k", .lit 100),
   ("rem", .bin .sub (.lit 101) (.var "i"))]

def cert : ECertificate :=
  { orig := #[
      .const "one" 1,              -- 0
      .const "k" 100,              -- 1
      .binop "rem" .sub "k" "i",  -- 2: loop head — recompute rem
      .ifgoto (.var "rem") 5,      -- 3
      .halt,                       -- 4
      .binop "i" .add "i" "one",  -- 5: i++
      .goto 2 ]                    -- 6: back to recomputation
    trans := #[
      .const "one" 1,              -- 0
      .const "k" 100,              -- 1
      .binop "rem" .sub "k" "i",  -- 2: initial rem (same)
      .ifgoto (.var "rem") 5,      -- 3: loop head
      .halt,                       -- 4
      .binop "i" .add "i" "one",  -- 5: i++
      .binop "rem" .sub "rem" "one", -- 6: IVE — countdown
      .goto 3 ]                    -- 7: skip recomputation
    inv_orig := #[
      [],                          -- 0
      [("one", .lit 1)],          -- 1
      inv_1k,                      -- 2: before rem computed
      inv_loop,                    -- 3: rem = 100 - i
      inv_loop,                    -- 4
      inv_loop,                    -- 5
      inv_post_inc ]               -- 6: after i++, rem = 101 - i
    inv_trans := #[
      [],                          -- 0
      [("one", .lit 1)],          -- 1
      inv_1k,                      -- 2
      inv_loop,                    -- 3: rem = 100 - i
      inv_loop,                    -- 4
      inv_loop,                    -- 5
      inv_post_inc,                -- 6: after i++, rem = 101 - i
      inv_loop ]                   -- 7: after rem--, rem = 100 - i
    observable := ["i"]
    instrCerts := #[
      ic 0 ([tc [1]]),                            -- trans 0→1 : orig 0→1
      ic 1 ([tc [2]]),                            -- trans 1→2 : orig 1→2
      ic 2 ([tc [3]]),                            -- trans 2→3 : orig 2→3
      ic 3 ([tc [5], tcObs [4] (obsRel ["i"])]),  -- trans 3→5 or 3→4
      icObs 4 (obsRel ["i"]),                     -- halt
      ic 5 ([tc [6]]),                            -- trans 5→6 : orig 5→6
      ic 6 ([tc [2, 3]]),                         -- trans 6→7 : orig 6→2→3 (the IVE step!)
      ic 3 ([tc []]) ]                            -- trans 7→3 : orig 3→3 (zero-step)
    haltCerts := #[hc 0, hc 0, hc 0, hc 0, hc 4, hc 0, hc 0, hc 0]
    measure := #[0, 0, 0, 0, 0, 0, 0, 1] }

#eval! checkCertificateExec cert              -- true
#eval! checkCertificateVerboseExec cert

end IVE
