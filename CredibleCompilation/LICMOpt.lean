import CredibleCompilation.CSEOpt

/-!
# Loop-Invariant Code Motion Optimizer

Takes a TAC program and a list of observable variables, identifies redundant
recomputations (instructions that assign a value the variable already holds),
and produces an `ECertificate` that the executable checker can verify.

## What it optimizes

**binop x op y z** where the available-expression analysis already shows that
`x = op(y, z)` at that point (i.e., `x` was previously computed as `op(y, z)`
and none of `x`, `y`, `z` have been modified since) → **goto (pc + 1)**

This is the classic LICM pattern: a pre-loop computation `t := a * b` makes
the same computation inside the loop body redundant, so the loop-body copy
becomes a no-op and is replaced with a simple fall-through goto.

## Invariant strategy

Reuses the CSE available-expression analysis.  The invariant at each PC
contains atoms `(result, expanded_expr)` from the available set.  The key
property: when an instruction is marked redundant, the invariant already
asserts that the result variable holds the computed value, so the checker
can verify the replacement `goto` produces the same store.
-/

namespace LICMOpt

-- ============================================================
-- § 1. Redundancy detection
-- ============================================================

/-- An instruction is redundant if it recomputes a value the target
    variable already holds (per the available-expression analysis).
    Safety: we also require that `x` does not appear as an operand
    in any other available entry, ensuring the kill/re-add cycle
    doesn't change the invariant. -/
def isRedundant (avail : CSEOpt.AvailSet) (instr : TAC) : Bool :=
  match instr with
  | .binop x op y z =>
    match CSEOpt.findAvail avail op y z with
    | some e =>
      e.result == x &&
      avail.all fun e' =>
        e'.result == x || (!(e'.lhs == x) && !(e'.rhs == x))
    | none => false
  | _ => false

-- ============================================================
-- § 2. Transformation
-- ============================================================

/-- Replace redundant instructions with `goto (pc + 1)`. -/
def transformProg (prog : Prog) (avails : Array (Option CSEOpt.AvailSet)) : Prog :=
  let arr := (List.range prog.size).map fun i =>
    match prog[i]?, avails[i]? with
    | some instr, some (some av) =>
      if isRedundant av instr then .goto (i + 1) else instr
    | some instr, _ => instr
    | none, _ => .halt
  { code := arr.toArray, tyCtx := prog.tyCtx, observable := prog.observable }

-- ============================================================
-- § 3. Certificate generation
-- ============================================================

/-- Build invariant arrays from the CSE analysis result.
    Both programs share the same invariants (1:1 PC mapping). -/
def buildInvariants (avails : Array (Option CSEOpt.AvailSet)) : Array EInv :=
  avails.map fun
    | some av => CSEOpt.availToInv av
    | none    => []


-- ============================================================
-- § 4. Main entry point
-- ============================================================

/-- Run LICM on `prog` and produce a certified transformation.
    The result is an `ECertificate` that `checkCertificateExec` will accept. -/
def optimize (prog : Prog) (observable : List Var) : ECertificate :=
  let avails := CSEOpt.analyze prog
  let trans := transformProg prog avails
  let inv := buildInvariants avails
  let instrCerts := _root_.buildInstrCerts1to1 trans
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    tyCtx := fun _ => VarTy.int
    inv_orig := inv
    inv_trans := inv
    observable := observable
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end LICMOpt
