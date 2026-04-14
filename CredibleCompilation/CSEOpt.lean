import CredibleCompilation.ExecChecker

/-!
# Common Subexpression Elimination Optimizer

Takes a TAC program and a list of observable variables, performs forward
available-expression analysis, and produces an `ECertificate` that the
executable checker can verify.

## What it optimizes

**binop x op y z** where the expression `y op z` was already computed into
some variable `w` (and neither `w`, `y`, nor `z` has been reassigned since)
→ **copy x w**

## Invariant strategy

The certificate invariant at each PC contains atoms `(w, expanded_expr)` for
each available expression.  Crucially, `expanded_expr` is **fully expanded**:
operands that are themselves results of available expressions are recursively
substituted so that only base variables remain.  This avoids a mismatch in
`Expr.simplify`, which does one-level lookup for `.var` but recurses into `.bin`.
-/

namespace CSEOpt

-- ============================================================
-- § 1. Available expressions
-- ============================================================

/-- Tag distinguishing integer vs float binary operations for CSE. -/
inductive AvailOp where
  | int   : BinOp → AvailOp
  | float : FloatBinOp → AvailOp
  deriving Repr, BEq

/-- An available expression entry: `result := lhs op rhs`.
    `invExpr` is the fully-expanded form for the certificate invariant. -/
structure AvailEntry where
  op      : AvailOp
  lhs     : Var
  rhs     : Var
  result  : Var
  invExpr : Expr
  deriving Repr

instance : BEq AvailEntry where
  beq a b := a.op == b.op && a.lhs == b.lhs && a.rhs == b.rhs &&
             a.result == b.result && a.invExpr == b.invExpr

abbrev AvailSet := List AvailEntry

/-- Does the expression reference variable `x`? -/
def exprRefsVar (e : Expr) (x : Var) : Bool :=
  match e with
  | .var v     => v == x
  | .bin _ a b => exprRefsVar a x || exprRefsVar b x
  | .fbin _ a b => exprRefsVar a x || exprRefsVar b x
  | .intToFloat a => exprRefsVar a x
  | .floatToInt a => exprRefsVar a x
  | .floatExp a   => exprRefsVar a x
  | .floatSqrt a  => exprRefsVar a x
  | .lit _     => false
  | .blit _    => false
  | .flit _    => false
  | _          => false

/-- Kill all entries that reference variable `x` as operand, result,
    or anywhere in the expanded invariant expression. -/
def killVar (avail : AvailSet) (x : Var) : AvailSet :=
  avail.filter fun e => !(e.lhs == x || e.rhs == x || e.result == x || exprRefsVar e.invExpr x)

/-- Find an available computation of `lhs op rhs`. -/
def findAvail (avail : AvailSet) (op : AvailOp) (lhs rhs : Var) : Option AvailEntry :=
  avail.find? fun e => e.op == op && e.lhs == lhs && e.rhs == rhs

/-- Expand a variable through the available set: if `v` is the result of
    an available expression, return its fully-expanded invariant expression;
    otherwise return `.var v`. -/
def expandVar (avail : AvailSet) (v : Var) : Expr :=
  match avail.find? (fun e => e.result == v) with
  | some e => e.invExpr
  | none   => .var v

/-- Intersection: keep entries present in both sets (all fields equal). -/
def availMerge (a b : AvailSet) : AvailSet :=
  a.filter fun e => b.any (· == e)

/-- Semantic equality (order-independent). -/
def availBeq (a b : AvailSet) : Bool :=
  a.length == b.length && a.all fun e => b.any (· == e)

-- ============================================================
-- § 2. Transfer function
-- ============================================================

/-- Update available expressions after executing one instruction. -/
def transfer (avail : AvailSet) (instr : TAC) : AvailSet :=
  match instr with
  | .const x _ => killVar avail x
  | .copy x _  => killVar avail x
  | .binop x op y z =>
    let avail' := killVar avail x
    -- Only add if x doesn't alias an operand (otherwise the expression
    -- would reference a variable that was just overwritten).
    if x == y || x == z then avail'
    else
      let invExpr := Expr.bin op (expandVar avail' y) (expandVar avail' z)
      { op := .int op, lhs := y, rhs := z, result := x, invExpr } :: avail'
  | .fbinop x fop y z =>
    let avail' := killVar avail x
    if x == y || x == z then avail'
    else
      let invExpr := Expr.fbin fop (expandVar avail' y) (expandVar avail' z)
      { op := .float fop, lhs := y, rhs := z, result := x, invExpr } :: avail'
  | .boolop x _        => killVar avail x
  | .arrLoad x _ _ _   => killVar avail x
  | .intToFloat x _    => killVar avail x
  | .floatToInt x _    => killVar avail x
  | .floatExp x _      => killVar avail x
  | .floatSqrt x _     => killVar avail x
  | _ => avail

-- ============================================================
-- § 3. Forward analysis (worklist)
-- ============================================================

private def propagate (prog : Prog) (avails : Array (Option AvailSet))
    (pc : Nat) : Array (Option AvailSet) × List Nat :=
  match prog[pc]?, avails[pc]? with
  | some instr, some (some av) =>
    let out := transfer av instr
    let succs := successors instr pc
    succs.foldl (fun (arr, wl) pc' =>
      if pc' < arr.size then
        match arr[pc']? with
        | some none | none =>
          (arr.set! pc' (some out), pc' :: wl)
        | some (some old) =>
          let merged := availMerge old out
          if availBeq merged old then (arr, wl)
          else (arr.set! pc' (some merged), pc' :: wl)
      else (arr, wl)
    ) (avails, [])
  | _, _ => (avails, [])

private partial def analyzeLoop (prog : Prog) (avails : Array (Option AvailSet))
    (worklist : List Nat) : Array (Option AvailSet) :=
  match worklist with
  | [] => avails
  | pc :: rest =>
    let (avails', newWork) := propagate prog avails pc
    analyzeLoop prog avails' (rest ++ newWork)

/-- Forward available-expression analysis.
    Returns `Option AvailSet` per PC (`none` = unreachable). -/
def analyze (prog : Prog) : Array (Option AvailSet) :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option AvailSet)).set! 0 (some [])
    analyzeLoop prog init (0 :: [])

-- ============================================================
-- § 4. Transformation
-- ============================================================

/-- Transform a single instruction using available expressions at its PC. -/
def transformInstr (avail : AvailSet) (instr : TAC) : TAC :=
  match instr with
  | .binop x op y z =>
    match findAvail avail (.int op) y z with
    | some e => if x == e.result then instr else .copy x e.result
    | none   => instr
  | .fbinop x fop y z =>
    match findAvail avail (.float fop) y z with
    | some e => if x == e.result then instr else .copy x e.result
    | none   => instr
  | other => other

/-- Transform the entire program. -/
def transformProg (prog : Prog) (avails : Array (Option AvailSet)) : Prog :=
  let arr := (List.range prog.size).map fun i =>
    match prog[i]?, avails[i]? with
    | some instr, some (some av) => transformInstr av instr
    | some instr, _              => instr
    | none, _                    => .halt
  { code := arr.toArray, tyCtx := prog.tyCtx, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Certificate generation
-- ============================================================

/-- Convert an available set to an EInv (invariant). -/
def availToInv (avail : AvailSet) : EInv :=
  avail.map fun e => (e.result, e.invExpr)

/-- Build invariant arrays from the analysis result. -/
def buildInvariants (avails : Array (Option AvailSet)) : Array EInv :=
  avails.map fun
    | some av => availToInv av
    | none    => []


-- ============================================================
-- § 6. Main entry point
-- ============================================================

/-- Run CSE on `prog` and produce a certified transformation.
    The result is an `ECertificate` that `checkCertificateExec` will accept. -/
def optimize (prog : Prog) : ECertificate :=
  let avails := analyze prog
  let trans := transformProg prog avails
  let inv := buildInvariants avails
  let instrCerts := _root_.buildInstrCerts1to1 trans (_root_.collectAllVars prog trans)
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    inv_orig := inv
    inv_trans := inv
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end CSEOpt
