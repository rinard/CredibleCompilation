import CredibleCompilation.PropChecker
import Std.Data.HashMap

/-!
# Executable Certificate Checker

An executable certificate checker that returns `Bool`.
Use `#eval! checkCertificateExec cert` or run `lake exe checker` from the terminal.

The checker uses **symbolic execution** and **expression simplification** to verify
that the transformed program's behavior matches the original. Invariants are
represented as lists of `(var, expr)` atoms. An explicit **expression relation**
(per transformed PC) relates expressions over original variables to expressions
over transformed variables via pairs `(e_orig, e_trans)` asserting equality.
-/

-- ============================================================
-- § 1. Executable invariants and helpers
-- ============================================================

/-- Executable invariant: conjunction of `var = expr` atoms.
    Each `(x, e)` asserts `σ x = e.eval σ` at runtime. -/
abbrev EInv := List (Var × Expr)

/-- Executable expression relation: pairs of expressions asserting equality
    across stores.  Each `(e_o, e_t)` asserts `e_o.eval(σ_orig) = e_t.eval(σ_trans)`.
    Generalizes the old variable map: `(v, e)` in the old map becomes `(e, .var v)`. -/
abbrev EExprRel := List (Expr × Expr)

def lookupExpr (inv : EInv) (v : Var) : Option Expr :=
  (inv.find? (fun p => p.1 == v)).map (·.2)

-- ============================================================
-- § 2. Symbolic expression simplification
-- ============================================================

/-- Reassociate sub-expressions involving literals after simplification.
    Normalizes patterns like `(n - x) - m → (n - m) - x` and
    `n - (x + m) → (n - m) - x` so that the checker can verify
    induction variable elimination (countdown vs recomputation).
    Also normalizes `(n - x) + m → (n + m) - x` and `n - (x - m) → (n + m) - x`
    for additive induction variable elimination. -/
def Expr.reassoc : BinOp → Expr → Expr → Expr
  | .add, .bin .sub (.lit na) x, .lit nb => .bin .sub (.lit (na + nb)) x
  | .sub, .bin .sub (.lit na) x, .lit nb => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .add x (.lit nb) => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .add (.lit nb) x => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .sub x (.lit nb) => .bin .sub (.lit (na + nb)) x
  | op, a, b => .bin op a b

/-- Simplify an `Expr` by substituting known variable expressions and constant-folding.
    After folding, applies `reassoc` to normalize sub/add patterns involving literals. -/
def Expr.simplify (inv : EInv) : Expr → Expr
  | .lit n => .lit n
  | .blit b => .blit b
  | .var v => match lookupExpr inv v with
    | some e => e
    | none   => .var v
  | .bin op a b =>
    match a.simplify inv, b.simplify inv with
    | .lit na, .lit nb => .lit (op.eval na nb)
    | a', b'           => Expr.reassoc op a' b'
  | .tobool e       => .tobool e
  | .cmpE op a b    => .cmpE op a b
  | .cmpLitE op a n => .cmpLitE op a n
  | .notE e         => .notE e
  | .andE a b       => .andE a b
  | .orE a b        => .orE a b
  | .arrRead arr idx => .arrRead arr (idx.simplify inv)
  | .flit n         => .flit n
  | .fbin op a b    =>
    let a' := a.simplify inv; let b' := b.simplify inv
    match op, a' with
    | .fadd, .fbin .fmul _ _ => .fbin .fadd b' a'  -- normalize: fmul on right
    | _, _ => .fbin op a' b'
  | .fcmpE op a b   => .fcmpE op (a.simplify inv) (b.simplify inv)
  | .intToFloat e   => .intToFloat (e.simplify inv)
  | .floatToInt e   => .floatToInt (e.simplify inv)
  | .floatUnary op e => .floatUnary op (e.simplify inv)
  | .ftern op a b c => match op with
    | .fmadd => .fbin .fadd (a.simplify inv) (.fbin .fmul (b.simplify inv) (c.simplify inv))
    | .fmsub => .fbin .fsub (a.simplify inv) (.fbin .fmul (b.simplify inv) (c.simplify inv))
  | .farrRead arr idx => .farrRead arr (idx.simplify inv)

-- ============================================================
-- § 3. Symbolic execution
-- ============================================================

/-- Symbolic store: maps modified variables to expressions over initial variables.
    Unmapped variables are implicitly `.var v` (identity). -/
abbrev SymStore := List (Var × Expr)

def ssGet (ss : SymStore) (v : Var) : Expr :=
  match ss.find? (fun p => p.1 == v) with
  | some (_, e) => e
  | none        => .var v

def ssSet (ss : SymStore) (x : Var) (e : Expr) : SymStore :=
  (x, e) :: ss.filter (fun p => !(p.1 == x))

/-- Convert a BoolExpr to a symbolic Expr by replacing each variable reference
    with its symbolic expression from the store. -/
def BoolExpr.toSymExpr (ss : SymStore) : BoolExpr → Expr
  | .lit b         => .blit b
  | .bvar x        => .tobool (ssGet ss x)
  | .cmp op x y    => .cmpE op (ssGet ss x) (ssGet ss y)
  | .cmpLit op x n => .cmpLitE op (ssGet ss x) n
  | .not e         => .notE (e.toSymExpr ss)
  | .fcmp op x y      => .fcmpE op (ssGet ss x) (ssGet ss y)
  | .fcmpLit op x n   => .fcmpE op (ssGet ss x) (.flit n)

/-- Symbolic array memory: tracks array writes as a list of (array, index, value) triples.
    Most recent writes are at the head. -/
abbrev SymArrayMem := List (ArrayName × Expr × Expr)

/-- Look up an array read in the symbolic array memory.
    Returns the written value if the array and index match, otherwise `.arrRead`. -/
def samGet (sam : SymArrayMem) (arr : ArrayName) (idx : Expr) (ty : VarTy := .int) : Expr :=
  match sam.find? (fun (a, i, _) => a == arr && i == idx) with
  | some (_, _, v) => v
  | none => match ty with
    | .int   => .arrRead arr idx
    | .float => .farrRead arr idx
    | .bool  => .cmpLitE .ne (.arrRead arr idx) 0

/-- Symbolically execute one TAC instruction.
    Expressions in the resulting store reference the *initial* variable values.
    Returns updated (SymStore, SymArrayMem). -/
def execSymbolic (ss : SymStore) (sam : SymArrayMem) (instr : TAC) : SymStore × SymArrayMem :=
  match instr with
  | .const x (.int n)  => (ssSet ss x (.lit n), sam)
  | .const x (.bool b) => (ssSet ss x (.blit b), sam)
  | .const x (.float f) => (ssSet ss x (.flit f), sam)
  | .boolop x be    => (ssSet ss x (be.toSymExpr ss), sam)
  | .copy x y       => (ssSet ss x (ssGet ss y), sam)
  | .binop x op y z => (ssSet ss x (.bin op (ssGet ss y) (ssGet ss z)), sam)
  | .fbinop x op y z => (ssSet ss x (.fbin op (ssGet ss y) (ssGet ss z)), sam)
  | .intToFloat x y => (ssSet ss x (.intToFloat (ssGet ss y)), sam)
  | .floatToInt x y => (ssSet ss x (.floatToInt (ssGet ss y)), sam)
  | .floatUnary x op y => (ssSet ss x (.floatUnary op (ssGet ss y)), sam)
  | .fternop x op a b c => (ssSet ss x (.ftern op (ssGet ss a) (ssGet ss b) (ssGet ss c)), sam)
  | .arrLoad x arr idx ty => (ssSet ss x (samGet sam arr (ssGet ss idx) ty), sam)
  | .arrStore arr idx val _ => (ss, (arr, ssGet ss idx, ssGet ss val) :: sam)
  | _               => (ss, sam)

/-- Symbolically execute along a path of labels in the original program.
    At each label, look up the instruction and execute it symbolically. -/
def execPath (orig : Prog) (ss : SymStore) (sam : SymArrayMem) (pc : Label) :
    List Label → SymStore × SymArrayMem
  | []             => (ss, sam)
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      let (ss', sam') := execSymbolic ss sam instr
      execPath orig ss' sam' nextPC rest
    | none       => (ss, sam)

-- ============================================================
-- § 4. Instruction helpers
-- ============================================================

def successors (instr : TAC) (pc : Label) : List Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _ => [pc + 1]
  | .fbinop _ _ _ _ | .intToFloat _ _ | .floatToInt _ _ | .floatUnary _ _ _ | .fternop _ _ _ _ _ => [pc + 1]
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _ => [pc + 1]
  | .printInt _ | .printFloat _ => [pc + 1]
  | .goto l        => [l]
  | .ifgoto _ l    => [l, pc + 1]
  | .halt          => []

def canReach (instr : TAC) (pc next : Label) : Bool :=
  (successors instr pc).contains next

/-- Check whether an expression is a non-zero literal. -/
def Expr.isNonZeroLit : Expr → Bool
  | .lit 0 => false
  | .lit _ => true
  | .blit true => true
  | .blit false | .var _ | .bin _ _ _ => false
  | .tobool _ | .cmpE _ _ _ | .cmpLitE _ _ _ | .notE _ | .andE _ _ | .orE _ _ | .arrRead _ _ => false
  | .flit _ | .fbin _ _ _ | .fcmpE _ _ _ | .intToFloat _ | .floatToInt _ | .floatUnary _ _ | .ftern _ _ _ _ | .farrRead _ _ => false

/-- Normalize a BoolExpr under a symbolic store and invariant: replace variables
    with known literal values and canonicalize `cmp` to `cmpLit` when possible. -/
def BoolExpr.normalize (ss : SymStore) (inv : EInv) : BoolExpr → BoolExpr
  | .lit b => .lit b
  | .bvar x =>
    match (ssGet ss x).simplify inv with
    | .blit b => .lit b
    | _ => .bvar x
  | .cmp op x y =>
    match (ssGet ss x).simplify inv, (ssGet ss y).simplify inv with
    | .lit a, .lit b => .lit (op.eval a b)
    | _, .lit n => .cmpLit op x n
    | .lit n, _ => match op with  -- left-literal: flip comparison
      | .eq => .cmpLit .eq y n       -- n == y ↔ y == n
      | .ne => .cmpLit .ne y n       -- n != y ↔ y != n
      | .lt => .not (.cmpLit .le y n) -- n < y ↔ ¬(y ≤ n)
      | .le => .not (.cmpLit .lt y n) -- n ≤ y ↔ ¬(y < n)
    | _, _ => .cmp op x y
  | .cmpLit op x n =>
    match (ssGet ss x).simplify inv with
    | .lit a => .lit (op.eval a n)
    | _ => .cmpLit op x n
  | .not e => match e.normalize ss inv with
    | .lit b => .lit (!b)
    | .not inner => inner  -- double negation elimination
    | e' => .not e'
  | .fcmp op x y =>
    match (ssGet ss x).simplify inv, (ssGet ss y).simplify inv with
    | .flit a, .flit b => .lit (FloatCmpOp.eval op a b)
    | _, .flit n => .fcmpLit op x n
    | _, _ => .fcmp op x y
  | .fcmpLit op x n =>
    match (ssGet ss x).simplify inv with
    | .flit a => .lit (FloatCmpOp.eval op a n)
    | _ => .fcmpLit op x n

/-- Symbolically evaluate a BoolExpr under a symbolic store and invariant.
    Returns `some true`/`some false` if the result can be determined, `none` otherwise. -/
def BoolExpr.symEval (ss : SymStore) (inv : EInv) : BoolExpr → Option Bool
  | .lit b => some b
  | .bvar x =>
    match (ssGet ss x).simplify inv with
    | .blit b => some b
    | _ => none
  | .cmp op x y =>
    match (ssGet ss x).simplify inv, (ssGet ss y).simplify inv with
    | .lit a, .lit b => some (op.eval a b)
    | _, _ => none
  | .cmpLit op x n =>
    match (ssGet ss x).simplify inv with
    | .lit a => some (op.eval a n)
    | _ => none
  | .not e => e.symEval ss inv |>.map (!·)
  | .fcmp _op _x _y => none  -- FloatCmpOp.eval is opaque; fall back to branchInfo
  | .fcmpLit _op _x _n => none  -- same

/-- Like `canReach`, but for `ifgoto` also verifies the branch direction
    via symbolic evaluation of the boolean condition under the invariant.
    Non-ifgoto instructions fall back to plain `canReach`. -/
def canReachSym (ss : SymStore) (inv : EInv) (instr : TAC) (pc next : Label) : Bool :=
  match instr with
  | .ifgoto b l =>
    match b.symEval ss inv with
    | some true  => next == l
    | some false => next == pc + 1
    | none       => canReach instr pc next
  | _ => canReach instr pc next

/-- Collect all variable names from both programs. -/
def collectAllVars (p1 p2 : Prog) : List Var :=
  let extract (instr : TAC) : List Var :=
    match instr with
    | .const x _     => [x]
    | .copy x y      => [x, y]
    | .binop x _ y z => [x, y, z]
    | .boolop x _    => [x]
    | .fbinop x _ y z => [x, y, z]
    | .intToFloat x y => [x, y]
    | .floatToInt x y => [x, y]
    | .floatUnary x _ y => [x, y]
    | .fternop x _ a b c => [x, a, b, c]
    | .arrLoad x _ idx _ => [x, idx]
    | .arrStore _ idx val _ => [idx, val]
    | .printInt v    => [v]
    | .printFloat v  => [v]
    | .ifgoto b _    => b.vars
    | _              => []
  let go (code : Array TAC) := code.toList.foldl (fun acc i => acc ++ extract i) ([] : List Var)
  go p1.code ++ go p2.code

-- ============================================================
-- § 5. Executable certificate types
-- ============================================================

/-- A single transition correspondence with labels of the original path. -/
structure ETransCorr where
  /-- Labels of original PCs visited (successors of pc_orig, ending at pc_orig'). -/
  origLabels : List Label
  /-- Expression relation at the source of this transition (should equal the
      enclosing `EInstrCert.rel`). -/
  rel        : EExprRel := []
  /-- Expression relation at the target of this transition (should equal
      the successor `EInstrCert.rel`). -/
  rel_next   : EExprRel := []
  deriving Repr, Inhabited

/-- Per-instruction certificate entry. -/
structure EInstrCert where
  pc_orig     : Label
  /-- Expression relation at this label: pairs `(e_o, e_t)` asserting
      `e_o.eval(σ_orig) = e_t.eval(σ_trans)`.  Empty list = no constraints. -/
  rel         : EExprRel := []
  transitions : List ETransCorr
  deriving Repr, Inhabited

/-- Per-halt certificate entry. -/
structure EHaltCert where
  pc_orig : Label
  /-- Expression relation at this halt label. -/
  rel     : EExprRel := []
  deriving Repr, Inhabited

/-- Shorthand: ETransCorr with empty (no constraints) relation. -/
abbrev ETransCorr.id (labels : List Label) : ETransCorr := { origLabels := labels }

/-- Shorthand: EInstrCert with empty relation. -/
abbrev EInstrCert.id (pc : Label) (trans : List ETransCorr) : EInstrCert :=
  { pc_orig := pc, transitions := trans }

/-- Shorthand: EHaltCert with empty relation. -/
abbrev EHaltCert.id (pc : Label) : EHaltCert := { pc_orig := pc }

/-- Look up the original-side expression for a transformed variable in a relation.
    Searches for a pair `(e_o, .var v)` and returns `e_o`.
    Defaults to `.var v` (identity) if not found. -/
def relGetOrigExpr (rel : EExprRel) (v : Var) : Expr :=
  match rel.find? (fun p => p.2 == .var v) with
  | some (e_o, _) => e_o
  | none => .var v

/-- Find the original variable name for a transformed variable in the relation.
    Returns `some v'` if there is a pair `(.var v', .var v)` in `rel`. -/
def relFindOrigVar (rel : EExprRel) (v : Var) : Option Var :=
  match rel.find? (fun p => p.2 == .var v) with
  | some (.var v', _) => some v'
  | _ => none

/-- Find the original-side expression for a transformed variable.
    For `(.var v', .var x)` returns `.var v'`; for `(lit c, .var x)` returns `lit c`. -/
def relFindOrigExpr (rel : EExprRel) (v : Var) : Option Expr :=
  match rel.find? (fun p => p.2 == .var v) with
  | some (e_o, _) => some e_o
  | _ => none

/-- Map variables in a BoolExpr through the expression relation.
    Resolves each variable to its original-side expression. For `(.var v', .var x)`
    maps to the original variable. For `(lit c, .var x)` (e.g., hoisted constants)
    folds the constant into the condition as `.cmpLit`. When the literal is on the
    left of a comparison (`lit n cmp var y`), flips the comparison using
    `.not (.cmpLit ...)` for lt/le (since we lack gt/ge operators). -/
def BoolExpr.mapVarsRel (rel : EExprRel) : BoolExpr → Option BoolExpr
  | .lit b => some (.lit b)
  | .bvar x => do
    let e ← relFindOrigExpr rel x
    match e with | .var v => return .bvar v | _ => none
  | .cmp op x y => do
    let ex ← relFindOrigExpr rel x
    let ey ← relFindOrigExpr rel y
    match ex, ey with
    | .var x', .var y' => return .cmp op x' y'
    | .var x', .lit n  => return .cmpLit op x' n
    | .lit n, .var y'  => match op with  -- hoisted constant on left: flip comparison
      | .eq => return .cmpLit .eq y' n       -- n == y ↔ y == n
      | .ne => return .cmpLit .ne y' n       -- n != y ↔ y != n
      | .lt => return .not (.cmpLit .le y' n) -- n < y ↔ ¬(y ≤ n)
      | .le => return .not (.cmpLit .lt y' n) -- n ≤ y ↔ ¬(y < n)
    | _, _ => none
  | .cmpLit op x n => do
    let e ← relFindOrigExpr rel x
    match e with | .var v => return .cmpLit op v n | _ => none
  | .not e => e.mapVarsRel rel |>.map fun
    | .not inner => inner  -- double negation elimination: ¬¬p = p
    | e' => .not e'
  | .fcmp op x y => do
    let ex ← relFindOrigExpr rel x
    let ey ← relFindOrigExpr rel y
    match ex, ey with
    | .var x', .var y'   => return .fcmp op x' y'
    | .var x', .flit n   => return .fcmpLit op x' n
    | _, _ => none  -- left-flit would need a flip, but FloatCmpOp.eval is opaque
  | .fcmpLit op x n => do
    let e ← relFindOrigExpr rel x
    match e with | .var v => return .fcmpLit op v n | _ => none

/-- Build a substitution map from pre-relation pairs of the form `(e_o, .var v)`.
    Maps transformed variable `v` to original expression `e_o`. -/
def buildSubstMap (rel : EExprRel) : SymStore :=
  rel.filterMap fun (e_o, e_t) =>
    match e_t with
    | .var v => some (v, e_o)
    | _ => none

/-- An executable certificate: all data needed to verify the transformation.
    The type context and observable variables are derived from the original program. -/
structure ECertificate where
  orig       : Prog
  trans      : Prog
  inv_orig   : Array EInv
  inv_trans  : Array EInv
  instrCerts : Array EInstrCert
  haltCerts  : Array EHaltCert
  /-- Well-founded measure for non-termination (per transformed label). -/
  measure    : Array Nat

instance : Inhabited ECertificate where
  default := { orig := ⟨#[], fun _ => .int, [], []⟩, trans := ⟨#[], fun _ => .int, [], []⟩,
               inv_orig := #[], inv_trans := #[], instrCerts := #[], haltCerts := #[], measure := #[] }

/-- The type context for the certificate, derived from the original program. -/
abbrev ECertificate.tyCtx (cert : ECertificate) : TyCtx := cert.orig.tyCtx

/-- The observable variables for the certificate, derived from the original program. -/
abbrev ECertificate.observable (cert : ECertificate) : List Var := cert.orig.observable

-- ============================================================
-- § 5b. Shared certificate-building utilities
-- ============================================================

/-- Build instrCerts for a 1:1 PC mapping (orig PC = trans PC).
    Used by optimizers that preserve program size (ConstProp, CSE, LICM).
    Identity pairs `(.var v, .var v)` are included for all variables in `allVars`
    so that the membership-based store relation covers all program variables. -/
def buildInstrCerts1to1 (trans : Prog) (allVars : List Var) : Array EInstrCert :=
  let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
  let arr := (List.range trans.size).map fun i =>
    match trans[i]? with
    | some .halt => { pc_orig := i, transitions := ([] : List ETransCorr), rel := idRel }
    | some (.const _ _) | some (.copy _ _) | some (.binop _ _ _ _) | some (.boolop _ _)
    | some (.fbinop _ _ _ _) | some (.intToFloat _ _) | some (.floatToInt _ _) | some (.floatUnary _ _ _)
    | some (.fternop _ _ _ _ _)
    | some (.arrLoad _ _ _ _) | some (.arrStore _ _ _ _)
    | some (.printInt _) | some (.printFloat _) =>
      { pc_orig := i, rel := idRel,
        transitions := [{ origLabels := [i + 1], rel := idRel, rel_next := idRel }] }
    | some (.goto l) =>
      { pc_orig := i, rel := idRel,
        transitions := [{ origLabels := [l], rel := idRel, rel_next := idRel }] }
    | some (.ifgoto _ l) =>
      { pc_orig := i, rel := idRel,
        transitions := [{ origLabels := [l], rel := idRel, rel_next := idRel },
                        { origLabels := [i + 1], rel := idRel, rel_next := idRel }] }
    | none => default
  arr.toArray

/-- Build haltCerts from instrCerts.  Shared by all optimizers.
    Inherits the `rel` from instrCerts so observable variable checks can use identity pairs. -/
def buildHaltCerts (instrCerts : Array EInstrCert) (trans : Prog)
    : Array EHaltCert :=
  let arr := (List.range trans.size).map fun i =>
    let ic := instrCerts.getD i default
    { pc_orig := ic.pc_orig, rel := ic.rel : EHaltCert }
  arr.toArray

/-- Sorted list of kept orig PCs, indexed by trans PC.
    `kept[i] = true` means orig PC `i` is retained.
    Used by compacting optimizers (DCE, Peephole). -/
def buildOrigMap (kept : Array Bool) : Array Nat :=
  ((List.range kept.size).filterMap fun i =>
    if kept.getD i false then some i else none).toArray

/-- Reverse mapping: orig PC → trans PC (0 for removed PCs).
    Used by compacting optimizers (DCE, Peephole). -/
def buildRevMap (origMap : Array Nat) (origSize : Nat) : Array Nat :=
  (List.range origMap.size).foldl (fun arr i =>
    match origMap[i]? with
    | some pc => if pc < arr.size then arr.set! pc i else arr
    | none => arr
  ) (Array.replicate origSize 0)

-- ============================================================
-- § 6. Individual check functions
-- ============================================================

/-- **Condition 1**: Start labels correspond, initial variable map is identity. -/
def checkStartCorrespondenceExec (cert : ECertificate) : Bool :=
  match cert.instrCerts[0]? with
  | some ic => ic.pc_orig == 0
  | none    => false

/-- **Condition 2a**: Invariants are trivially true at label 0. -/
def checkInvariantsAtStartExec (cert : ECertificate) : Bool :=
  (cert.inv_orig.getD 0 ([] : EInv)).isEmpty &&
  (cert.inv_trans.getD 0 ([] : EInv)).isEmpty

/-- **Condition 2c**: Expression relation at label 0 consists only of identity pairs
    (both programs start from the same initial state). -/
def checkRelAtStartExec (cert : ECertificate) : Bool :=
  (cert.instrCerts.getD 0 default).rel.all fun (e_o, e_t) => e_o == e_t

-- ============================================================
-- § 2d. Fast HashMap-based lookups for checker performance
-- ============================================================

abbrev FastVarMap := Std.HashMap String Expr

def FastVarMap.ofList (ss : List (Var × Expr)) : FastVarMap :=
  ss.reverse.foldl (fun m (v, e) => m.insert v e) {}

def Expr.substSymFast (m : FastVarMap) : Expr → Expr
  | .lit n      => .lit n
  | .blit b     => .blit b
  | .var v      => m.getD v (.var v)
  | .bin op a b => .bin op (a.substSymFast m) (b.substSymFast m)
  | .tobool e       => .tobool (e.substSymFast m)
  | .cmpE op a b    => .cmpE op (a.substSymFast m) (b.substSymFast m)
  | .cmpLitE op a n => .cmpLitE op (a.substSymFast m) n
  | .notE e         => .notE (e.substSymFast m)
  | .andE a b       => .andE (a.substSymFast m) (b.substSymFast m)
  | .orE a b        => .orE (a.substSymFast m) (b.substSymFast m)
  | .arrRead arr idx => .arrRead arr (idx.substSymFast m)
  | .flit n          => .flit n
  | .fbin op a b     => .fbin op (a.substSymFast m) (b.substSymFast m)
  | .fcmpE op a b    => .fcmpE op (a.substSymFast m) (b.substSymFast m)
  | .intToFloat e    => .intToFloat (e.substSymFast m)
  | .floatToInt e    => .floatToInt (e.substSymFast m)
  | .floatUnary op e  => .floatUnary op (e.substSymFast m)
  | .ftern op a b c   => .ftern op (a.substSymFast m) (b.substSymFast m) (c.substSymFast m)
  | .farrRead arr idx => .farrRead arr (idx.substSymFast m)

def Expr.simplifyFast (m : FastVarMap) : Expr → Expr
  | .lit n => .lit n
  | .blit b => .blit b
  | .var v => m.getD v (.var v)
  | .bin op a b =>
    match a.simplifyFast m, b.simplifyFast m with
    | .lit na, .lit nb => .lit (op.eval na nb)
    | a', b'           => Expr.reassoc op a' b'
  | .tobool e       => .tobool e
  | .cmpE op a b    => .cmpE op a b
  | .cmpLitE op a n => .cmpLitE op a n
  | .notE e         => .notE e
  | .andE a b       => .andE a b
  | .orE a b        => .orE a b
  | .arrRead arr idx => .arrRead arr (idx.simplifyFast m)
  | .flit n         => .flit n
  | .fbin op a b    =>
    let a' := a.simplifyFast m; let b' := b.simplifyFast m
    match op, a' with
    | .fadd, .fbin .fmul _ _ => .fbin .fadd b' a'  -- normalize: fmul on right
    | _, _ => .fbin op a' b'
  | .fcmpE op a b   => .fcmpE op (a.simplifyFast m) (b.simplifyFast m)
  | .intToFloat e   => .intToFloat (e.simplifyFast m)
  | .floatToInt e   => .floatToInt (e.simplifyFast m)
  | .floatUnary op e => .floatUnary op (e.simplifyFast m)
  | .ftern op a b c => match op with
    | .fmadd => .fbin .fadd (a.simplifyFast m) (.fbin .fmul (b.simplifyFast m) (c.simplifyFast m))
    | .fmsub => .fbin .fsub (a.simplifyFast m) (.fbin .fmul (b.simplifyFast m) (c.simplifyFast m))
  | .farrRead arr idx => .farrRead arr (idx.simplifyFast m)

-- ============================================================
-- § 4a. FastVarMap ↔ list-based lookup equivalence
-- ============================================================

/-- Core lemma: `foldl insert` with last-wins semantics relates to `find?` on the
    reversed list (which finds the last matching entry, i.e. same as foldl's winner). -/
private theorem foldl_insert_getD
    (l : List (Var × Expr)) (m : FastVarMap) (v : Var) (d : Expr) :
    (l.foldl (fun m (p : Var × Expr) => m.insert p.1 p.2) m).getD v d =
    match l.reverse.find? (fun p => p.1 == v) with
    | some (_, e) => e
    | none => m.getD v d := by
  induction l generalizing m with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl]; rw [ih]
    simp only [List.reverse_cons, List.find?_append]
    cases hfind : rest.reverse.find? (fun p => p.1 == v) with
    | some val => simp [Option.or]
    | none =>
      simp only [Option.or, List.find?_cons, List.find?_nil, Std.HashMap.getD_insert]
      cases hbeq : (p.1 == v) <;> simp

/-- `FastVarMap.ofList` lookup agrees with `List.find?` (first-match semantics). -/
theorem FastVarMap.ofList_getD (ss : List (Var × Expr)) (v : Var) (d : Expr) :
    (FastVarMap.ofList ss).getD v d =
    match ss.find? (fun p => p.1 == v) with
    | some (_, e) => e
    | none => d := by
  unfold FastVarMap.ofList
  rw [foldl_insert_getD]
  simp only [Std.HashMap.getD_empty, List.reverse_reverse]

/-- `FastVarMap.ofList` lookup agrees with `ssGet`. -/
theorem FastVarMap.ofList_getD_eq_ssGet (ss : List (Var × Expr)) (v : Var) :
    (FastVarMap.ofList ss).getD v (.var v) = ssGet ss v := by
  rw [FastVarMap.ofList_getD]; unfold ssGet; rfl

/-- `FastVarMap.ofList` lookup agrees with `lookupExpr` (used by `simplify`). -/
theorem FastVarMap.ofList_getD_eq_lookupExpr (inv : EInv) (v : Var) :
    (FastVarMap.ofList inv).getD v (.var v) =
    match lookupExpr inv v with
    | some e => e
    | none   => .var v := by
  rw [FastVarMap.ofList_getD]; unfold lookupExpr
  cases hf : inv.find? (fun p => p.1 == v) with
  | none => rfl
  | some p => simp [Option.map]

/-- Substitute each variable in an expression with its symbolic post-value. -/
def Expr.substSym (ss : SymStore) : Expr → Expr
  | .lit n      => .lit n
  | .blit b     => .blit b
  | .var v      => ssGet ss v
  | .bin op a b => .bin op (a.substSym ss) (b.substSym ss)
  | .tobool e       => .tobool (e.substSym ss)
  | .cmpE op a b    => .cmpE op (a.substSym ss) (b.substSym ss)
  | .cmpLitE op a n => .cmpLitE op (a.substSym ss) n
  | .notE e         => .notE (e.substSym ss)
  | .andE a b       => .andE (a.substSym ss) (b.substSym ss)
  | .orE a b        => .orE (a.substSym ss) (b.substSym ss)
  | .arrRead arr idx => .arrRead arr (idx.substSym ss)
  | .flit n          => .flit n
  | .fbin op a b     => .fbin op (a.substSym ss) (b.substSym ss)
  | .fcmpE op a b    => .fcmpE op (a.substSym ss) (b.substSym ss)
  | .intToFloat e    => .intToFloat (e.substSym ss)
  | .floatToInt e    => .floatToInt (e.substSym ss)
  | .floatUnary op e  => .floatUnary op (e.substSym ss)
  | .ftern op a b c   => .ftern op (a.substSym ss) (b.substSym ss) (c.substSym ss)
  | .farrRead arr idx => .farrRead arr (idx.substSym ss)

/-- `substSymFast` with `FastVarMap.ofList` equals `substSym`. -/
theorem Expr.substSymFast_eq_substSym (e : Expr) (ss : SymStore) :
    e.substSymFast (FastVarMap.ofList ss) = e.substSym ss := by
  induction e with
  | lit _ | blit _ | flit _ => rfl
  | var v => exact FastVarMap.ofList_getD_eq_ssGet ss v
  | bin op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | tobool e ih => simp only [substSymFast, substSym, ih]
  | cmpE op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | cmpLitE op a n ih => simp only [substSymFast, substSym, ih]
  | notE e ih => simp only [substSymFast, substSym, ih]
  | andE a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | orE a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | arrRead arr idx ih => simp only [substSymFast, substSym, ih]
  | fbin op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | fcmpE op a b iha ihb => simp only [substSymFast, substSym, iha, ihb]
  | intToFloat e ih => simp only [substSymFast, substSym, ih]
  | floatToInt e ih => simp only [substSymFast, substSym, ih]
  | floatUnary op e ih => simp only [substSymFast, substSym, ih]
  | ftern op a b c iha ihb ihc => simp only [substSymFast, substSym, iha, ihb, ihc]
  | farrRead arr idx ih => simp only [substSymFast, substSym, ih]

/-- `simplifyFast` with `FastVarMap.ofList` equals `simplify`. -/
theorem Expr.simplifyFast_eq_simplify (e : Expr) (inv : EInv) :
    e.simplifyFast (FastVarMap.ofList inv) = e.simplify inv := by
  induction e with
  | lit _ | blit _ | flit _ => rfl
  | var v => exact FastVarMap.ofList_getD_eq_lookupExpr inv v
  | bin op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | tobool _ | cmpE _ _ _ | cmpLitE _ _ _ | notE _ | andE _ _ | orE _ _ => rfl
  | arrRead arr idx ih => simp only [simplifyFast, simplify, ih]
  | fbin op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | fcmpE op a b iha ihb => simp only [simplifyFast, simplify, iha, ihb]
  | intToFloat e ih => simp only [simplifyFast, simplify, ih]
  | floatToInt e ih => simp only [simplifyFast, simplify, ih]
  | floatUnary op e ih => simp only [simplifyFast, simplify, ih]
  | ftern op a b c iha ihb ihc => cases op <;> simp only [simplifyFast, simplify, iha, ihb, ihc]
  | farrRead arr idx ih => simp only [simplifyFast, simplify, ih]

/-- The HashMap-based variable set lookup used in `checkRelConsistency` is equivalent
    to the list-based `any` check used in the spec theorems. -/
theorem relVarSet_contains_eq_any (rel_pre : EExprRel) (w : Var) :
    (Std.HashMap.ofList (rel_pre.filterMap fun (_, e_t') =>
      match e_t' with | .var v => some (v, ()) | _ => none)).contains w =
    (rel_pre.any fun (_, e_t') => e_t' == .var w) := by
  rw [Std.HashMap.contains_ofList]
  induction rel_pre with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨e_o, e_t'⟩ := p
    simp only [List.filterMap_cons, List.any_cons]
    cases e_t' with
    | var v =>
      simp only [List.map_cons, List.contains_cons, BEq.beq, Expr.var.injEq, ih]
      congr 1; exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
    | _ => simpa [BEq.beq] using ih

/-- Check that a single invariant atom `(x, e)` is preserved by an instruction.
    Uses symbolic execution: the post-value of `x` and the post-value of `e`
    (with each variable replaced by its symbolic post-value) must be equal
    when simplified under the pre-invariant. -/
def checkInvAtom (inv_pre : EInv) (instr : TAC) (atom : Var × Expr) : Bool :=
  let (ss, _) := execSymbolic ([] : SymStore) ([] : SymArrayMem) instr
  let lhs := (ssGet ss atom.1).simplify inv_pre
  let rhs := (atom.2.substSym ss).simplify inv_pre
  lhs == rhs

/-- Compute reachable PCs from PC 0 via successor edges. -/
partial def reachable (prog : Prog) : Array Bool :=
  let rec go (visited : Array Bool) (worklist : List Nat) : Array Bool :=
    match worklist with
    | [] => visited
    | pc :: rest =>
      if pc < prog.size && !(visited.getD pc false) then
        let visited' := visited.set! pc true
        let succs := match prog[pc]? with
          | some instr => successors instr pc
          | none => []
        go visited' (succs ++ rest)
      else go visited rest
  go (Array.replicate prog.size false) (0 :: [])

/-- Compact a program: remove unreachable PCs and remap labels.
    Returns `(compacted, origMap, revMap)`. -/
def compactProg (prog : Prog) (reached : Array Bool) : Prog × Array Nat × Array Nat :=
  let origMap := buildOrigMap reached
  let revMap := buildRevMap origMap prog.size
  let arr := (List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc =>
      match prog[pc]? with
      | some (.goto l)    => .goto (revMap.getD l 0)
      | some (.ifgoto b l) => .ifgoto b (revMap.getD l 0)
      | some instr        => instr
      | none              => .halt
    | none => .halt
  ({ code := arr.toArray, tyCtx := prog.tyCtx,
     observable := prog.observable, arrayDecls := prog.arrayDecls },
   origMap, revMap)

/-- **Condition 2b**: Invariants are preserved by both programs. -/
def checkInvariantsPreservedExec (cert : ECertificate) : Bool :=
  let checkProg (prog : Prog) (inv : Array EInv) : Bool :=
    (List.range prog.size).all fun pc =>
      match prog[pc]? with
      | some instr =>
        (successors instr pc).all fun pc' =>
          (inv.getD pc' ([] : EInv)).all (checkInvAtom (inv.getD pc ([] : EInv)) instr)
      | none => true
  checkProg cert.orig cert.inv_orig &&
  checkProg cert.trans cert.inv_trans

/-- **Condition 4a**: Each halt in trans corresponds to a halt in orig.
    Uses `instrCerts` (not `haltCerts`) for consistency with the simulation. -/
def checkHaltCorrespondenceExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some .halt =>
      match cert.orig[(cert.instrCerts.getD pc default).pc_orig]? with
      | some .halt => true
      | _          => false
    | _ => true

/-- **Condition 4b**: Observable equivalence at halt.
    For each halt in trans, every observable variable must map to itself
    via `buildSubstMap` of the expression relation (i.e., `ssGet (buildSubstMap rel) v = .var v`).
    This ensures the transformed program produces the same observable values
    as the original at halt. -/
def checkHaltObservableExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some .halt =>
      let ic := cert.instrCerts.getD pc default
      cert.observable.all fun v =>
        ic.rel.any fun (e_o, e_t) => e_t == .var v && e_o == .var v
    | _ => true

/-- Compute the next PC from an instruction, using symbolic evaluation for ifgoto. -/
def computeNextPC (instr : TAC) (pc : Label) (ss : SymStore) (inv : EInv) : Option Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _ => some (pc + 1)
  | .fbinop _ _ _ _ | .intToFloat _ _ | .floatToInt _ _ | .floatUnary _ _ _ | .fternop _ _ _ _ _ => some (pc + 1)
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _ => some (pc + 1)
  | .printInt _ | .printFloat _ => some (pc + 1)
  | .goto l => some l
  | .ifgoto b l =>
    match b.symEval ss inv with
    | some true  => some l
    | some false => some (pc + 1)
    | none       => none
  | .halt => none

/-- Check that a binop instruction is safe to execute: for `div`, the
    symbolic denominator must simplify to a non-zero literal under the invariant.
    All other operations are unconditionally safe. -/
def checkBinopSafe (instr : TAC) (ss : SymStore) (inv : EInv) : Bool :=
  match instr with
  | .binop _ .div _ z | .binop _ .mod _ z =>
    match (ssGet ss z).simplify inv with
    | .lit n => n != 0
    | _ => true  -- runtime variable: safety proven by div-preservation check
  | _ => true


/-- Returns `true` if the instruction is a div/mod by literal zero — an error exit. -/
def isDivByZero (instr : TAC) (ss : SymStore) (inv : EInv) : Bool :=
  match instr with
  | .binop _ .div _ z | .binop _ .mod _ z =>
    match (ssGet ss z).simplify inv with
    | .lit n => n == 0
    | _ => false
  | _ => false

/-- Check that an arrLoad/arrStore instruction's index doesn't alias any existing SAM entry
    for the same array.  Uses simplification under the invariant to compare indices. -/
def checkInstrAliasOk (instr : TAC) (ss : SymStore) (sam : SymArrayMem) (inv : EInv) : Bool :=
  match instr with
  | .arrLoad _ arr idx _ | .arrStore arr idx _ _ =>
    let idx_sym := ssGet ss idx
    sam.all fun (a, i, _) =>
      !(a == arr) || (i == idx_sym) ||
      match i.simplify inv, idx_sym.simplify inv with
      | .lit n, .lit m => !(n == m)
      | _, _ => false
  | _ => true

/-- Verify that the original path is structurally valid:
    at each PC, the instruction's successor matches the next label. -/
def checkOrigPath (orig : Prog) (ss : SymStore) (sam : SymArrayMem) (inv : EInv)
    (pc : Label) (labels : List Label) (pc_next : Label)
    (branchInfo : Option (BoolExpr × Bool) := none) : Bool :=
  match labels with
  | [] => pc == pc_next
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      let pcOk := match computeNextPC instr pc ss inv with
        | some pc' => pc' == nextPC
        | none =>
          match branchInfo, instr with
          | some (origCond, true),  .ifgoto b l =>
            b.normalize ss inv == origCond.normalize ss inv && nextPC == l
          | some (origCond, false), .ifgoto b _ =>
            b.normalize ss inv == origCond.normalize ss inv && nextPC == pc + 1
          | _, _ => false
      let aliasOk := checkInstrAliasOk instr ss sam inv
      let (ss', sam') := execSymbolic ss sam instr
      pcOk && aliasOk &&
      checkOrigPath orig ss' sam' inv nextPC rest pc_next none
    | none => false

/-- Check expression relation consistency via symbolic execution.
    For every `(e_o, e_t)` pair in `rel_post`, the original-side expression
    after symbolic execution must agree with the transformed symbolic execution
    value after substituting the pre-relation map, both simplified under `inv_orig`.
    Only iterates over pairs claimed by the certificate — no all-variables sweep. -/
def checkRelConsistency
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (rel_pre rel_post : EExprRel) : Bool :=
  let (origSS, origSAM) := execPath orig ([] : SymStore) ([] : SymArrayMem) pc_orig origLabels
  let (transSS, transSAM) := execSymbolic ([] : SymStore) ([] : SymArrayMem) transInstr
  let preSubst := buildSubstMap rel_pre
  -- Build HashMap versions for O(1) lookups in the hot inner loop
  let origSSMap := FastVarMap.ofList origSS
  let transSSMap := FastVarMap.ofList transSS
  let preSubstMap := FastVarMap.ofList preSubst
  let invMap := FastVarMap.ofList inv_orig
  let pairCheck := rel_post.all fun (e_o, e_t) =>
    let origVal := e_o.substSymFast origSSMap |>.simplifyFast invMap
    let transVal := (e_t.substSymFast transSSMap).substSymFast preSubstMap |>.simplifyFast invMap
    origVal == transVal
  -- Free-variable coverage: for each (_, e_t) in rel_post, all free variables of
  -- (e_t.substSym transSS) must have a pair in rel_pre.
  -- Also covers array memory expression variables (i_t, v_t from transSAM).
  let relVarSet := Std.HashMap.ofList (rel_pre.filterMap fun (_, e_t') =>
    match e_t' with | .var w => some (w, ()) | _ => none)
  let relHasVar (w : Var) := relVarSet.contains w
  let fvCheck := rel_post.all fun (_, e_t) =>
    (e_t.substSymFast transSSMap).freeVars.all fun w => relHasVar w
  let amFvCheck := transSAM.all fun (_, i_t, v_t) =>
    i_t.freeVars.all (fun w => relHasVar w) &&
    v_t.freeVars.all (fun w => relHasVar w)
  let amCheck := origSAM.length == transSAM.length &&
    (origSAM.zip transSAM).all fun ((a_o, i_o, v_o), (a_t, i_t, v_t)) =>
      a_o == a_t &&
      i_o.simplifyFast invMap == (i_t.substSymFast preSubstMap).simplifyFast invMap &&
      v_o.simplifyFast invMap == (v_t.substSymFast preSubstMap).simplifyFast invMap
  pairCheck && fvCheck && amFvCheck && amCheck

/-- **Condition 3**: Every transition in the transformed program has a
    corresponding original-program path with consistent variable effects. -/
def checkAllTransitionsExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        (successors instr pc_t).all fun pc_t' =>
          let ic' := cert.instrCerts.getD pc_t' default
          let branchInfo := match instr with
            | .ifgoto b l =>
              match b.mapVarsRel ic.rel with
              | some origCond =>
                if !(l == pc_t + 1) then some (origCond, pc_t' == l) else none
              | none => none
            | _ => none
          ic.transitions.any fun tc =>
            tc.rel == ic.rel &&
            tc.rel_next == ic'.rel &&
            checkOrigPath cert.orig ([] : SymStore) ([] : SymArrayMem) (cert.inv_orig.getD ic.pc_orig ([] : EInv))
              ic.pc_orig tc.origLabels ic'.pc_orig branchInfo &&
            checkRelConsistency cert.orig ic.pc_orig tc.origLabels instr
              (cert.inv_orig.getD ic.pc_orig ([] : EInv))
              tc.rel tc.rel_next
      | none => false
    | none => true

/-- **Condition 5**: Zero-step original transitions decrease the measure. -/
def checkNonterminationExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        (successors instr pc_t).all fun pc_t' =>
          let ic' := cert.instrCerts.getD pc_t' default
          if ic.pc_orig == ic'.pc_orig then
            cert.measure.getD pc_t' 0 < cert.measure.getD pc_t 0
          else true
      | none => false
    | none => true

/-- **Condition 6**: The transformed program is non-empty and every successor
    PC is in bounds.  This ensures the transformed program never reaches an
    error state from an out-of-bounds PC. -/
def checkSuccessorsInBounds (cert : ECertificate) : Bool :=
  cert.trans.size > 0 &&
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some instr => (successors instr pc).all (· < cert.trans.size)
    | none => true

-- ============================================================
-- § 7. Main checker
-- ============================================================

/-- Condition 9 (error preservation for binop): for every `binop` in the
    transformed program, the original at the mapped PC also has a `binop`
    with the same operator, and both operands are related through the
    expression relation. This ensures div-by-zero errors on the
    transformed side also occur on the original side. -/
def checkDivPreservationExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some (.binop _ op y z) =>
      let ic := cert.instrCerts.getD pc_t default
      match cert.orig[ic.pc_orig]? with
      | some (.binop _ op' y' z') =>
        op == op' &&
        -- Only div/mod need operand correspondence via relFindOrigVar;
        -- add/sub/mul are always safe so operand mapping is not required.
        match op with
        | .div | .mod =>
          -- If the original divisor is a known non-zero constant from the invariant
          -- (e.g., a hoisted loop-invariant constant), both error preservation and
          -- transition safety hold: the divisor can never be zero.
          let inv := cert.inv_orig.getD ic.pc_orig ([] : EInv)
          (match inv.find? (fun (v, _) => v == z') with
           | some (_, .lit c) => c != (0 : BitVec 64)
           | _ => false) ||
          (relFindOrigVar ic.rel y == some y' &&
           relFindOrigVar ic.rel z == some z')
        | _ => true
      | _ => false
    | _ =>
      -- When the trans instruction is not a binop, verify the mapped orig
      -- instruction is not div/mod (otherwise we cannot transfer div-safety).
      -- Exception: if the orig invariant proves the divisor is a non-zero
      -- constant, the division is provably safe and needs no trans counterpart.
      let ic := cert.instrCerts.getD pc_t default
      match cert.orig[ic.pc_orig]? with
      | some (.binop _ .div _ z) | some (.binop _ .mod _ z) =>
        let inv := cert.inv_orig.getD ic.pc_orig ([] : EInv)
        match inv.find? (fun (v, _) => v == z) with
        | some (_, .lit c) => c != 0
        | _ => false
      | _ => true

/-- **Condition 10 (error preservation for array bounds)**: for every
    `arrLoad`/`arrStore` in the transformed program, the original at the
    mapped PC has a matching array instruction on the same array with the
    same index (via the expression relation).  Combined with equal array
    sizes, this ensures OOB errors on the transformed side also occur on
    the original side. -/
def checkBoundsPreservationExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    let ic := cert.instrCerts.getD pc_t default
    let inv := cert.inv_orig.getD ic.pc_orig ([] : EInv)
    -- Check index mapping: either via relFindOrigVar or both indices are
    -- the same known constant from the original invariant (hoisted by LICM).
    let idxOk (idx idx' : Var) :=
      relFindOrigVar ic.rel idx == some idx' ||
      (match inv.find? (fun (v, _) => v == idx') with
       | some (_, .lit c) =>
         match relFindOrigExpr ic.rel idx with
         | some (.lit c') => c == c'
         | _ => false
       | _ => false)
    match cert.trans[pc_t]? with
    | some (.arrLoad _ arr idx _) =>
      match cert.orig[ic.pc_orig]? with
      | some (.arrLoad _ arr' idx' _) =>
        arr == arr' && idxOk idx idx'
      | _ => false
    | some (.arrStore arr idx _ _) =>
      match cert.orig[ic.pc_orig]? with
      | some (.arrStore arr' idx' _ _) =>
        arr == arr' && idxOk idx idx'
      | _ => false
    | _ => true

/-- **Condition 12**: On each orig path, all instructions after the first are scalar,
    AND if the first orig instruction is an array op, the trans instruction at pc_t must
    also be an array op (so bounds transfer from the trans step).
    This ensures array bounds can always be established on the orig path. -/
def checkOrigPathBoundsOk (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some _ =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        -- If orig at ic.pc_orig is an array op, trans must also be an array op
        (match cert.orig[ic.pc_orig]? with
         | some (.arrLoad ..) | some (.arrStore ..) =>
           match cert.trans[pc_t]? with
           | some (.arrLoad ..) | some (.arrStore ..) => true
           | _ => false
         | _ => true) &&
        -- All intermediate orig path labels have scalar, non-div/mod instructions
        ic.transitions.all fun tc =>
          tc.origLabels.dropLast.all fun l =>
            match cert.orig[l]? with
            | some (.binop _ .div _ _) => false
            | some (.binop _ .mod _ _) => false
            | some instr => instr.isScalar
            | none => true
      | none => false
    | none => true

/-- **Condition 11**: Both programs declare the same array sizes. -/
def checkArraySizesExec (cert : ECertificate) : Bool :=
  cert.orig.arrayDecls == cert.trans.arrayDecls

/-- Check that a program contains no array instructions (arrLoad/arrStore). -/
def checkNoArrayInstrs (p : Prog) : Bool :=
  p.code.all TAC.isScalar

/-- Check that all invariant expressions are arrRead-free. -/
def checkNoArrReadInInvs (invs : Array EInv) : Bool :=
  invs.all fun inv => inv.all fun (_, e) => !e.hasArrRead

/-- Check that all original-side expressions in relations are arrRead-free.
    buildSubstMap extracts the first element of (e_o, .var v) pairs, so we check e_o. -/
def checkNoArrReadInRels (certs : Array EInstrCert) : Bool :=
  certs.all fun ic =>
    ic.rel.all (fun (e, _) => !e.hasArrRead) &&
    ic.transitions.all fun tc =>
      tc.rel.all (fun (e, _) => !e.hasArrRead) &&
      tc.rel_next.all (fun (e, _) => !e.hasArrRead)

/-- All arrLoad/arrStore instructions in a program use element type `.int`. -/
def AllArrayOpsInt (p : Prog) : Prop :=
  ∀ i (h : i < p.size), match p[i] with
    | .arrLoad _ _ _ ty => ty = .int
    | .arrStore _ _ _ ty => ty = .int
    | _ => True

/-- Decidable check for `AllArrayOpsInt`.
    Rejects `.bool` and `.float` element types on array ops. -/
def checkAllArrayOpsInt (p : Prog) : Bool :=
  p.code.all fun instr =>
    match instr with
    | .arrLoad _ _ _ ty | .arrStore _ _ _ ty => ty == .int
    | _ => true

/-- Lenient version of `checkAllArrayOpsInt` that accepts both `.int` and `.float`
    element types.  Used in `checkCertificateExec` so that float-array programs
    pass the executable checker (their soundness is handled separately). -/
def checkAllArrayOpsNotBool (p : Prog) : Bool :=
  p.code.all fun instr =>
    match instr with
    | .arrLoad _ _ _ .bool | .arrStore _ _ _ .bool => false
    | _ => true

theorem checkAllArrayOpsInt_sound (p : Prog) (h : checkAllArrayOpsInt p = true) :
    AllArrayOpsInt p := by
  intro i hi
  unfold checkAllArrayOpsInt at h
  have hall := (Array.all_eq_true.mp h) i hi
  revert hall
  cases p.code[i] <;> simp [beq_iff_eq]

theorem AllArrayOpsInt.arrLoad_int {p : Prog} {pc : Nat} {x : Var} {arr : ArrayName}
    {idx : Var} {ty : VarTy} (h : AllArrayOpsInt p)
    (hinstr : p[pc]? = some (.arrLoad x arr idx ty)) :
    ty = .int := by
  have hlt : pc < p.size := bound_of_getElem? hinstr
  have hmatch := h pc hlt
  have heq := Option.some.inj ((Prog.getElem?_eq_getElem hlt).symm.trans hinstr)
  simp [heq] at hmatch; exact hmatch

theorem AllArrayOpsInt.arrStore_int {p : Prog} {pc : Nat} {arr : ArrayName}
    {idx val : Var} {ty : VarTy} (h : AllArrayOpsInt p)
    (hinstr : p[pc]? = some (.arrStore arr idx val ty)) :
    ty = .int := by
  have hlt : pc < p.size := bound_of_getElem? hinstr
  have hmatch := h pc hlt
  have heq := Option.some.inj ((Prog.getElem?_eq_getElem hlt).symm.trans hinstr)
  simp [heq] at hmatch; exact hmatch

/-- Check all certificate conditions. Returns `true` iff the certificate is valid. -/
def checkCertificateExec (cert : ECertificate) : Bool :=
  checkWellTypedProg cert.orig.tyCtx cert.orig &&
  checkWellTypedProg cert.trans.tyCtx cert.trans &&
  (cert.orig.observable == cert.trans.observable) &&
  checkStartCorrespondenceExec cert &&
  checkInvariantsAtStartExec cert &&
  checkRelAtStartExec cert &&
  checkInvariantsPreservedExec cert &&
  checkNoArrReadInInvs cert.inv_orig &&
  checkNoArrReadInInvs cert.inv_trans &&
  checkNoArrReadInRels cert.instrCerts &&
  checkAllTransitionsExec cert &&
  checkHaltCorrespondenceExec cert &&
  checkHaltObservableExec cert &&
  checkNonterminationExec cert &&
  checkDivPreservationExec cert &&
  checkBoundsPreservationExec cert &&
  checkArraySizesExec cert &&
  checkOrigPathBoundsOk cert &&
  checkSuccessorsInBounds cert

/-- Verbose check: returns the result of each individual condition. -/
def checkCertificateVerboseExec (cert : ECertificate) : List (String × Bool) :=
  [ ("well_typed_orig",       checkWellTypedProg cert.orig.tyCtx cert.orig),
    ("well_typed_trans",      checkWellTypedProg cert.trans.tyCtx cert.trans),
    ("same_observable",       cert.orig.observable == cert.trans.observable),
    ("start_correspondence",  checkStartCorrespondenceExec cert),
    ("invariants_at_start",   checkInvariantsAtStartExec cert),
    ("rel_at_start",          checkRelAtStartExec cert),
    ("invariants_preserved",  checkInvariantsPreservedExec cert),
    ("no_arrread_inv_orig",   checkNoArrReadInInvs cert.inv_orig),
    ("no_arrread_inv_trans",  checkNoArrReadInInvs cert.inv_trans),
    ("no_arrread_rels",       checkNoArrReadInRels cert.instrCerts),
    ("all_transitions",       checkAllTransitionsExec cert),
    ("halt_correspondence",   checkHaltCorrespondenceExec cert),
    ("halt_observable",       checkHaltObservableExec cert),
    ("nontermination",        checkNonterminationExec cert),
    ("div_preservation",      checkDivPreservationExec cert),
    ("bounds_preservation",   checkBoundsPreservationExec cert),
    ("array_sizes_equal",     checkArraySizesExec cert),
    ("orig_path_bounds_ok",   checkOrigPathBoundsOk cert),
    ("successors_in_bounds",  checkSuccessorsInBounds cert) ]

/-- Observable output of a configuration with respect to an executable certificate.
    - If the current instruction is `halt`, returns `halt` with observable variable–value pairs.
    - If the configuration is an error, returns `error`.
    - If the PC is out of bounds, returns `error`.
    - Otherwise returns `nothing`. -/
def observeExec (cert : ECertificate) (c : Cfg) : Observation :=
  match c with
  | .halt σ _      => Observation.halt (cert.observable.map fun v => (v, σ v))
  | .error _ _     => Observation.error
  | .typeError _ _ => Observation.typeError
  | .run pc σ _    =>
    match cert.trans[pc]? with
    | some .halt => Observation.halt (cert.observable.map fun v => (v, σ v))
    | some _     => Observation.nothing
    | none       => Observation.error

