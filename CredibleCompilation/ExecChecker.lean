import CredibleCompilation.PropChecker

/-!
# Executable Certificate Checker

An executable certificate checker that returns `Bool`.
Use `#eval! checkCertificateExec cert` or run `lake exe checker` from the terminal.

The checker uses **symbolic execution** and **expression simplification** to verify
that the transformed program's behavior matches the original. Invariants are
represented as lists of `(var, expr)` atoms. An explicit **variable map** (per
transformed PC) relates transformed variables to expressions over original
variables; unmapped variables default to identity.
-/

-- ============================================================
-- § 1. Executable invariants and helpers
-- ============================================================

/-- Executable invariant: conjunction of `var = expr` atoms.
    Each `(x, e)` asserts `σ x = e.eval σ` at runtime. -/
abbrev EInv := List (Var × Expr)

/-- Executable variable map: maps transformed variable names to expressions
    over original variable names.  Each `(v, e)` asserts
    `σ_trans(v) = e.eval(σ_orig)`.  Variables not in the map are implicitly
    identity (`.var v`).  Same representation as `EInv` / `SymStore`. -/
abbrev EVarMap := List (Var × Expr)

def lookupExpr (inv : EInv) (v : Var) : Option Expr :=
  (inv.find? (fun p => p.1 == v)).map (·.2)

-- ============================================================
-- § 2. Symbolic expression simplification
-- ============================================================

/-- Reassociate sub-expressions involving literals after simplification.
    Normalizes patterns like `(n - x) - m → (n - m) - x` and
    `n - (x + m) → (n - m) - x` so that the checker can verify
    induction variable elimination (countdown vs recomputation). -/
def Expr.reassoc : BinOp → Expr → Expr → Expr
  | .sub, .bin .sub (.lit na) x, .lit nb => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .add x (.lit nb) => .bin .sub (.lit (na - nb)) x
  | .sub, .lit na, .bin .add (.lit nb) x => .bin .sub (.lit (na - nb)) x
  | op, a, b => .bin op a b

/-- Simplify an `Expr` by substituting known variable expressions and constant-folding.
    After folding, applies `reassoc` to normalize sub/add patterns involving literals. -/
def Expr.simplify (inv : EInv) : Expr → Expr
  | .lit n => .lit n
  | .var v => match lookupExpr inv v with
    | some e => e
    | none   => .var v
  | .bin op a b =>
    match a.simplify inv, b.simplify inv with
    | .lit na, .lit nb => .lit (op.eval na nb)
    | a', b'           => Expr.reassoc op a' b'

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

/-- Symbolically execute one TAC instruction.
    Expressions in the resulting store reference the *initial* variable values. -/
def execSymbolic (ss : SymStore) (instr : TAC) : SymStore :=
  match instr with
  | .const x n      => ssSet ss x (.lit n)
  | .copy x y       => ssSet ss x (ssGet ss y)
  | .binop x op y z => ssSet ss x (.bin op (ssGet ss y) (ssGet ss z))
  | _               => ss

/-- Symbolically execute along a path of labels in the original program.
    At each label, look up the instruction and execute it symbolically. -/
def execPath (orig : Prog) (ss : SymStore) (pc : Label) : List Label → SymStore
  | []             => ss
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr => execPath orig (execSymbolic ss instr) nextPC rest
    | none       => ss

-- ============================================================
-- § 4. Instruction helpers
-- ============================================================

def successors (instr : TAC) (pc : Label) : List Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ => [pc + 1]
  | .goto l       => [l]
  | .ifgoto _ l   => [l, pc + 1]
  | .halt         => []

def canReach (instr : TAC) (pc next : Label) : Bool :=
  (successors instr pc).contains next

/-- Check whether an expression is a non-zero literal. -/
def Expr.isNonZeroLit : Expr → Bool
  | .lit 0 => false
  | .lit _ => true
  | _      => false

/-- Like `canReach`, but for `ifgoto` also verifies the branch direction
    via the symbolic value of the condition variable under the invariant.
    Non-ifgoto instructions fall back to plain `canReach`. -/
def canReachSym (ss : SymStore) (inv : EInv) (instr : TAC) (pc next : Label) : Bool :=
  match instr with
  | .ifgoto x l =>
    let sv := (ssGet ss x).simplify inv
    (next == l && sv.isNonZeroLit) || (next == pc + 1 && sv == .lit 0)
  | _ => canReach instr pc next

/-- Collect all variable names from both programs. -/
def collectAllVars (p1 p2 : Prog) : List Var :=
  let extract (instr : TAC) : List Var :=
    match instr with
    | .const x _     => [x]
    | .copy x y      => [x, y]
    | .binop x _ y z => [x, y, z]
    | .ifgoto x _    => [x]
    | _              => []
  let go (p : Prog) := p.toList.foldl (fun acc i => acc ++ extract i) ([] : List Var)
  go p1 ++ go p2

-- ============================================================
-- § 5. Executable certificate types
-- ============================================================

/-- A single transition correspondence with labels of the original path. -/
structure ETransCorr where
  /-- Labels of original PCs visited (successors of pc_orig, ending at pc_orig'). -/
  origLabels : List Label
  /-- Variable map at the source of this transition (should equal the
      enclosing `EInstrCert.vm`). -/
  vm         : EVarMap := []
  /-- Variable map at the target of this transition (should equal
      the successor `EInstrCert.vm`). -/
  vm_next    : EVarMap := []
  deriving Repr, Inhabited

/-- Per-instruction certificate entry. -/
structure EInstrCert where
  pc_orig     : Label
  /-- Variable map at this label: maps transformed vars to expressions
      over original vars.  Empty list = identity. -/
  vm          : EVarMap := []
  transitions : List ETransCorr
  deriving Repr, Inhabited

/-- Per-halt certificate entry. -/
structure EHaltCert where
  pc_orig : Label
  /-- Variable map at this halt label. -/
  vm      : EVarMap := []
  deriving Repr, Inhabited

/-- Shorthand: ETransCorr with identity (empty) variable maps. -/
abbrev ETransCorr.id (labels : List Label) : ETransCorr := { origLabels := labels }

/-- Shorthand: EInstrCert with identity (empty) variable map. -/
abbrev EInstrCert.id (pc : Label) (trans : List ETransCorr) : EInstrCert :=
  { pc_orig := pc, transitions := trans }

/-- Shorthand: EHaltCert with identity (empty) variable map. -/
abbrev EHaltCert.id (pc : Label) : EHaltCert := { pc_orig := pc }

/-- An executable certificate: all data needed to verify the transformation. -/
structure ECertificate where
  orig       : Prog
  trans      : Prog
  inv_orig   : Array EInv
  inv_trans  : Array EInv
  observable : List Var
  instrCerts : Array EInstrCert
  haltCerts  : Array EHaltCert
  /-- Well-founded measure for non-termination (per transformed label). -/
  measure    : Array Nat

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

/-- **Condition 2c**: Variable map is identity at label 0
    (both programs start from the same initial state). -/
def checkVarMapAtStartExec (cert : ECertificate) : Bool :=
  (cert.instrCerts.getD 0 default).vm.isEmpty

/-- Substitute each variable in an expression with its symbolic post-value. -/
def Expr.substSym (ss : SymStore) : Expr → Expr
  | .lit n      => .lit n
  | .var v      => ssGet ss v
  | .bin op a b => .bin op (a.substSym ss) (b.substSym ss)

/-- Check that a single invariant atom `(x, e)` is preserved by an instruction.
    Uses symbolic execution: the post-value of `x` and the post-value of `e`
    (with each variable replaced by its symbolic post-value) must be equal
    when simplified under the pre-invariant. -/
def checkInvAtom (inv_pre : EInv) (instr : TAC) (atom : Var × Expr) : Bool :=
  let ss := execSymbolic ([] : SymStore) instr
  let lhs := (ssGet ss atom.1).simplify inv_pre
  let rhs := (atom.2.substSym ss).simplify inv_pre
  lhs == rhs

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
    For each halt in trans, every observable variable's varMap entry
    must be identity (`.var v`).  This ensures the transformed program
    produces the same observable values as the original at halt. -/
def checkHaltObservableExec (cert : ECertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some .halt =>
      let ic := cert.instrCerts.getD pc default
      cert.observable.all fun v => ssGet ic.vm v == .var v
    | _ => true

/-- Compute the next PC from an instruction, using symbolic branch analysis for ifgoto. -/
def computeNextPC (instr : TAC) (pc : Label) (ss : SymStore) (inv : EInv) : Option Label :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ => some (pc + 1)
  | .goto l => some l
  | .ifgoto x l =>
    let sv := (ssGet ss x).simplify inv
    if sv.isNonZeroLit then some l
    else if sv == .lit 0 then some (pc + 1)
    else none
  | .halt => none

/-- Verify that the original path is structurally valid:
    at each PC, the instruction's successor matches the next label.
    `branchInfo` provides the condition variable and branch direction from the
    transformed instruction's ifgoto, used as a fallback when symbolic analysis
    of the original ifgoto is inconclusive (both programs check the same variable
    and stores agree via identity varmap). Only applies to the first step. -/
def checkOrigPath (orig : Prog) (ss : SymStore) (inv : EInv)
    (pc : Label) (labels : List Label) (pc_next : Label)
    (branchInfo : Option (Var × Bool) := none) : Bool :=
  match labels with
  | [] => pc == pc_next
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      let pcOk := match computeNextPC instr pc ss inv with
        | some pc' => pc' == nextPC
        | none =>
          -- Fallback: if the transformed ifgoto checks the same variable,
          -- use its branch direction (stores agree via identity varmap)
          match branchInfo, instr with
          | some (xv, true),  .ifgoto x l => x == xv && nextPC == l
          | some (xv, false), .ifgoto x _ => x == xv && nextPC == pc + 1
          | _, _ => false
      pcOk &&
      checkOrigPath orig (execSymbolic ss instr) inv nextPC rest pc_next none
    | none => false

/-- Check variable map consistency via symbolic execution.
    Symbolically executes both sides, then for each variable `v`:
    - **trans side**: substitute the pre-varMap into the trans post-value
      (mapping trans pre-vars to orig expressions), then simplify under `inv_orig`.
    - **orig side**: substitute the orig post-symbolic-store into the
      post-varMap entry for `v`, then simplify under `inv_orig`.
    Both expressions must agree. -/
def checkVarMapConsistency (vars : List Var)
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig : EInv) (vm_pre vm_post : EVarMap) : Bool :=
  let allVars := vars ++ vm_pre.map Prod.fst ++ vm_post.map Prod.fst
  let origSS := execPath orig ([] : SymStore) pc_orig origLabels
  let transSS := execSymbolic ([] : SymStore) transInstr
  allVars.all fun v =>
    let transVal := (ssGet transSS v).substSym vm_pre |>.simplify inv_orig
    let origVal := (ssGet vm_post v).substSym origSS |>.simplify inv_orig
    transVal == origVal

/-- **Condition 3**: Every transition in the transformed program has a
    corresponding original-program path with consistent variable effects. -/
def checkAllTransitionsExec (cert : ECertificate) : Bool :=
  let vars := collectAllVars cert.orig cert.trans
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        (successors instr pc_t).all fun pc_t' =>
          let ic' := cert.instrCerts.getD pc_t' default
          -- For ifgoto: pass branch direction to checkOrigPath.
          -- Map the condition variable through the varMap to orig space.
          -- Guard: l ≠ pc+1 ensures pc_t' disambiguates taken vs fallthrough.
          let branchInfo := match instr with
            | .ifgoto x l =>
              match ssGet ic.vm x with
              | .var origX =>
                if !(l == pc_t + 1) then some (origX, pc_t' == l) else none
              | _ => none  -- non-variable: computeNextPC resolves via invariant
            | _ => none
          ic.transitions.any fun tc =>
            tc.vm == ic.vm &&
            tc.vm_next == ic'.vm &&
            checkOrigPath cert.orig ([] : SymStore) (cert.inv_orig.getD ic.pc_orig ([] : EInv))
              ic.pc_orig tc.origLabels ic'.pc_orig branchInfo &&
            checkVarMapConsistency vars cert.orig ic.pc_orig tc.origLabels instr
              (cert.inv_orig.getD ic.pc_orig ([] : EInv))
              tc.vm tc.vm_next
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

-- ============================================================
-- § 7. Main checker
-- ============================================================

/-- Check all certificate conditions. Returns `true` iff the certificate is valid. -/
def checkCertificateExec (cert : ECertificate) : Bool :=
  checkStartCorrespondenceExec cert &&
  checkInvariantsAtStartExec cert &&
  checkVarMapAtStartExec cert &&
  checkInvariantsPreservedExec cert &&
  checkAllTransitionsExec cert &&
  checkHaltCorrespondenceExec cert &&
  checkHaltObservableExec cert &&
  checkNonterminationExec cert

/-- Verbose check: returns the result of each individual condition. -/
def checkCertificateVerboseExec (cert : ECertificate) : List (String × Bool) :=
  [ ("start_correspondence",  checkStartCorrespondenceExec cert),
    ("invariants_at_start",   checkInvariantsAtStartExec cert),
    ("varmap_at_start",       checkVarMapAtStartExec cert),
    ("invariants_preserved",  checkInvariantsPreservedExec cert),
    ("all_transitions",       checkAllTransitionsExec cert),
    ("halt_correspondence",   checkHaltCorrespondenceExec cert),
    ("halt_observable",       checkHaltObservableExec cert),
    ("nontermination",        checkNonterminationExec cert) ]

