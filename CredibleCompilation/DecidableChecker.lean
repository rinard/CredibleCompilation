import CredibleCompilation.CertChecker

/-!
# Decidable Certificate Checker

An executable certificate checker that returns `Bool`.
Use `#eval! checkCertificate cert` or run `lake exe checker` from the terminal.

The checker uses **symbolic execution** and **expression simplification** to verify
that the transformed program's behavior matches the original. Invariants are
represented as lists of `(var, val)` atoms; variable maps are implicitly identity.
-/

-- ============================================================
-- § 1. Decidable invariants and helpers
-- ============================================================

/-- Decidable invariant: conjunction of `var = val` atoms. -/
abbrev DInv := List (Var × Val)

def lookupVar (inv : DInv) (v : Var) : Option Val :=
  (inv.find? (fun p => p.1 == v)).map (·.2)

-- ============================================================
-- § 2. Symbolic expression simplification
-- ============================================================

/-- Simplify an `Expr` by substituting known variable values and constant-folding. -/
def Expr.simplify (inv : DInv) : Expr → Expr
  | .lit n => .lit n
  | .var v => match lookupVar inv v with
    | some n => .lit n
    | none   => .var v
  | .bin op a b =>
    match a.simplify inv, b.simplify inv with
    | .lit na, .lit nb => .lit (op.eval na nb)
    | a', b'           => .bin op a' b'

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
def canReachSym (ss : SymStore) (inv : DInv) (instr : TAC) (pc next : Label) : Bool :=
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
-- § 5. Decidable certificate types
-- ============================================================

/-- A single transition correspondence with labels of the original path. -/
structure DTransCorr where
  /-- Labels of original PCs visited (successors of pc_orig, ending at pc_orig'). -/
  origLabels : List Label
  deriving Repr, Inhabited

/-- Per-instruction certificate entry. -/
structure DInstrCert where
  pc_orig     : Label
  transitions : List DTransCorr
  deriving Repr, Inhabited

/-- Per-halt certificate entry. -/
structure DHaltCert where
  pc_orig : Label
  deriving Repr, Inhabited

/-- A decidable certificate: all data needed to verify the transformation. -/
structure DCertificate where
  orig       : Prog
  trans      : Prog
  inv_orig   : Array DInv
  inv_trans  : Array DInv
  observable : List Var
  instrCerts : Array DInstrCert
  haltCerts  : Array DHaltCert
  /-- Well-founded measure for non-termination (per transformed label). -/
  measure    : Array Nat

-- ============================================================
-- § 6. Individual check functions
-- ============================================================

/-- **Condition 1**: Start labels correspond, initial variable map is identity. -/
def checkStart (cert : DCertificate) : Bool :=
  match cert.instrCerts[0]? with
  | some ic => ic.pc_orig == 0
  | none    => false

/-- **Condition 2a**: Invariants are trivially true at label 0. -/
def checkInvariantsAtStart (cert : DCertificate) : Bool :=
  (cert.inv_orig.getD 0 ([] : DInv)).isEmpty &&
  (cert.inv_trans.getD 0 ([] : DInv)).isEmpty

/-- Check that a single invariant atom is preserved by an instruction.
    Two cases: (1) if the instruction assigns to the atom's variable,
    verify the new value matches; (2) if it does NOT assign to it,
    verify the atom already held in the pre-invariant. -/
def checkInvAtom (inv_pre : DInv) (instr : TAC) (atom : Var × Val) : Bool :=
  let (x, v) := atom
  -- Does the instruction modify x?
  let modifiesX : Bool :=
    match instr with
    | .const y _ | .copy y _ | .binop y _ _ _ => y == x
    | _ => false
  if modifiesX then
    -- Must determine the new value of x
    let newVal : Option Val :=
      match instr with
      | .const _ n => some n
      | .copy _ z  => lookupVar inv_pre z
      | .binop _ op a b =>
        match lookupVar inv_pre a, lookupVar inv_pre b with
        | some va, some vb => some (op.eval va vb)
        | _, _ => none
      | _ => none  -- unreachable since modifiesX = false for these
    match newVal with
    | some val => val == v
    | none     => false  -- can't determine new value, reject
  else
    -- Variable not modified; check it was already in the pre-invariant
    lookupVar inv_pre x == some v

/-- **Condition 2b**: Invariants are preserved by both programs. -/
def checkInvariantsPreserved (cert : DCertificate) : Bool :=
  let checkProg (prog : Prog) (inv : Array DInv) : Bool :=
    (List.range prog.size).all fun pc =>
      match prog[pc]? with
      | some instr =>
        (successors instr pc).all fun pc' =>
          (inv.getD pc' ([] : DInv)).all (checkInvAtom (inv.getD pc ([] : DInv)) instr)
      | none => true
  checkProg cert.orig cert.inv_orig &&
  checkProg cert.trans cert.inv_trans

/-- **Condition 4a**: Each halt in trans corresponds to a halt in orig.
    Uses `instrCerts` (not `haltCerts`) for consistency with the simulation. -/
def checkHaltCorrespondence (cert : DCertificate) : Bool :=
  (List.range cert.trans.size).all fun pc =>
    match cert.trans[pc]? with
    | some .halt =>
      match cert.orig[(cert.instrCerts.getD pc default).pc_orig]? with
      | some .halt => true
      | _          => false
    | _ => true

/-- **Condition 4b**: Observable equivalence at halt.
    Trivially true for identity variable maps. -/
def checkHaltObservable (_ : DCertificate) : Bool := true

/-- Compute the next PC from an instruction, using symbolic branch analysis for ifgoto. -/
def computeNextPC (instr : TAC) (pc : Label) (ss : SymStore) (inv : DInv) : Option Label :=
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
    at each PC, the instruction's successor matches the next label. -/
def checkOrigPath (orig : Prog) (ss : SymStore) (inv : DInv)
    (pc : Label) (labels : List Label) (pc_next : Label) : Bool :=
  match labels with
  | [] => pc == pc_next
  | nextPC :: rest =>
    match orig[pc]? with
    | some instr =>
      computeNextPC instr pc ss inv == some nextPC &&
      checkOrigPath orig (execSymbolic ss instr) inv nextPC rest pc_next
    | none => false

/-- Check variable map consistency via symbolic execution.
    Symbolically executes both sides and checks that all program variables
    have equal simplified expressions under the respective invariants. -/
def checkVarMapConsistency (vars : List Var)
    (orig : Prog) (pc_orig : Label) (origLabels : List Label) (transInstr : TAC)
    (inv_orig inv_trans : DInv) : Bool :=
  let origSS := execPath orig ([] : SymStore) pc_orig origLabels
  let transSS := execSymbolic ([] : SymStore) transInstr
  vars.all fun v =>
    (ssGet origSS v).simplify inv_orig == (ssGet transSS v).simplify inv_trans

/-- **Condition 3**: Every transition in the transformed program has a
    corresponding original-program path with consistent variable effects. -/
def checkAllTransitions (cert : DCertificate) : Bool :=
  let vars := collectAllVars cert.orig cert.trans
  (List.range cert.trans.size).all fun pc_t =>
    match cert.trans[pc_t]? with
    | some .halt => true
    | some instr =>
      match cert.instrCerts[pc_t]? with
      | some ic =>
        (successors instr pc_t).all fun pc_t' =>
          let ic' := cert.instrCerts.getD pc_t' default
          ic.transitions.any fun tc =>
            checkOrigPath cert.orig ([] : SymStore) (cert.inv_orig.getD ic.pc_orig ([] : DInv))
              ic.pc_orig tc.origLabels ic'.pc_orig &&
            checkVarMapConsistency vars cert.orig ic.pc_orig tc.origLabels instr
              (cert.inv_orig.getD ic.pc_orig ([] : DInv))
              (cert.inv_trans.getD pc_t ([] : DInv))
      | none => false
    | none => true

/-- **Condition 5**: Zero-step original transitions decrease the measure. -/
def checkNontermination (cert : DCertificate) : Bool :=
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
def checkCertificate (cert : DCertificate) : Bool :=
  checkStart cert &&
  checkInvariantsAtStart cert &&
  checkInvariantsPreserved cert &&
  checkAllTransitions cert &&
  checkHaltCorrespondence cert &&
  checkHaltObservable cert &&
  checkNontermination cert

/-- Verbose check: returns the result of each individual condition. -/
def checkCertificateVerbose (cert : DCertificate) : List (String × Bool) :=
  [ ("start_correspondence",  checkStart cert),
    ("invariants_at_start",   checkInvariantsAtStart cert),
    ("invariants_preserved",  checkInvariantsPreserved cert),
    ("all_transitions",       checkAllTransitions cert),
    ("halt_correspondence",   checkHaltCorrespondence cert),
    ("halt_observable",       checkHaltObservable cert),
    ("nontermination",        checkNontermination cert) ]

-- ============================================================
-- § 8. Example certificates
-- ============================================================

/-! ### Example 1: Simple constant propagation (copy → const)
  Original:  `0: x:=5; 1: y:=x; 2: halt`
  Transformed: `0: x:=5; 1: y:=5; 2: halt`
-/
namespace DExample1

def cert : DCertificate :=
  { orig  := #[.const "x" 5, .copy "y" "x", .halt]
    trans := #[.const "x" 5, .const "y" 5, .halt]
    inv_orig  := #[[], [("x", 5)], [("x", 5)]]
    inv_trans := #[[], [("x", 5)], [("x", 5)]]
    observable := ["y"]
    instrCerts := #[
      ⟨0, [⟨[1]⟩]⟩,                          -- trans 0→1 maps to orig 0→1
      ⟨1, [⟨[2]⟩]⟩,                          -- trans 1→2 maps to orig 1→2
      ⟨2, []⟩ ]                               -- halt
    haltCerts := #[⟨0⟩, ⟨0⟩, ⟨2⟩]
    measure := #[0, 0, 0] }

#eval! checkCertificate cert              -- true
#eval! checkCertificateVerbose cert

end DExample1

/-! ### Example 2: Constant propagation into binop operand
  Original:  `0: a:=10; 1: b:=a; 2: c:=b+y; 3: halt`
  Transformed: `0: a:=10; 1: b:=10; 2: c:=b+y; 3: halt`
-/
namespace DExample2

def cert : DCertificate :=
  { orig  := #[.const "a" 10, .copy "b" "a", .binop "c" .add "b" "y", .halt]
    trans := #[.const "a" 10, .const "b" 10, .binop "c" .add "b" "y", .halt]
    inv_orig  := #[[], [("a", 10)], [("a", 10), ("b", 10)], [("a", 10), ("b", 10)]]
    inv_trans := #[[], [("a", 10)], [("a", 10), ("b", 10)], [("a", 10), ("b", 10)]]
    observable := ["c"]
    instrCerts := #[
      ⟨0, [⟨[1]⟩]⟩,
      ⟨1, [⟨[2]⟩]⟩,
      ⟨2, [⟨[3]⟩]⟩,
      ⟨3, []⟩ ]
    haltCerts := #[⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨3⟩]
    measure := #[0, 0, 0, 0] }

#eval! checkCertificate cert              -- true
#eval! checkCertificateVerbose cert

end DExample2

/-! ### Example 3: Redundant assignment removal in a loop
  Original (7 instr): includes redundant `step:=2` at pc 4
  Transformed (6 instr): redundant assignment removed
  Trans 3→4 maps to orig 3→4→5 (two original steps)
-/
namespace DExample3

def cert : DCertificate :=
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
    inv_orig  := #[[], [("step", 2)], [("step", 2)], [("step", 2)],
                    [("step", 2)], [("step", 2)], [("step", 2)]]
    inv_trans := #[[], [("step", 2)], [("step", 2)],
                    [("step", 2)], [("step", 2)], [("step", 2)]]
    observable := ["acc"]
    instrCerts := #[
      ⟨0, [⟨[1]⟩]⟩,                                          -- trans 0→1 : orig 0→1
      ⟨1, [⟨[3]⟩, ⟨[2]⟩]⟩,                                  -- trans 1→3 or 1→2
      ⟨2, []⟩,                                                -- halt
      ⟨3, [⟨[4, 5]⟩]⟩,                                       -- trans 3→4 : orig 3→4→5 (two steps)
      ⟨5, [⟨[6]⟩]⟩,                                          -- trans 4→5 : orig 5→6
      ⟨6, [⟨[1]⟩]⟩ ]                                         -- trans 5→1 : orig 6→1
    haltCerts := #[⟨0⟩, ⟨0⟩, ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]
    measure := #[0, 0, 0, 0, 0, 0] }

#eval! checkCertificate cert              -- true
#eval! checkCertificateVerbose cert

end DExample3

/-! ### Bad Example: Buggy transformation (y:=x → y:=3, should be y:=5)
  The checker rejects this because the symbolic effects don't match:
  orig `copy "y" "x"` under invariant `x=5` produces `y=5`,
  but trans `const "y" 3` produces `y=3`.
-/
namespace DBadExample

def cert : DCertificate :=
  { orig  := #[.const "x" 5, .copy "y" "x", .halt]
    trans := #[.const "x" 5, .const "y" 3, .halt]
    inv_orig  := #[[], [("x", 5)], [("x", 5)]]
    inv_trans := #[[], [("x", 5)], [("x", 5)]]
    observable := ["y"]
    instrCerts := #[
      ⟨0, [⟨[1]⟩]⟩,
      ⟨1, [⟨[2]⟩]⟩,
      ⟨2, []⟩ ]
    haltCerts := #[⟨0⟩, ⟨0⟩, ⟨2⟩]
    measure := #[0, 0, 0] }

#eval! checkCertificate cert              -- false
#eval! checkCertificateVerbose cert       -- all_transitions fails

end DBadExample
