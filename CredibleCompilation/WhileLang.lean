import CredibleCompilation.Semantics

/-!
# While Language — Source Language and Compiler to TAC

A simple structured imperative language with while loops, if/else,
assignment, and sequencing. Variables are typed: integer or boolean.

The compiler translates source programs to TAC (three-address code)
programs suitable for optimization and certificate checking.

## Design note

The compiler is **not verified** — this is intentional. The credible
compilation framework means we don't need to trust the compiler: the
certificate checker verifies that any subsequent optimization preserves
TAC-level semantics. The source language serves as a convenient front-end
for writing programs.
-/

-- ============================================================
-- § 1. Source language AST
-- ============================================================

/-- Arithmetic expressions (tree-structured, unlike TAC operands). -/
inductive SExpr where
  | lit  : Int → SExpr
  | var  : Var → SExpr
  | bin  : BinOp → SExpr → SExpr → SExpr
  deriving Repr

/-- Boolean expressions over arithmetic sub-expressions. -/
inductive SBool where
  | bvar : Var → SBool                          -- read a boolean variable
  | cmp  : CmpOp → SExpr → SExpr → SBool
  | not  : SBool → SBool
  | and  : SBool → SBool → SBool
  | or   : SBool → SBool → SBool
  deriving Repr

/-- Statements. -/
inductive Stmt where
  | skip    : Stmt
  | assign  : Var → SExpr → Stmt                -- integer assignment
  | bassign : Var → SBool → Stmt                -- boolean assignment
  | seq     : Stmt → Stmt → Stmt
  | ite     : SBool → Stmt → Stmt → Stmt        -- if-then-else
  | loop    : SBool → Stmt → Stmt
  deriving Repr

-- Syntactic sugar
infixr:30 " ;; " => Stmt.seq

-- ============================================================
-- § 2. Direct interpretation (for testing / specification)
-- ============================================================

/-- Evaluate an arithmetic expression. Returns Int; reads integer
    values from the store via `.toInt`. -/
def SExpr.eval (σ : Store) : SExpr → Int
  | .lit n      => n
  | .var x      => (σ x).toInt
  | .bin op a b => op.eval (a.eval σ) (b.eval σ)

/-- Evaluate a boolean expression. -/
def SBool.eval (σ : Store) : SBool → Bool
  | .bvar x     => (σ x).toBool
  | .cmp op a b => op.eval (a.eval σ) (b.eval σ)
  | .not e      => !e.eval σ
  | .and a b    => a.eval σ && b.eval σ
  | .or a b     => a.eval σ || b.eval σ

/-- Interpret a statement directly, with a fuel bound to ensure termination. -/
def Stmt.interp (fuel : Nat) (σ : Store) : Stmt → Option Store
  | .skip        => some σ
  | .assign x e  => some (σ[x ↦ .int (e.eval σ)])
  | .bassign x b => some (σ[x ↦ .bool (b.eval σ)])
  | .seq s1 s2   => do let σ' ← s1.interp fuel σ; s2.interp fuel σ'
  | .ite b s1 s2 =>
    if b.eval σ then s1.interp fuel σ else s2.interp fuel σ
  | .loop b body =>
    match fuel with
    | 0 => none  -- out of fuel
    | fuel' + 1 =>
      if b.eval σ then do
        let σ' ← body.interp fuel' σ
        (Stmt.loop b body).interp fuel' σ'
      else some σ

-- ============================================================
-- § 3. Compiler: While language → TAC
-- ============================================================

/-- Compilation state: emitted code buffer + fresh temporary counter. -/
structure CompState where
  code    : Array TAC := #[]
  nextTmp : Nat       := 0

abbrev CompM := StateM CompState

/-- Emit an instruction, returning its label (index). -/
def emit (instr : TAC) : CompM Label := do
  let s ← get
  let idx := s.code.size
  set { s with code := s.code.push instr }
  return idx

/-- Get a fresh temporary variable name. -/
def freshVar : CompM Var := do
  let s ← get
  set { s with nextTmp := s.nextTmp + 1 }
  return s!"__t{s.nextTmp}"

/-- Current label (index of next instruction to be emitted). -/
def currentLabel : CompM Label := do
  return (← get).code.size

/-- Patch an already-emitted instruction at the given index. -/
def patch (idx : Label) (instr : TAC) : CompM Unit := do
  let s ← get
  set { s with code := s.code.set! idx instr }

-- ============================================================
-- § 3a. Expression compilation
-- ============================================================

/-- Compile an arithmetic expression, returning the variable holding the result.
    Leaf variables are returned directly; literals and binops use fresh temps. -/
def compileExpr (e : SExpr) : CompM Var := do
  match e with
  | .lit n =>
    let t ← freshVar
    let _ ← emit (.const t (.int n))
    return t
  | .var x => return x
  | .bin op a b =>
    let va ← compileExpr a
    let vb ← compileExpr b
    let t ← freshVar
    let _ ← emit (.binop t op va vb)
    return t

/-- Compile a boolean expression, returning a `BoolExpr` over variables
    (sub-expressions have been materialized into temporaries). -/
def compileBool (b : SBool) : CompM BoolExpr := do
  match b with
  | .bvar x => return .bvar x
  | .cmp op a b => do
    let va ← compileExpr a
    let vb ← compileExpr b
    return .cmp op va vb
  | .not e => do
    let be ← compileBool e
    return .not be
  | .and a b => do
    let ba ← compileBool a
    let bb ← compileBool b
    return .and ba bb
  | .or a b => do
    let ba ← compileBool a
    let bb ← compileBool b
    return .or ba bb

-- ============================================================
-- § 3b. Statement compilation
-- ============================================================

/-- Compile a statement, emitting TAC instructions into the buffer. -/
def compileStmt (s : Stmt) : CompM Unit := do
  match s with
  | .skip => return ()
  | .assign x e =>
    match e with
    | .lit n => let _ ← emit (.const x (.int n))
    | .var y => let _ ← emit (.copy x y)
    | .bin op a b =>
      let va ← compileExpr a
      let vb ← compileExpr b
      let _ ← emit (.binop x op va vb)
  | .bassign x b =>
    let be ← compileBool b
    let _ ← emit (.boolop x be)
  | .seq s1 s2 =>
    compileStmt s1
    compileStmt s2
  | .ite b s1 s2 =>
    let be ← compileBool b
    -- ifgoto be <then_label> — will be patched
    let ifSlot ← emit (.ifgoto be 0)
    -- fall-through: else branch
    compileStmt s2
    -- goto <end_label> — will be patched
    let gotoEndSlot ← emit (.goto 0)
    -- then branch
    let thenLabel ← currentLabel
    compileStmt s1
    let endLabel ← currentLabel
    -- patch jump targets
    patch ifSlot (.ifgoto be thenLabel)
    patch gotoEndSlot (.goto endLabel)
  | .loop b body =>
    let condLabel ← currentLabel
    let be ← compileBool b
    -- if condition false, exit loop — will be patched
    let exitSlot ← emit (.ifgoto (.not be) 0)
    -- loop body
    compileStmt body
    -- loop back to condition
    let _ ← emit (.goto condLabel)
    let exitLabel ← currentLabel
    -- patch exit jump
    patch exitSlot (.ifgoto (.not be) exitLabel)

-- ============================================================
-- § 3c. Top-level compilation
-- ============================================================

/-- Compile a while-language program to a TAC program.
    Appends `halt` at the end. -/
def compile (s : Stmt) : Prog :=
  let (_, state) := (do compileStmt s; let _ ← emit .halt).run {}
  state.code

-- ============================================================
-- § 4. Pretty-printing
-- ============================================================

def SExpr.toString : SExpr → String
  | .lit n => s!"{n}"
  | .var x => x
  | .bin op a b =>
    let opStr := match op with | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
    s!"({a.toString} {opStr} {b.toString})"

def SBool.toString : SBool → String
  | .bvar x => x
  | .cmp op a b =>
    let opStr := match op with | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="
    s!"({a.toString} {opStr} {b.toString})"
  | .not e => s!"!{e.toString}"
  | .and a b => s!"({a.toString} && {b.toString})"
  | .or a b => s!"({a.toString} || {b.toString})"

def Stmt.toString : Stmt → String
  | .skip => "skip"
  | .assign x e => s!"{x} := {e.toString}"
  | .bassign x b => s!"{x} := {b.toString}"
  | .seq s1 s2 => s!"{s1.toString};\n{s2.toString}"
  | .ite b s1 s2 => s!"if {b.toString} then\n  {s1.toString}\nelse\n  {s2.toString}"
  | .loop b body => s!"while {b.toString} do\n  {body.toString}"

instance : ToString Stmt := ⟨Stmt.toString⟩
instance : ToString SExpr := ⟨SExpr.toString⟩
instance : ToString SBool := ⟨SBool.toString⟩
