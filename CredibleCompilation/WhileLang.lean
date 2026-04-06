import CredibleCompilation.Semantics
import CredibleCompilation.PropChecker

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

The reference compiler (`RefCompiler.lean`) provides a verified alternative
with a complete correctness proof and zero sorry holes.
-/

-- ============================================================
-- § 1. Source language AST
-- ============================================================

/-- Arithmetic expressions (tree-structured, unlike TAC operands). -/
inductive SExpr where
  | lit     : Int → SExpr
  | var     : Var → SExpr
  | bin     : BinOp → SExpr → SExpr → SExpr
  | arrRead : ArrayName → SExpr → SExpr          -- arr[idx]
  deriving Repr

/-- Boolean expressions over arithmetic sub-expressions. -/
inductive SBool where
  | lit  : Bool → SBool                          -- true / false literal
  | bvar : Var → SBool                           -- read a boolean variable
  | cmp  : CmpOp → SExpr → SExpr → SBool
  | not  : SBool → SBool
  | and      : SBool → SBool → SBool
  | or       : SBool → SBool → SBool
  | barrRead : ArrayName → SExpr → SBool        -- arr[idx] (boolean array read)
  deriving Repr

/-- Statements. -/
inductive Stmt where
  | skip     : Stmt
  | assign   : Var → SExpr → Stmt               -- integer assignment
  | bassign  : Var → SBool → Stmt               -- boolean assignment
  | arrWrite  : ArrayName → SExpr → SExpr → Stmt  -- arr[idx] := val (int)
  | barrWrite : ArrayName → SExpr → SBool → Stmt  -- arr[idx] := bval (bool)
  | seq      : Stmt → Stmt → Stmt
  | ite      : SBool → Stmt → Stmt → Stmt       -- if-then-else
  | loop     : SBool → Stmt → Stmt
  deriving Repr

-- Syntactic sugar
infixr:30 " ;; " => Stmt.seq

-- ============================================================
-- § 2. Direct interpretation (for testing / specification)
-- ============================================================

/-- Evaluate an arithmetic expression. Returns BitVec 64; reads integer
    values from the store via `.toInt`. -/
def SExpr.eval (σ : Store) (am : ArrayMem) : SExpr → BitVec 64
  | .lit n      => BitVec.ofInt 64 n
  | .var x      => (σ x).toInt
  | .bin op a b => op.eval (a.eval σ am) (b.eval σ am)
  | .arrRead arr idx => am.read arr (idx.eval σ am).toNat

/-- Evaluate a boolean expression. -/
def SBool.eval (σ : Store) (am : ArrayMem) : SBool → Bool
  | .lit b      => b
  | .bvar x     => (σ x).toBool
  | .cmp op a b => op.eval (a.eval σ am) (b.eval σ am)
  | .not e      => !e.eval σ am
  | .and a b    => a.eval σ am && b.eval σ am
  | .or a b        => a.eval σ am || b.eval σ am
  | .barrRead arr idx => (am.read arr (idx.eval σ am).toNat) != 0

/-- Check whether an arithmetic expression is safe to evaluate (no div-by-zero,
    array accesses in bounds). Returns `Bool` for use in `Stmt.interp`. -/
def SExpr.isSafe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .bin .div a b => a.isSafe σ am decls && b.isSafe σ am decls && decide (b.eval σ am ≠ 0)
  | .bin .mod a b => a.isSafe σ am decls && b.isSafe σ am decls && decide (b.eval σ am ≠ 0)
  | .bin _ a b => a.isSafe σ am decls && b.isSafe σ am decls
  | .arrRead arr idx => idx.isSafe σ am decls && decide ((idx.eval σ am).toNat < arraySize decls arr)

/-- Check whether a boolean expression is safe to evaluate. -/
def SBool.isSafe (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : SBool → Bool
  | .lit _ => true
  | .bvar _ => true
  | .cmp _ a b => a.isSafe σ am decls && b.isSafe σ am decls
  | .not e => e.isSafe σ am decls
  | .and a b => a.isSafe σ am decls && (if a.eval σ am then b.isSafe σ am decls else true)
  | .or a b => a.isSafe σ am decls && (if !(a.eval σ am) then b.isSafe σ am decls else true)
  | .barrRead arr idx => idx.isSafe σ am decls && decide ((idx.eval σ am).toNat < arraySize decls arr)

/-- Interpret a statement directly, with a fuel bound to ensure termination.
    Returns `none` if out of fuel or if a safety check fails (div-by-zero, array out-of-bounds). -/
def Stmt.interp (fuel : Nat) (σ : Store) (am : ArrayMem)
    (decls : List (ArrayName × Nat × VarTy)) : Stmt → Option (Store × ArrayMem)
  | .skip        => some (σ, am)
  | .assign x e  =>
    if e.isSafe σ am decls then some (σ[x ↦ .int (e.eval σ am)], am) else none
  | .bassign x b =>
    if b.isSafe σ am decls then some (σ[x ↦ .bool (b.eval σ am)], am) else none
  | .arrWrite arr idx val =>
    if idx.isSafe σ am decls && val.isSafe σ am decls &&
       decide ((idx.eval σ am).toNat < arraySize decls arr)
    then some (σ, am.write arr (idx.eval σ am).toNat (val.eval σ am))
    else none
  | .barrWrite arr idx bval =>
    if (idx : SExpr).isSafe σ am decls && bval.isSafe σ am decls &&
       decide ((idx.eval σ am).toNat < arraySize decls arr)
    then let b := bval.eval σ am
         let v : BitVec 64 := if b then 1 else 0
         some (σ, am.write arr (idx.eval σ am).toNat v)
    else none
  | .seq s1 s2   => do
    let (σ', am') ← s1.interp fuel σ am decls
    s2.interp fuel σ' am' decls
  | .ite b s1 s2 =>
    if b.isSafe σ am decls then
      if b.eval σ am then s1.interp fuel σ am decls else s2.interp fuel σ am decls
    else none
  | .loop b body =>
    match fuel with
    | 0 => none  -- out of fuel
    | fuel' + 1 =>
      if b.isSafe σ am decls then
        if b.eval σ am then do
          let (σ', am') ← body.interp fuel' σ am decls
          (Stmt.loop b body).interp fuel' σ' am' decls
        else some (σ, am)
      else none

-- ============================================================
-- § 3. Compiler: While language → TAC (pure functional)
-- ============================================================

/-- Temporary variable name from index. -/
def tmpName (k : Nat) : Var := s!"__t{k}"

/-- A variable is a temporary iff its name starts with `__t`.
    Defined on `String` so dot notation works (since `Var` is `abbrev String`). -/
def String.isTmp (v : String) : Bool :=
  match v.toList with
  | '_' :: '_' :: 't' :: _ => true
  | _ => false

/-- Compile an arithmetic expression. Returns (code, result variable, next temp index).
    Pre-computes code lengths so no patching is needed. -/
def compileExpr (e : SExpr) (offset nextTmp : Nat) : List TAC × Var × Nat :=
  match e with
  | .lit n =>
    let t := tmpName nextTmp
    ([.const t (.int (BitVec.ofInt 64 n))], t, nextTmp + 1)
  | .var x => ([], x, nextTmp)
  | .bin op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    let t := tmpName tmp2
    (codeA ++ codeB ++ [.binop t op va vb], t, tmp2 + 1)
  | .arrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let t := tmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .int], t, tmp1 + 1)

/-- Compile a boolean expression. Returns (code, BoolExpr, next temp index). -/
def compileBool (b : SBool) (offset nextTmp : Nat) : List TAC × BoolExpr × Nat :=
  match b with
  | .lit b => ([], .lit b, nextTmp)
  | .bvar x => ([], .bvar x, nextTmp)
  | .cmp op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    (codeA ++ codeB, .cmp op va vb, tmp2)
  | .not e =>
    let (code, be, tmp') := compileBool e offset nextTmp
    (code, .not be, tmp')
  | .and a b =>
    -- Flatten a && b: if !a goto false; if !b goto false; tR := 1; goto end; false: tR := 0; end:
    let (codeA, ba, tmp1) := compileBool a offset nextTmp
    let tR := tmpName tmp1
    let (codeB, bb, tmp2) := compileBool b (offset + codeA.length + 1) (tmp1 + 1)
    -- Layout:
    --   codeA                        -- evaluate a's subexpressions
    --   ifgoto (not ba) falseL       -- if !a goto false
    --   codeB                        -- evaluate b's subexpressions
    --   ifgoto (not bb) falseL       -- if !b goto false
    --   const tR (.int 1)            -- both true → tR = 1
    --   goto endL
    --   falseL: const tR (.int 0)    -- at least one false → tR = 0
    --   endL: ...
    let afterCodeB := offset + codeA.length + 1 + codeB.length
    let falseL := afterCodeB + 3  -- after ifgoto + const + goto
    let endL := falseL + 1
    let code := codeA ++
      [TAC.ifgoto (.not ba) falseL] ++
      codeB ++
      [TAC.ifgoto (.not bb) falseL,
       TAC.const tR (.int (1 : BitVec 64)),
       TAC.goto endL,
       TAC.const tR (.int (0 : BitVec 64))]
    (code, .cmpLit .ne tR 0, tmp2)
  | .or a b =>
    -- Flatten a || b: if a goto true; if b goto true; tR := 0; goto end; true: tR := 1; end:
    let (codeA, ba, tmp1) := compileBool a offset nextTmp
    let tR := tmpName tmp1
    let (codeB, bb, tmp2) := compileBool b (offset + codeA.length + 1) (tmp1 + 1)
    let afterCodeB := offset + codeA.length + 1 + codeB.length
    let trueL := afterCodeB + 3
    let endL := trueL + 1
    let code := codeA ++
      [TAC.ifgoto ba trueL] ++
      codeB ++
      [TAC.ifgoto bb trueL,
       TAC.const tR (.int (0 : BitVec 64)),
       TAC.goto endL,
       TAC.const tR (.int (1 : BitVec 64))]
    (code, .cmpLit .ne tR 0, tmp2)
  | .barrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let t := tmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .int], .cmpLit .ne t 0, tmp1 + 1)

/-- Compile a statement. Returns (code, next temp index).
    Jump targets are pre-computed from code lengths. -/
def compileStmt (s : Stmt) (offset nextTmp : Nat) : List TAC × Nat :=
  match s with
  | .skip => ([], nextTmp)
  | .assign x e =>
    match e with
    | .lit n => ([.const x (.int (BitVec.ofInt 64 n))], nextTmp)
    | .var y => ([.copy x y], nextTmp)
    | .bin op a b =>
      let (codeA, va, tmp1) := compileExpr a offset nextTmp
      let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
      (codeA ++ codeB ++ [.binop x op va vb], tmp2)
    | .arrRead arr idx =>
      let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
      let t := tmpName tmp1
      (codeIdx ++ [.arrLoad t arr vIdx .int, .copy x t], tmp1 + 1)
  | .bassign x b =>
    let (code, be, tmp') := compileBool b offset nextTmp
    (code ++ [.boolop x be], tmp')
  | .arrWrite arr idx val =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let (codeVal, vVal, tmp2) := compileExpr val (offset + codeIdx.length) tmp1
    (codeIdx ++ codeVal ++ [.arrStore arr vIdx vVal .int], tmp2)
  | .barrWrite arr idx bval =>
    let (codeIdx, vIdx, tmp1) := compileExpr idx offset nextTmp
    let (codeBool, be, tmp2) := compileBool bval (offset + codeIdx.length) tmp1
    let tInt := tmpName tmp2
    -- Convert bool expression to int 0/1: if be then tInt := 1 else tInt := 0
    let afterCodeBool := offset + codeIdx.length + codeBool.length
    let trueL := afterCodeBool + 3  -- ifgoto + const 0 + goto
    let endL := trueL + 1
    let convCode : List TAC :=
      [TAC.ifgoto be trueL,
       TAC.const tInt (.int (0 : BitVec 64)),
       TAC.goto endL,
       TAC.const tInt (.int (1 : BitVec 64))]
    (codeIdx ++ codeBool ++ convCode ++ [.arrStore arr vIdx tInt .int], tmp2 + 1)
  | .seq s1 s2 =>
    let (code1, tmp1) := compileStmt s1 offset nextTmp
    let (code2, tmp2) := compileStmt s2 (offset + code1.length) tmp1
    (code1 ++ code2, tmp2)
  | .ite b s1 s2 =>
    let (codeB, be, tmpB) := compileBool b offset nextTmp
    -- ifgoto be <then>; <else code>; goto <end>; <then code>
    let elseStart := offset + codeB.length + 1
    let (codeElse, tmpE) := compileStmt s2 elseStart tmpB
    let thenStart := elseStart + codeElse.length + 1
    let (codeThen, tmpT) := compileStmt s1 thenStart tmpE
    let endLabel := thenStart + codeThen.length
    (codeB ++ [.ifgoto be thenStart] ++ codeElse ++ [.goto endLabel] ++ codeThen, tmpT)
  | .loop b body =>
    let condLabel := offset
    let (codeB, be, tmpB) := compileBool b offset nextTmp
    let bodyStart := offset + codeB.length + 1
    let (codeBody, tmpBody) := compileStmt body bodyStart tmpB
    let exitLabel := bodyStart + codeBody.length + 1
    (codeB ++ [.ifgoto (.not be) exitLabel] ++ codeBody ++ [.goto condLabel], tmpBody)

/-- Compile a while-language program to a TAC program.
    Appends `halt` at the end. -/
def compile (s : Stmt) : Prog :=
  let (code, _) := compileStmt s 0 0
  .ofCode (code ++ [TAC.halt]).toArray

-- ============================================================
-- § 4. Pretty-printing
-- ============================================================

def SExpr.toString : SExpr → String
  | .lit n => s!"{n}"
  | .var x => x
  | .bin op a b =>
    let opStr := match op with | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
    s!"({a.toString} {opStr} {b.toString})"
  | .arrRead arr idx => s!"{arr}[{idx.toString}]"

def SBool.toString : SBool → String
  | .lit true => "true"
  | .lit false => "false"
  | .bvar x => x
  | .cmp op a b =>
    let opStr := match op with | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="
    s!"({a.toString} {opStr} {b.toString})"
  | .not e => s!"!{e.toString}"
  | .and a b => s!"({a.toString} && {b.toString})"
  | .or a b => s!"({a.toString} || {b.toString})"
  | .barrRead arr idx => s!"{arr}[{idx.toString}]"

def Stmt.toString : Stmt → String
  | .skip => "skip"
  | .assign x e => s!"{x} := {e.toString}"
  | .bassign x b => s!"{x} := {b.toString}"
  | .arrWrite arr idx val => s!"{arr}[{idx.toString}] := {val.toString}"
  | .barrWrite arr idx bval => s!"{arr}[{idx.toString}] := {bval.toString}"
  | .seq s1 s2 => s!"{s1.toString};\n{s2.toString}"
  | .ite b s1 s2 => s!"if {b.toString} then\n  {s1.toString}\nelse\n  {s2.toString}"
  | .loop b body => s!"while {b.toString} do\n  {body.toString}"

instance : ToString Stmt := ⟨Stmt.toString⟩
instance : ToString SExpr := ⟨SExpr.toString⟩
instance : ToString SBool := ⟨SBool.toString⟩

-- ============================================================
-- § 5. Typed programs with static type checking
-- ============================================================

/-- A typed program: explicit variable declarations followed by a statement body.
    All variables used in the body must be declared with their type.
    This enables static type checking that guarantees no type errors at runtime. -/
structure Program where
  decls      : List (Var × VarTy)
  arrayDecls : List (ArrayName × Nat × VarTy) := []
  body       : Stmt
  deriving Repr

namespace Program

/-- Look up a variable's declared type. -/
def lookupTy (prog : Program) (x : Var) : Option VarTy :=
  prog.decls.lookup x

/-- Build a total TyCtx from declarations. Undeclared variables default to `.int`
    (matching `Store.init`). -/
def tyCtx (prog : Program) : TyCtx :=
  fun x => (prog.lookupTy x).getD .int

-- ============================================================
-- § 5a. Static type checker
-- ============================================================

/-- No duplicate variable declarations. -/
private def noDups : List Var → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDups xs

/-- No declared variable uses a compiler-reserved temporary name (`__t`-prefixed).
    Required so that compiler-generated integer temporaries are always typed as `.int`
    by `tyCtx` (which maps undeclared variables to `.int` by default).
    Not private: used by `CompilerCorrectness.typeCheck_tmpFree`. -/
def noTmpDecls (decls : List (Var × VarTy)) : Bool :=
  decls.all fun (x, _) => !x.isTmp

/-- Check that an array name is declared. -/
private def arrayDeclared (arrayDecls : List (ArrayName × Nat × VarTy)) (arr : ArrayName) : Bool :=
  arrayDecls.any fun (a, _, _) => a == arr

/-- Check that all variables in an arithmetic expression are declared as `int`,
    and all array names are declared. -/
def checkSExpr (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) : SExpr → Bool
  | .lit _ => true
  | .var x => lookup x == some .int
  | .bin _ a b => checkSExpr lookup arrayDecls a && checkSExpr lookup arrayDecls b
  | .arrRead arr idx => arrayDeclared arrayDecls arr && checkSExpr lookup arrayDecls idx

/-- Check that a boolean expression uses properly-typed declared variables. -/
def checkSBool (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) : SBool → Bool
  | .lit _ => true
  | .bvar x => lookup x == some .bool
  | .cmp _ a b => checkSExpr lookup arrayDecls a && checkSExpr lookup arrayDecls b
  | .not e => checkSBool lookup arrayDecls e
  | .and a b => checkSBool lookup arrayDecls a && checkSBool lookup arrayDecls b
  | .or a b => checkSBool lookup arrayDecls a && checkSBool lookup arrayDecls b
  | .barrRead arr idx => arrayDeclared arrayDecls arr && checkSExpr lookup arrayDecls idx

/-- Check that a statement body is well-typed w.r.t. declarations. -/
def checkStmt (lookup : Var → Option VarTy) (arrayDecls : List (ArrayName × Nat × VarTy)) : Stmt → Bool
  | .skip => true
  | .assign x e => lookup x == some .int && checkSExpr lookup arrayDecls e
  | .bassign x b => lookup x == some .bool && checkSBool lookup arrayDecls b
  | .arrWrite arr idx val =>
    arrayDeclared arrayDecls arr && checkSExpr lookup arrayDecls idx && checkSExpr lookup arrayDecls val
  | .barrWrite arr idx bval =>
    arrayDeclared arrayDecls arr && checkSExpr lookup arrayDecls idx && checkSBool lookup arrayDecls bval
  | .seq s1 s2 => checkStmt lookup arrayDecls s1 && checkStmt lookup arrayDecls s2
  | .ite b s1 s2 =>
    checkSBool lookup arrayDecls b && checkStmt lookup arrayDecls s1 && checkStmt lookup arrayDecls s2
  | .loop b body => checkSBool lookup arrayDecls b && checkStmt lookup arrayDecls body

/-- Full static type check: no duplicate declarations, no compiler-reserved
    temporary names in declarations, and the body is well-typed w.r.t.
    the declared variable types. -/
def typeCheck (prog : Program) : Bool :=
  noDups (prog.decls.map Prod.fst) &&
  noTmpDecls prog.decls &&
  checkStmt prog.lookupTy prog.arrayDecls prog.body

-- ============================================================
-- § 5b. Compilation
-- ============================================================

/-- Emit initialization code for declared variables. -/
private def initCode (decls : List (Var × VarTy)) : List TAC :=
  decls.map fun (x, ty) =>
    match ty with
    | .int  => .const x (.int (0 : BitVec 64))
    | .bool => .const x (.bool false)

/-- Compile a typed program: initialize declared variables, then compile body.
    Appends `halt` at the end. -/
def compile (prog : Program) : Prog :=
  let inits := initCode prog.decls
  let (body, _) := compileStmt prog.body inits.length 0
  { code := (inits ++ body ++ [TAC.halt]).toArray
    tyCtx := prog.tyCtx
    observable := prog.decls.map Prod.fst
    arrayDecls := prog.arrayDecls }


-- ============================================================
-- § 5c. Interpretation
-- ============================================================

/-- Build an initial store from declarations with type-appropriate defaults.
    Int variables get 0, bool variables get false. -/
def initStore (prog : Program) : Store :=
  prog.decls.foldl (fun σ (x, ty) =>
    match ty with
    | .int  => σ[x ↦ .int (0 : BitVec 64)]
    | .bool => σ[x ↦ .bool false]) Store.init

/-- Interpret a typed program. Starts from the declaration-initialized store,
    with optional input overrides. -/
def interp (prog : Program) (fuel : Nat)
    (inputs : List (Var × Value) := []) : Option (Store × ArrayMem) :=
  let σ₀ := inputs.foldl (fun σ (x, v) => σ[x ↦ v]) prog.initStore
  prog.body.interp fuel σ₀ ArrayMem.init prog.arrayDecls

-- ============================================================
-- § 5d. initStore is well-typed
-- ============================================================

-- The fold step for initStore
private def initFold (σ : Store) (p : Var × VarTy) : Store :=
  match p.2 with
  | .int  => σ[p.1 ↦ .int (0 : BitVec 64)]
  | .bool => σ[p.1 ↦ .bool false]

-- `contains` false implies not a member (for Var = String with LawfulBEq)
private theorem notMem_of_contains_false {x : Var} {xs : List Var}
    (h : xs.contains x = false) : x ∉ xs := by
  intro hmem
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := h
    cases hmem with
    | head => simp at h1
    | tail _ hmem => exact ih h2 hmem

-- Fold over decls does not change variables not in the domain
private theorem initFold_notMem (ds : List (Var × VarTy)) (σ : Store) (x : Var)
    (h : x ∉ ds.map Prod.fst) :
    ds.foldl initFold σ x = σ x := by
  induction ds generalizing σ with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, hnot⟩ := h
    simp only [List.foldl, initFold]
    rw [ih _ hnot]
    -- update(y, ...) x = σ x since x ≠ y
    have hbeq : (x == y) = false := by simp [hne]
    cases ty <;> simp [Store.update, hbeq]

-- Core lemma: the fold value type matches lookup default
private theorem initFold_typeOf (ds : List (Var × VarTy)) (σ : Store) (x : Var)
    (hnd : noDups (ds.map Prod.fst) = true) :
    (ds.foldl initFold σ x).typeOf = (ds.lookup x).getD (σ x).typeOf := by
  induction ds generalizing σ with
  | nil => simp [List.lookup]
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [List.map_cons, noDups, Bool.not_eq_true', Bool.and_eq_true] at hnd
    obtain ⟨hny, hnd_rest⟩ := hnd
    have hny_notMem : y ∉ rest.map Prod.fst := notMem_of_contains_false hny
    simp only [List.foldl, List.lookup_cons]
    by_cases hxy : x = y
    · -- x = y: update sets x, rest never touches it (no dup)
      subst hxy
      simp only [beq_self_eq_true]
      rw [initFold_notMem rest _ x hny_notMem]
      cases ty <;> simp [initFold, Store.update_self, Value.typeOf]
    · -- x ≠ y: lookup skips y, initFold(y,..) leaves x unchanged
      have hbeq : (x == y) = false := by simp [hxy]
      simp only [hbeq]
      rw [ih _ hnd_rest]
      -- initFold (σ[y ↦ v]) x = σ x since x ≠ y
      cases ty <;> simp [initFold, Store.update, hbeq]

/-- The initial store from declarations is well-typed w.r.t. the program's TyCtx. -/
theorem initStore_typedStore (prog : Program)
    (hnd : noDups (prog.decls.map Prod.fst) = true) :
    TypedStore prog.tyCtx prog.initStore := by
  intro x
  simp only [initStore, tyCtx, lookupTy]
  -- The foldl in initStore is definitionally equal to foldl initFold
  show (prog.decls.foldl initFold Store.init x).typeOf = _
  rw [initFold_typeOf prog.decls Store.init x hnd]
  simp [Store.init, Value.typeOf]

/-- Extract noDups from typeCheck (public, so other files can use it). -/
theorem typeCheck_noDups (prog : Program) (h : prog.typeCheck = true) :
    noDups (prog.decls.map Prod.fst) = true := by
  simp [typeCheck, Bool.and_eq_true] at h; exact h.1.1

/-- If a program type-checks, its initial store is well-typed. -/
theorem typeCheck_initStore_typedStore (prog : Program) (h : prog.typeCheck = true) :
    TypedStore prog.tyCtx prog.initStore :=
  initStore_typedStore prog (typeCheck_noDups prog h)

-- ============================================================
-- § 5d'. initStore declared-variable values and init code execution
-- ============================================================

/-- For a declared variable in a no-dup list, the fold assigns its default value. -/
private theorem initFold_declared (ds : List (Var × VarTy)) (σ : Store) (x : Var) (ty : VarTy)
    (hmem : (x, ty) ∈ ds) (hnd : noDups (ds.map Prod.fst) = true) :
    ds.foldl initFold σ x = ty.defaultVal := by
  induction ds generalizing σ with
  | nil => contradiction
  | cons hd rest ih =>
    simp only [List.map_cons, noDups, Bool.not_eq_true', Bool.and_eq_true] at hnd
    obtain ⟨hny, hnd_rest⟩ := hnd
    simp only [List.foldl]
    cases hmem with
    | head =>
      rw [initFold_notMem rest _ x (notMem_of_contains_false hny)]
      cases ty <;> simp [initFold, Store.update_self, VarTy.defaultVal]
    | tail _ hmem_rest =>
      exact ih (initFold σ hd) hmem_rest hnd_rest

/-- For each declared variable, `initStore` holds the type-appropriate default. -/
theorem initStore_declared (prog : Program) {x : Var} {ty : VarTy}
    (hmem : (x, ty) ∈ prog.decls) (hnd : noDups (prog.decls.map Prod.fst) = true) :
    prog.initStore x = ty.defaultVal :=
  initFold_declared prog.decls Store.init x ty hmem hnd

/-- `initCode` has the same length as the declaration list. -/
private theorem initCode_length (decls : List (Var × VarTy)) :
    (initCode decls).length = decls.length := by
  simp [initCode, List.length_map]

/-- Running init code from `initStore` is idempotent: each `const x v` sets a variable
    that already holds `v`, so the store is unchanged. -/
theorem compile_initExec (prog : Program)
    (hnd : noDups (prog.decls.map Prod.fst) = true) :
    prog.compile ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* Cfg.run prog.decls.length prog.initStore ArrayMem.init := by
  suffices h : ∀ (k : Nat), k ≤ prog.decls.length →
      prog.compile ⊩ Cfg.run 0 prog.initStore ArrayMem.init ⟶* Cfg.run k prog.initStore ArrayMem.init from
    h prog.decls.length (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact Steps.refl
  | succ k ih =>
    have ih_steps := ih (by omega)
    have hk_lt : k < prog.decls.length := by omega
    -- The k-th declaration and its init instruction
    have hmem_decl : prog.decls[k] ∈ prog.decls := List.getElem_mem hk_lt
    have hval := initStore_declared prog hmem_decl hnd
    -- The const step is a no-op because the value is already present
    have hstep : Step prog.compile (.run k prog.initStore ArrayMem.init)
        (.run (k + 1) prog.initStore ArrayMem.init) := by
      -- Normalize get/getElem
      have hget : prog.decls.get ⟨k, hk_lt⟩ = prog.decls[k] := rfl
      rw [hget] at hval
      -- Case split on the type of the k-th declaration
      cases hty : (prog.decls[k]).2 with
      | int =>
        simp only [hty, VarTy.defaultVal] at hval
        have hinst : prog.compile[k]? =
            some (.const (prog.decls[k]).1 (.int 0)) := by
          simp only [Prog.getElem?_code, Program.compile, List.getElem?_toArray]
          rw [List.getElem?_append_left (by rw [List.length_append, initCode_length]; omega)]
          rw [List.getElem?_append_left (by rw [initCode_length]; omega)]
          simp only [initCode, List.getElem?_map, List.getElem?_eq_getElem hk_lt,
            Option.map_some, hty]
        have := Step.const hinst (σ := prog.initStore) (am := ArrayMem.init)
        rwa [Store.update_of_eq _ _ _ hval] at this
      | bool =>
        simp only [hty, VarTy.defaultVal] at hval
        have hinst : prog.compile[k]? =
            some (.const (prog.decls[k]).1 (.bool false)) := by
          simp only [Prog.getElem?_code, Program.compile, List.getElem?_toArray]
          rw [List.getElem?_append_left (by rw [List.length_append, initCode_length]; omega)]
          rw [List.getElem?_append_left (by rw [initCode_length]; omega)]
          simp only [initCode, List.getElem?_map, List.getElem?_eq_getElem hk_lt,
            Option.map_some, hty]
        have := Step.const hinst (σ := prog.initStore) (am := ArrayMem.init)
        rwa [Store.update_of_eq _ _ _ hval] at this
    exact Steps.trans ih_steps (Steps.step hstep Steps.refl)

/-- Index into body code within `prog.compile`. The body starts at offset `decls.length`. -/
theorem compile_body_getElem (prog : Program) (i : Nat)
    (hi : i < (compileStmt prog.body prog.decls.length 0).1.length) :
    prog.compile[prog.decls.length + i]? =
      (compileStmt prog.body prog.decls.length 0).1[i]? := by
  simp only [Prog.getElem?_code, Program.compile, List.getElem?_toArray]
  rw [List.getElem?_append_left (by rw [List.length_append, initCode_length]; omega)]
  rw [List.getElem?_append_right (by rw [initCode_length]; omega)]
  simp [initCode_length]

/-- The halt instruction sits right after the body code in `prog.compile`. -/
theorem compile_halt_getElem (prog : Program) :
    prog.compile[prog.decls.length +
      (compileStmt prog.body prog.decls.length 0).1.length]? = some .halt := by
  simp only [Prog.getElem?_code, Program.compile, List.getElem?_toArray]
  rw [List.getElem?_append_right (by rw [List.length_append, initCode_length]; omega)]
  simp [List.length_append, initCode_length]

-- ============================================================
-- § 5e. Executable well-typedness check for compiled output
-- ============================================================

/-- Check that every instruction in a compiled program is well-typed. -/
def checkWellTypedProg (Γ : TyCtx) (p : Prog) : Bool :=
  (List.range p.size).all fun i =>
    match p[i]? with
    | some instr => checkWellTypedInstr Γ instr
    | none => true

/-- Executable verification: if the source type-checks, the compiled TAC
    is well-typed under the program's TyCtx. -/
def verifyWellTyped (prog : Program) : Bool :=
  prog.typeCheck && checkWellTypedProg prog.tyCtx prog.compile

-- ============================================================
-- § 5f. Soundness: type checking ⟹ compiled TAC is well-typed
-- ============================================================

end Program  -- temporarily close namespace for helper definitions

-- Helper: every element of a list satisfies WellTypedInstr
def AllWTI (Γ : TyCtx) (l : List TAC) : Prop :=
  ∀ instr, instr ∈ l → WellTypedInstr Γ instr

theorem allWTI_nil' (Γ : TyCtx) : AllWTI Γ List.nil := by
  intro _ h; simp at h

theorem allWTI_cons' {Γ : TyCtx} {x : TAC} {xs : List TAC}
    (hx : WellTypedInstr Γ x) (hxs : AllWTI Γ xs) :
    AllWTI Γ (x :: xs) := by
  intro instr hmem
  simp at hmem
  rcases hmem with rfl | hmem
  · exact hx
  · exact hxs instr hmem

theorem allWTI_one {Γ : TyCtx} {x : TAC}
    (h : WellTypedInstr Γ x) : AllWTI Γ (x :: List.nil) :=
  allWTI_cons' h (allWTI_nil' Γ)

theorem allWTI_append' {Γ : TyCtx} {l1 l2 : List TAC}
    (h1 : AllWTI Γ l1) (h2 : AllWTI Γ l2) :
    AllWTI Γ (l1 ++ l2) := by
  intro instr hmem
  simp at hmem
  rcases hmem with h | h
  · exact h1 instr h
  · exact h2 instr h

theorem allWTI_append3 {Γ : TyCtx} {l1 l2 l3 : List TAC}
    (h1 : AllWTI Γ l1) (h2 : AllWTI Γ l2) (h3 : AllWTI Γ l3) :
    AllWTI Γ (l1 ++ l2 ++ l3) :=
  allWTI_append' (allWTI_append' h1 h2) h3

theorem allWTI_toArray' {Γ : TyCtx} {l : List TAC} {p : Prog}
    (hcode : p.code = l.toArray)
    (h : AllWTI Γ l) : WellTypedProg Γ p := by
  intro i hi
  have hi' : i < l.length := by rw [Prog.size, hcode] at hi; simp at hi; exact hi
  have hmem : l[i] ∈ l := List.getElem_mem hi'
  show WellTypedInstr Γ p[i]
  have : p[i] = l[i] := by simp [Prog.getElem_eq, hcode, List.getElem_toArray]
  rw [this]
  exact h _ hmem

-- If (x, ty) ∈ decls and noDups, then lookup x = some ty
theorem lookup_of_mem_noDups_wt {decls : List (Var × VarTy)} {x : Var} {ty : VarTy}
    (hmem : (x, ty) ∈ decls) (hnd : Program.noDups (decls.map Prod.fst) = true) :
    decls.lookup x = some ty := by
  induction decls with
  | nil => simp at hmem
  | cons hd rest ih =>
    obtain ⟨y, ty'⟩ := hd
    simp only [List.map_cons, Program.noDups, Bool.not_eq_true', Bool.and_eq_true] at hnd
    obtain ⟨hny, hnd_rest⟩ := hnd
    simp at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_rest
    · simp [List.lookup]
    · simp only [List.lookup_cons]
      by_cases hxy : x == y
      · simp at hxy; subst hxy
        have : x ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(x, ty), hmem_rest, rfl⟩
        exact absurd this (Program.notMem_of_contains_false hny)
      · simp [hxy]
        exact ih hmem_rest hnd_rest

-- If noTmpDecls and x.isTmp, then lookup returns none
theorem lookup_none_of_isTmp_wt {decls : List (Var × VarTy)}
    (hnt : Program.noTmpDecls decls = true) {x : Var} (hx : x.isTmp = true) :
    decls.lookup x = none := by
  induction decls with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [Program.noTmpDecls, List.all_cons, Bool.and_eq_true] at hnt
    obtain ⟨hny, hnt_rest⟩ := hnt
    simp only [List.lookup_cons]
    have hne : (x == y) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro heq; subst heq
      simp only [Bool.not_eq_true'] at hny
      rw [hx] at hny; exact Bool.noConfusion hny
    simp only [hne, ite_false]
    exact ih hnt_rest

-- tmpName k is a temporary variable
theorem tmpName_isTmp_wt (k : Nat) : (tmpName k).isTmp = true := by
  simp only [String.isTmp, tmpName, String.toList_append]
  show (match '_' :: '_' :: 't' :: (toString k).toList with
    | '_' :: '_' :: 't' :: _ => true | _ => false) = true
  rfl

-- tyCtx maps temporaries to .int
theorem tyCtx_tmp_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true) (k : Nat) :
    prog.tyCtx (tmpName k) = .int := by
  unfold Program.tyCtx Program.lookupTy
  rw [lookup_none_of_isTmp_wt hnt (tmpName_isTmp_wt k)]
  rfl

-- If lookupTy x = some ty, then tyCtx x = ty
theorem tyCtx_of_lookup_wt (prog : Program) (x : Var) (ty : VarTy)
    (h : prog.lookupTy x = some ty) : prog.tyCtx x = ty := by
  unfold Program.tyCtx
  rw [h]; rfl

-- compileExpr produces well-typed instructions and the result var has type .int
theorem compileExpr_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (e : SExpr) (hchk : Program.checkSExpr prog.lookupTy prog.arrayDecls e = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx (compileExpr e offset nextTmp).1
    ∧ prog.tyCtx (compileExpr e offset nextTmp).2.1 = .int := by
  induction e generalizing offset nextTmp with
  | lit n =>
    simp only [compileExpr]
    exact ⟨allWTI_one (.const (by simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt _).symm)),
           tyCtx_tmp_wt prog hnt _⟩
  | var x =>
    simp only [compileExpr]
    constructor
    · exact allWTI_nil' _
    · simp [Program.checkSExpr, beq_iff_eq] at hchk
      exact tyCtx_of_lookup_wt prog x .int hchk
  | bin op a b iha ihb =>
    simp [Program.checkSExpr, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := iha hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := ihb hcb
      (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2
    simp only [compileExpr]
    constructor
    · exact allWTI_append3 ha_wt hb_wt
        (allWTI_one (.binop (tyCtx_tmp_wt prog hnt _) ha_ty hb_ty))
    · exact tyCtx_tmp_wt prog hnt _
  | arrRead _arr idx ih =>
    simp [Program.checkSExpr, Bool.and_eq_true] at hchk
    have ⟨hi_wt, hi_ty⟩ := ih hchk.2 offset nextTmp
    simp only [compileExpr]
    exact ⟨allWTI_append' hi_wt (allWTI_one (.arrLoad (tyCtx_tmp_wt prog hnt _) hi_ty)),
           tyCtx_tmp_wt prog hnt _⟩

-- compileBool produces well-typed instructions and a WellTypedBoolExpr
theorem compileBool_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (b : SBool) (hchk : Program.checkSBool prog.lookupTy prog.arrayDecls b = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx (compileBool b offset nextTmp).1
    ∧ WellTypedBoolExpr prog.tyCtx (compileBool b offset nextTmp).2.1 := by
  induction b generalizing offset nextTmp with
  | lit b =>
    simp only [compileBool]
    exact ⟨allWTI_nil' _, .lit⟩
  | bvar x =>
    simp only [compileBool]
    constructor
    · exact allWTI_nil' _
    · simp [Program.checkSBool, beq_iff_eq] at hchk
      exact .bvar (tyCtx_of_lookup_wt prog x .bool hchk)
  | cmp op a b =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := compileExpr_wt prog hnt a hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := compileExpr_wt prog hnt b hcb
      (offset + (compileExpr a offset nextTmp).1.length)
      (compileExpr a offset nextTmp).2.2
    simp only [compileBool]
    exact ⟨allWTI_append' ha_wt hb_wt, .cmp ha_ty hb_ty⟩
  | not e ih =>
    simp [Program.checkSBool] at hchk
    have ⟨he_wt, he_ty⟩ := ih hchk offset nextTmp
    simp only [compileBool]
    exact ⟨he_wt, .not he_ty⟩
  | and a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := iha hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := ihb hcb
      (offset + (compileBool a offset nextTmp).1.length + 1)
      ((compileBool a offset nextTmp).2.2 + 1)
    simp only [compileBool]
    refine ⟨?_, .cmpLit (tyCtx_tmp_wt prog hnt _) (by native_decide) (by native_decide)⟩
    let tmp1 := (compileBool a offset nextTmp).2.2
    have htR : (Value.int 1).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    have htR0 : (Value.int 0).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    exact allWTI_append' (allWTI_append' (allWTI_append' ha_wt
      (allWTI_one (.ifgoto (.not ha_ty))))
      hb_wt)
      (allWTI_cons' (.ifgoto (.not hb_ty))
        (allWTI_cons' (.const htR)
          (allWTI_cons' .goto
            (allWTI_one (.const htR0)))))
  | or a b iha ihb =>

    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := iha hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := ihb hcb
      (offset + (compileBool a offset nextTmp).1.length + 1)
      ((compileBool a offset nextTmp).2.2 + 1)
    simp only [compileBool]
    refine ⟨?_, .cmpLit (tyCtx_tmp_wt prog hnt _) (by native_decide) (by native_decide)⟩
    let tmp1 := (compileBool a offset nextTmp).2.2
    have htR : (Value.int 0).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    have htR1 : (Value.int 1).typeOf = prog.tyCtx (tmpName tmp1) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt tmp1).symm
    exact allWTI_append' (allWTI_append' (allWTI_append' ha_wt
      (allWTI_one (.ifgoto ha_ty)))
      hb_wt)
      (allWTI_cons' (.ifgoto hb_ty)
        (allWTI_cons' (.const htR)
          (allWTI_cons' .goto
            (allWTI_one (.const htR1)))))
  | barrRead _arr idx =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hchk.2 offset nextTmp
    simp only [compileBool]
    exact ⟨allWTI_append' hi_wt (allWTI_one (.arrLoad (tyCtx_tmp_wt prog hnt _) hi_ty)),
           .cmpLit (tyCtx_tmp_wt prog hnt _) (by native_decide) (by native_decide)⟩

-- compileStmt produces well-typed instructions
theorem compileStmt_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (s : Stmt) (hchk : Program.checkStmt prog.lookupTy prog.arrayDecls s = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx (compileStmt s offset nextTmp).1 := by
  induction s generalizing offset nextTmp with
  | skip => simp [compileStmt]; exact allWTI_nil' _
  | assign x e =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hx, he⟩ := hchk
    have hxty : prog.tyCtx x = .int := tyCtx_of_lookup_wt prog x .int hx
    cases e with
    | lit n =>
      simp only [compileStmt]
      exact allWTI_one (.const (by simp [Value.typeOf]; exact hxty.symm))
    | var y =>
      simp only [compileStmt]
      simp [Program.checkSExpr] at he
      have hyty : prog.tyCtx y = .int := tyCtx_of_lookup_wt prog y .int he
      exact allWTI_one (.copy (by rw [hxty, hyty]))
    | bin op a b =>
      simp [Program.checkSExpr, Bool.and_eq_true] at he
      obtain ⟨ha, hb⟩ := he
      have ⟨ha_wt, ha_ty⟩ := compileExpr_wt prog hnt a ha offset nextTmp
      have ⟨hb_wt, hb_ty⟩ := compileExpr_wt prog hnt b hb
        (offset + (compileExpr a offset nextTmp).1.length)
        (compileExpr a offset nextTmp).2.2
      simp only [compileStmt]
      exact allWTI_append3 ha_wt hb_wt
        (allWTI_one (.binop hxty ha_ty hb_ty))
    | arrRead _arr idx =>
      simp [Program.checkSExpr, Bool.and_eq_true] at he
      have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx he.2 offset nextTmp
      simp only [compileStmt]
      have htmp_ty := tyCtx_tmp_wt prog hnt (compileExpr idx offset nextTmp).2.2
      exact allWTI_append' hi_wt
        (allWTI_cons' (.arrLoad htmp_ty hi_ty)
          (allWTI_one (.copy (by rw [hxty, htmp_ty]))))
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hx, hb⟩ := hchk
    have hxty : prog.tyCtx x = .bool := tyCtx_of_lookup_wt prog x .bool hx
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hb offset nextTmp
    simp only [compileStmt]
    exact allWTI_append' hb_wt (allWTI_one (.boolop hxty hb_ty))
  | arrWrite _arr idx val =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hv⟩ := hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hi offset nextTmp
    have ⟨hv_wt, hv_ty⟩ := compileExpr_wt prog hnt val hv
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2
    simp only [compileStmt]
    exact allWTI_append3 hi_wt hv_wt (allWTI_one (.arrStore hi_ty hv_ty))
  | barrWrite arr idx bval =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨_, hi⟩, hb⟩ := hchk
    have ⟨hi_wt, hi_ty⟩ := compileExpr_wt prog hnt idx hi offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt bval hb
      (offset + (compileExpr idx offset nextTmp).1.length)
      (compileExpr idx offset nextTmp).2.2
    simp only [compileStmt]
    have htR : (Value.int (0 : BitVec 64)).typeOf = prog.tyCtx (tmpName (compileBool bval (offset + (compileExpr idx offset nextTmp).1.length) (compileExpr idx offset nextTmp).2.2).2.2) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt _).symm
    have htR1 : (Value.int (1 : BitVec 64)).typeOf = prog.tyCtx (tmpName (compileBool bval (offset + (compileExpr idx offset nextTmp).1.length) (compileExpr idx offset nextTmp).2.2).2.2) := by
      simp [Value.typeOf]; exact (tyCtx_tmp_wt prog hnt _).symm
    exact allWTI_append'
      (allWTI_append'
        (allWTI_append' hi_wt hb_wt)
        (allWTI_cons' (.ifgoto hb_ty)
          (allWTI_cons' (.const htR)
            (allWTI_cons' .goto
              (allWTI_one (.const htR1))))))
      (allWTI_one (.arrStore hi_ty (tyCtx_tmp_wt prog hnt _)))
  | seq s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hc1, hc2⟩ := hchk
    simp only [compileStmt]
    exact allWTI_append' (ih1 hc1 offset nextTmp)
      (ih2 hc2 (offset + (compileStmt s1 offset nextTmp).1.length)
                (compileStmt s1 offset nextTmp).2)
  | ite b s1 s2 ih1 ih2 =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨⟨hcb, hc1⟩, hc2⟩ := hchk
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hcb offset nextTmp
    simp only [compileStmt]
    -- The compiled code is left-associated:
    -- ((((codeB ++ [ifgoto]) ++ codeElse) ++ [goto]) ++ codeThen)
    have h_else := ih2 hc2
      (offset + (compileBool b offset nextTmp).1.length + 1)
      (compileBool b offset nextTmp).2.2
    have h_then := ih1 hc1
      (offset + (compileBool b offset nextTmp).1.length + 1 +
        (compileStmt s2 (offset + (compileBool b offset nextTmp).1.length + 1)
          (compileBool b offset nextTmp).2.2).1.length + 1)
      (compileStmt s2 (offset + (compileBool b offset nextTmp).1.length + 1)
        (compileBool b offset nextTmp).2.2).2
    exact allWTI_append'
      (allWTI_append'
        (allWTI_append'
          (allWTI_append' hb_wt (allWTI_one (.ifgoto hb_ty)))
          h_else)
        (allWTI_one .goto))
      h_then
  | loop b body ih =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hcb, hcbody⟩ := hchk
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hcb offset nextTmp
    simp only [compileStmt]
    have h_body := ih hcbody
      (offset + (compileBool b offset nextTmp).1.length + 1)
      (compileBool b offset nextTmp).2.2
    exact allWTI_append'
      (allWTI_append'
        (allWTI_append' hb_wt (allWTI_one (.ifgoto (.not hb_ty))))
        h_body)
      (allWTI_one .goto)

-- initCode produces well-typed instructions
theorem initCode_wt (prog : Program)
    (hnd : Program.noDups (prog.decls.map Prod.fst) = true) :
    AllWTI prog.tyCtx (Program.initCode prog.decls) := by
  intro instr hmem
  simp only [Program.initCode, List.mem_map] at hmem
  obtain ⟨⟨x, ty⟩, hmem_decl, hgen⟩ := hmem
  have hlookup : prog.decls.lookup x = some ty :=
    lookup_of_mem_noDups_wt hmem_decl hnd
  have hty : prog.tyCtx x = ty := tyCtx_of_lookup_wt prog x ty hlookup
  cases ty with
  | int =>
    simp at hgen; subst hgen
    exact .const (by simp [Value.typeOf]; exact hty.symm)
  | bool =>
    simp at hgen; subst hgen
    exact .const (by simp [Value.typeOf]; exact hty.symm)

namespace Program  -- reopen namespace

/-- **Key theorem**: A program that passes the static type checker compiles to
    a well-typed TAC program. Combined with the progress theorem from Semantics,
    this guarantees that no type errors can occur at runtime — only division by
    zero can cause the program to get stuck.

    Note: `prog.tyCtx` maps declared variables to their declared type, and
    all undeclared variables (including compiler temporaries `__tN`) to `.int`.
    This works because the compiler only generates integer temporaries. -/
theorem compile_wellTyped (prog : Program) (h : prog.typeCheck = true) :
    WellTypedProg prog.tyCtx prog.compile := by
  simp [typeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hnd, hnt⟩, hchk⟩ := h
  have : prog.compile.code = (initCode prog.decls ++
      (compileStmt prog.body (initCode prog.decls).length 0).1 ++ [TAC.halt]).toArray :=
    by simp [Program.compile]
  exact allWTI_toArray' this (allWTI_append3 (initCode_wt prog hnd)
    (compileStmt_wt prog hnt prog.body hchk _ _) (allWTI_one .halt))

/-- **Corollary**: A type-checked program with a well-typed initial store
    always makes progress. The next configuration may be `run`, `halt`, or
    `error` (for div-by-zero). This follows directly from `compile_wellTyped`
    and the progress theorem (`Step.progress`). -/
theorem no_type_stuck (prog : Program)
    (htc : prog.typeCheck = true)
    (σ : Store) (hts : TypedStore prog.tyCtx σ)
    (pc : Nat) (hpc : pc < prog.compile.size) :
    ∀ am, ∃ c', Step prog.compile (Cfg.run pc σ am) c' :=
  fun am => Step.progress prog.compile pc σ am prog.tyCtx hpc
    (prog.compile_wellTyped htc) hts

-- ============================================================
-- § 5g. Compiled programs are step-closed in bounds
-- ============================================================

/-- All goto/ifgoto targets in `code` are ≤ `bound`. -/
def AllJumpsLe (bound : Nat) (code : List TAC) : Prop :=
  ∀ instr, instr ∈ code →
    match instr with
    | .goto l => l ≤ bound
    | .ifgoto _ l => l ≤ bound
    | _ => True

@[simp] theorem AllJumpsLe_nil : AllJumpsLe bound ([] : List TAC) := by
  intro _ h; simp at h

theorem AllJumpsLe_append (h1 : AllJumpsLe b l1) (h2 : AllJumpsLe b l2) :
    AllJumpsLe b (l1 ++ l2) :=
  fun instr hmem => (List.mem_append.mp hmem).elim (h1 instr) (h2 instr)

theorem AllJumpsLe_mono (h : AllJumpsLe b1 code) (hle : b1 ≤ b2) :
    AllJumpsLe b2 code := by
  intro instr hmem
  have hi := h instr hmem
  cases instr with
  | goto l => exact Nat.le_trans hi hle
  | ifgoto _ l => exact Nat.le_trans hi hle
  | _ => trivial

theorem AllJumpsLe_single_goto (hle : l ≤ bound) :
    AllJumpsLe bound ([TAC.goto l] : List TAC) := by
  intro instr hmem; simp at hmem; subst hmem; exact hle

theorem AllJumpsLe_single_ifgoto {be : BoolExpr} (hle : l ≤ bound) :
    AllJumpsLe bound ([TAC.ifgoto be l] : List TAC) := by
  intro instr hmem; simp at hmem; subst hmem; exact hle

/-- Code with no goto/ifgoto/halt satisfies AllJumpsLe for any bound. -/
def IsSeqInstr (instr : TAC) : Prop :=
  match instr with
  | .const _ _ | .copy _ _ | .binop _ _ _ _ | .boolop _ _
  | .arrLoad _ _ _ _ | .arrStore _ _ _ _ => True
  | _ => False

theorem AllJumpsLe_of_allSeq {code : List TAC}
    (h : ∀ instr, instr ∈ code → IsSeqInstr instr) : AllJumpsLe bound code := by
  intro instr hmem; have := h instr hmem; cases instr <;> simp_all [IsSeqInstr]

theorem compileExpr_allSeq (e : SExpr) (offset nextTmp : Nat) :
    ∀ instr, instr ∈ (compileExpr e offset nextTmp).1 → IsSeqInstr instr := by
  induction e generalizing offset nextTmp with
  | lit _ => intro instr hmem; simp [compileExpr] at hmem; subst hmem; trivial
  | var _ => intro _ hmem; simp [compileExpr] at hmem
  | bin _ a b iha ihb =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with ha | hb | rfl
    · exact iha _ _ instr ha
    · exact ihb _ _ instr hb
    · trivial
  | arrRead _ idx ih =>
    intro instr hmem; simp [compileExpr, List.mem_append] at hmem
    rcases hmem with hi | rfl
    · exact ih _ _ instr hi
    · trivial

theorem compileBool_allJumpsLe (b : SBool) (offset nextTmp bound : Nat)
    (hbound : offset + (compileBool b offset nextTmp).1.length ≤ bound) :
    AllJumpsLe bound (compileBool b offset nextTmp).1 := by
  induction b generalizing offset nextTmp bound with
  | lit _ => exact AllJumpsLe_nil
  | bvar _ => exact AllJumpsLe_nil
  | cmp _ a b =>
    exact AllJumpsLe_of_allSeq (fun instr hmem => by
      simp [compileBool, List.mem_append] at hmem
      rcases hmem with ha | hb
      · exact compileExpr_allSeq a _ _ instr ha
      · exact compileExpr_allSeq b _ _ instr hb)
  | not _ ih =>
    simp only [compileBool] at hbound ⊢
    exact ih offset nextTmp bound hbound
  | and _ _ iha ihb =>
    simp only [compileBool, List.length_append, List.length_cons, List.length_nil] at hbound ⊢
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · apply AllJumpsLe_append
        · exact AllJumpsLe_mono (iha offset nextTmp _ (Nat.le_refl _)) (by omega)
        · exact AllJumpsLe_single_ifgoto (by omega)
      · exact AllJumpsLe_mono (ihb _ _ _ (Nat.le_refl _)) (by omega)
    · intro instr hmem
      simp [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Nat.le_trans (by omega) hbound  -- ifgoto: falseL ≤ bound
      · trivial  -- const
      · exact Nat.le_trans (by omega) hbound  -- goto: endL ≤ bound
      · trivial  -- const
  | or _ _ iha ihb =>
    simp only [compileBool, List.length_append, List.length_cons, List.length_nil] at hbound ⊢
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · apply AllJumpsLe_append
        · exact AllJumpsLe_mono (iha offset nextTmp _ (Nat.le_refl _)) (by omega)
        · exact AllJumpsLe_single_ifgoto (by omega)
      · exact AllJumpsLe_mono (ihb _ _ _ (Nat.le_refl _)) (by omega)
    · intro instr hmem
      simp [List.mem_cons] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Nat.le_trans (by omega) hbound
      · trivial
      · exact Nat.le_trans (by omega) hbound
      · trivial
  | barrRead arr idx =>
    simp only [compileBool, List.length_append, List.length_cons, List.length_nil] at hbound ⊢
    exact AllJumpsLe_of_allSeq (fun instr hmem => by
      simp [compileBool, List.mem_append] at hmem
      rcases hmem with hi | rfl
      · exact compileExpr_allSeq idx _ _ instr hi
      · trivial)

theorem initCode_allSeq (decls : List (Var × VarTy)) :
    ∀ instr, instr ∈ initCode decls → IsSeqInstr instr := by
  intro instr hmem; simp only [initCode, List.mem_map] at hmem
  obtain ⟨⟨_, ty⟩, _, rfl⟩ := hmem; cases ty <;> trivial

/-- All jump targets in compiled statement code are ≤ offset + code.length. -/
theorem compileStmt_allJumpsLe (s : Stmt) (offset nextTmp : Nat) :
    AllJumpsLe (offset + (compileStmt s offset nextTmp).1.length)
      (compileStmt s offset nextTmp).1 := by
  induction s generalizing offset nextTmp with
  | skip => exact AllJumpsLe_nil
  | assign x e =>
    cases e with
    | lit _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; trivial
    | var _ => intro _ hmem; simp [compileStmt] at hmem; subst hmem; trivial
    | bin _ a b =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with ha | hb | rfl
        · exact compileExpr_allSeq a _ _ instr ha
        · exact compileExpr_allSeq b _ _ instr hb
        · trivial)
    | arrRead _ idx =>
      exact AllJumpsLe_of_allSeq (by
        intro instr hmem; simp [compileStmt, List.mem_append] at hmem
        rcases hmem with hi | rfl | rfl
        · exact compileExpr_allSeq idx _ _ instr hi
        · trivial
        · trivial)
  | bassign _ b =>
    simp only [compileStmt, List.length_append, List.length_singleton]
    exact AllJumpsLe_append
      (AllJumpsLe_mono (compileBool_allJumpsLe b offset nextTmp _ (Nat.le_refl _)) (by omega))
      (AllJumpsLe_of_allSeq (fun instr hmem => by simp at hmem; subst hmem; trivial))
  | arrWrite _ idx val =>
    exact AllJumpsLe_of_allSeq (by
      intro instr hmem; simp [compileStmt, List.mem_append] at hmem
      rcases hmem with hi | hv | rfl
      · exact compileExpr_allSeq idx _ _ instr hi
      · exact compileExpr_allSeq val _ _ instr hv
      · trivial)
  | barrWrite arr idx bval =>
    match hci : compileExpr idx offset nextTmp with
    | (codeIdx, vIdx, tmp1) =>
    match hcb : compileBool bval (offset + codeIdx.length) tmp1 with
    | (codeBool, be, tmp2) =>
    simp only [compileStmt, hci, hcb, List.length_append, List.length_cons, List.length_nil]
    have hi : AllJumpsLe (offset + codeIdx.length) codeIdx :=
      AllJumpsLe_of_allSeq (fun instr hmem => by
        have := compileExpr_allSeq idx offset nextTmp instr; simp [hci] at this; exact this hmem)
    have hb : AllJumpsLe (offset + codeIdx.length + codeBool.length) codeBool := by
      have := compileBool_allJumpsLe bval (offset + codeIdx.length) tmp1
        (offset + codeIdx.length + codeBool.length) (by simp [hcb])
      simp [hcb] at this; exact this
    apply AllJumpsLe_append
    · apply AllJumpsLe_append
      · apply AllJumpsLe_append
        · exact AllJumpsLe_mono hi (by omega)
        · exact AllJumpsLe_mono hb (by omega)
      · have h_ifgt : offset + codeIdx.length + codeBool.length + 3 ≤
            offset + (codeIdx.length + codeBool.length + (0 + 1 + 1 + 1 + 1) + (0 + 1)) := by omega
        have h_goto : offset + codeIdx.length + codeBool.length + 3 + 1 ≤
            offset + (codeIdx.length + codeBool.length + (0 + 1 + 1 + 1 + 1) + (0 + 1)) := by omega
        intro instr hmem; simp at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact h_ifgt
        · exact trivial
        · exact h_goto
        · exact trivial
    · exact AllJumpsLe_of_allSeq (fun instr hmem => by simp at hmem; subst hmem; trivial)
  | seq s1 s2 ih1 ih2 =>
    simp only [compileStmt, List.length_append]
    exact AllJumpsLe_append (AllJumpsLe_mono (ih1 offset nextTmp) (by omega))
      (AllJumpsLe_mono (ih2 _ _) (by omega))
  | ite b s1 s2 ih1 ih2 =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hs2 : compileStmt s2 (offset + codeB.length + 1) tmpB with
    | (codeElse, tmpE) =>
    match hs1 : compileStmt s1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE with
    | (codeThen, _) =>
    simp only [compileStmt, hcb, hs2, hs1, List.length_append, List.length_singleton]
    have hb : AllJumpsLe (offset + codeB.length) codeB := by
      have := compileBool_allJumpsLe b offset nextTmp (offset + codeB.length) (by simp [hcb])
      simp [hcb] at this; exact this
    have h2 := ih2 (offset + codeB.length + 1) tmpB
    simp only [hs2] at h2
    have h1 := ih1 (offset + codeB.length + 1 + codeElse.length + 1) tmpE
    simp only [hs1] at h1
    -- ++ is left-associative: ((((codeB ++ [ifgoto]) ++ codeElse) ++ [goto]) ++ codeThen)
    exact AllJumpsLe_append
      (AllJumpsLe_append
        (AllJumpsLe_append
          (AllJumpsLe_append (AllJumpsLe_mono hb (by omega))
            (AllJumpsLe_single_ifgoto (by omega)))
          (AllJumpsLe_mono h2 (by omega)))
        (AllJumpsLe_single_goto (by omega)))
      (AllJumpsLe_mono h1 (by omega))
  | loop b body ih =>
    match hcb : compileBool b offset nextTmp with
    | (codeB, be, tmpB) =>
    match hsbody : compileStmt body (offset + codeB.length + 1) tmpB with
    | (codeBody, _) =>
    simp only [compileStmt, hcb, hsbody, List.length_append, List.length_singleton]
    have hb : AllJumpsLe (offset + codeB.length) codeB := by
      have := compileBool_allJumpsLe b offset nextTmp (offset + codeB.length) (by simp [hcb])
      simp [hcb] at this; exact this
    have hih := ih (offset + codeB.length + 1) tmpB
    simp only [hsbody] at hih
    -- ++ is left-associative: (((codeB ++ [ifgoto]) ++ codeBody) ++ [goto])
    exact AllJumpsLe_append
      (AllJumpsLe_append
        (AllJumpsLe_append (AllJumpsLe_mono hb (by omega))
          (AllJumpsLe_single_ifgoto (by omega)))
        (AllJumpsLe_mono hih (by omega)))
      (AllJumpsLe_single_goto (by omega))

/-- Bridge: if all jump targets in `code` are ≤ `code.length`, then
    `(code ++ [halt]).toArray` is step-closed in bounds. -/
private theorem stepClosed_of_allJumpsLe {code : List TAC} {p : Prog}
    (hcode : p.code = (code ++ [TAC.halt]).toArray)
    (hjumps : AllJumpsLe code.length code) :
    StepClosedInBounds p := by
  have hlen : p.size = code.length + 1 := by simp [Prog.size, hcode]
  constructor
  · omega
  · intro pc pc' σ σ' am am' hpc hstep
    obtain ⟨instr, hinstr, hmem⟩ := Step.mem_successors hstep
    rw [hlen] at hpc ⊢
    rw [show p[pc]? = (code ++ [TAC.halt])[pc]? from by
      simp [Prog.getElem?_code, hcode, List.getElem?_toArray]] at hinstr
    by_cases hlt : pc < code.length
    · -- Instruction is from `code`
      rw [List.getElem?_append_left hlt] at hinstr
      have hmem_code := List.mem_of_getElem? hinstr
      have hj := hjumps instr hmem_code
      cases instr with
      | const _ _ | copy _ _ | binop _ _ _ _ | boolop _ _ =>
        simp [TAC.successors] at hmem; omega
      | arrLoad _ _ _ _ | arrStore _ _ _ _ =>
        simp [TAC.successors] at hmem; omega
      | goto l => simp [TAC.successors] at hmem; subst hmem; exact Nat.lt_of_le_of_lt hj (by omega)
      | ifgoto _ l =>
        simp [TAC.successors, List.mem_cons] at hmem
        rcases hmem with rfl | rfl
        · exact Nat.lt_of_le_of_lt hj (by omega)
        · omega
      | halt => simp [TAC.successors] at hmem
    · -- Instruction is halt (at position code.length)
      have hpc_eq : pc = code.length := by omega
      subst hpc_eq
      rw [List.getElem?_append_right (by omega)] at hinstr
      simp at hinstr; subst hinstr
      simp [TAC.successors] at hmem

/-- **Step-closedness**: A type-checked program's compiled output has all
    jump targets within bounds — no instruction can jump outside the program. -/
theorem compile_stepClosed (prog : Program) (_h : prog.typeCheck = true) :
    StepClosedInBounds prog.compile := by
  apply stepClosed_of_allJumpsLe (code := initCode prog.decls ++
    (compileStmt prog.body (initCode prog.decls).length 0).1)
  · simp [Program.compile, List.append_assoc]
  · simp only [List.length_append]
    exact AllJumpsLe_append (AllJumpsLe_of_allSeq (initCode_allSeq prog.decls))
      (compileStmt_allJumpsLe prog.body (initCode prog.decls).length 0)

/-- **No-stuck guarantee**: A type-checked program always has a behavior —
    it either halts, errors (div-by-zero), or diverges. No execution can
    get stuck. Combines `compile_wellTyped`, `compile_stepClosed`, and
    `has_behavior`. -/
theorem compile_has_behavior (prog : Program) (htc : prog.typeCheck = true)
    (σ₀ : Store) :
    ∃ b, program_behavior prog.compile σ₀ b :=
  has_behavior prog.compile σ₀ (prog.compile_stepClosed htc)

-- ============================================================
-- § 5h. Pretty-printing
-- ============================================================

private def tyToString : VarTy → String
  | .int  => "int"
  | .bool => "bool"

def toString (prog : Program) : String :=
  let declStrs := prog.decls.map fun (x, ty) => s!"var {x} : {tyToString ty}"
  let declBlock := String.intercalate ";\n" declStrs
  s!"{declBlock};\n{prog.body}"

instance : ToString Program := ⟨Program.toString⟩

end Program
