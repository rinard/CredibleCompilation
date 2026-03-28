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

The reference compiler (`RefCompiler.lean`) provides a verified alternative
with a complete correctness proof and zero sorry holes.
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
-- § 3. Compiler: While language → TAC (pure functional)
-- ============================================================

/-- Temporary variable name from index. -/
def tmpName (k : Nat) : Var := s!"__t{k}"

/-- Compile an arithmetic expression. Returns (code, result variable, next temp index).
    Pre-computes code lengths so no patching is needed. -/
def compileExpr (e : SExpr) (offset nextTmp : Nat) : List TAC × Var × Nat :=
  match e with
  | .lit n =>
    let t := tmpName nextTmp
    ([.const t (.int n)], t, nextTmp + 1)
  | .var x => ([], x, nextTmp)
  | .bin op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    let t := tmpName tmp2
    (codeA ++ codeB ++ [.binop t op va vb], t, tmp2 + 1)

/-- Compile a boolean expression. Returns (code, BoolExpr, next temp index). -/
def compileBool (b : SBool) (offset nextTmp : Nat) : List TAC × BoolExpr × Nat :=
  match b with
  | .bvar x => ([], .bvar x, nextTmp)
  | .cmp op a b =>
    let (codeA, va, tmp1) := compileExpr a offset nextTmp
    let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
    (codeA ++ codeB, .cmp op va vb, tmp2)
  | .not e =>
    let (code, be, tmp') := compileBool e offset nextTmp
    (code, .not be, tmp')
  | .and a b =>
    let (codeA, ba, tmp1) := compileBool a offset nextTmp
    let (codeB, bb, tmp2) := compileBool b (offset + codeA.length) tmp1
    (codeA ++ codeB, .and ba bb, tmp2)
  | .or a b =>
    let (codeA, ba, tmp1) := compileBool a offset nextTmp
    let (codeB, bb, tmp2) := compileBool b (offset + codeA.length) tmp1
    (codeA ++ codeB, .or ba bb, tmp2)

/-- Compile a statement. Returns (code, next temp index).
    Jump targets are pre-computed from code lengths. -/
def compileStmt (s : Stmt) (offset nextTmp : Nat) : List TAC × Nat :=
  match s with
  | .skip => ([], nextTmp)
  | .assign x e =>
    match e with
    | .lit n => ([.const x (.int n)], nextTmp)
    | .var y => ([.copy x y], nextTmp)
    | .bin op a b =>
      let (codeA, va, tmp1) := compileExpr a offset nextTmp
      let (codeB, vb, tmp2) := compileExpr b (offset + codeA.length) tmp1
      (codeA ++ codeB ++ [.binop x op va vb], tmp2)
  | .bassign x b =>
    let (code, be, tmp') := compileBool b offset nextTmp
    (code ++ [.boolop x be], tmp')
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
  (code ++ [TAC.halt]).toArray

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

-- ============================================================
-- § 5. Typed programs with static type checking
-- ============================================================

/-- A typed program: explicit variable declarations followed by a statement body.
    All variables used in the body must be declared with their type.
    This enables static type checking that guarantees no type errors at runtime. -/
structure Program where
  decls : List (Var × VarTy)
  body  : Stmt
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
    by `tyCtx` (which maps undeclared variables to `.int` by default). -/
private def noTmpDecls (decls : List (Var × VarTy)) : Bool :=
  decls.all fun (x, _) => !x.startsWith "__t"

/-- Check that all variables in an arithmetic expression are declared as `int`. -/
def checkSExpr (lookup : Var → Option VarTy) : SExpr → Bool
  | .lit _ => true
  | .var x => lookup x == some .int
  | .bin _ a b => checkSExpr lookup a && checkSExpr lookup b

/-- Check that a boolean expression uses properly-typed declared variables. -/
def checkSBool (lookup : Var → Option VarTy) : SBool → Bool
  | .bvar x => lookup x == some .bool
  | .cmp _ a b => checkSExpr lookup a && checkSExpr lookup b
  | .not e => checkSBool lookup e
  | .and a b => checkSBool lookup a && checkSBool lookup b
  | .or a b => checkSBool lookup a && checkSBool lookup b

/-- Check that a statement body is well-typed w.r.t. declarations. -/
def checkStmt (lookup : Var → Option VarTy) : Stmt → Bool
  | .skip => true
  | .assign x e => lookup x == some .int && checkSExpr lookup e
  | .bassign x b => lookup x == some .bool && checkSBool lookup b
  | .seq s1 s2 => checkStmt lookup s1 && checkStmt lookup s2
  | .ite b s1 s2 => checkSBool lookup b && checkStmt lookup s1 && checkStmt lookup s2
  | .loop b body => checkSBool lookup b && checkStmt lookup body

/-- Full static type check: no duplicate declarations, no compiler-reserved
    temporary names in declarations, and the body is well-typed w.r.t.
    the declared variable types. -/
def typeCheck (prog : Program) : Bool :=
  noDups (prog.decls.map Prod.fst) &&
  noTmpDecls prog.decls &&
  checkStmt prog.lookupTy prog.body

-- ============================================================
-- § 5b. Compilation
-- ============================================================

/-- Emit initialization code for declared variables. -/
private def initCode (decls : List (Var × VarTy)) : List TAC :=
  decls.map fun (x, ty) =>
    match ty with
    | .int  => .const x (.int 0)
    | .bool => .const x (.bool false)

/-- Compile a typed program: initialize declared variables, then compile body.
    Appends `halt` at the end. -/
def compile (prog : Program) : Prog :=
  let inits := initCode prog.decls
  let (body, _) := compileStmt prog.body inits.length 0
  (inits ++ body ++ [TAC.halt]).toArray

-- ============================================================
-- § 5c. Interpretation
-- ============================================================

/-- Build an initial store from declarations with type-appropriate defaults.
    Int variables get 0, bool variables get false. -/
def initStore (prog : Program) : Store :=
  prog.decls.foldl (fun σ (x, ty) =>
    match ty with
    | .int  => σ[x ↦ .int 0]
    | .bool => σ[x ↦ .bool false]) Store.init

/-- Interpret a typed program. Starts from the declaration-initialized store,
    with optional input overrides. -/
def interp (prog : Program) (fuel : Nat)
    (inputs : List (Var × Value) := []) : Option Store :=
  let σ₀ := inputs.foldl (fun σ (x, v) => σ[x ↦ v]) prog.initStore
  prog.body.interp fuel σ₀

-- ============================================================
-- § 5d. initStore is well-typed
-- ============================================================

-- The fold step for initStore
private def initFold (σ : Store) (p : Var × VarTy) : Store :=
  match p.2 with
  | .int  => σ[p.1 ↦ .int 0]
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

theorem allWTI_toArray' {Γ : TyCtx} {l : List TAC}
    (h : AllWTI Γ l) : WellTypedProg Γ l.toArray := by
  intro i hi
  have hi' : i < l.length := by simp at hi; exact hi
  have hmem : l[i] ∈ l := List.getElem_mem hi'
  show WellTypedInstr Γ l.toArray[i]
  have : l.toArray[i] = l[i] := by simp [List.getElem_toArray]
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

-- String.startsWith for concrete prefix appended to arbitrary suffix
private axiom string_startsWith_append_left' (s t : String) :
    (s ++ t).startsWith s = true

-- If noTmpDecls and x starts with "__t", then lookup returns none
theorem lookup_none_of_startsWith_tmp_wt {decls : List (Var × VarTy)}
    (hnt : Program.noTmpDecls decls = true) {x : Var} (hx : x.startsWith "__t" = true) :
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
      simp [hx] at hny
    simp only [hne, ite_false]
    exact ih hnt_rest

-- tmpName k starts with "__t"
theorem tmpName_startsWith_wt (k : Nat) : (tmpName k).startsWith "__t" = true :=
  string_startsWith_append_left' "__t" (toString k)

-- tyCtx maps temporaries to .int
theorem tyCtx_tmp_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true) (k : Nat) :
    prog.tyCtx (tmpName k) = .int := by
  unfold Program.tyCtx Program.lookupTy
  rw [lookup_none_of_startsWith_tmp_wt hnt (tmpName_startsWith_wt k)]
  rfl

-- If lookupTy x = some ty, then tyCtx x = ty
theorem tyCtx_of_lookup_wt (prog : Program) (x : Var) (ty : VarTy)
    (h : prog.lookupTy x = some ty) : prog.tyCtx x = ty := by
  unfold Program.tyCtx
  rw [h]; rfl

-- compileExpr produces well-typed instructions and the result var has type .int
theorem compileExpr_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (e : SExpr) (hchk : Program.checkSExpr prog.lookupTy e = true)
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

-- compileBool produces well-typed instructions and a WellTypedBoolExpr
theorem compileBool_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (b : SBool) (hchk : Program.checkSBool prog.lookupTy b = true)
    (offset nextTmp : Nat) :
    AllWTI prog.tyCtx (compileBool b offset nextTmp).1
    ∧ WellTypedBoolExpr prog.tyCtx (compileBool b offset nextTmp).2.1 := by
  induction b generalizing offset nextTmp with
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
      (offset + (compileBool a offset nextTmp).1.length)
      (compileBool a offset nextTmp).2.2
    simp only [compileBool]
    exact ⟨allWTI_append' ha_wt hb_wt, .and ha_ty hb_ty⟩
  | or a b iha ihb =>
    simp [Program.checkSBool, Bool.and_eq_true] at hchk
    obtain ⟨hca, hcb⟩ := hchk
    have ⟨ha_wt, ha_ty⟩ := iha hca offset nextTmp
    have ⟨hb_wt, hb_ty⟩ := ihb hcb
      (offset + (compileBool a offset nextTmp).1.length)
      (compileBool a offset nextTmp).2.2
    simp only [compileBool]
    exact ⟨allWTI_append' ha_wt hb_wt, .or ha_ty hb_ty⟩

-- compileStmt produces well-typed instructions
theorem compileStmt_wt (prog : Program)
    (hnt : Program.noTmpDecls prog.decls = true)
    (s : Stmt) (hchk : Program.checkStmt prog.lookupTy s = true)
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
  | bassign x b =>
    simp [Program.checkStmt, Bool.and_eq_true] at hchk
    obtain ⟨hx, hb⟩ := hchk
    have hxty : prog.tyCtx x = .bool := tyCtx_of_lookup_wt prog x .bool hx
    have ⟨hb_wt, hb_ty⟩ := compileBool_wt prog hnt b hb offset nextTmp
    simp only [compileStmt]
    exact allWTI_append' hb_wt (allWTI_one (.boolop hxty hb_ty))
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
  simp only [Program.compile]
  apply allWTI_toArray'
  apply allWTI_append' (allWTI_append' (initCode_wt prog hnd)
    (compileStmt_wt prog hnt prog.body hchk _ _))
  exact allWTI_one .halt

/-- **Corollary**: A type-checked program with a well-typed initial store
    always makes progress. The next configuration may be `run`, `halt`, or
    `error` (for div-by-zero). This follows directly from `compile_wellTyped`
    and the progress theorem (`Step.progress`). -/
theorem no_type_stuck (prog : Program)
    (htc : prog.typeCheck = true)
    (σ : Store) (hts : TypedStore prog.tyCtx σ)
    (pc : Nat) (hpc : pc < prog.compile.size) :
    ∃ c', Step prog.compile (Cfg.run pc σ) c' :=
  Step.progress prog.compile pc σ prog.tyCtx hpc
    (prog.compile_wellTyped htc) hts

-- ============================================================
-- § 5g. Pretty-printing
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
