import CredibleCompilation.CompilerCorrectness
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-!
# Reference Compiler: Definitions and Helpers

Temporary variable helpers, compiler definitions, code embedding,
single-step execution helpers, and store update lemmas.
-/

-- ============================================================
-- § 1. Temporary variable helpers
-- ============================================================

-- -----------------------------------------------
-- Proving tmpName injective
-- -----------------------------------------------

/-- Clean base-10 digit representation. -/
private noncomputable def myDigits (n : Nat) : List Char :=
  if n < 10 then [(n % 10).digitChar]
  else myDigits (n / 10) ++ [(n % 10).digitChar]
termination_by n
decreasing_by omega

private theorem digitChar_injective {m n : Nat} (hm : m < 10) (hn : n < 10)
    (h : m.digitChar = n.digitChar) : m = n := by
  interval_cases m <;> interval_cases n <;> simp_all [Nat.digitChar]

private theorem digitChar_toNat {n : Nat} (hn : n < 10) :
    n.digitChar.toNat - '0'.toNat = n := by
  interval_cases n <;> simp [Nat.digitChar]

private def parseNat (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private theorem parseNat_myDigits (n : Nat) : parseNat (myDigits n) = n := by
  rw [myDigits]
  split
  · rename_i hn
    simp only [parseNat, List.foldl]
    rw [digitChar_toNat (by omega : n % 10 < 10)]
    omega
  · rename_i hn
    simp only [parseNat, List.foldl_append, List.foldl]
    show List.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
        (myDigits (n / 10)) * 10 + ((n % 10).digitChar.toNat - '0'.toNat) = n
    have ih := parseNat_myDigits (n / 10)
    simp only [parseNat] at ih
    rw [ih, digitChar_toNat (by omega : n % 10 < 10)]
    omega
termination_by n
decreasing_by omega

private theorem myDigits_injective : Function.Injective myDigits := by
  intro m n h
  have hm := parseNat_myDigits m
  have hn := parseNat_myDigits n
  rw [h] at hm; omega

private theorem tdc_eq_aux (fuel n : Nat) (ds : List Char) (hfuel : n ≤ fuel) :
    Nat.toDigitsCore 10 (fuel + 1) n ds = myDigits n ++ ds := by
  induction fuel generalizing n ds with
  | zero =>
    have : n = 0 := by omega
    subst this
    simp [Nat.toDigitsCore, myDigits]
  | succ fuel ih =>
    show (let d := (n % 10).digitChar
          let n' := n / 10
          if n' = 0 then d :: ds
          else Nat.toDigitsCore 10 (fuel + 1) n' (d :: ds)) = myDigits n ++ ds
    by_cases hn : n < 10
    · simp [show n / 10 = 0 by omega, myDigits, hn]
    · simp only [show ¬(n / 10 = 0) by omega, ite_false]
      rw [ih (n / 10) _ (by omega)]
      conv_rhs => rw [myDigits, if_neg hn]
      simp [List.append_assoc]

private theorem myDigits_eq_toDigits (n : Nat) : myDigits n = Nat.toDigits 10 n := by
  simp only [Nat.toDigits]
  rw [tdc_eq_aux n n List.nil (by omega)]
  simp

private theorem Nat_toString_injective : Function.Injective (toString : Nat → String) := by
  intro m n h
  have h_toList : (toString m : String).toList = (toString n : String).toList :=
    String.ext_iff.mp h
  show m = n
  simp only [show (toString m : String) = Nat.repr m from rfl,
             show (toString n : String) = Nat.repr n from rfl,
             Nat.repr, String.toList_ofList] at h_toList
  rw [← myDigits_eq_toDigits, ← myDigits_eq_toDigits] at h_toList
  exact myDigits_injective h_toList

private theorem tmpName_injective : Function.Injective tmpName := by
  intro k j h
  have h2 := String.ext_iff.mp h
  simp only [tmpName, String.toList_append] at h2
  have h3 := List.append_cancel_left h2
  exact Nat_toString_injective (String.ext_iff.mpr h3)

-- -----------------------------------------------

theorem tmpName_ne {k j : Nat} (h : k ≠ j) : tmpName k ≠ tmpName j :=
  fun heq => h (tmpName_injective heq)

theorem tmpName_isTmp (k : Nat) : (tmpName k).isTmp = true :=
  tmpName_isTmp_wt k

theorem isTmp_false_ne_tmpName {v : Var} {k : Nat} (h : v.isTmp = false) : v ≠ tmpName k := by
  intro heq; have := tmpName_isTmp k; rw [← heq] at this; simp [h] at this

-- ============================================================
-- § 1b. Integer free-variable helpers
-- ============================================================

/-- Free variables that appear in `SExpr` positions within a `SBool`. -/
def SBool.exprFreeVars : SBool → List Var
  | .lit _      => []
  | .bvar _     => []
  | .cmp _ a b  => a.freeVars ++ b.freeVars
  | .not e      => e.exprFreeVars
  | .and a b    => a.exprFreeVars ++ b.exprFreeVars
  | .or a b     => a.exprFreeVars ++ b.exprFreeVars
  | .barrRead _ idx => idx.freeVars

/-- Integer-safety: all variables used in `SExpr` positions have `.int` values,
    threaded through interpretation just like `Stmt.safe`. -/
def Stmt.intSafe (fuel : Nat) (σ : Store) (am : ArrayMem) (decls : List (ArrayName × Nat × VarTy)) : Stmt → Prop
  | .skip        => True
  | .assign _ e  => ∀ v ∈ e.freeVars, ∃ n, σ v = .int n
  | .bassign _ b => ∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n
  | .arrWrite _ idx val => (∀ v ∈ idx.freeVars, ∃ n, σ v = .int n) ∧
                           (∀ v ∈ val.freeVars, ∃ n, σ v = .int n)
  | .barrWrite _ idx bval => (∀ v ∈ idx.freeVars, ∃ n, σ v = .int n) ∧
                              (∀ v ∈ bval.exprFreeVars, ∃ n, σ v = .int n)
  | .seq s₁ s₂  =>
    s₁.intSafe fuel σ am decls ∧
    match s₁.interp fuel σ am decls with
    | some (σ', am') => s₂.intSafe fuel σ' am' decls
    | none    => True
  | .ite b s₁ s₂ =>
    (∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n) ∧
    (if b.eval σ am then s₁.intSafe fuel σ am decls else s₂.intSafe fuel σ am decls)
  | .loop b body =>
    (∀ v ∈ b.exprFreeVars, ∃ n, σ v = .int n) ∧
    match fuel with
    | 0 => True
    | fuel' + 1 =>
      if b.eval σ am then
        body.intSafe fuel' σ am decls ∧
        match body.interp fuel' σ am decls with
        | some (σ', am') => (Stmt.loop b body).intSafe fuel' σ' am' decls
        | none    => True
      else True

-- ============================================================
-- § 2. Reference compiler definitions
-- ============================================================

def refCompileExpr (e : SExpr) (offset nextTmp : Nat) : List TAC × Var × Nat :=
  match e with
  | .lit n =>
    let t := tmpName nextTmp
    ([.const t (.int (BitVec.ofInt 64 n))], t, nextTmp + 1)
  | .var x => ([], x, nextTmp)
  | .bin op a b =>
    let (codeA, va, tmp1) := refCompileExpr a offset nextTmp
    let (codeB, vb, tmp2) := refCompileExpr b (offset + codeA.length) tmp1
    let t := tmpName tmp2
    (codeA ++ codeB ++ [.binop t op va vb], t, tmp2 + 1)
  | .arrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := refCompileExpr idx offset nextTmp
    let t := tmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .int], t, tmp1 + 1)

def refCompileBool (b : SBool) (offset nextTmp : Nat) : List TAC × BoolExpr × Nat :=
  match b with
  | .lit b => ([], .lit b, nextTmp)
  | .bvar x => ([], .bvar x, nextTmp)
  | .cmp op a b =>
    let (codeA, va, tmp1) := refCompileExpr a offset nextTmp
    let (codeB, vb, tmp2) := refCompileExpr b (offset + codeA.length) tmp1
    (codeA ++ codeB, .cmp op va vb, tmp2)
  | .not e =>
    let (code, be, tmp') := refCompileBool e offset nextTmp
    (code, .not be, tmp')
  | .and a b =>
    -- Flatten a && b: if !a goto false; if !b goto false; tR := 1; goto end; false: tR := 0
    let (codeA, ba, tmp1) := refCompileBool a offset nextTmp
    let tR := tmpName tmp1
    let (codeB, bb, tmp2) := refCompileBool b (offset + codeA.length + 1) (tmp1 + 1)
    let afterCodeB := offset + codeA.length + 1 + codeB.length
    let falseL := afterCodeB + 3
    let endL := falseL + 1
    let code := codeA ++
      [TAC.ifgoto (.not ba) falseL] ++
      codeB ++
      [TAC.ifgoto (.not bb) falseL,
       TAC.const tR (.int 1),
       TAC.goto endL,
       TAC.const tR (.int 0)]
    (code, .cmpLit .ne tR 0, tmp2)
  | .or a b =>
    -- Flatten a || b: if a goto true; if b goto true; tR := 0; goto end; true: tR := 1
    let (codeA, ba, tmp1) := refCompileBool a offset nextTmp
    let tR := tmpName tmp1
    let (codeB, bb, tmp2) := refCompileBool b (offset + codeA.length + 1) (tmp1 + 1)
    let afterCodeB := offset + codeA.length + 1 + codeB.length
    let trueL := afterCodeB + 3
    let endL := trueL + 1
    let code := codeA ++
      [TAC.ifgoto ba trueL] ++
      codeB ++
      [TAC.ifgoto bb trueL,
       TAC.const tR (.int 0),
       TAC.goto endL,
       TAC.const tR (.int 1)]
    (code, .cmpLit .ne tR 0, tmp2)
  | .barrRead arr idx =>
    let (codeIdx, vIdx, tmp1) := refCompileExpr idx offset nextTmp
    let t := tmpName tmp1
    (codeIdx ++ [.arrLoad t arr vIdx .int], .cmpLit .ne t 0, tmp1 + 1)

def refCompileStmt (s : Stmt) (offset nextTmp : Nat) : List TAC × Nat :=
  match s with
  | .skip => ([], nextTmp)
  | .assign x e =>
    match e with
    | .lit n => ([.const x (.int (BitVec.ofInt 64 n))], nextTmp)
    | .var y => ([.copy x y], nextTmp)
    | .bin op a b =>
      let (codeA, va, tmp1) := refCompileExpr a offset nextTmp
      let (codeB, vb, tmp2) := refCompileExpr b (offset + codeA.length) tmp1
      (codeA ++ codeB ++ [.binop x op va vb], tmp2)
    | .arrRead arr idx =>
      let (codeIdx, vIdx, tmp1) := refCompileExpr idx offset nextTmp
      let t := tmpName tmp1
      (codeIdx ++ [.arrLoad t arr vIdx .int, .copy x t], tmp1 + 1)
  | .bassign x b =>
    let (code, be, tmp') := refCompileBool b offset nextTmp
    (code ++ [.boolop x be], tmp')
  | .arrWrite arr idx val =>
    let (codeIdx, vIdx, tmp1) := refCompileExpr idx offset nextTmp
    let (codeVal, vVal, tmp2) := refCompileExpr val (offset + codeIdx.length) tmp1
    (codeIdx ++ codeVal ++ [.arrStore arr vIdx vVal .int], tmp2)
  | .barrWrite arr idx bval =>
    let (codeIdx, vIdx, tmp1) := refCompileExpr idx offset nextTmp
    let (codeBool, be, tmp2) := refCompileBool bval (offset + codeIdx.length) tmp1
    let tInt := tmpName tmp2
    let afterCodeBool := offset + codeIdx.length + codeBool.length
    let trueL := afterCodeBool + 3
    let endL := trueL + 1
    let convCode : List TAC :=
      [TAC.ifgoto be trueL,
       TAC.const tInt (.int (0 : BitVec 64)),
       TAC.goto endL,
       TAC.const tInt (.int (1 : BitVec 64))]
    (codeIdx ++ codeBool ++ convCode ++ [.arrStore arr vIdx tInt .int], tmp2 + 1)
  | .seq s1 s2 =>
    let (code1, tmp1) := refCompileStmt s1 offset nextTmp
    let (code2, tmp2) := refCompileStmt s2 (offset + code1.length) tmp1
    (code1 ++ code2, tmp2)
  | .ite b s1 s2 =>
    let (codeBool, be, tmpB) := refCompileBool b offset nextTmp
    let elseStart := offset + codeBool.length + 1
    let (codeElse, tmpElse) := refCompileStmt s2 elseStart tmpB
    let thenStart := elseStart + codeElse.length + 1
    let (codeThen, tmpThen) := refCompileStmt s1 thenStart tmpElse
    let endLabel := thenStart + codeThen.length
    (codeBool ++ [.ifgoto be thenStart] ++ codeElse ++ [.goto endLabel] ++ codeThen, tmpThen)
  | .loop b body =>
    let condLabel := offset
    let (codeBool, be, tmpB) := refCompileBool b offset nextTmp
    let bodyStart := offset + codeBool.length + 1
    let (codeBody, tmpBody) := refCompileStmt body bodyStart tmpB
    let exitLabel := bodyStart + codeBody.length + 1
    (codeBool ++ [.ifgoto (.not be) exitLabel] ++ codeBody ++ [.goto condLabel], tmpBody)

def refCompile (s : Stmt) : Prog :=
  let (code, _) := refCompileStmt s 0 0
  .ofCode (code ++ [TAC.halt]).toArray

-- ============================================================
-- § 3. Code embedding predicate
-- ============================================================

def CodeAt (code : List TAC) (p : Prog) (offset : Nat) : Prop :=
  ∀ i, i < code.length → p[offset + i]? = code[i]?

@[simp] theorem CodeAt.nil : CodeAt [] p offset :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem CodeAt.left {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h : CodeAt (c₁ ++ c₂) p offset) : CodeAt c₁ p offset := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem?_append_left (by exact hi)] at this

theorem CodeAt.right {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h : CodeAt (c₁ ++ c₂) p offset) : CodeAt c₂ p (offset + c₁.length) := by
  intro i hi
  have := h (c₁.length + i) (by simp; omega)
  rw [show offset + (c₁.length + i) = offset + c₁.length + i from by omega] at this
  rwa [List.getElem?_append_right (by omega),
       show c₁.length + i - c₁.length = i from by omega] at this

theorem CodeAt.head {x : TAC} {xs : List TAC} {p : Prog} {offset : Nat}
    (h : CodeAt (x :: xs) p offset) : p[offset]? = some x := by
  have := h 0 (by simp); simpa using this

theorem CodeAt.intro {c₁ c₂ : List TAC} {p : Prog} {offset : Nat}
    (h₁ : CodeAt c₁ p offset) (h₂ : CodeAt c₂ p (offset + c₁.length)) :
    CodeAt (c₁ ++ c₂) p offset := by
  intro i hi
  by_cases hlt : i < c₁.length
  · rw [List.getElem?_append_left hlt]; exact h₁ i hlt
  · rw [List.getElem?_append_right (by omega)]
    have := h₂ (i - c₁.length) (by simp at hi; omega)
    rwa [show offset + c₁.length + (i - c₁.length) = offset + i from by omega] at this

-- ============================================================
-- § 4. FragExec single-step helpers
-- ============================================================

theorem FragExec.single_const {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {x : Var} {v : Value}
    (h : p[pc]? = some (.const x v)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ v]) am am :=
  Steps.single (Step.const h)

theorem FragExec.single_copy {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {x y : Var}
    (h : p[pc]? = some (.copy x y)) :
    FragExec p pc σ (pc + 1) (σ[x ↦ σ y]) am am :=
  Steps.single (Step.copy h)

theorem FragExec.single_binop {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {op : BinOp} {y z : Var} {a b : BitVec 64}
    (h : p[pc]? = some (.binop x op y z))
    (hy : σ y = .int a) (hz : σ z = .int b) (hsafe : op.safe a b) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .int (op.eval a b)]) am am :=
  Steps.single (Step.binop h hy hz hsafe)

theorem FragExec.single_goto {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {l : Label}
    (h : p[pc]? = some (.goto l)) :
    FragExec p pc σ l σ am am :=
  Steps.single (Step.goto h)

theorem FragExec.single_iftrue {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {b : BoolExpr} {l : Label}
    (h : p[pc]? = some (.ifgoto b l)) (hb : b.eval σ = true) :
    FragExec p pc σ l σ am am :=
  Steps.single (Step.iftrue h hb)

theorem FragExec.single_iffalse {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem} {b : BoolExpr} {l : Label}
    (h : p[pc]? = some (.ifgoto b l)) (hb : b.eval σ = false) :
    FragExec p pc σ (pc + 1) σ am am :=
  Steps.single (Step.iffall h hb)

theorem FragExec.single_arrLoad {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {x : Var} {arr : ArrayName} {idx : Var} {idxVal : BitVec 64}
    (h : p[pc]? = some (.arrLoad x arr idx .int))
    (hidx : σ idx = .int idxVal)
    (hbounds : idxVal.toNat < p.arraySize arr) :
    FragExec p pc σ (pc + 1) (σ[x ↦ .int (am.read arr idxVal.toNat)]) am am := by
  have := Steps.single (Step.arrLoad (am := am) h hidx hbounds)
  simp [Value.ofBitVec] at this
  exact this

theorem FragExec.single_arrStore {p : Prog} {pc : Nat} {σ : Store} {am : ArrayMem}
    {arr : ArrayName} {idx val : Var} {idxVal v : BitVec 64}
    (h : p[pc]? = some (.arrStore arr idx val .int))
    (hidx : σ idx = .int idxVal) (hval : σ val = .int v)
    (hbounds : idxVal.toNat < p.arraySize arr) :
    FragExec p pc σ (pc + 1) σ am (am.write arr idxVal.toNat v) := by
  have hty : (σ val).typeOf = .int := by rw [hval]; simp [Value.typeOf]
  have := Steps.single (Step.arrStore (am := am) h hidx hty hbounds)
  simp [hval, Value.toBits] at this
  exact this

-- ============================================================
-- § 5. BoolExpr evaluation congruence (pointwise)
-- ============================================================

theorem BoolExpr.eval_agree' (cond : BoolExpr) (σ τ : Store)
    (h : ∀ v ∈ cond.vars, σ v = τ v) : cond.eval σ = cond.eval τ := by
  induction cond with
  | lit _ => rfl
  | bvar x =>
    simp only [BoolExpr.eval]
    rw [h x (by simp [BoolExpr.vars])]
  | cmp op x y =>
    simp only [BoolExpr.eval]
    rw [h x (by simp [BoolExpr.vars]), h y (by simp [BoolExpr.vars])]
  | cmpLit op x n =>
    simp only [BoolExpr.eval]
    rw [h x (by simp [BoolExpr.vars])]
  | not e ih =>
    simp only [BoolExpr.eval]; rw [ih (fun v hv => h v hv)]

-- ============================================================
-- § 6. Division safety helpers
-- ============================================================

theorem SExpr.safe_bin_safe {op : BinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.bin op a b).safe σ am decls) : op.safe (a.eval σ am) (b.eval σ am) := by
  cases op <;> simp_all [SExpr.safe, BinOp.safe]

theorem SExpr.safe_bin_left {op : BinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.bin op a b).safe σ am decls) : a.safe σ am decls := by
  cases op <;> simp_all [SExpr.safe]

theorem SExpr.safe_bin_right {op : BinOp} {a b : SExpr} {σ : Store} {am : ArrayMem}
    {decls : List (ArrayName × Nat × VarTy)}
    (h : (SExpr.bin op a b).safe σ am decls) : b.safe σ am decls := by
  cases op <;> simp_all [SExpr.safe]

-- ============================================================
-- § 7. Store update helpers
-- ============================================================

theorem Store.update_tmpName_ne {σ : Store} {k j : Nat} {v : Value}
    (hne : j ≠ k) : (σ[tmpName k ↦ v]) (tmpName j) = σ (tmpName j) :=
  Store.update_other σ (tmpName k) (tmpName j) v (tmpName_ne hne)

theorem Store.update_isTmp_ne {σ : Store} {t : Var} {v : Value}
    {w : Var} (ht : t.isTmp = true) (hw : w.isTmp = false) :
    (σ[t ↦ v]) w = σ w :=
  Store.update_other σ t w v (fun heq => by rw [heq] at hw; simp [hw] at ht)
