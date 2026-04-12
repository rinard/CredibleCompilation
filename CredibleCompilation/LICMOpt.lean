import CredibleCompilation.ConstPropOpt
import CredibleCompilation.DAEOpt

/-!
# Loop-Invariant Code Motion Optimizer

Hoists loop-invariant `const` instructions by modifying their init-block
counterpart and replacing the in-loop copy with `goto (pc+1)`.

## Strategy

For each `const x v` at PC `p` inside a loop where `x` is a compiler temporary:
1. Change the init `const x 0` at PC `i` to `const x v`
2. Replace the in-loop const at PC `p` with `goto (p+1)`

Uses expression relation `(lit v, var x)` for hoisted vars, identity for rest.
Must run before ConstProp/DCE to ensure init block still exists.
-/

namespace LICMOpt

-- ============================================================
-- § 1. Loop detection
-- ============================================================

def findLoopPCs (prog : Prog) : Array Bool :=
  let arr := Array.replicate prog.size false
  (List.range prog.size).foldl (fun arr pc =>
    match prog[pc]? with
    | some instr =>
      (successors instr pc).foldl (fun arr target =>
        if target ≤ pc then
          (List.range (pc - target + 1)).foldl (fun arr offset =>
            arr.set! (target + offset) true
          ) arr
        else arr
      ) arr
    | none => arr
  ) arr

-- ============================================================
-- § 2. Hoistable detection
-- ============================================================

private def isTmp (v : Var) : Bool :=
  v.startsWith "__t" || v.startsWith "__ft"

private def findInitPC (prog : Prog) (inLoop : Array Bool) (x : Var) : Option Nat :=
  (List.range prog.size).find? fun pc =>
    !(inLoop.getD pc false) &&
    match prog[pc]? with
    | some (.const y _) => x == y
    | _ => false

private def usedInRange (prog : Prog) (x : Var) (lo hi : Nat) : Bool :=
  (List.range (hi - lo)).any fun offset =>
    match prog[lo + offset]? with
    | some instr => (DAEOpt.instrUse instr).contains x
    | none => false

private def definedInRange (prog : Prog) (x : Var) (lo hi : Nat) : Bool :=
  if hi ≤ lo + 1 then false
  else (List.range (hi - lo - 1)).any fun offset =>
    match prog[lo + 1 + offset]? with
    | some instr => DAEOpt.instrDef instr == some x
    | none => false

def findHoistable (prog : Prog) (inLoop : Array Bool) : List (Nat × Nat × Var × Value) :=
  let candidates := (List.range prog.size).filterMap fun pc =>
    if !(inLoop.getD pc false) then none
    else match prog[pc]? with
    | some (.const x v) =>
      if !isTmp x then none
      else match findInitPC prog inLoop x with
      | none => none
      | some initPC =>
        if initPC >= pc then none
        else if usedInRange prog x (initPC + 1) pc then none
        else if definedInRange prog x initPC pc then none
        else some (initPC, pc, x, v)
    | _ => none
  candidates.foldl (fun acc (i, p, x, v) =>
    if acc.any (fun (_, _, x', _) => x' == x) then acc
    else acc ++ [(i, p, x, v)]
  ) ([] : List (Nat × Nat × Var × Value))

-- ============================================================
-- § 3. Transformation (1:1, size-preserving)
-- ============================================================

def transform (prog : Prog) (hoistable : List (Nat × Nat × Var × Value)) : Prog :=
  let code := hoistable.foldl (fun code (initPC, constPC, x, v) =>
    let code := code.set! initPC (.const x v)
    let code := code.set! constPC (.goto (constPC + 1))
    code
  ) prog.code
  { code := code, tyCtx := prog.tyCtx, observable := prog.observable,
    arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 4. Certificate with (lit v, var x) rel
-- ============================================================

private def buildRel (allVars : List Var) (hoisted : List (Var × Value)) : EExprRel :=
  allVars.map fun v =>
    match hoisted.find? (fun (hv, _) => hv == v) with
    | some (_, val) =>
      let litExpr := match val with
        | .int n => Expr.lit n | .bool b => .blit b | .float f => .flit f
      (litExpr, .var v)
    | none => (.var v, .var v)

private def buildInstrCertsLICM (trans : Prog) (rel : EExprRel) : Array EInstrCert :=
  let arr := (List.range trans.size).map fun i =>
    match trans[i]? with
    | some .halt => { pc_orig := i, transitions := ([] : List ETransCorr), rel := rel }
    | some (.goto l) =>
      { pc_orig := i, rel := rel,
        transitions := [{ origLabels := [l], rel := rel, rel_next := rel }] }
    | some (.ifgoto _ l) =>
      { pc_orig := i, rel := rel,
        transitions := [{ origLabels := [l], rel := rel, rel_next := rel },
                        { origLabels := [i + 1], rel := rel, rel_next := rel }] }
    | some _ =>
      { pc_orig := i, rel := rel,
        transitions := [{ origLabels := [i + 1], rel := rel, rel_next := rel }] }
    | none => default
  arr.toArray

def numHoistable (prog : Prog) : Nat :=
  let inLoop := findLoopPCs prog
  (findHoistable prog inLoop).length

def optimize (prog : Prog) : ECertificate :=
  let inLoop := findLoopPCs prog
  let hoistable := findHoistable prog inLoop
  let trans := transform prog hoistable
  let hoistedVars := hoistable.map fun (_, _, x, v) => (x, v)
  let allVars := _root_.collectAllVars prog trans
  let rel := buildRel allVars hoistedVars
  let consts_orig := ConstPropOpt.analyze prog
  let inv_orig := ConstPropOpt.buildInvariants consts_orig
  let consts_trans := ConstPropOpt.analyze trans
  let inv_trans := ConstPropOpt.buildInvariants consts_trans
  let instrCerts := buildInstrCertsLICM trans rel
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    inv_orig := inv_orig
    inv_trans := inv_trans
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end LICMOpt
