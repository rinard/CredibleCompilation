import CredibleCompilation.ConstPropOpt
import CredibleCompilation.DAEOpt

/-!
# Loop-Invariant Code Motion Optimizer

Hoists loop-invariant `const` instructions by inserting them before the
INNERMOST loop header and replacing the in-loop original with `goto (pc+1)`.

Each invocation hoists consts from ONE loop header only. Run repeatedly
to hoist across nested loops — each pass lifts consts one loop level out.

## Certificate strategy

Uses `(lit c, var x)` pairs in the expression relation for hoisted variables.
- origVal = `(lit c).substSym origSS` = `lit c` (literals self-evaluate)
- transVal = `(var x).substSym transSS .substSym preSubst` = `lit c` (via preSubst)
Both sides always equal `lit c` regardless of orig's state for x.
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

/-- Find the OUTERMOST loop header containing `pc`. -/
def findOutermostHeader (prog : Prog) (pc : Nat) : Option Nat :=
  let backEdges := (List.range prog.size).foldl (fun acc spc =>
    match prog[spc]? with
    | some instr =>
      (successors instr spc).foldl (fun acc target =>
        if target ≤ spc then acc ++ [(target, spc)] else acc
      ) acc
    | none => acc
  ) ([] : List (Nat × Nat))
  let candidates := backEdges.filterMap fun (header, tail) =>
    if header ≤ pc && pc ≤ tail then some header else none
  -- Return the SMALLEST (outermost) header
  candidates.foldl (fun best h => match best with | none => some h | some b => some (min b h)) none

-- ============================================================
-- § 2. Hoistable detection (single header only)
-- ============================================================

private def isTmp (v : Var) : Bool :=
  v.startsWith "__t" || v.startsWith "__ft"

/-- Find hoistable consts for ONE loop header only (the innermost).
    Returns list of (header, constPC, variable, value), all with same header. -/
def findHoistable (prog : Prog) (inLoop : Array Bool) : List (Nat × Nat × Var × Value) :=
  let candidates := (List.range prog.size).filterMap fun pc =>
    if !(inLoop.getD pc false) then none
    else match prog[pc]? with
    | some (.const x v) =>
      if !isTmp x then none
      else match findOutermostHeader prog pc with
      | none => none
      | some header =>
        let usedBefore := (List.range (pc - header)).any fun offset =>
          match prog[header + offset]? with
          | some instr => (DAEOpt.instrUse instr).contains x
          | none => false
        if usedBefore then none else some (header, pc, x, v)
    | _ => none
  -- Reject variables with conflicting values, then deduplicate
  let conflicting := candidates.filter fun (_, _, x, v) =>
    candidates.any fun (_, _, x', v') => x' == x && v' != v
  let conflictVars := conflicting.map fun (_, _, x, _) => x
  let filtered := candidates.filter fun (_, _, x, _) => !conflictVars.contains x
  let deduped := filtered.foldl (fun acc (h, pc, x, v) =>
    if acc.any (fun (_, _, x', _) => x' == x) then acc
    else acc ++ [(h, pc, x, v)]
  ) ([] : List (Nat × Nat × Var × Value))
  deduped

-- ============================================================
-- § 3. PC mapping
-- ============================================================

private def countsPerHeader (hoistable : List (Nat × Nat × Var × Value)) : List (Nat × Nat) :=
  hoistable.foldl (fun acc (h, _, _, _) =>
    match acc.find? (fun (h', _) => h' == h) with
    | some _ => acc.map (fun (h', n) => if h' == h then (h', n + 1) else (h', n))
    | none => acc ++ [(h, 1)]
  ) ([] : List (Nat × Nat))

def computePCMap (progSize : Nat) (hoistable : List (Nat × Nat × Var × Value)) : Array Nat :=
  let perHeader := countsPerHeader hoistable
  let (arr, _) := (List.range progSize).foldl (fun (arr, offset) origPC =>
    let insertHere := match perHeader.find? (fun (h, _) => h == origPC) with
      | some (_, n) => n | none => 0
    (arr.push (origPC + offset + insertHere), offset + insertHere)
  ) (Array.mkEmpty progSize, 0)
  arr

def buildOrigPCMap (progSize : Nat) (pcMap : Array Nat) (transSize : Nat)
    (hoistable : List (Nat × Nat × Var × Value)) : Array Nat :=
  let arr := Array.replicate transSize 0
  let arr := (List.range progSize).foldl (fun arr origPC =>
    arr.set! (pcMap.getD origPC origPC) origPC
  ) arr
  let perHeader := countsPerHeader hoistable
  perHeader.foldl (fun arr (h, count) =>
    let headerTrans := pcMap.getD h h
    (List.range count).foldl (fun arr offset =>
      arr.set! (headerTrans - count + offset) h
    ) arr
  ) arr

def isHoisted (trans : Prog) (origPCMap : Array Nat) (tpc : Nat) : Bool :=
  if tpc + 1 >= origPCMap.size then false
  else
    origPCMap.getD tpc tpc == origPCMap.getD (tpc + 1) (tpc + 1) &&
    match trans[tpc]? with | some (.const _ _) => true | _ => false

-- ============================================================
-- § 4. Transformation
-- ============================================================

def buildTrans (prog : Prog) (hoistable : List (Nat × Nat × Var × Value)) : Prog :=
  let pcMap := computePCMap prog.size hoistable
  let mapPC (origPC : Nat) : Nat := pcMap.getD origPC origPC
  let constsForHeader (h : Nat) : List TAC :=
    (hoistable.filter fun (h', _, _, _) => h' == h).map fun (_, _, x, v) => .const x v
  let replacedPCs := hoistable.map fun (_, pc, _, _) => pc
  let newCode := (List.range prog.size).foldl (fun acc origPC =>
    let toInsert := constsForHeader origPC
    let instr := prog.code.getD origPC .halt
    let adjusted := if replacedPCs.contains origPC then
      TAC.goto (mapPC origPC + 1)
    else match instr with
      | .goto l => .goto (mapPC l)
      | .ifgoto be l => .ifgoto be (mapPC l)
      | other => other
    acc ++ toInsert ++ [adjusted]
  ) ([] : List TAC)
  { code := newCode.toArray, tyCtx := prog.tyCtx,
    observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Certificate with (lit c, var x) rel
-- ============================================================

private def buildHoistRel (allVars : List Var) (hoisted : List (Var × Value)) : EExprRel :=
  allVars.map fun v =>
    match hoisted.find? (fun (hv, _) => hv == v) with
    | some (_, val) =>
      let litExpr := match val with
        | .int n => Expr.lit n | .bool b => .blit b | .float f => .flit f
      (litExpr, .var v)
    | none => (.var v, .var v)

private def buildInstrCerts (trans : Prog) (origPCMap : Array Nat)
    (allVars : List Var) (hoistedVars : List (Var × Value)) : Array EInstrCert :=
  let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
  let hoistRel := buildHoistRel allVars hoistedVars
  -- Cumulative rels: one group only, so straightforward scan
  let (relArray, _) := (List.range trans.size).foldl (fun (arr, curRel) tpc =>
    if isHoisted trans origPCMap tpc then
      let nextRel := match trans[tpc]? with
        | some (.const x v) =>
          let litExpr := match v with
            | .int n => Expr.lit n | .bool b => .blit b | .float f => .flit f
          curRel.map fun (eo, et) =>
            if et == .var x then (litExpr, .var x) else (eo, et)
        | _ => curRel
      (arr.push (curRel, nextRel), nextRel)
    else
      (arr.push (curRel, curRel), curRel)
  ) (Array.mkEmpty trans.size, idRel)
  let relAt (tpc : Nat) : EExprRel :=
    (relArray.getD tpc (idRel, idRel)).1
  let relAfter (tpc : Nat) : EExprRel :=
    (relArray.getD tpc (idRel, idRel)).2
  -- The replaced goto is a back-edge target. On re-entry, all hoisted vars
  -- are set. Its rel should be hoistRel (= cumulative after all hoisted consts).
  -- Override relAt for back-edge targets that are replaced gotos.
  let replacedGotoRel (tpc : Nat) : EExprRel :=
    match trans[tpc]? with
    | some (.goto _) =>
      -- Check if this is a replaced goto (goto to next PC, orig was a const)
      let opc := origPCMap.getD tpc tpc
      if relAt tpc != hoistRel &&
         (hoistedVars.any fun (x, _) =>
           match trans[tpc]? with | some (.goto _) => true | _ => false) then
        hoistRel
      else relAt tpc
    | _ => relAt tpc
  -- After all hoisted consts, use hoistRel everywhere (vars never change back)
  let lastHoisted := (List.range trans.size).foldl (fun last tpc =>
    if isHoisted trans origPCMap tpc then tpc else last) 0
  let effectiveRelAt (tpc : Nat) : EExprRel :=
    if tpc > lastHoisted && lastHoisted > 0 then hoistRel
    else relAt tpc
  let arr := (List.range trans.size).map fun tpc =>
    let pc_orig := origPCMap.getD tpc tpc
    let rel := effectiveRelAt tpc
    match trans[tpc]? with
    | some .halt =>
      { pc_orig := pc_orig, rel := rel, transitions := ([] : List ETransCorr) }
    | some (.goto l) =>
      let origTarget := origPCMap.getD l l
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := effectiveRelAt l }] }
    | some (.ifgoto _ l) =>
      let origTarget := origPCMap.getD l l
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := effectiveRelAt l },
                        { origLabels := [origPCMap.getD (tpc + 1) (tpc + 1)],
                          rel := rel, rel_next := effectiveRelAt (tpc + 1) }] }
    | some _ =>
      if isHoisted trans origPCMap tpc then
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [], rel := rel, rel_next := relAfter tpc }] }
      else
        let origNext := origPCMap.getD (tpc + 1) (tpc + 1)
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [origNext], rel := rel, rel_next := effectiveRelAt (tpc + 1) }] }
    | none => default
  arr.toArray

def numHoistable (prog : Prog) : Nat :=
  let inLoop := findLoopPCs prog
  (findHoistable prog inLoop).length

def optimize (prog : Prog) : ECertificate :=
  let inLoop := findLoopPCs prog
  let hoistable := findHoistable prog inLoop
  let trans := buildTrans prog hoistable
  let pcMap := computePCMap prog.size hoistable
  let origPCMap := buildOrigPCMap prog.size pcMap trans.size hoistable
  let allVars := _root_.collectAllVars prog trans
  let hoistedVars := hoistable.map fun (_, _, x, v) => (x, v)
  let consts_orig := ConstPropOpt.analyze prog
  let inv_orig := ConstPropOpt.buildInvariants consts_orig
  let consts_trans := ConstPropOpt.analyze trans
  let inv_trans := ConstPropOpt.buildInvariants consts_trans
  let instrCerts := buildInstrCerts trans origPCMap allVars hoistedVars
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  let measure := (List.range trans.size).map fun tpc =>
    if isHoisted trans origPCMap tpc then
      let opc := origPCMap.getD tpc tpc
      let remaining := (List.range (trans.size - tpc - 1)).filter fun offset =>
        isHoisted trans origPCMap (tpc + 1 + offset) &&
        origPCMap.getD (tpc + 1 + offset) 0 == opc
      remaining.length + 1
    else 0
  { orig := prog, trans := trans,
    inv_orig := inv_orig, inv_trans := inv_trans,
    instrCerts := instrCerts, haltCerts := haltCerts,
    measure := measure.toArray }

end LICMOpt
