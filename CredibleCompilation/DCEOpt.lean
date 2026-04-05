import CredibleCompilation.ConstPropOpt

/-!
# Dead Code Elimination Optimizer

Takes a TAC program and a list of observable variables, removes unreachable
instructions, and produces an `ECertificate` that the executable checker
can verify.

## What it optimizes

Uses constant propagation to resolve deterministic branches, then computes
reachable PCs from the entry point.  Unreachable instructions are removed and
labels are remapped to form a compact program.  Deterministic `ifgoto`
instructions are replaced with `goto`.
-/

namespace DCEOpt

-- ============================================================
-- § 1. Smart successors using constant analysis
-- ============================================================

/-- Successors of `pc` considering constant analysis: deterministic
    branches follow only the taken direction. -/
def smartSuccessors (prog : Prog) (consts : Array (Option ConstPropOpt.ConstMap))
    (pc : Nat) : List Nat :=
  match prog[pc]? with
  | some (.ifgoto b l) =>
    match consts[pc]? with
    | some (some cm) =>
      match ConstPropOpt.evalBoolConst cm b with
      | some true  => [l]
      | some false => [pc + 1]
      | none       => [l, pc + 1]
    | _ => [l, pc + 1]
  | some instr => successors instr pc
  | none => []

-- ============================================================
-- § 2. Reachability analysis
-- ============================================================

private partial def reachLoop (prog : Prog)
    (consts : Array (Option ConstPropOpt.ConstMap))
    (visited : Array Bool) (worklist : List Nat) : Array Bool :=
  match worklist with
  | [] => visited
  | pc :: rest =>
    if pc < prog.size && !(visited.getD pc false) then
      let visited' := visited.set! pc true
      let succs := smartSuccessors prog consts pc
      reachLoop prog consts visited' (succs ++ rest)
    else
      reachLoop prog consts visited rest

/-- Compute the set of reachable PCs from PC 0, using smart successors. -/
def reachable (prog : Prog) (consts : Array (Option ConstPropOpt.ConstMap))
    : Array Bool :=
  reachLoop prog consts (Array.replicate prog.size false) (0 :: [])


-- ============================================================
-- § 4. Transform instructions
-- ============================================================

/-- Transform a single original instruction: remap labels,
    replace deterministic ifgoto with goto. -/
def transformInstr (prog : Prog) (consts : Array (Option ConstPropOpt.ConstMap))
    (revMap : Array Nat) (origPC : Nat) : TAC :=
  match prog[origPC]? with
  | some (.const x n)      => .const x n
  | some (.copy x y)       => .copy x y
  | some (.binop x op y z) => .binop x op y z
  | some (.boolop x b)     => .boolop x b
  | some (.arrLoad x arr idx)   => .arrLoad x arr idx
  | some (.arrStore arr idx val) => .arrStore arr idx val
  | some .halt             => .halt
  | some (.goto l)         => .goto (revMap.getD l 0)
  | some (.ifgoto b l) =>
    match consts[origPC]? with
    | some (some cm) =>
      match ConstPropOpt.evalBoolConst cm b with
      | some true  => .goto (revMap.getD l 0)
      | some false => .goto (revMap.getD (origPC + 1) 0)
      | none       => .ifgoto b (revMap.getD l 0)
    | _ => .ifgoto b (revMap.getD l 0)
  | none => .halt

/-- Build the compacted program from reachable PCs. -/
def transformProg (prog : Prog) (consts : Array (Option ConstPropOpt.ConstMap))
    (origMap : Array Nat) (revMap : Array Nat) : Prog :=
  let arr := (List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc => transformInstr prog consts revMap pc
    | none => .halt
  { code := arr.toArray, tyCtx := prog.tyCtx, observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 5. Certificate generation
-- ============================================================

/-- Invariants for the original program (indexed by orig PC). -/
def buildOrigInvariants (consts : Array (Option ConstPropOpt.ConstMap)) : Array EInv :=
  consts.map fun
    | some cm => ConstPropOpt.constMapToInv cm
    | none    => []

/-- Invariants for the transformed program (indexed by trans PC). -/
def buildTransInvariants (consts : Array (Option ConstPropOpt.ConstMap))
    (origMap : Array Nat) : Array EInv :=
  let arr := (List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc =>
      match consts[pc]? with
      | some (some cm) => ConstPropOpt.constMapToInv cm
      | _ => []
    | none => []
  arr.toArray

/-- Build per-instruction certificates.
    Each trans instruction corresponds to exactly one orig instruction step. -/
def buildInstrCerts (origMap : Array Nat) (trans : Prog) : Array EInstrCert :=
  let arr := (List.range trans.size).map fun i =>
    let origPC := origMap.getD i 0
    match trans[i]? with
    | some .halt =>
      { pc_orig := origPC, transitions := ([] : List ETransCorr) }
    | some (.const _ _) | some (.copy _ _) | some (.binop _ _ _ _) | some (.boolop _ _)
    | some (.arrLoad _ _ _) | some (.arrStore _ _ _) =>
      let nextOrigPC := origMap.getD (i + 1) 0
      { pc_orig := origPC, transitions := [{ origLabels := (nextOrigPC :: []) }] }
    | some (.goto l) =>
      let targetOrigPC := origMap.getD l 0
      { pc_orig := origPC, transitions := [{ origLabels := (targetOrigPC :: []) }] }
    | some (.ifgoto _ l) =>
      let takenOrigPC := origMap.getD l 0
      let fallOrigPC := origMap.getD (i + 1) 0
      { pc_orig := origPC,
        transitions := [{ origLabels := (takenOrigPC :: []) },
                        { origLabels := (fallOrigPC :: []) }] }
    | none => default
  arr.toArray

-- ============================================================
-- § 6. Main entry point
-- ============================================================

/-- Run dead code elimination on `prog` and produce a certified transformation.
    The result is an `ECertificate` that `checkCertificateExec` will accept. -/
def optimize (prog : Prog) : ECertificate :=
  let consts := ConstPropOpt.analyze prog
  let reached := reachable prog consts
  let origMap := _root_.buildOrigMap reached
  let revMap := _root_.buildRevMap origMap prog.size
  let trans := transformProg prog consts origMap revMap
  let inv_orig := buildOrigInvariants consts
  let inv_trans := buildTransInvariants consts origMap
  let instrCerts := buildInstrCerts origMap trans
  let haltCerts := _root_.buildHaltCerts instrCerts trans
  { orig := prog
    trans := trans
    inv_orig := inv_orig
    inv_trans := inv_trans
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := Array.replicate trans.size 0 }

end DCEOpt
