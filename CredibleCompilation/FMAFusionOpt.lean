import CredibleCompilation.DAEOpt
import CredibleCompilation.PeepholeOpt

/-!
# FMA Fusion Optimizer

Fuses adjacent `fmul` + `fadd`/`fsub` pairs into single `fmadd`/`fmsub`
ternary instructions, then compacts the program (removing the absorbed fmul).

## What it optimizes

**Pattern 1 — fmadd:**
  `t := fmul(b, c);  x := fadd(a, t)`  →  `x := fmadd(a, b, c)`
  `t := fmul(b, c);  x := fadd(t, a)`  →  `x := fmadd(a, b, c)`

**Pattern 2 — fmsub:**
  `t := fmul(b, c);  x := fsub(a, t)`  →  `x := fmsub(a, b, c)`

Constraints: the two instructions are adjacent, no jump targets the second,
the temp `t` is dead after the fadd/fsub, and `t ≠ a`.

## Certificate strategy

Identity expression relations throughout — `FloatTernOp.eval .fmadd a b c`
is definitionally `FloatBinOp.eval .fadd a (FloatBinOp.eval .fmul b c)`.
At fused PCs the `origLabels` path covers both original instructions.
-/

namespace FMAFusionOpt

-- ============================================================
-- § 1. Pattern detection
-- ============================================================

/-- Check whether `pc` starts a fusible fmul+fadd/fsub pair.
    Returns `(dst, ternOp, addend, mulL, mulR)` on success. -/
def isFusible (prog : Prog) (liveOut : Array (List Var))
    (preds : Array (List Nat)) (pc : Nat)
    : Option (Var × FloatTernOp × Var × Var × Var) :=
  match prog[pc]?, prog[pc + 1]? with
  | some (.fbinop t .fmul b c), some (.fbinop x .fadd lhs rhs) =>
    -- pc+1 must not be a branch target from elsewhere
    let predsOf := preds.getD (pc + 1) ([] : List Nat)
    if predsOf.length > 1 || (predsOf.length == 1 && !predsOf.contains pc) then none
    else
      -- t must be dead after the fadd
      let live := liveOut.getD (pc + 1) ([] : List Var)
      if live.contains t then none
      else if t == rhs && t != lhs then
        -- x := fadd(a, t) → fmadd(a, b, c)
        -- fmadd semantics: a + b*c, matching fadd(a, fmul(b,c))
        some (x, .fmadd, lhs, b, c)
      else none
  | some (.fbinop t .fmul b c), some (.fbinop x .fsub lhs rhs) =>
    -- fsub: only a - t pattern (not t - a, which would be -(a - b*c))
    let predsOf := preds.getD (pc + 1) ([] : List Nat)
    if predsOf.length > 1 || (predsOf.length == 1 && !predsOf.contains pc) then none
    else
      let live := liveOut.getD (pc + 1) ([] : List Var)
      if live.contains t then none
      else if t == rhs && t != lhs then
        some (x, .fmsub, lhs, b, c)
      else none
  | _, _ => none

-- ============================================================
-- § 2. Scan for all fusible pairs
-- ============================================================

/-- Find all fusible PCs.  Returns parallel arrays:
    - `removed[pc] = true` for the fmul that gets absorbed
    - `replaced` maps each fadd/fsub PC to its fternop replacement
    - `deadTemps[pc]` records the dead temp var at fmul PC `pc` -/
def findFusions (prog : Prog) (liveOut : Array (List Var))
    (preds : Array (List Nat))
    : Array Bool × Array (Option TAC) × Array (Option Var) :=
  let n := prog.size
  let init := (Array.replicate n false, Array.replicate n (none : Option TAC),
               Array.replicate n (none : Option Var))
  (List.range n).foldl (fun (removed, replaced, deadTemps) pc =>
    -- Skip if this PC is already the second half of a previous fusion
    if removed.getD pc false then (removed, replaced, deadTemps)
    else match prog[pc]? with
    | some (.fbinop t .fmul _ _) =>
      match isFusible prog liveOut preds pc with
      | some (dst, op, a, b, c) =>
        (removed.set! pc true,
         replaced.set! (pc + 1) (some (.fternop dst op a b c)),
         deadTemps.set! pc (some t))
      | none => (removed, replaced, deadTemps)
    | _ => (removed, replaced, deadTemps)
  ) init

-- ============================================================
-- § 3. Transformation (pre-compact)
-- ============================================================

/-- Apply fusions: replace fadd/fsub with fternop, mark fmul as removed. -/
def applyFusions (prog : Prog) (replaced : Array (Option TAC)) : Prog :=
  let arr := (List.range prog.size).map fun pc =>
    match replaced[pc]? with
    | some (some instr) => instr
    | _ => match prog[pc]? with
      | some instr => instr
      | none => .halt
  { code := arr.toArray, tyCtx := prog.tyCtx,
    observable := prog.observable, arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 4. Compaction (reuses ExecChecker infrastructure)
-- ============================================================

/-- Remap goto/ifgoto labels through skip and reverse maps. -/
def transformInstr (instr : TAC) (skipArr : Array Nat)
    (revMap : Array Nat) : TAC :=
  match instr with
  | .goto l    => .goto (revMap.getD (skipArr.getD l l) 0)
  | .ifgoto b l => .ifgoto b (revMap.getD (skipArr.getD l l) 0)
  | other      => other

/-- Build the compacted program from the fused (pre-compact) program. -/
def compactProg (fused : Prog) (origMap : Array Nat)
    (skipArr : Array Nat) (revMap : Array Nat) : Prog :=
  { code := ((List.range origMap.size).map fun i =>
    match origMap[i]? with
    | some pc =>
      match fused[pc]? with
      | some instr => transformInstr instr skipArr revMap
      | none => .halt
    | none => .halt).toArray,
    tyCtx := fused.tyCtx,
    observable := fused.observable,
    arrayDecls := fused.arrayDecls }

-- ============================================================
-- § 5. Certificate generation
-- ============================================================

/-- Build a path `[start, start+1, ..., end_]` (inclusive). -/
def buildPath (start end_ : Nat) : List Nat :=
  if start > end_ then [end_]
  else (List.range (end_ - start + 1)).map (· + start)

/-- Compute pc_orig for each trans PC: normally origMap[i], but for
    fused instructions it backs up one to include the removed fmul. -/
def buildPcOrigMap (origMap : Array Nat) (removed : Array Bool)
    (transSize : Nat) : Array Nat :=
  ((List.range transSize).map fun i =>
    let origPC := origMap.getD i 0
    if removed.getD (origPC - 1) false then origPC - 1
    else origPC).toArray

/-- Build per-instruction certificates.
    For fused instructions, origLabels covers both the removed fmul
    and the replaced fadd/fsub in the original program. -/
def buildInstrCerts (origProg : Prog) (origMap : Array Nat)
    (skipArr : Array Nat) (trans : Prog) (allVars : List Var)
    (removed : Array Bool) (deadTemps : Array (Option Var)) : Array EInstrCert :=
  -- Collect all dead temp vars from fusions
  let deadTempVars := deadTemps.foldl (fun acc dt =>
    match dt with | some t => t :: acc | none => acc) ([] : List Var)
  -- Identity relation excluding dead temps (they diverge between orig and trans
  -- after the fusion point; since they're dead, no downstream instruction reads them)
  let baseRel : EExprRel := allVars.filter (fun v => !deadTempVars.contains v)
    |>.map fun v => (.var v, .var v)
  let pcOrigMap := buildPcOrigMap origMap removed trans.size
  ((List.range trans.size).map fun i =>
    let myPcOrig := pcOrigMap.getD i 0
    let nextPcOrig := pcOrigMap.getD (i + 1) 0
    match trans[i]? with
    | some .halt =>
      { pc_orig := myPcOrig, rel := baseRel,
        transitions := ([] : List ETransCorr) }
    | some (.goto _) =>
      let origTarget := match origProg[myPcOrig]? with
        | some (.goto l) => l
        | _ => myPcOrig + 1
      let finalOrigTarget := skipArr.getD origTarget origTarget
      { pc_orig := myPcOrig, rel := baseRel,
        transitions := [{ origLabels := buildPath origTarget finalOrigTarget,
                          rel := baseRel, rel_next := baseRel }] }
    | some (.ifgoto _ _) =>
      let origTaken := match origProg[myPcOrig]? with
        | some (.ifgoto _ l) => l
        | _ => myPcOrig
      let takenFinal := skipArr.getD origTaken origTaken
      { pc_orig := myPcOrig, rel := baseRel,
        transitions := [{ origLabels := buildPath origTaken takenFinal,
                          rel := baseRel, rel_next := baseRel },
                        { origLabels := buildPath (myPcOrig + 1) nextPcOrig,
                          rel := baseRel, rel_next := baseRel }] }
    | some _ =>
      let origPC := origMap.getD i 0
      if removed.getD (origPC - 1) false then
        -- Fused: orig executes fmul at origPC-1, then fadd at origPC
        { pc_orig := origPC - 1, rel := baseRel,
          transitions := [{ origLabels := origPC :: buildPath (origPC + 1) nextPcOrig,
                            rel := baseRel, rel_next := baseRel }] }
      else
        { pc_orig := origPC, rel := baseRel,
          transitions := [{ origLabels := buildPath (origPC + 1) nextPcOrig,
                            rel := baseRel, rel_next := baseRel }] }
    | none => default).toArray

-- ============================================================
-- § 6. Main entry point
-- ============================================================

/-- Run FMA fusion optimization: fuse fmul+fadd/fsub into fmadd/fmsub,
    compact the program, and produce a certified transformation. -/
def optimize (prog : Prog) : ECertificate :=
  let n := prog.size
  let liveOut := DAEOpt.analyzeLiveness prog
  let preds := DAEOpt.buildPredecessors prog
  let (removed, replaced, deadTemps) := findFusions prog liveOut preds
  -- Check if any fusions found; if not, return identity certificate
  if removed.toList.all (!·) then
    let allVars := collectAllVars prog prog
    let idRel : EExprRel := allVars.map fun v => (.var v, .var v)
    let instrCerts := ((List.range n).map fun i =>
      match prog[i]? with
      | some .halt =>
        { pc_orig := i, rel := idRel,
          transitions := ([] : List ETransCorr) }
      | some (.goto l) =>
        { pc_orig := i, rel := idRel,
          transitions := [{ origLabels := [l], rel := idRel, rel_next := idRel }] }
      | some (.ifgoto _ l) =>
        { pc_orig := i, rel := idRel,
          transitions := [{ origLabels := [l], rel := idRel, rel_next := idRel },
                          { origLabels := [i + 1], rel := idRel, rel_next := idRel }] }
      | some _ =>
        { pc_orig := i, rel := idRel,
          transitions := [{ origLabels := [i + 1], rel := idRel, rel_next := idRel }] }
      | none => default).toArray
    let haltCerts := buildHaltCerts instrCerts prog
    { orig := prog
      trans := prog
      inv_orig := Array.replicate n ([] : EInv)
      inv_trans := Array.replicate n ([] : EInv)
      instrCerts := instrCerts
      haltCerts := haltCerts
      measure := Array.replicate n 0 }
  else
    -- Apply fusions and compact
    let fused := applyFusions prog replaced
    let kept := removed.map (!·)
    let origMap := buildOrigMap kept
    let revMap := buildRevMap origMap n
    let skipArr := PeepholeOpt.buildSkipArr removed
    let trans := compactProg fused origMap skipArr revMap
    let allVars := collectAllVars prog trans
    let instrCerts := buildInstrCerts prog origMap skipArr trans allVars removed deadTemps
    let haltCerts := buildHaltCerts instrCerts trans
    { orig := prog
      trans := trans
      inv_orig := Array.replicate n ([] : EInv)
      inv_trans := Array.replicate trans.size ([] : EInv)
      instrCerts := instrCerts
      haltCerts := haltCerts
      measure := Array.replicate trans.size 0 }

end FMAFusionOpt
