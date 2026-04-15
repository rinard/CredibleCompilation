import CredibleCompilation.DAEOpt

/-!
# Register Allocation Optimizer

Computes graph-coloring register allocation for TAC programs. Variables are
assigned to ARM64 registers when possible; remaining variables are spilled
to the stack.

The TAC program is unchanged (identity transformation). Register assignments
are consumed by CodeGen to emit register-aware instructions.

## Register budget

| Pool | Registers | Count |
|------|-----------|-------|
| Int scratch | x0, x1, x2 | 3 |
| Addr scratch | x8 | 1 |
| Int caller-saved | x3-x7, x9-x15 | 12 |
| Int callee-saved | x19-x28 | 10 |
| Reserved         | x16-x17 (IP0/IP1), x18 (platform) | 3 |
| Float scratch | d0, d1, d2 | 3 |
| Float allocatable | d3-d15 | 13 |

## Algorithm: graph coloring

1. Backward liveness analysis (reuse `DAEOpt.analyzeLiveness`)
2. Build interference graph: two variables interfere if both live at the
   same PC. Separate graphs for int and float variables.
3. Simplify: repeatedly remove nodes with degree < K, push onto stack
4. Spill selection: if no node has degree < K, spill the variable with
   the longest live range
5. Color: pop from stack, assign lowest-numbered available register
-/

namespace RegAllocOpt

-- ============================================================
-- § 1. Liveness helpers
-- ============================================================

/-- Collect all variables that appear in any liveOut set. -/
def collectLiveVars (liveOut : Array (List Var)) : List Var :=
  liveOut.foldl (fun acc lo =>
    lo.foldl (fun a v => if a.contains v then a else a ++ [v]) acc
  ) ([] : List Var)

/-- Compute the live range length for each variable (number of PCs where live). -/
def computeLiveRanges (liveOut : Array (List Var)) : List (Var × Nat) :=
  let vars := collectLiveVars liveOut
  vars.map fun v =>
    let range := liveOut.foldl (fun count lo =>
      if lo.contains v then count + 1 else count
    ) 0
    (v, range)

-- ============================================================
-- § 2. Interference graph
-- ============================================================

/-- Build interference graph: two variables interfere if both in liveOut at
    the same PC. Returns adjacency list. -/
def buildInterference (vars : List Var) (liveOut : Array (List Var)) : List (Var × List Var) :=
  vars.map fun v =>
    let neighbors := vars.filter fun w =>
      v != w && liveOut.any fun lo => lo.contains v && lo.contains w
    (v, neighbors)

/-- Remove a node and all its edges from the graph. -/
def removeNode (graph : List (Var × List Var)) (v : Var) : List (Var × List Var) :=
  graph.filterMap fun (w, nbrs) =>
    if w == v then none
    else some (w, nbrs.filter (· != v))

/-- Get neighbors of a node in the graph. -/
def neighbors (graph : List (Var × List Var)) (v : Var) : List Var :=
  match graph.find? (fun (x, _) => x == v) with
  | some (_, nbrs) => nbrs
  | none => []

-- ============================================================
-- § 3. Graph coloring with spill selection
-- ============================================================

/-- Find the lowest non-negative integer not in the used set. -/
private def lowestAvailable (used : List Nat) : Nat :=
  let rec go (n : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => n
    | fuel + 1 => if used.contains n then go (n + 1) fuel else n
  go 0 (used.length + 1)

/-- Select the best variable to spill: longest live range (most likely to
    free other nodes by reducing degree). -/
private def selectSpill (graph : List (Var × List Var)) (liveRanges : List (Var × Nat)) : Var :=
  let graphVars := graph.map Prod.fst
  match graphVars with
  | [] => ""
  | v :: rest =>
    rest.foldl (fun best w =>
      let bestRange := match liveRanges.find? (fun (x, _) => x == best) with
        | some (_, r) => r | none => 0
      let wRange := match liveRanges.find? (fun (x, _) => x == w) with
        | some (_, r) => r | none => 0
      if wRange > bestRange then w else best
    ) v

/-- Graph coloring with spill selection.
    Returns (coloring: var → color index, spilled: list of spilled vars).
    Caller-saved registers are listed first in intRegNums/floatRegNums,
    so `lowestAvailable` naturally prioritizes them. -/
partial def graphColor (graph : List (Var × List Var)) (K : Nat)
    (liveRanges : List (Var × Nat))
    : List (Var × Nat) × List Var :=
  if graph.isEmpty then ([], [])
  else
    -- Try simplify: find node with degree < K
    match graph.find? (fun (_, nbrs) => nbrs.length < K) with
    | some (v, _) =>
      let nbrs_v := neighbors graph v
      let graph' := removeNode graph v
      let (coloring, spilled) := graphColor graph' K liveRanges
      -- Assign lowest color not used by colored neighbors
      let usedColors := coloring.filterMap fun (w, c) =>
        if nbrs_v.contains w then some c else none
      let color := lowestAvailable usedColors
      ((v, color) :: coloring, spilled)
    | none =>
      -- All nodes have degree ≥ K → spill the longest-lived variable
      let spillVar := selectSpill graph liveRanges
      let graph' := removeNode graph spillVar
      let (coloring, spilled) := graphColor graph' K liveRanges
      (coloring, spillVar :: spilled)

-- ============================================================
-- § 4. Register mapping
-- ============================================================

/-- Integer allocatable registers: x3-x7, x9-x15 (caller-saved), x19-x28 (callee-saved).
    Caller-saved listed first so graph coloring prefers them under low pressure.
    x0-x2 reserved as scratch, x8 reserved for array address,
    x16-x17 reserved (linker scratch IP0/IP1), x18 reserved (platform register). -/
def intRegNums : Array Nat :=
  #[3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15,   -- caller-saved (12)
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28]       -- callee-saved (10)

/-- Float allocatable registers: d3-d15 (13 total).
    d0-d2 reserved as scratch (d2 used by fcmp/fbinop fallback). -/
def floatRegNums : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Compute register allocation for a program.
    Returns a list of (variable_name, register_name) pairs.
    Register names are like "x3", "x10", "d5", etc. -/
def computeColoring (prog : Prog) : List (Var × String) :=
  if prog.size == 0 then []
  else
    let liveOut := DAEOpt.analyzeLiveness prog
    let allVars := collectLiveVars liveOut
    if allVars.isEmpty then []
    else
      let liveRanges := computeLiveRanges liveOut
      -- Separate int+bool (xN registers) from float (dN registers).
      -- Int and bool share the same physical registers but need consistent
      -- TAC types. We add type-conflict edges: int and bool variables always
      -- interfere, forcing each register color to have a single type.
      let intBoolVars := allVars.filter fun v => prog.tyCtx v != .float
      let floatVars := allVars.filter fun v => prog.tyCtx v == .float
      -- Build interference graph with type-conflict edges
      let baseGraph := buildInterference intBoolVars liveOut
      -- Add edges between every int-bool pair (different types must not share a color)
      let intBoolGraph := baseGraph.map fun (v, nbrs) =>
        let extraNbrs := intBoolVars.filter fun w =>
          v != w && prog.tyCtx v != prog.tyCtx w && !nbrs.contains w
        (v, nbrs ++ extraNbrs)
      let floatGraph := buildInterference floatVars liveOut
      -- Color each graph. Caller-saved registers are listed first in
      -- intRegNums/floatRegNums, so lowestAvailable naturally prioritizes them.
      -- CodeGen inserts save/restore around call sites for live caller-saved regs.
      let (intBoolColoring, _) := graphColor intBoolGraph intRegNums.size liveRanges
      let (floatColoring, _) := graphColor floatGraph floatRegNums.size liveRanges
      -- Determine the type of each color from the first variable that uses it
      let colorTypes := intBoolColoring.foldl (fun (acc : List (Nat × VarTy)) (v, c) =>
        if acc.any (fun (c', _) => c' == c) then acc
        else (c, prog.tyCtx v) :: acc
      ) ([] : List (Nat × VarTy))
      -- Map color indices to register names — all use __xN, typed per color
      let intBoolMap := intBoolColoring.filterMap fun (v, c) =>
        if h : c < intRegNums.size then some (v, s!"x{intRegNums[c]}")
        else none
      let floatMap := floatColoring.filterMap fun (v, c) =>
        if h : c < floatRegNums.size then some (v, s!"d{floatRegNums[c]}")
        else none
      intBoolMap ++ floatMap

-- ============================================================
-- § 5. TAC-level renaming
-- ============================================================

/-- Map a variable name through the coloring.
    Colored variables get register-prefixed names (__x{N} or __d{N});
    spilled variables keep their original names. -/
def renameVar (coloring : List (Var × String)) (v : Var) : Var :=
  match coloring.find? (fun (x, _) => x == v) with
  | some (_, reg) => s!"__{reg}"
  | none => v

/-- Rename all variables in a TAC instruction using the coloring. -/
def renameInstr (coloring : List (Var × String)) (instr : TAC) : TAC :=
  let r := renameVar coloring
  match instr with
  | .const x v       => .const (r x) v
  | .copy x y        => .copy (r x) (r y)
  | .binop x op y z  => .binop (r x) op (r y) (r z)
  | .boolop x be     => .boolop (r x) (renameBoolExpr coloring be)
  | .arrLoad x arr idx ty => .arrLoad (r x) arr (r idx) ty
  | .arrStore arr idx val ty => .arrStore arr (r idx) (r val) ty
  | .fbinop x op y z => .fbinop (r x) op (r y) (r z)
  | .intToFloat x y  => .intToFloat (r x) (r y)
  | .floatToInt x y  => .floatToInt (r x) (r y)
  | .floatUnary x op y => .floatUnary (r x) op (r y)
  | .fternop x op a b c => .fternop (r x) op (r a) (r b) (r c)
  | .goto l          => .goto l
  | .ifgoto be l     => .ifgoto (renameBoolExpr coloring be) l
  | .halt            => .halt
  | .printInt v      => .printInt (r v)
  | .printFloat v    => .printFloat (r v)
where
  renameBoolExpr (coloring : List (Var × String)) (be : BoolExpr) : BoolExpr :=
    let r := renameVar coloring
    match be with
    | .lit b       => .lit b
    | .bvar v      => .bvar (r v)
    | .cmp op a b  => .cmp op (renameExprVars r a) (renameExprVars r b)
    | .not e       => .not (renameBoolExpr coloring e)
    | .fcmp op a b => .fcmp op (renameExprVars r a) (renameExprVars r b)
  renameExprVars (r : Var → Var) : Expr → Expr
    | .var v  => .var (r v)
    | .lit n  => .lit n
    | .flit f => .flit f
    | .blit b => .blit b
    | e       => e  -- complex Expr: shouldn't occur in BoolExpr operands

/-- Generate copy-back instructions for observable variables that were renamed.
    Returns `copy origName regName` for each observable that has a coloring entry. -/
def copyBackInstrs (coloring : List (Var × String)) (observables : List Var) : List TAC :=
  observables.filterMap fun v =>
    match coloring.find? (fun (x, _) => x == v) with
    | some (_, reg) => some (.copy v (s!"__{reg}"))  -- copy r __x3
    | none => none

/-- Compute the PC offset array: for each original PC, how many extra instructions
    were inserted before it due to halt expansion. -/
def computePCMap (prog : Prog) (copyBacks : List TAC) : Array Nat :=
  let numCopyBacks := copyBacks.length
  let arr := (List.range prog.size).foldl (fun (acc : Array Nat × Nat) origPC =>
    let (arr, offset) := acc
    let arr' := arr.push (origPC + offset)
    match prog[origPC]? with
    | some .halt => (arr', offset + numCopyBacks)
    | _ => (arr', offset)
  ) (#[], 0)
  arr.1

/-- Build the renamed program from the coloring with copy-back before halts.
    ALL variables are renamed (including observables), but copy-back instructions
    are inserted before each halt to restore observable values to their original names.
    PCs are adjusted for the inserted instructions. -/
def renameProg (prog : Prog) (coloring : List (Var × String)) : Prog :=
  let copyBacks := copyBackInstrs coloring prog.observable
  let pcMap := computePCMap prog copyBacks
  let mapPC (origPC : Nat) : Nat := pcMap.getD origPC origPC
  let newCode := (List.range prog.size).foldl (fun acc origPC =>
    let instr := prog.code.getD origPC .halt
    let renamed := renameInstr coloring instr
    -- Adjust goto/ifgoto targets
    let adjusted : TAC := match renamed with
      | .goto l => .goto (mapPC l)
      | .ifgoto be l => .ifgoto be (mapPC l)
      | other => other
    match adjusted with
    | TAC.halt =>
      -- Insert copy-backs before halt
      acc ++ copyBacks ++ [TAC.halt]
    | i => acc ++ [i]
  ) ([] : List TAC)
  -- Build type context from the trans code: each defining instruction determines
  -- the type of the defined variable. This correctly handles register reuse
  -- (e.g., __x3 is bool when defined by boolop, int when defined by binop).
  -- For copy, the destination inherits the type of the source.
  let newTyCtx : Var → VarTy := newCode.toArray.foldl (fun ctx instr =>
    match instr with
    | .const x v        => fun w => if w == x then v.typeOf else ctx w
    | .copy x y         => fun w => if w == x then ctx y else ctx w
    | .binop x _ _ _    => fun w => if w == x then .int else ctx w
    | .boolop x _       => fun w => if w == x then .bool else ctx w
    | .fbinop x _ _ _   => fun w => if w == x then .float else ctx w
    | .intToFloat x _   => fun w => if w == x then .float else ctx w
    | .floatToInt x _   => fun w => if w == x then .int else ctx w
    | .floatUnary x _ _  => fun w => if w == x then .float else ctx w
    | .fternop x _ _ _ _ => fun w => if w == x then .float else ctx w
    | .arrLoad x _ _ ty => fun w => if w == x then ty else ctx w
    | _                  => ctx
  ) prog.tyCtx
  { code := newCode.toArray
    tyCtx := newTyCtx
    observable := prog.observable
    arrayDecls := prog.arrayDecls }

-- ============================================================
-- § 6. Expression relation computation (forward worklist)
-- ============================================================

/-- Compute expression relations on the ORIG program.
    At each orig PC, the relation tracks `(.var origName, .var regName)` pairs.
    We use the orig instruction to determine the defined variable, then look up
    its register name in the coloring. This correctly handles register reuse
    (e.g., x3 used for a, d, e, r at different PCs). -/
partial def computeOrigRels (prog : Prog) (coloring : List (Var × String))
    : Array EExprRel :=
  if prog.size == 0 then #[]
  else
    let init := (Array.replicate prog.size (none : Option EExprRel)).set! 0 (some ([] : EExprRel))
    let result := relLoop prog coloring init (0 :: ([] : List Nat))
    result.map fun
      | some rel => rel
      | none => ([] : EExprRel)
where
  relMerge (a b : EExprRel) : EExprRel :=
    a.filter fun (eo, et) => b.any fun (eo', et') => eo == eo' && et == et'
  relBeq (a b : EExprRel) : Bool :=
    a.length == b.length && a.all fun (eo, et) => b.any fun (eo', et') => eo == eo' && et == et'
  relTransfer (rel : EExprRel) (_pc : Nat) (instr : TAC) (coloring : List (Var × String)) : EExprRel :=
    match DAEOpt.instrDef instr with
    | some origVar =>
      let regVar := renameVar coloring origVar
      -- Drop old entries whose trans side is this register (handles register reuse)
      let rel' := rel.filter fun (_, et) => et != .var regVar
      if regVar != origVar then
        -- Colored: add (.var origName, .var regName)
        (.var origVar, .var regVar) :: rel'
      else
        -- Identity: add (.var v, .var v) so free-variable coverage holds
        (.var origVar, .var origVar) :: rel'
    | none => rel
  relLoop (prog : Prog) (coloring : List (Var × String))
      (rels : Array (Option EExprRel)) (worklist : List Nat) : Array (Option EExprRel) :=
    match worklist with
    | [] => rels
    | pc :: rest =>
      match prog[pc]?, rels[pc]? with
      | some instr, some (some rel) =>
        let out := relTransfer rel pc instr coloring
        let succs := successors instr pc
        let (rels', newWork) := succs.foldl (fun (arr, wl) pc' =>
          if pc' < arr.size then
            match arr[pc']? with
            | some none | none =>
              (arr.set! pc' (some out), pc' :: wl)
            | some (some old) =>
              let merged := relMerge old out
              if relBeq merged old then (arr, wl)
              else (arr.set! pc' (some merged), pc' :: wl)
          else (arr, wl)
        ) (rels, rest)
        relLoop prog coloring rels' newWork
      | _, _ => relLoop prog coloring rels rest

/-- Map orig-PC-indexed rels to trans-PC-indexed rels.
    Non-copy-back PCs get the rel from the corresponding orig PC.
    Copy-back groups (before each halt) are processed sequentially:
    each copy-back `copy origName regName` removes the `(*, .var regName)`
    entry from the flowing relation. -/
private def isCB (trans : Prog) (origPCMap : Array Nat) (tpc : Nat) : Bool :=
  let opc := origPCMap.getD tpc tpc
  let nextOpc := origPCMap.getD (tpc + 1) (tpc + 1)
  opc == nextOpc && match trans[tpc]? with | some (.copy _ _) => true | _ => false

def mapRelsToTrans (origRels : Array EExprRel) (origPCMap : Array Nat)
    (trans : Prog) : Array EExprRel :=
  -- First pass: assign base rels from orig
  let baseRels : Array EExprRel := ((List.range trans.size).map fun tpc =>
    let opc := origPCMap.getD tpc tpc
    origRels.getD opc ([] : EExprRel)).toArray
  -- Second pass: for copy-back sequences, flow the rel forward
  -- After each `copy dest src`, replace the rename pair (orig, .var src) with
  -- an identity pair (.var dest, .var dest) since dest now holds orig's value.
  (List.range trans.size).foldl (fun (rels : Array EExprRel) tpc =>
    let curIsCB := isCB trans origPCMap tpc
    let prevIsCB := tpc > 0 && isCB trans origPCMap (tpc - 1)
    if curIsCB && prevIsCB then
      -- Continuing copy-back sequence: apply previous copy's effect
      match trans[tpc - 1]? with
      | some (.copy dest src) =>
        let prevRel := rels.getD (tpc - 1) ([] : EExprRel)
        let filtered := prevRel.filter fun (_, et) => et != Expr.var src
        rels.set! tpc ((.var dest, .var dest) :: filtered)
      | _ => rels
    else if !curIsCB && prevIsCB then
      -- Halt right after copy-backs: apply final copy's effect
      match trans[tpc - 1]? with
      | some (.copy dest src) =>
        let prevRel := rels.getD (tpc - 1) ([] : EExprRel)
        let filtered := prevRel.filter fun (_, et) => et != Expr.var src
        rels.set! tpc ((.var dest, .var dest) :: filtered)
      | _ => rels
    else
      rels
  ) baseRels

-- ============================================================
-- § 7. Certificate generation
-- ============================================================

/-- Build the reverse PC map: for each trans PC, what is the corresponding orig PC.
    Copy-back instructions before a halt share the halt's orig PC. -/
def buildRevPCMap (prog : Prog) (pcMap : Array Nat) (transSize : Nat) : Array Nat :=
  let arr := Array.replicate transSize 0
  -- For each orig PC, fill its trans PC and any copy-back PCs before the next orig PC
  (List.range prog.size).foldl (fun arr origPC =>
    let transPC := pcMap.getD origPC origPC
    -- Fill from transPC to the next orig PC's transPC (or transSize)
    let nextTransPC := if origPC + 1 < pcMap.size then pcMap.getD (origPC + 1) transSize
                       else transSize
    (List.range (nextTransPC - transPC)).foldl (fun arr offset =>
      arr.set! (transPC + offset) origPC
    ) arr
  ) arr

/-- Build instrCerts for RegAlloc with PC mapping from orig to trans.
    Copy-back instructions use zero-step orig paths (origLabels = []). -/
def buildRegAllocInstrCerts (trans : Prog) (rels : Array EExprRel)
    (origPCMap : Array Nat) : Array EInstrCert :=
  let arr := (List.range trans.size).map fun i =>
    let rel := rels.getD i ([] : EExprRel)
    let relNext (target : Nat) : EExprRel := rels.getD target ([] : EExprRel)
    let pc_orig := origPCMap.getD i i
    match trans[i]? with
    | some .halt =>
      { pc_orig := pc_orig, rel := rel, transitions := ([] : List ETransCorr) }
    | some (.goto l) =>
      let origTarget := origPCMap.getD l l
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := relNext l }] }
    | some (.ifgoto _ l) =>
      let origTarget := origPCMap.getD l l
      let origFall := origPCMap.getD (i + 1) (i + 1)
      { pc_orig := pc_orig, rel := rel,
        transitions := [{ origLabels := [origTarget], rel := rel, rel_next := relNext l },
                        { origLabels := [origFall], rel := rel, rel_next := relNext (i + 1) }] }
    | some _ =>
      if isCB trans origPCMap i then
        -- Copy-back: zero-step orig path (empty labels, stay at same orig PC)
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [], rel := rel, rel_next := relNext (i + 1) }] }
      else
        let origNext := origPCMap.getD (i + 1) (i + 1)
        { pc_orig := pc_orig, rel := rel,
          transitions := [{ origLabels := [origNext], rel := rel, rel_next := relNext (i + 1) }] }
    | none => default
  arr.toArray

-- ============================================================
-- § 8. Main entry point
-- ============================================================

/-- Register allocation as an optimization pass. Renames TAC variables to
    register names (__x{N}/__d{N}) and produces a certificate with expression
    relations tracking the renaming. -/
def optimize (prog : Prog) : ECertificate :=
  let coloring := computeColoring prog
  let trans := renameProg prog coloring
  let copyBacks := copyBackInstrs coloring prog.observable
  let pcMap := computePCMap prog copyBacks
  let origPCMap := buildRevPCMap prog pcMap trans.size
  let origRels := computeOrigRels prog coloring
  let rels := mapRelsToTrans origRels origPCMap trans
  let consts_orig := ConstPropOpt.analyze prog
  let inv_orig := ConstPropOpt.buildInvariants consts_orig
  let consts_trans := ConstPropOpt.analyze trans
  let inv_trans := ConstPropOpt.buildInvariants consts_trans
  let instrCerts := buildRegAllocInstrCerts trans rels origPCMap
  let haltCerts := buildHaltCerts instrCerts trans
  -- Measures: copy-back PCs count down to 0 at halt
  -- For a group of N copy-backs before halt, measures are N, N-1, ..., 1, 0
  let measure := (List.range trans.size).map fun tpc =>
    if isCB trans origPCMap tpc then
      -- Count how many copy-backs remain after this one (including halt)
      let remaining := (List.range (trans.size - tpc)).filter fun offset =>
        isCB trans origPCMap (tpc + offset)
      remaining.length
    else 0
  { orig := prog
    trans := trans
    inv_orig := inv_orig
    inv_trans := inv_trans
    instrCerts := instrCerts
    haltCerts := haltCerts
    measure := measure.toArray }

end RegAllocOpt
