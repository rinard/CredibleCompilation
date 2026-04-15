# FMA Fusion Optimization Pass

## Context

The compiler generates `fmul` followed by `fadd` as two separate `fbinop` TAC instructions, which compile to two ARM instructions. The TAC IR already has `fternop .fmadd` (and `.fmsub`) which compiles to a single ARM `fmaddR` instruction. This pass fuses the two-instruction pattern into one, reducing instruction count and enabling hardware FMA.

The semantics are definitionally equal — `FloatTernOp.eval .fmadd a b c` unfolds to `FloatBinOp.eval .fadd a (FloatBinOp.eval .fmul b c)` in Core.lean:334-335.

## Patterns to Fuse

**Pattern 1 — fmadd:** `t := fmul(b, c); x := fadd(a, t)` or `x := fadd(t, a)` → `x := fmadd(a, b, c)`
**Pattern 2 — fmsub:** `t := fmul(b, c); x := fsub(a, t)` → `x := fmsub(a, b, c)`

Constraints for fusion:
- The two instructions must be **adjacent** (consecutive PCs, no control flow between them)
- The temp `t` must **not be live** after the fadd/fsub (otherwise we'd lose its value)
- The temp `t` must not be the same as `a` (would be overwritten before use in fadd)
- The fmul must not be a branch target (no incoming jumps between the pair)

## New File

**`CredibleCompilation/FMAFusionOpt.lean`** — follows the Peephole pass structure (compacting pass)

### Section 1: Pattern Detection

```
def isFusible (prog : Prog) (liveOut : Array (List Var)) (pc : Nat) :
    Option (Var × FloatTernOp × Var × Var × Var)
```

- Check `prog[pc]? = fbinop t .fmul b c` and `prog[pc+1]? = fbinop x .fadd a t'` (or `fadd t' a`) where `t == t'`
- Also match fsub variant for fmsub
- Verify `t` not in `liveOut[pc+1]` (reuse DAEOpt.analyzeLiveness)
- Verify `t != a` (avoid clobbering the addend)
- Verify no jumps target `pc+1` (use predecessor analysis — if `pc+1` has any predecessor other than `pc`, skip)

### Section 2: Transformation

Mark fusible fmul PCs as "removed" and replace the fadd at `pc+1` with `fternop x op a b c`. Then compact the program using the existing `buildOrigMap`/`buildRevMap`/`buildSkipArr` infrastructure from ExecChecker.lean.

For each fusible pair at `(pc, pc+1)`:
- `removed[pc] = true` (the fmul is absorbed)
- `prog'[pc+1] = .fternop x op a b c` (the fadd becomes fmadd)

Then compact using existing helpers to remove the marked instructions and remap labels.

### Section 3: Certificate Generation

Uses identity expression relations (all variables equal on both sides) — this is sound because `FloatTernOp.eval .fmadd` is definitionally `fadd(a, fmul(b,c))`.

For the fused instruction, `origLabels` includes the path through both original PCs (the removed fmul and the replaced fadd), same pattern as Peephole's handling of removed NOPs.

### Section 4: Main Entry Point

```
def optimize (prog : Prog) : ECertificate
```

1. Run `DAEOpt.analyzeLiveness prog` to get liveOut info
2. Build predecessors to check jump targets
3. Scan for fusible pairs
4. Transform + compact
5. Build certificates
6. Return ECertificate

## Pipeline Integration

**File:** CodeGen.lean:1565-1575

Insert after DAE and before CSE:

```
let p ← applyPass "DAE" DAEOpt.optimize p
let p ← applyPass "FMAFusion" FMAFusionOpt.optimize p   -- NEW
let p ← applyPass "CSE" CSEOpt.optimize p
```

Rationale: After DAE cleans up dead assignments, the fmul+fadd pairs are likely adjacent. Before CSE, so CSE can further optimize around the fused instructions. Before RegAlloc, so register allocation sees the fused 3-operand instruction.

**File:** PipelineCorrectness.lean:196+ — add `hty_fma` and `htyO_fma` hypotheses to `optimizePipeline_preserves_behavior`, plus one more `bind_ok` decomposition step.

## Files to Modify

| File | Change |
|------|--------|
| `CredibleCompilation/FMAFusionOpt.lean` | **New file** — the optimization pass |
| `CredibleCompilation/CodeGen.lean` | Add import + insert pass in `optimizePipeline` |
| `CredibleCompilation/PipelineCorrectness.lean` | Add pass to pipeline correctness theorem |

## Key Reusable Infrastructure

- `DAEOpt.analyzeLiveness` — liveness analysis (DAEOpt.lean:100)
- `DAEOpt.buildPredecessors` — predecessor computation (DAEOpt.lean:34)
- `buildOrigMap`, `buildRevMap` — compaction maps (ExecChecker.lean:440-451)
- `PeepholeOpt.buildSkipArr` — skip array for removed PCs (PeepholeOpt.lean:43)
- `collectAllVars`, `buildHaltCerts` — certificate helpers (ExecChecker.lean:246, 430)

## Verification

1. `lake build` — ensure everything compiles with zero errors
2. Write a test program with `float x = a + b * c` and verify the optimized TAC contains `fternop fmadd` instead of separate `fbinop fmul` + `fbinop fadd`
3. Check generated ARM assembly contains `fmadd` instruction
4. Run existing benchmarks to confirm no regressions
5. Verify sorry count unchanged (pass should be sorry-free since semantics are definitionally equal)
