# Register-allocator spill heuristic (2026-04-26, late session)

Replaced the FIL register allocator's spill heuristic with a Chaitin-style
cost-per-degree, weighted by loop depth. Heavy-kernel runtime drops
**1.55–1.85×** with the verified-cert pipeline still validating all 24
canonical Livermore kernels.

## Problem

Profiling the worst FIL-O2 / gfortran-O2 gap kernels (k08_adi 8.5×,
k15_casual 10.2×, k18_hydro_2d 10.3×) showed the dominant cost was
**stack spilling inside the inner loop body**:

| Kernel | Axon spills (ldr/str sp) | F-O2 spills | Axon `adrp` | F-O2 `adrp` |
|---|---|---|---|---|
| k08_adi | 411 | 0 | 51 | 20 |
| k15_casual | 466 | 0 | 45 | 19 |
| k18_hydro_2d | 573 | 0 | 65 | 26 |

Each `ldr xN, [sp, #M]` is a wasted L1-cache hit for what should be a
register-resident value. F-O2 keeps everything in registers through the
inner loop; FIL was spilling 400–600 values per iteration.

## Root cause

`RegAllocOpt.selectSpill` used "spill the variable with the longest
live range" as its heuristic:

```lean
-- BEFORE: pick the var alive at the most PCs
if wRange > bestRange then w else best
```

Long live range was used as a proxy for "node with the most interferences
(highest degree)". But for our IR shape it actively targets the **wrong**
variables:

- Loop-invariant constants like `101` (the column stride): live across the
  whole loop body (long range), used inside an inner loop (high frequency).
  These should be in a register.
- Array base addresses (TAC variables holding the result of `adrp+add`):
  live for the whole loop, used at every array access.
- Loop induction variables: same.

All three are precisely what the conventional Chaitin cost function
*protects*. Ours was *targeting* them.

### Probe (probe 3 from the analysis): direction check

Flipped the comparison to `wRange < bestRange` (shortest-live-range spill).
Result on heavy kernels:

| Kernel | Original (longest spill) | Probe (shortest spill) |
|---|---|---|
| k08_adi | 20.96 s | 57.86 s (2.76× **slower**) |
| k15_casual | 19.57 s | 30.89 s (1.58× slower) |
| k18_hydro_2d | 20.34 s | 55.39 s (2.72× slower) |

So the original direction was approximately right — long-range *should*
generally be more spillable than short-range — but it ignores use density
and loop residency. The fix is the standard Chaitin cost, not a flip.

## Fix

`RegAllocOpt.lean` got three new pieces (~50 lines total):

1. **`findBackEdges : Prog → List (Nat × Nat)`** — a back edge is any
   `goto` or `ifgoto` whose target is ≤ the source PC. The TAC `successors`
   function already had everything we need.

2. **`computeLoopDepth : Prog → Array Nat`** — for each PC, count how many
   back-edge ranges `[header, latch]` contain it. Nested loops naturally
   accumulate depth.

3. **`computeUseCost : Prog → Array Nat → List (Var × Nat)`** — for each
   variable, sum `10^loop_depth(pc)` over every PC where the variable is
   used. A variable used at depth-2 contributes 100 per use; depth-1 = 10;
   straight-line code = 1.

4. **`selectSpill`** rewritten to minimize **`useCost(v) / degree(v)`**
   via cross-multiplication on naturals (no division):

   ```lean
   if wC * (max bestD 1) < bestC * (max wD 1) then w else best
   ```

   Variables with low Chaitin cost (few/cheap uses) and high degree (many
   interferences) are the best spill candidates — exactly the conventional
   choice.

`graphColor` and `computeColoring` have one parameter swap each
(`liveRanges` → `useCost`). No other call sites.

## Validation

Running `./run_fast.sh` (24 kernels × 3 variants × 1 run, ÷1000 NREPS):
**24/24 pass** the cert validator under the new heuristic. Since the
allocator is unverified (credible compilation: certificate-checked at
runtime), validation is "compile, run, observe outputs match across .f /
.c / .w within 1e-4". No proof obligations.

## Results

Best-of-3 wall-clock seconds at full NREPS (calibrated for ~20s
FIL-O2 baseline):

| Kernel | Before | After | Speedup | FIL-O2/F-O2 ratio |
|---|---|---|---|---|
| k08_adi | 20.96 | **11.30** | **1.85×** | 8.50× → 4.57× |
| k15_casual | 19.57 | **12.60** | **1.55×** | 10.22× → 6.56× |
| k18_hydro_2d | 20.34 | **12.99** | **1.57×** | 10.34× → 6.59× |
| k09_integrate | 19.68 | **14.57** | **1.35×** | 5.36× → 3.97× |
| k07_eos | 20.74 | 20.39 | 1.02× | 4.00× → 3.93× |
| k21_matmul | 20.31 | 20.11 | 1.01× | 4.97× → 4.92× |

The three worst-gap kernels (k08, k15, k18) all improved by 1.55–1.85×.
K07 and k21 saw no change: their gaps are dominated by F-O2 vectorization
or polynomial scheduling, not register allocation, so the new heuristic
has nothing to optimize.

## What this didn't fix

The 6× residual gap on k15/k18 has shifted to a different bottleneck:
**address-base rematerialization**. Every `arrLoad` and `arrStore` still
emits a fresh `adrp + add + ldr` triple. For k18 with 9 distinct arrays,
that's 65 `adrp`s where 9 should suffice. F-O2 holds each array base in
a dedicated register (one `adrp` per array per loop entry).

Fixing this requires a TAC-level pass that introduces a virtual `arrayBase`
variable per array, which then naturally falls under register allocation
and LICM. Not a register-allocator problem; a code-generation problem.
Estimated 2 days work; expected 30–50% additional speedup on memory-heavy
kernels.

## Effort accounting

- Reading existing allocator + DAEOpt liveness helpers: 30 min
- Writing back-edge / loop-depth / use-cost analyses: 1 hour
- Rewriting `selectSpill` and threading `useCost` through `graphColor` /
  `computeColoring`: 30 min
- Compile + cert validation + benchmark cycles: 30 min
- **Total: ~2.5 hours**

The credible-compilation contract makes this kind of work cheap: no proof
obligations on algorithm changes, just "does the cert validator still
accept the output?" If yes, ship.

## Next priorities

Ranked by impact-per-day:

1. **Address-base hoisting** (2 days, 30–50% additional speedup on memory
   kernels). Highest single remaining win.
2. **Coalescing on `x := y` copies** (1 day, 10–20% broad). Compounds with
   above.
3. **Re-enable bounds-check elision via the existing `BoundsOptCert` plan**
   (1–3 days, 5–10% on bounds-heavy kernels).
4. **Auto-vectorization for stride-1 stencils** (multi-week, caps the ratio
   at ~1.1–1.2× but only for the ~6 kernels F-O2 vectorizes anyway).

After (1)+(2)+(3), I'd estimate FIL-O2 / F-O2 geomean drops from current
~2.0× toward 1.3–1.5×.
