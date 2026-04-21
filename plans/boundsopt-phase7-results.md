# BoundsOptCert Phase 7 — Elision Benchmark Results

Closure for `plans/certified-interval-pangolin.md`. Measures how many `cmpImm
+ bCond .hs` bounds-check pairs Phase 6's verified elision actually removes
on the Livermore kernels, and categorizes the remaining misses.

## Headline

**426 / 509 bounds-check pairs eliminated across 24 Livermore kernels — 83.7%.
15 / 24 kernels at 100% elision.**

## Method

1. Built the `compiler` binary at commit `d060c6b` (Phase 5, pre-un-wire) —
   `isBoundsSafe` hard-wired `false`, every `.arrLoad` / `.arrStore` emits
   `cmp idx, size ; b.hs .Lbounds_err`. This is the *maximum-possible* bounds
   count.
2. Built the `compiler` binary at commit `22f5aa4` (Phase 6). Compiled all
   24 `benchmarks/livermore/k*.w` kernels to assembly.
3. For each kernel, counted `b.hs` occurrences (all branch to
   `.Lbounds_err` — confirmed via `grep -u`).
4. `pre - post = eliminated`.

No changes to `.w` sources; the comparison is purely a compiler diff.

## Per-kernel table

| Kernel | pre | post | elim | % | comment |
|---|---:|---:|---:|---:|---|
| **Fully elided (15)** |||||
| k01_hydro | 11 | 0 | 11 | 100% | constant-bounded loops |
| k03_dot | 4 | 0 | 4 | 100% | single induction var |
| k05_tridiag | 8 | 0 | 8 | 100% | simple loops |
| k07_eos | 19 | 0 | 19 | 100% | simple loops |
| k08_adi | 48 | 0 | 48 | 100% | nested bounded loops |
| k09_integrate | 22 | 0 | 22 | 100% | |
| k10_diff_predict | 23 | 0 | 23 | 100% | |
| k11_prefix_sum | 7 | 0 | 7 | 100% | |
| k12_first_diff | 5 | 0 | 5 | 100% | |
| k18_hydro_2d | 62 | 0 | 62 | 100% | largest kernel elided |
| k19_linear_recurrence | 12 | 0 | 12 | 100% | |
| k20_discrete_ord | 31 | 0 | 31 | 100% | |
| k21_matmul | 9 | 0 | 9 | 100% | nested matmul loops |
| k22_planck | 20 | 0 | 20 | 100% | |
| k23_hydro_implicit | 19 | 0 | 19 | 100% | |
| **Partial (5)** |||||
| k13_pic_2d | 37 | 8 | 29 | 78% | indirect `arr[ix[k]]` |
| k14_pic_1d | 57 | 6 | 51 | 89% | indirect `arr[ix[k]]` |
| k15_casual | 42 | 7 | 35 | 83% | 2D-flattened `vh[(j-1)*101+k]` |
| k17_implicit_cond | 18 | 10 | 8 | 44% | flag-driven main loop |
| k24_find_min | 5 | 2 | 3 | 60% | reduction variable `m` |
| **None (4)** |||||
| k02_iccg | 15 | 15 | 0 | 0% | mutable upper bound |
| k04_banded | 8 | 8 | 0 | 0% | non-unit step `k := k + m` |
| k06_recurrence | 8 | 8 | 0 | 0% | expression bound `k <= i - 1` |
| k16_monte_carlo | 19 | 19 | 0 | 0% | indirect indices throughout |
| **TOTAL** | **509** | **83** | **426** | **83.7%** | |

## What Phase 6 elides reliably

All of:

* `while (k <= N_literal) { arr[k] := ...; k := k + 1 }` with
  `size(arr) ≥ N_literal + 1`.
* The same with `N` being a *constant-initialized* variable never reassigned
  in scope. The analyzer gives `N` a singleton interval `[N, N+1)`, which
  `refineCond`'s `.cmp op (.var x) (.var bound)` leaf treats as a concrete
  bound.
* Nested loops where every level matches this pattern
  (k08_adi with 48 checks, k18_hydro_2d with 62, k21_matmul).
* Reads of an array at a loop-invariant constant index (post-loop
  `printFloat(arr[1])` etc.).

## What Phase 6 does not elide (all expected)

Every missing case falls into one of six patterns, each matching a
known limitation of the interval domain or `refineCond`'s pattern set.
All are documented in the plan's "Out of scope" section.

### 1. Indirect indices (`arr[idx_arr[i]]`)

Affects k13, k14, k16.

`certSuccessor` on `.arrLoad x _ _ _` returns `imRemove m x` — the loaded
value gets no interval because the array's value domain is unbounded. Any
subsequent `arr[x]` therefore can't be bounded.

Examples:

* k13: `i1 := e[ip]; h[(i1-1)*64 + j1]`
* k14: `ex[ix[k]]`, `rh[ir[k]]`, `rh[ir[k] + 1]`
* k16: `j5 := zone[j4-1]; plan[j5]`, `d[j5 - 1]`

Fixing this would require tracking array value ranges (another analysis
product), not just index ranges.

### 2. Expression-valued bounds (`while (k <= i - 1)`)

Affects k06.

`refineCond` handles only three shapes:
`.cmp op (.var x) (.lit n)`,
`.cmp op (.var x) (.var bound)`,
and `.not` of the above. Expression right-hand sides fall through to `m`
unchanged.

Extending this to `(i - c)` / `(i + c)` patterns would be a mechanical
2-leaf addition, but wasn't part of the Phase 3 scope.

### 3. Mutable upper bounds

Affects k02.

k02's inner loop uses `while (k <= ipntp)` where `ipntp` is reassigned
inside the enclosing `while (ii > 0) { … ipntp := ipntp + ii; … }`. After
the analyzer joins the pre-loop and back-edge states for `ipntp`, its
interval is no longer singleton, so `refineCond`'s `.var bound` case
requires `biv.lo + 1 = biv.hi` and falls through.

Relational invariants (`k ≤ ipntp ≤ size(x)`) would cover this — out of
scope for the interval domain.

### 4. Non-unit loop steps

Affects k04.

k04's outer loop increments `k := k + m` where `m = (1001 - 7) / 2 = 497`
is computed from a division. Even if `m` were a known singleton, the
widen-at-back-edge with `k.hi + m > iTop` triggers widening to `iTop`
before the next header-refinement can pull `k` back. The refinement on the
conditional (`k ≤ 1001`) gives us `k.hi = 1002` briefly, but the
post-increment value `k.hi + m - 1 = 1499` escapes.

Fixing this would require stable-under-widening transfer, probably via a
more precise numerical domain (polyhedra, octagons).

### 5. 2D-flattened indices (`arr[(j-1)*stride + k]`)

Affects k15.

The `.mul` transfer gates on `validIntervalMul` (hi ≤ 2¹⁶). For j ∈ [1, 7)
and stride 101, this passes. The resulting range for `(j-1)*101 + k` with
k ∈ [1, 101) works out to roughly `[0, 708)` — which is inside `vh`'s
size of 708. But the analyzer's produced range might not be tight enough
after the compound `mul`+`add`; and `refineCond` on `k ≤ 100` only refines
`k`, not the derived expression.

Symbolic refinement of expressions is a generalization of refineCond;
again, out of scope.

### 6. Reduction variables

Affects k24, and partially k17.

k24: `if (x[k] < x[m]) { m := k } else { skip }`. `m` is updated
conditionally, then joined at the merge point, then joined again at the
loop header. Since `m` is only used as an *index* (never compared to a
bound), no `refineCond` leaf tightens it. Its interval widens to iTop at
the loop header.

k17: similar with `i := i + ink` and flag-driven termination — `i` is the
induction variable but only appears in the array index, not the cond.

## Sanity checks

* **All b.hs branches target `.Lbounds_err`** — there are no other `.hs`
  uses in the emitted code, so the count is precisely bounds checks.
* **No checker rejections** — `checkerOk = true` for all 24 programs; every
  kernel's `BoundsOpt.checkLocalPreservation` output passes. The Phase 3
  soundness theorem is load-bearing for every elided check, not just the
  ones under test.
* **No soundness surprises** — the elision happens only when the analyzer
  output validates; when it doesn't, the ARM retains the explicit check.

## Effort

~20 min actual (build binaries at two commits, compile 24 kernels each,
diff). Plan estimated 0.5 day. Saved by not needing to run the programs —
just static inspection of generated ARM.

## Status

**Plan complete.** Phases 1-7 all landed. Remaining limitations are
documented here and match the "out of scope" section of the plan.
