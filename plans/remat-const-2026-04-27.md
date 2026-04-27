# Rematerialize-constant pass (2026-04-27, documented negative result)

Implemented a conservative `.const`-instruction-sinking pass to test whether
TAC-level rematerialization could close part of the post-Stage-1 register
allocation gap. **The conservative variant validates cleanly but produces
no measurable speedup**; the impactful variant requires the non-1:1
certificate framework that FMAFusionOpt uses, which is more substantial
work than I budgeted.

## Motivation

After Stage 1 (Chaitin-style spill heuristic, commit `db98888`), the
worst Axon-O / F-O2 ratios were:

| Kernel             | Axon-O / F-O2 |
|--------------------|---------------|
| k18_hydro_2d       | 6.69×         |
| k15_casual         | 6.65×         |
| k13_pic_2d         | 5.28×         |
| k21_matmul         | 5.01×         |

Assembly inspection showed two structural issues:

1. **Per-array-access `adrp + add` rematerialization** — every `arrLoad`
   emits a fresh 3-instruction sequence; gfortran holds the base in a
   register and reuses across accesses.

2. **Multiple stack slots holding the same constant** — for example, k15's
   inner loop has the constant `101` in two different stack slots
   simultaneously, with `ldr x2, [sp, #408]` and `ldr x2, [sp, #416]`
   reloading the same value into a scratch register.

This file addresses (2). (1) requires a separate change: address-base
hoisting via a new TAC instruction or a codegen-level peephole. Not
attempted in this session.

## The conservative variant (implemented + validated, negative result)

`CredibleCompilation/RematConstOpt.lean`. For each `.const v c` instruction
followed by an instruction that doesn't reference `v` and isn't a branch,
swap the two — shortens `v`'s live range by one PC. Iterated up to 64×
to sink `.const` defs past long stretches of unrelated code.

This is a 1:1 transformation (no instructions added or removed), so it
fits the existing certificate framework directly via `buildInstrCerts1to1`.

Validation: all 24 canonical Livermore kernels pass cert validation under
this pass.

Measured runtime impact (heavy kernels, best-of-3 at full NREPS):

| Kernel             | Stage 1 baseline | + RematConst sink | Δ        |
|--------------------|------------------|-------------------|----------|
| k08_adi            | 19.35            | 19.38             | flat     |
| k15_casual         | 19.45            | 19.39             | flat     |
| k18_hydro_2d       | 19.57            | 19.55             | flat     |
| k09_integrate      | 19.66            | 19.61             | flat     |
| k01_hydro          | 19.91            | 19.97             | flat     |
| k07_eos            | 20.60            | 20.57             | flat     |

All within ~0.3% of baseline — measurement noise.

### Why the conservative variant didn't help

The transformation that *would* help is per-use-site splitting:

```
.const v c                            (delete original)
... (long stretch) ...        →
use1: ... v ...                       use1: .const v_a c; ... v_a ...
use2: ... v ...                       use2: .const v_b c; ... v_b ...
```

This converts ONE variable with a long live range (and therefore high
register pressure across the whole loop body) into MANY tiny live ranges
(each `v_x` is alive for one instruction). RegAlloc trivially fits each
short-range `v_x` into a register; the original `v` is dead and gets DCE'd.

The conservative sink-only form attempted here only moves the **single**
`.const v c` instruction one PC at a time, never duplicating it. It can
therefore only shorten the live range up to the first use; subsequent
uses still see `v` alive across the gap. Net register-pressure change:
zero on multi-use constants, which is most of what the spill data shows.

## What the impactful variant needs

The per-use-site split adds instructions to the program. The existing
certificate generators (used by ConstProp, CSE, ConstHoist, CopyProp,
DCE, RematConst-conservative) all use `buildInstrCerts1to1` which assumes
the trans program has the same number of PCs as the orig program.

`FMAFusionOpt.lean` is the existing precedent for non-1:1 transformations:
it removes one of two adjacent instructions (the `fmul` absorbed into a
`fmadd`). The cert generation builds a `pcOrigMap` that maps trans-PCs
back to orig-PCs, with PC remapping for goto/ifgoto targets.

To implement per-use-split rematerialization with the existing framework,
RematConstOpt would need to:

1. **Find candidates**: walk program for `.const v c` instructions; for
   each, collect use-PC list via forward dataflow.
2. **Insert per-use defs**: for each use, allocate a fresh variable name,
   insert `.const v_use_i c` immediately before the use, rewrite the use
   to reference `v_use_i`. Original `.const v c` becomes dead.
3. **Build origMap**: map each trans-PC back to its orig-PC (or the
   immediate predecessor's orig-PC for inserted-before instructions).
4. **PC remapping**: scan trans for `goto target` and `ifgoto _ target`;
   compute new target via reverse origMap. Same shape as FMAFusionOpt's
   `compactProg` but for insertions instead of removals.
5. **Cert generation**: at each inserted-`.const`-PC, the EInv adds
   `(v_use_i, .lit c)`; at use sites, no rel change since the value is
   the same. Existing `buildInstrCerts` (the non-1:1 form in DCEOpt /
   FMAFusionOpt) accepts this if origMap is correct.

Estimated effort: **1–2 days** of focused work. The core algorithm is
straightforward; the cert plumbing is the bulk of the work.

## Estimated impact (if implemented)

Based on the asm analysis showing ~30–50% of stack-spill instructions on
heavy kernels are reloads of constants:

| Kernel             | Predicted speedup |
|--------------------|-------------------|
| k09_integrate      | 15–25%            |
| k15_casual         | 10–20%            |
| k01_hydro          | 5–15%             |
| k04_banded         | 5–15%             |
| k07_eos            | 5–15%             |
| k18_hydro_2d       | 0–5%              |

Geomean Axon-O / F-O2: probably drops from current 2.18× toward ~1.9×.

Not as impactful as Stage 1 was (which gave 1.55–1.85× on heavy kernels),
but a clean 5–10% additional gain across the corpus for ~2 days of work.

## Files

- `CredibleCompilation/RematConstOpt.lean` — conservative sink-only
  implementation, all certs validate. NOT wired into `suffixPasses`. The
  file's docstring describes the situation in detail and points to this
  report.

## What I'd do differently next time

When the cert framework constraint is the bottleneck, the first
investigation should be "does the impactful variant fit the existing
non-1:1 cert pattern?" — not "can I make a degraded variant fit the
1:1 pattern?". The conservative variant was 2 hours of code that
delivered zero impact; the same 2 hours spent reading `FMAFusionOpt`'s
cert structure would have made the impactful variant tractable.
