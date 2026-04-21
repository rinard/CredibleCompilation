# Phase 5b Design Note — step_simulation refactor path

Context for the Phase 5b implementation of `while_to_arm_divergence_preservation` producing `ArmDiverges r.bodyFlat init`. Written 2026-04-21 after a design-session exchange that narrowed the approach.

## Goal

Strengthen `while_to_arm_divergence_preservation` at [PipelineCorrectness.lean:481](CredibleCompilation/PipelineCorrectness.lean#L481) to conclude `ArmDiverges r.bodyFlat initState` (reachability form: `∀ n, ∃ s, ArmStepsN r.bodyFlat init s n`), completing Phase 5 of plans/backward-jumping-octopus.md.

Phase 5a already shipped `ArmStepsN` + `ArmDiverges` + six utility lemmas (commit 9fdc351). Phase 5b's remaining piece is the forward direction: TAC divergence ⇒ ARM divergence.

## Initial approach (from the plan file)

The plan proposed ~160 LOC:
1. `verifiedGenBoolExpr_length_pos` — static: `be.hasSimpleOps = true ⇒ |output| ≥ 1`. ~15 LOC.
2. `verifiedGenInstr_output_pos` — static: 19-constructor case analysis under full `GenAsmSpec` invariants. ~115 LOC.
3. `bodyPerPCLengthPos` field on `GenAsmSpec` — every live PC's ARM block is non-empty. ~30 LOC.
4. Divergence theorem: `tacToArm_refinement` over N TAC steps → `ArmSteps init s` → `ArmStepsN init s k` → show `k ≥ n` via `bodyPerPCLengthPos + pcMapLengths`.

Step 1 landed cleanly (commit 3c4532e). Steps 2–4 ran into trouble.

## Obstacle: step-count positivity

Step 4's "show `k ≥ n`" has a gap: `bodyPerPCLengthPos` is a *static* length property on `bodyPerPC[pc]`, but the `ArmStepsN` step count `k` obtained post-hoc from an opaque `ArmSteps` depends on the ArmSteps proof term's structure. Without tracking step count inside `step_simulation`'s signature, there's no way to extract `k ≥ bodyPerPC[pc].length` after the fact.

The natural workaround — `cases hArm` to rule out `.refl` — requires `s ≠ s'` (since `.refl` forces `s = s'`). But `s = s'` is *legitimately possible* for `.goto pc` self-loops at PC pc: ARM executes `.b pcMap(pc)` which doesn't change any state when target = current PC. Same for some `.ifgoto pc` self-loops if initial ARM state happens to coincide with post-cmp state.

## Probes and findings

**Probe B — which Step rules can produce `c' = c`?** Only `.goto l` with `l = pc`, and `.iftrue` (`.ifgoto b l` with `b.eval = true`) with `l = pc`. Both preserve σ and am per their Step rules.

**Probe C — σ-change → ExtSimRel-visible change?** Uniform: every σ-modifying Step rule writes `σ[x ↦ _]` where `x ∈ instr.vars`, so `layoutComplete` covers the modified variable. `ExtStateRel` forces the corresponding ARM reg/stack slot to change value.

**Probe D — `.ifgoto` self-loop ARM trajectory?** `verifiedGenInstr_correct.iftrue` at [ArmCorrectness.lean:3126](CredibleCompilation/ArmCorrectness.lean#L3126) concludes final state is `{s3 with pc := pcMap l}` where `s3` has updated flags/regs. For self-loop (l = pc), pc unchanged but flags/regs differ. From the second iteration, state becomes a fixed point (flags recompute to same values). So `.ifgoto` self-loop *does* have convergent state evolution, but extracting the iteration step count from opaque `ArmSteps` is the same positivity gap.

## Interaction — three user insights that narrowed the design

**Insight 1 (checker)**: "Any way to close the gap at `.goto pc` self-loops by ruling out this case with a check elsewhere?" — pointed to Option A: static `checkNoSelfLoop` at the pipeline level, which rules out both self-loop constructors. WhileLang's compilation never produces self-loops structurally (every `while`/`if` emits forward-only jumps, with at least one intervening instruction before any backward goto).

**Insight 2 (direct witness)**: "If `.goto pc` or `.ifgoto be pc` at PC pc occurs, program diverges, so the outcome is known." — reframed Case A: in a self-loop, ARM divergence is directly constructible via iteration, not requiring the positivity argument. Answer: partial — `.goto` is straightforward (build `ArmStep.branch s s` + iterate), but `.ifgoto` still needs per-iteration step count, which is the same gap.

**Insight 3 (state-change vs PC-change)**: "Why do you need the state to change?" — surfaced that by Probe B's characterization, `f(n) ≠ f(n+1) ↔ pc_{n+1} ≠ pc_n` (PC-unchanged ⇒ Step is self-targeted goto/iftrue ⇒ σ, am also unchanged ⇒ configs equal). So Case B's state-change argument collapses to pure PC-change + pcMap strict monotonicity — no σ/am analysis needed. Cuts Case B from ~80 LOC to ~40 LOC.

**Insight 3, pushed further (current point)**: "What is the proof technique and why does it require a state change?" — identified that `s ≠ s'` is an *artifact* of the post-hoc `ArmSteps_to_ArmStepsN` extraction technique, not a genuine requirement of the theorem. `step_simulation` structurally always builds `.step _ _` (via `.single`/`.trans` of non-refl chunks), but this structural fact is invisible in the output type `ArmSteps prog s s'`. The clean fix is to refactor `step_simulation`'s signature to make the step count visible, removing the post-hoc dance entirely.

## Decision: Option 1 (refactor step_simulation)

User chose the refactor path over the post-hoc + checker combination.

**Reasoning**:
- Post-hoc + Option A: works, but carries the indirect proof dependency on `s ≠ s'` and adds pipeline plumbing for the checker plus a WhileLang structural-induction proof. The s ≠ s' dance is a workaround the refactor eliminates.
- Refactor: bakes positivity into step_simulation's type; every caller (`tacToArm_refinement`) gets the step count for free. Larger mechanical edit, smaller proof-theoretic surface. No checker needed since self-loops are handled by the structural step count without special casing.

## Scope

**Refactor `step_simulation`'s return type**:

Current:
```lean
∃ s', ArmSteps r.bodyFlat s s' ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)
```

New:
```lean
∃ s' k, ArmStepsN r.bodyFlat s s' (k + 1) ∧
        ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
        (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)
```

Each of step_simulation's three internal cases (lib-call / print / normal+halt-intercept) already builds ArmSteps via `.trans` and `.single` of concrete chunks with known positive lengths — the refactor propagates ArmStepsN step counts through these compositions.

**Supporting infra still needed**:
- `verifiedGenInstr_output_pos` (~115 LOC) — for the normal case's ArmStepsN length bound.
- `bodyPerPCLengthPos` (~30 LOC) — consumed by `step_simulation_posN` and the divergence theorem.
- `ArmStepsN` composition helpers (ArmStepsN for ArmSteps.single / ArmSteps.trans, etc.) — some already exist (`ArmStepsN_trans`, `ArmStepsN_extend`), need to verify coverage for the internal pattern step_simulation uses.

**Downstream adaptations**:
- `tacToArm_refinement` — one caller, threads the k through the induction, accumulates via `ArmStepsN_trans`.
- Divergence theorem — trivial once tacToArm_refinement yields ArmStepsN with K ≥ N; then `ArmStepsN_prefix` gives ArmStepsN of exactly n.

## Budget and confidence (initial estimate)

| Piece | LOC | Confidence |
|---|---|---|
| `verifiedGenInstr_output_pos` (retry with `by_cases` on layout instead of `split at hGen`) | ~115 | 65% |
| `bodyPerPCLengthPos` spec field + discharge | ~30 | 85% |
| `step_simulation` refactor (3 cases, tracking step count through each internal lemma composition) | ~150 | 60% |
| `tacToArm_refinement` adaptation | ~30 | 85% |
| Divergence theorem (now straightforward) | ~30 | 90% |
| **Total** | **~355 LOC** | **~50% first attempt, ~80% with 1–2 iterations** |

Risk concentration: `verifiedGenInstr_output_pos` technique issue (first attempt used `split at hGen` + `injection` that didn't reduce cleanly for nested matches in `.const .float` and `.copy` non-trivial arms — retry uses `by_cases` on layout, pattern from `ext_backward_simulation`'s `.copy` arm), and step_simulation's internal sub-lemmas (e.g., `armSteps_saves`, `armSteps_haltSaveBlock`, `ext_backward_simulation`) — these return `ArmSteps` currently; need to either add ArmStepsN-returning variants or post-hoc-convert per-chunk (potentially leveraging their explicit length facts like `s'.pc = s.pc + block.length`).

## Implementation progress (post-initial-estimate)

### Commit `496894a` — hardest-case-first landing

Following the "hardest case first" risk-management strategy (pick the biggest unknown; if it works, the rest is easier; if it fails, pivot early), `.copy` was proven as a standalone private theorem `verifiedGenInstr_copy_output_pos`. **It compiled cleanly on first attempt** using the refined technique.

**What landed** (1 file, +173 LOC):
- `vLoadVar_length_pos_of_not_freg` helper — under `RegConventionSafe` + `layoutComplete` + `layout v` not in `.freg`, `vLoadVar layout v .x0` emits ≥ 1 instruction. Rules out the `.ireg .x0` sub-case via `RegConventionSafe.not_x0`; `.freg _` and `none` via hypotheses.
- `verifiedGenInstr_copy_output_pos` — proves `1 ≤ instrs.length` for `verifiedGenInstr .copy dst src = some instrs` under the full `GenAsmSpec` invariants. All four subcases handled: self-copy (trivial `[.movR .x0 .x0]`), freg-src (vStoreVarFP uses `VarLayoutInjective` + `WellTypedLayout` to rule out the `r' == r` elision and the `.ireg` branch), non-freg-src + freg-dst (output ends with `[.fmovToFP]`), non-freg-src + non-freg-dst (`vLoadVar` positivity via helper).

**Technique that worked**: `cases h : layout v with` (tactic-level) rather than `match h : layout v with` (term-level inside `by`). The term-level pattern confused the outer `cases instr with` parsing. The successful blueprint mirrors `ext_backward_simulation`'s `.copy` arm at [ArmCorrectness.lean:2359](CredibleCompilation/ArmCorrectness.lean#L2359).

### Attempt at unified `verifiedGenInstr_output_pos`

After `.copy`, attempted to add the remaining 18 cases to a single `verifiedGenInstr_output_pos` that dispatches to `verifiedGenInstr_copy_output_pos` for `.copy` and inlines the others. **This hit a distinct roadblock**: the other constructors have nested conditionals after the outer `regConv`/`inj` guard is simplified, and `split at hGen` splits only one level at a time. Specifically:

- `.binop` — outer if + 4-arm match on `layout y, z, x` + inner `if op ∈ {div, mod} then ... else ...`. Requires 3 levels of splits.
- `.boolop` — outer if (regConv guard) + if `!be.hasSimpleOps` + if `notFreg`. Three levels.
- `.ifgoto` — outer + if `!be.hasSimpleOps` + 3-arm match (`.not .cmp`, `.not .fcmp`, fallback). Three levels.
- `.arrLoad`, `.arrStore` — outer + `cases ty` + if `boundsSafe`. Three levels (and the `if boundsSafe` appears inside a list concat, not at the top).
- `.fbinop`, `.fternop`, `.intToFloat`, `.floatToInt`, `.floatUnary` — outer + 3-to-5-arm `match` on layout positions. Two levels.

Attempted macros like `split at hGen <;> first | simp at hGen | (split at hGen <;> ...)` didn't cleanly handle the mix — `simp at hGen` on `some = some` made partial progress but didn't close, breaking the `first` combinator's fallthrough logic. Attempted `all_goals try (simp at hGen; done)` worked for some branches but left `case foo.isFalse` unsolved for nested-conditional cases.

**Diagnosis**: the monolithic `cases instr with | <19 cases>` pattern combined with ad-hoc split tactics doesn't compose cleanly. The cleanest path forward is **per-constructor standalone theorems**, mirroring the `.copy` pattern: each constructor gets its own `verifiedGenInstr_X_output_pos` that hand-unfolds its specific nesting.

### Revised scope and LOC estimates

Based on the `.copy` precedent (~170 LOC for the hardest case), and the nesting structure of the remaining 18:

| Piece | Revised LOC | Confidence | Status |
|---|---|---|---|
| `verifiedGenBoolExpr_length_pos` side lemma | 20 | — | ✅ commit `3c4532e` |
| `vLoadVar_length_pos_of_not_freg` helper | 20 | — | ✅ commit `496894a` |
| `verifiedGenInstr_copy_output_pos` (hardest case, standalone) | 170 | — | ✅ commit `496894a` |
| Remaining 18 per-constructor standalones (blueprint: follow `.copy` pattern) | ~360 | 70% | Pending |
| Main `verifiedGenInstr_output_pos` dispatcher (case on `instr`, call per-case theorem) | ~50 | 90% | Pending |
| `bodyPerPCLengthPos` spec field + discharge | ~30 | 85% | Pending |
| `step_simulation` refactor | ~150 | 60% | Pending |
| `tacToArm_refinement` adaptation | ~30 | 85% | Pending |
| Divergence theorem | ~30 | 90% | Pending |
| **Total remaining** | **~650 LOC** | **~50% first attempt, ~75% with 1–2 iterations** | |

The revised total (~650 LOC including what's landed) is almost **2× the initial estimate** — driven by the per-constructor standalone approach being the only reliable path, rather than a single cross-constructor lemma.

**Per-case budget for the 18 remaining standalones** (rough):
- Simple (fixed-output, no nesting): `.goto`, `.halt`, `.printString` — ~5 LOC × 3.
- Single-nesting (outer guard + single `cases`): `.printInt`, `.printBool`, `.printFloat`, `.const .int`, `.const .bool`, `.const .float` — ~15 LOC × 6.
- Two-nesting: `.fbinop`, `.fternop`, `.intToFloat`, `.floatToInt`, `.floatUnary`, `.arrLoad`, `.arrStore` — ~25 LOC × 7.
- Three-nesting: `.binop`, `.boolop`, `.ifgoto` — ~40 LOC × 3.
- Vacuous: `.print` (returns `none` unconditionally) — ~2 LOC.

Totals: 15 + 90 + 175 + 120 + 2 = ~400 LOC. Plus the main dispatcher and some slop → ~450 LOC for the 18 cases.

### Alternative path (not taken): unified macro

A `Lean.Parser.Tactic.split_recurse` macro that recursively applies `split at hGen` + `simp at hGen` + nested handling could fit all 18 cases in ~50 LOC. Not attempted because the macro tuning risk is similar to the per-case work for a smaller savings. If the per-case approach gets tedious, this is a reasonable refactor.

## Why this isn't on Phase 7's critical path (the plan's escape hatch)

If this path stalls, Phase 6/7's backward theorems can locally build "source diverges → ARM reaches arbitrary length" from `tacToArm_correctness` + PC-determinism without needing an explicit `ArmDiverges` forward theorem. The clean `ArmDiverges` forward theorem is the more elegant factoring but not strictly required.

## Handoff summary for next session

**Landed and ready to build on**:
- `verifiedGenBoolExpr_length_pos` (`3c4532e`)
- `vLoadVar_length_pos_of_not_freg` + `verifiedGenInstr_copy_output_pos` (`496894a`) — the `.copy` blueprint is the reference pattern for the remaining cases.

**Next concrete step**: port the `.copy` blueprint to the 18 other constructors as per-case standalone theorems. Recommended order (least-to-most-risk, same as `.copy`-first justification):
1. Simple cases to build confidence: `.goto`, `.halt`, `.printString`, `.printInt/Bool/Float`.
2. Single-nesting: `.const .int/.bool/.float`.
3. Two-nesting: `.intToFloat`, `.floatToInt`, `.floatUnary`, `.fbinop`, `.fternop`, `.arrLoad`, `.arrStore`.
4. Three-nesting: `.binop`, `.boolop`, `.ifgoto`. These have the same complexity shape as `.copy` and the same hypothesis bundle, so the pattern transfers directly.

Commit granularity: batch by complexity tier (4 commits for the 18 cases), each validated by `lake build CredibleCompilation.ArmSemantics` before committing.

After all 19 cases land: combine into the main dispatcher `verifiedGenInstr_output_pos` (~50 LOC case-on-instr + per-case delegation). Then proceed with `bodyPerPCLengthPos`, step_simulation refactor, divergence theorem as originally scoped.

**What surprised me this session**: the `.copy` case — expected to be the hardest — landed cleanly on first attempt once the `cases h : layout v with` pattern was locked in. The surprise was that the *simpler* cases needed *more* manual structure than anticipated (the nested-conditional proof terms confused `split at hGen`'s default behavior more than `.copy`'s injectivity-driven chain of cases did).
