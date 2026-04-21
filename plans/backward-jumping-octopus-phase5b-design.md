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

## Budget and confidence

| Piece | LOC | Confidence |
|---|---|---|
| `verifiedGenInstr_output_pos` (retry with `by_cases` on layout instead of `split at hGen`) | ~115 | 65% |
| `bodyPerPCLengthPos` spec field + discharge | ~30 | 85% |
| `step_simulation` refactor (3 cases, tracking step count through each internal lemma composition) | ~150 | 60% |
| `tacToArm_refinement` adaptation | ~30 | 85% |
| Divergence theorem (now straightforward) | ~30 | 90% |
| **Total** | **~355 LOC** | **~50% first attempt, ~80% with 1–2 iterations** |

Risk concentration: `verifiedGenInstr_output_pos` technique issue (first attempt used `split at hGen` + `injection` that didn't reduce cleanly for nested matches in `.const .float` and `.copy` non-trivial arms — retry uses `by_cases` on layout, pattern from `ext_backward_simulation`'s `.copy` arm), and step_simulation's internal sub-lemmas (e.g., `armSteps_saves`, `armSteps_haltSaveBlock`, `ext_backward_simulation`) — these return `ArmSteps` currently; need to either add ArmStepsN-returning variants or post-hoc-convert per-chunk (potentially leveraging their explicit length facts like `s'.pc = s.pc + block.length`).

## Why this isn't on Phase 7's critical path (the plan's escape hatch)

If this path stalls, Phase 6/7's backward theorems can locally build "source diverges → ARM reaches arbitrary length" from `tacToArm_correctness` + PC-determinism without needing an explicit `ArmDiverges` forward theorem. The clean `ArmDiverges` forward theorem is the more elegant factoring but not strictly required.
