# Phase 6/7 Next Session — Final Plan and Handoff

**Read this first.**  Supersedes all earlier Phase 6/7 planning documents
in this directory.  Last updated: 2026-04-23 after **session 7** —
**Phase B.0 + 21 of 31 Phase B.1 cases complete**; 10 cases remain in
verifiedGenInstr_correct plus Phases C–H.

## TL;DR for next session (session 8)

Sorry count stands at **5** — 4 pre-existing in PipelineCorrectness.lean
(3 Phase 6 out-of-scope + 1 Phase 7 target), and 1 on
`verifiedGenInstr_correct` with 10 internal per-case sorries remaining.
Build green. Phase B signature is locked in place and cannot be reverted
mid-way — session 8 must finish filling the remaining 10 cases atomically
before committing any sig-level change.

**Session 8 starts with Phase B.1 continuation.** Reference the session 7
commits (f7b5b78 through 48b0778) for worked examples spanning terminal,
sentinel, and multi-helper .run cases. The spec's hard-first order:
`.binop` → `.iftrue/.iffall` → `.floatUnary` → `.arrLoad/.arrStore` →
`.const/.copy/.fbinop/.fternop`.

### 10 cases remaining

| Case | Complexity | Sketch |
|---|---|---|
| `.const` | complex | 3 value types × 4 layouts = ~12 leaves; FA1 probe covers stack-int |
| `.copy` | complex | self-copy + freg + int; 4 layout combos |
| `.binop` | complex | per-op (10 ops) with ×/÷ div-check prefix |
| `.iftrue`, `.iffall` | complex | BoolExpr nested, ~400 LOC each |
| `.arrLoad`, `.arrStore` | complex | 3 types × 3 layouts + bounds-check prefix |
| `.fbinop` | complex | per-op native + libcall (fpow) |
| `.floatUnary` | complex | native + libcall variants |
| `.fternop` | complex | 3-arg load chain + per-op |

### Session 7 patterns — REUSE THESE

1. **Length-claim proof for `.run` cases**:
   ```lean
   · intro pc' σ' am' _hCfg
     rw [hInstrs, hk1, hk2, ...]; simp [List.length_append]; omega
   ```
   `rw [hInstrs]` is CRITICAL — the cascade rewrite
   `rw [hInstrs] at hCodeInstr hPcNext` does NOT propagate to the
   length-claim subgoal, which still has `instrs.length` literally.
   Omega closes associativity mismatches after simp.

2. **Vacuous length-claim for sentinel/terminal cfg'**:
   ```lean
   · intro pc' σ' am' h; cases h
   ```
   Discharges impossible `.errorDiv/.typeError/.halt = .run` equation.

3. **Chain construction** via `ArmStepsN_trans` with visible arithmetic:
   ```lean
   have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
   have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepN
   ```
   Drop the session-6 compat bridge `hStepsX := ArmStepsN_to_ArmSteps hStepsXN`
   per-case as each case rewrites.

4. **Syntax gotcha**: `exact ⟨..., by tac, next⟩` parses the comma into
   the `by`-block. Use `refine ⟨..., ?_, next⟩` then prove subgoals.

5. **Prelude is already in place** at the top of `verifiedGenInstr_correct`
   (hRC, hII, hRegConv, hInjective, ⟨hStateRel, hPcRel, hArrayMem⟩). Each
   case body should reference these directly — do not re-derive.

### After Phase B completes

Phase C (`ext_backward_simulation` — sig already changed to mirror;
body already delegates via term-mode. Trivial ~0 LOC.). Phase D
(`step_simulation` body is already cascaded with the `ArmStepsN_to_ArmSteps`
bridge at the one call site in CodeGen.lean:5942 — nothing more to do
unless we want to fully thread ArmStepsN through step_simulation's signature,
which is Phase D proper and spec-estimated at 80-120 LOC). Phases E-H follow.

Realistically session 8 covers B.1 completion + C. Phases D-H would be
session 9.

**Read [plans/flavor-a-signatures.md](flavor-a-signatures.md) in full
before continuing.**  That doc is the authoritative execution guide;
this handoff is a pointer.  The **two procedural rules** remain:

1. **Sorry-ratchet within each phase** — update all signatures + cascade
   destructures in one pass with sorried bodies (sub-step X.0), then fill
   sorrys individually (sub-step X.1+).  Build stays green throughout.
   Sorry count temporarily balloons then monotonically decreases.
2. **Hard cases first within each sub-step** — validate the signature by
   attempting the hardest case first.  Specific ordering in spec.

The spec enumerates every theorem in the chain
(helpers → `verifiedGenInstr_correct` → `ext_backward_simulation` →
`step_simulation` → `tacToArm_refinement` → `tacToArm_correctness` →
`while_to_arm_*` → `source_diverges_gives_ArmDiverges_init`) with exact
new signatures, length-claim forms, caller-update expectations, and a
per-sub-step checkpoint table showing expected sorry counts.

**Revised scope: ~1000 LOC, 2–3 focused sessions.**  Phase B is the
largest (~60 cases in `verifiedGenInstr_correct`); everything else is
smaller.  Phase H (closing the target sorry) is ~40 LOC once phases A–G
are in.

## Session 6 retrospective — what worked for A.15

For future phases, the pattern proven effective in session 6 A.15:

1. **Intermediate state lets** — `let s3 := { s2 with flags := ... }`
   for each chain step. Include `s3` in simp sets where needed.
2. **Explicit ArmStepsN chain construction** — bind each step's
   `hStepN : ArmStepsN prog sPrev sNext 1` separately, then chain
   via `ArmStepsN_trans` with visible arithmetic:
   ```lean
   have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
   have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
   ```
3. **k-equality proof** — after the refine, prove
   `k_total = (verifiedGenBoolExpr layout be).length` via:
   ```lean
   rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
   ```
4. **surgical `simp only`** — for cases where simp over-unfolds and
   breaks the expected normal form (e.g., flit+flit `Flags.condHolds_
   float_correct`), use `simp only [sN, ...specific lemmas...]` first
   to stage the form, then `simp` + `exact` for the final step.

These patterns should transfer directly to Phase B's per-case fills.

### Where everything lives

| Artifact | Location |
|---|---|
| Signature spec + execution rules | [plans/flavor-a-signatures.md](flavor-a-signatures.md) |
| Session 5 root-cause analysis | [CHANGELOG.md](../CHANGELOG.md) §Phase 6/7 session 5 |
| Session 6 outcome | [CHANGELOG.md](../CHANGELOG.md) §Phase 6/7 session 6 |
| Target sorry to close | [PipelineCorrectness.lean:1324](../CredibleCompilation/PipelineCorrectness.lean#L1324) (`source_diverges_gives_ArmDiverges_init`) |
| `ArmStepsN` + length-tracking primitives | [ArmSemantics.lean:299–353](../CredibleCompilation/ArmSemantics.lean#L299) |
| `ArmStepsN_to_ArmSteps` bridging lemma | [ArmSemantics.lean](../CredibleCompilation/ArmSemantics.lean) (after `ArmSteps_to_ArmStepsN`) |
| Phase A helpers (all landed except A.15) | [ArmCorrectness.lean:81–1000](../CredibleCompilation/ArmCorrectness.lean#L81) |
| **A.15 `verifiedGenBoolExpr_correct` (session 7 start)** | [ArmCorrectness.lean:1005](../CredibleCompilation/ArmCorrectness.lean#L1005) — sorried |
| A.15 old proof (reference) | [ArmCorrectness.lean:1024-](../CredibleCompilation/ArmCorrectness.lean#L1024) in comment block |
| `verifiedGenInstr_correct` (Phase B) | [ArmCorrectness.lean] `grep -n "^theorem verifiedGenInstr_correct"` (was line 1748; shifted after session 6 edits) |
| `ext_backward_simulation` (Phase C) | [ArmCorrectness.lean] `grep -n "^theorem ext_backward_simulation"` |
| `step_simulation` (Phase D) | [CodeGen.lean:4182](../CredibleCompilation/CodeGen.lean#L4182) |
| `tacToArm_refinement` (Phase E) | [CodeGen.lean:6044](../CredibleCompilation/CodeGen.lean#L6044) |
| `tacToArm_correctness` (Phase F) | [CodeGen.lean:6135](../CredibleCompilation/CodeGen.lean#L6135) |
| `while_to_arm_*` callers (Phase G) | [PipelineCorrectness.lean:349, 443, 470](../CredibleCompilation/PipelineCorrectness.lean#L349) |
| `verifiedGenInstr_output_pos` (consumed by length claims) | [ArmSemantics.lean:2615](../CredibleCompilation/ArmSemantics.lean#L2615) |
| Bridge pattern used at Phase B callsites | `have hStepsX := ArmStepsN_to_ArmSteps hStepsXN` — preserved across ~100 cascade sites in `verifiedGenInstr_correct` to keep old proofs compiling on ArmSteps. Phase B will remove these bridges per-case as it rewrites bodies. |

### Why Flavor A and nothing else

Session 5 exhaustively explored alternatives and confirmed all of them
fail at the `.ifgoto pc_self` stable-state case due to Lean 4's proof
irrelevance for theorems (see CHANGELOG.md §Phase 6/7 session 5 for the
analysis).  The root cause is that `∃ s', ArmSteps s s'` hides length in
the opaque proof body.  The only fix is to put length in the observable
return type — Flavor A does exactly this.

Phase 6 exhaustion (`bodyFlat_branch_target_bounded` +
`arm_behavior_exhaustive` + `verifiedGenInstr_ifgoto_branch_bounded`)
remains OUT OF SCOPE — separate ~700 LOC deliverable.

## Session 4 outcome (2026-04-23)

**Achieved: 7 → 4 sorrys.**  See CHANGELOG.md §Phase 6/7 session 4
for the full report.  Summary:

- `halt_state_observables_deterministic` closed (~30 LOC; full state
  equality via `step_count_state_uniqueness` + `sentinel_stuck`).
- `sentinel_state_unique` helper added — generalizes the above to any
  pair of sentinel endpoints.
- Phase 7a/b/c (`arm_halts_implies_while_halts`, `arm_div_implies_
  while_unsafe_div`, `arm_bounds_implies_while_unsafe_bounds`) all
  closed by case-splitting on `has_behavior_init`, using
  `sentinel_state_unique` for cross-sentinel contradiction and
  reducing the `.diverges` case to `source_diverges_gives_ArmDiverges_
  init` + `sentinel_stuck`.
- `source_diverges_gives_ArmDiverges_init` introduced as a **stated
  theorem with `sorry` body** — a single deferred obligation.  No
  axioms introduced.

### Why the earlier compositional plan was abandoned

Session 4 considered a compositional approach (Fix B' cycle
primitives + self-loop detection + non-self-loop dichotomy).
Analysis revealed:

1. The `.ifgoto`-true self-loop Fix B' primitive requires showing
   `ArmStepsN s s k ≥ 1` where s cycles back to itself.  In practice
   the first iteration changes flags (s ≠ s'), but the cycle only
   establishes after a steady state is reached, which requires
   reasoning about `.ifgoto`'s multi-instruction ARM block.

2. The "non-self-loop ⇒ s ≠ s' ⇒ length ≥ 1" case analysis STILL
   fails for self-loop cases (where `cfg' = cfg`, so ExtSimRel admits
   s = s' propositionally), and we cannot externally rule out
   `.refl` from `tacToArm_refinement`'s output.

3. Both obstacles trace back to the same root cause: `ArmSteps`
   propositions don't track length.  `step_simulation`'s proof
   internally constructs length-≥-1 chains for every case, but the
   length is **erased** in the return type.

Flavor A addresses the root cause directly by adding length
tracking.  This makes every downstream closing argument trivial.

## Session 5 work plan — Flavor A specification

### Goal

Change the return type of `ext_backward_simulation` /
`step_simulation` / `tacToArm_refinement` / `tacToArm_correctness`
from `∃ s', ArmSteps ... ∧ ...` to
`∃ s' k, ArmStepsN ... k ∧ k ≥ 1 ∧ ...`
(or `∃ s' k, ArmStepsN ... k ∧ k ≥ <step-count> ∧ ...` for the
multi-step versions).

Then close `source_diverges_gives_ArmDiverges_init` using the
enhanced interface.

### Signature-change specification

**Target 1: [`verifiedGenInstr_correct`](../CredibleCompilation/ArmCorrectness.lean#L1748)**
— the per-TAC-instruction forward-sim core at ArmCorrectness.lean:1748,
~3700 lines.  Currently returns:

```lean
∃ s', ArmSteps prog s s' ∧ ExtSimRel layout pcMap divLabel boundsLabel cfg' s'
```

Change to:

```lean
∃ s' k, ArmStepsN prog s s' k ∧ 1 ≤ k ∧
        ExtSimRel layout pcMap divLabel boundsLabel cfg' s'
```

**Target 2: [`ext_backward_simulation`](../CredibleCompilation/ArmCorrectness.lean#L5433)**
— thin re-export at ArmCorrectness.lean:5433.  Same return-type
change; body unchanged (just threads the enhanced tuple through).

**Target 3: [`step_simulation`](../CredibleCompilation/CodeGen.lean#L4182)**
— wrapper at CodeGen.lean:4182, ~1800 lines.  Currently returns:

```lean
∃ s', ArmSteps r.bodyFlat s s' ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)
```

Change to:

```lean
∃ s' k, ArmStepsN r.bodyFlat s s' k ∧ 1 ≤ k ∧
        ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
        (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)
```

**Target 4: [`tacToArm_refinement`](../CredibleCompilation/CodeGen.lean#L6044)**
— the multi-step theorem at CodeGen.lean:6044.  Currently returns:

```lean
∃ s', ArmSteps r.bodyFlat s s' ∧
      ExtSimRel ... cfg' s' ∧ (halt-pc conj)
```

Change to (parameterizing over TAC step count via StepsN input):

```lean
theorem tacToArm_refinement ... {n : Nat} (hSteps : StepsN p ... cfg' n) :
    ∃ s' k, ArmStepsN r.bodyFlat s s' k ∧ n ≤ k ∧
            ExtSimRel ... cfg' s' ∧ (halt-pc conj)
```

(If StepsN isn't directly available, keep the Steps signature but
return `∃ s' k, k ≥ 0 ∧ ArmStepsN ... k ∧ ...` — though then session
5's main theorem needs to extract step count another way.  StepsN is
preferred.)

**Target 5: [`tacToArm_correctness`](../CredibleCompilation/CodeGen.lean#L6135)**
— wraps `tacToArm_refinement` with initial state.  Signature change
mirrors Target 4.

**Targets 6–8: `while_to_arm_correctness`, `while_to_arm_div_
preservation`, `while_to_arm_bounds_preservation`** in
PipelineCorrectness.lean.  These destructure `tacToArm_correctness`'s
output; only need a cosmetic update (add a `_` or `k` binder in the
`obtain ⟨s, hArm, hRel, hPC⟩ := tacToArm_correctness ...` lines, and
either discard k or thread it through if callers want it).

### Helper theorems that also need length tracking

`verifiedGenInstr_correct` invokes ~15 helper theorems that all
return `∃ s', ArmSteps prog s s' ∧ ...` without length tracking.
Each helper must be updated (bottom-up, so `verifiedGenInstr_correct`
can consume the enhanced helpers):

| Line | Helper | Typical length |
|---|---|---|
| 81 | `loadImm64_correct` | = `loadImm64 n`.length (≤ 4, ≥ 1 unless n has trivial zero-shifts) |
| 253 | `optional_movk_step'` | 0 or 1 (length 0 case — skip if skipMovk) |
| 272 | `loadImm64_fregs_preserved` | mirrors loadImm64_correct |
| 488 | `vStoreVar_x0_correct` | = `vStoreVar x`.length (≥ 1 if stack/freg; 0 if ireg-same) |
| 508 | `vStoreVar_x0_ireg_correct` | same |
| 527 | `vLoadVar_exec` | similar |
| 590 | `vLoadVar_eff_exec` | similar |
| 618 | `vStoreVar_exec` | similar |
| 659 | `vStoreVarFP_exec` | similar |
| 701 | `fp_exec_and_store` | composite, ≥ 1 |
| 762 | `vLoadVarFP_exec` | similar to vLoadVar |
| 824 | `vLoadVarFP_eff_exec` | similar |
| 859 | `loadFloatExpr_exec` | ≥ 1 (always emits at least one step) |
| 925 | `verifiedGenBoolExpr_correct` | ≥ 1 |

**Flag**: some helpers (e.g., `vStoreVar_x0_correct` when src == dst
register) have a degenerate 0-step case.  For Flavor A at the
`verifiedGenInstr_correct` level we need **k ≥ 1**, not k ≥ 0, so
the helpers may return `k ≥ 0` while the composition at the
`verifiedGenInstr_correct` level adds a final non-degenerate step
(like a branch or cmp) that guarantees the total ≥ 1.

Alternative: relax the top-level claim to `k ≥ 0` everywhere, then
add a separate "total block has ≥ 1 instruction" argument at
`source_diverges_gives_ArmDiverges_init` using
`bodyPerPC_length_pos`.  **This is likely the cleaner path** —
avoids per-helper length-positivity tracking.

**Refined signature recommendation**:
- Helpers: return `∃ s' k, ArmStepsN ... k ∧ k = <helper-specific-
  length> ∧ ...`.  The equality is more informative than a bound.
- `verifiedGenInstr_correct`: return `∃ s' k, ArmStepsN ... k ∧
  k = instrs.length ∧ ...`.  Since `instrs.length ≥ 1` from
  `bodyPerPC_length_pos` (via `verifiedGenInstr_output_pos`), the
  `k ≥ 1` follows at the call site.
- `step_simulation`: return `∃ s' k, ArmStepsN ... k ∧ 1 ≤ k ∧ ...`
  (simpler bound; length varies by case).
- `tacToArm_refinement` / `tacToArm_correctness`: return
  `∃ s' k, ArmStepsN ... k ∧ n ≤ k ∧ ...` where n = StepsN count.

### Case-conversion pattern

For each case of the enhanced theorems, the conversion is rote.
Example: `verifiedGenInstr_correct` for `.goto`:

**Before** (line 1798-1799):
```lean
exact ⟨{ s with pc := pcMap _ }, .single (.branch _ hb),
  ⟨hStateRel, rfl, hArrayMem⟩⟩
```

**After**:
```lean
exact ⟨{ s with pc := pcMap _ }, 1,
  ArmStepsN.single (.branch _ hb), rfl,
  ⟨hStateRel, rfl, hArrayMem⟩⟩
```

(The `rfl` discharges `k = instrs.length` since `instrs = [.b ...]`
has length 1.)

Pattern transformations:
- `.single h` (ArmSteps) → `ArmStepsN.single h` (ArmStepsN ... 1)
- `hArm1.trans hArm2` → `ArmStepsN_trans hArmN1 hArmN2`
  (where hArmN1/hArmN2 are enhanced versions from helpers)
- `.step h1 h2` → unfolded to `⟨s_mid, h1, h2_N⟩` (ArmStepsN ... (k+1))
- `ArmSteps.refl` → `(rfl : ArmStepsN ... _ _ 0)` — but this case
  should not arise at the `verifiedGenInstr_correct` level since
  every block is non-empty; if it appears in a helper, track k = 0
  explicitly.

### Work order (session 5)

Work bottom-up to keep `lake build` green after each phase.

**Phase A: helpers (ArmCorrectness.lean lines 81-1000)** — ~150 LOC.
Update each helper's return type to include length tracking.  Prove
case-by-case.  Most helpers have trivial structure — either emit a
single instruction (length 1) or chain via `.trans` (length sum).

Checkpoint after Phase A: `lake build` green, same sorry count (4).

**Phase B: `verifiedGenInstr_correct`** — ~300 LOC across ~60 cases.
Work through each `| constructor => ...` arm.  Many cases delegate
to helpers — the enhanced helper output plugs in directly.

Checkpoint after Phase B: `lake build` green, same sorry count (4).

**Phase C: `ext_backward_simulation` + `step_simulation`** — ~60 LOC.
Thin wrappers; mechanical updates.

**Phase D: `tacToArm_refinement` + `tacToArm_correctness`** —
~30 LOC.  Consumes `step_simulation`'s enhanced output; composes
via `ArmStepsN_trans` instead of `ArmSteps.trans`.  Induction on
`Steps` or `StepsN` — recommend introducing StepsN-indexed variant
alongside for clean step-count threading.

Checkpoint after Phase D: `lake build` green, same sorry count (4).

**Phase E: `while_to_arm_*`** — ~20 LOC.  Purely cosmetic:
destructure the enhanced tuple with an extra `_` or `k` binder.

**Phase F: close `source_diverges_gives_ArmDiverges_init`** —
~40 LOC.  Sketch:

```lean
private theorem source_diverges_gives_ArmDiverges_init ... := by
  intro N
  -- Extract first (N+1) TAC steps from IsInfiniteExec.
  have hStepsN : StepsN (applyPassesPure ...) (f 0) (f (N+1)) (N+1) := by
    induction (N+1) with
    | zero => exact rfl
    | succ n ih => exact ⟨f n, hinf.2 n, ih⟩  -- or similar
  -- Convert StepsN to Steps; apply enhanced tacToArm_correctness_N.
  -- Enhanced return: ∃ s_fwd k, ArmStepsN init s_fwd k ∧ k ≥ N+1 ∧ ExtSimRel ...
  rw [hf0] at hStepsN
  obtain ⟨s_fwd, k, hArmN, hk_ge, _⟩ :=
    tacToArm_correctness_N hGen (by exact hStepsN.toSteps)
  -- Truncate to length N via ArmStepsN_prefix.
  have hN_le_k : N ≤ k := by omega
  obtain ⟨diff, hdiff⟩ : ∃ d, k = N + d := ⟨k - N, by omega⟩
  rw [hdiff] at hArmN
  exact ArmStepsN_prefix hArmN
```

Checkpoint after Phase F: `lake build` green, **sorry count 3**
(the deferred lemma closed).  Phase 7 fully done.

### Budget

| Phase | LOC | Risk |
|---|---|---|
| A: helpers | ~150 | Low |
| B: verifiedGenInstr_correct | ~300 | Low-medium (scale) |
| C: ext_backward_simulation + step_simulation | ~60 | Low |
| D: tacToArm_refinement + tacToArm_correctness | ~30 | Medium (StepsN threading) |
| E: while_to_arm_* | ~20 | Trivial |
| F: source_diverges_gives_ArmDiverges_init | ~40 | Low (once D is done) |
| **Total** | **~600** | **Overall ~85% confidence** |

Estimated wall-clock: 1 focused day if ratchet is maintained
case-by-case; 2 days if debugging obstructs.

### Risks and mitigations

1. **Helper with length-0 case** (e.g., `vStoreVar_x0` when
   layout == source register yields empty ArmSteps).  Mitigation:
   track exact length (`k = <helper-list>.length`) rather than a
   lower bound; this preserves compositionality and lets
   `verifiedGenInstr_correct` derive `k ≥ 1` from
   `bodyPerPC_length_pos`.

2. **StepsN isn't in the TAC infrastructure.**  Check
   [TAC.lean](../CredibleCompilation/TAC.lean) and
   [PropChecker.lean](../CredibleCompilation/PropChecker.lean) — if
   StepsN isn't defined with a length index, add a local variant
   alongside the Steps-indexed refinement theorem.  If the search
   shows StepsN exists (used by Refinement.lean's has_behavior_init
   proof — line 252-257 in Refinement.lean), adapt to that variant.

3. **Unexpected downstream caller breakage.**  Beyond the listed
   callers, `grep -rn 'tacToArm_correctness\|tacToArm_refinement\|
   step_simulation\|ext_backward_simulation\|verifiedGenInstr_correct'`
   across CredibleCompilation/ and CCTests/ to catch anything
   missed.  Probe files in CCTests/Tests/PivotProbe*.lean may
   reference old signatures — update or retire.

4. **Stuck on a specific case.**  If any case of
   `verifiedGenInstr_correct` resists length tracking after 30
   minutes, document the obstacle in a CHANGELOG-style note and
   stop.  Partial progress (green build, subset of cases updated)
   still reduces risk for a follow-up session.

### Rollback plan

If the session stalls partway:
- **Phase A partial**: commit what's done; the enhanced helpers
  exist alongside old signatures (if kept via Flavor-B-style
  coexistence) OR in a clean intermediate state (if in-place).
- **Phase B partial**: `verifiedGenInstr_correct` has mixed return
  types — not composable.  Either finish Phase B fully before
  committing, or revert Phase B.
- **Phase D partial**: `tacToArm_refinement` / `tacToArm_
  correctness` similarly need atomic commit.

Net: Phases B and D are the only "must-complete" units.  Phases A,
C, E, F are incrementally commitable.

### Success criteria

- `lake build` green.
- Sorry count: 4 → 3 (source_diverges_gives_ArmDiverges_init closed).
- `grep -rE "axiom\s" CredibleCompilation/` shows no new axioms.
- `git log --oneline -10` shows session 5's commits on top of
  `fd2d542` (session 4's handoff commit).
- CHANGELOG.md updated with session 5 entry.
- This plan doc updated: replace "Session 5 work plan" with
  "Session 5 outcome" + open items for Phase 6 exhaustion.

## TL;DR of the original plan (historical)

Close Phase 7 by doing **pivot (deterministic havoc) + Fix B' (direct
ArmDiverges from self-loops)**.  Total budget ~750 LOC.  All major
risks validated by probes.  Work order in § Next Session Work Plan.

## Final decision

After extensive exploration, the cheapest robust path is:

1. **Deterministic havoc pivot** — refactor `ArmStep`'s 5 libcall
   constructors to use opaque havoc functions instead of existential
   arguments.  Cost: ~370 LOC (refactor + call-site updates +
   `arm_step_det`).  Gives `step_count_state_uniqueness` at ~15 LOC.
2. **Fix B'** — handle TAC self-loops by direct ArmDiverges derivation
   (no handler, no ExtSimRel revision).  Cost: ~250 LOC.  Complementary
   to the pivot; stacks cleanly.
3. **Phase 7a/b/c/d** — ~200 LOC given the above.  `halt_state_
   observables_deterministic` collapses to ~15 LOC under state
   uniqueness.

**Phase 6 exhaustion** (`bodyFlat_branch_target_bounded` + 14-case
sweep + `arm_behavior_exhaustive` König) is separate, optional,
~700 LOC.  Not required to close Phase 7.

## Why not alternatives

| Rejected | Why |
|---|---|
| **Fix B' alone (no pivot)** | `step_count_pc_uniqueness` under nondeterministic `ArmStep` requires ~300+ LOC of per-PC spec-structure analysis.  Micro-probe PF3 confirmed naive induction fails at the inductive step (two intermediate states have same PC but potentially different regs due to havoc).  Comparable or worse total cost vs pivot, with reactive-stacking hindsight penalty risk. |
| **Pivot alone (no Fix B')** | Step 6's `source_diverges_arm_pc_in_bodyFlat` requires partial Phase 5b (step-count positivity) — ~150 LOC of its own, even under the pivot.  Fix B' eliminates this with a direct ArmDiverges argument for ~100 LOC less. |
| **Full Phase 5b** | ~660–1940 LOC per phase5b-design.md.  Overkill for just Phase 7's needs. |
| **Handler approach (Fix B with ARM-level diverge trampoline)** | Changes ExtSimRel.run invariant.  Ripples through all forward-sim proofs: ~300+ LOC.  Fix B' is strictly better. |

## What's landed (branch `phase6-prep`)

### Infrastructure (commit `63e88d3`)

In [`CredibleCompilation/PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean):

- `sentinel_stuck`: sentinel PC ⇒ no ArmStep.
- `pcMap_le_haltS`: live TAC PCs map to ARM PCs ≤ haltS.
- `checkBranchTargets_to_labels_in_bounds`: spec bridge.
- `haltFinal_ne_divS`, `haltFinal_ne_boundsS`, `divS_ne_boundsS`:
  sentinel distinctness.
- `stepClosed_of_checkCertificateExec`: extract condition 6.
- `applyPass_preserves_stepClosedInBounds` /
  `applyPassesPure_preserves_stepClosedInBounds`.
- `pipelined_has_behavior` (wrapper over `has_behavior`).
- `pipelined_no_typeError` (wrapper over `type_safety`).

### Probes — all confirmed working

All probes at `CCTests/Tests/PivotProbe{PD,PE,PF}*.lean`:

| Probe | Status | What it validates |
|---|---|---|
| PD1 — opaque interaction | ✅ | `opaque` functions work with rfl/simp/exact/rw |
| PD2 — mini arm_step_det | ✅ | Projection trick scales to full state (5 constructors) |
| PD3 — forward-sim composability | ⚠️ sig only | Step 6 would be ~150 LOC without Fix B' |
| PE1 — 1-TAC-step positivity | ⚠️ partial | Works for halt/error sub-cases; blocked for diverges |
| PE2 — call-site grep | ✅ | 19 sites, ~210 LOC mechanical update |
| PE3 — .ifgoto inline | ✅ | 14-case sweep pattern validated |
| **PF1' — self-loop ArmDiverges** | ✅ | `ArmStep s s → ArmDiverges s` (~10 LOC). Works under nondet. |
| **PF2' — TAC→ARM self-loop** | ✅ | spec + TAC self-loop → ArmStep s s (~55 LOC) |
| PF3 — step_count_pc_uniqueness | ❌ blocks | Naive induction stalls; confirms pivot is necessary |

Probe files (reusable blueprints — **clone for the real proofs**):
- [`CCTests/Tests/PivotProbePD2.lean`](../CCTests/Tests/PivotProbePD2.lean) — mini `ArmStepDet` + `arm_step_det` via projection.  Blueprint for pivot Step 3.
- [`CCTests/Tests/PivotProbePF1.lean`](../CCTests/Tests/PivotProbePF1.lean) — `arm_self_loop_diverges` + `arm_diverges_of_prefix_reaches_self_loop`.  Copy-ready for Fix B'.
- [`CCTests/Tests/PivotProbePF2.lean`](../CCTests/Tests/PivotProbePF2.lean) — `tac_goto_self_loop_implies_arm_self_loop`.  Blueprint for Fix B' self-loop analysis.
- [`CCTests/Tests/PivotProbePE3.lean`](../CCTests/Tests/PivotProbePE3.lean) — `.ifgoto` inline-style branch-bound proof.  Blueprint for the 14-case sweep (if Phase 6 tackled).

### Un-privatized infrastructure

For probe and pivot support, these `CodeGen.lean` declarations were
un-privatized (no semantic change):
- `buildPcMap_eq_take_length`
- `codeAt_of_bodyFlat`
- `codeAt_of_bodyFlat'`
- `isLibCallTAC`

### What landed in session 3 (2026-04-23)

**Phase A — deterministic havoc pivot** (commit `d41636e`, ~302 LOC,
9 → 8 sorrys):

- Added opaque `havocRegsFn` / `havocFRegsFn` in [ArmDefs.lean:208-210](../CredibleCompilation/ArmDefs.lean#L208-L210).
- Refactored 7 `ArmStep` libcall constructors in [ArmSemantics.lean](../CredibleCompilation/ArmSemantics.lean)
  (dropped `newRegs`/`newFregs` args; successors now determined by
  `havocRegsFn s` / `havocFRegsFn s`).
- Updated 19 call sites across ArmSemantics (6), ArmCorrectness (6),
  CodeGen (7), and ArmStep.pc_eq_armNextPC binders in
  PipelineCorrectness.
- Added `armStepResult` (~85 LOC match), `ArmStep.eq_armStepResult`
  (~65 LOC cases), `arm_step_det` (6 LOC), `step_count_state_
  uniqueness` (15 LOC direct induction), and filled the
  `step_count_pc_uniqueness` sorry as a 2-line corollary via `.pc`
  projection.

**Phase B partial — Phase 7d + Fix B' primitives** (commit `8524574`,
~184 LOC, 8 → 7 sorrys):

- In [Refinement.lean](../CredibleCompilation/RefCompiler/Refinement.lean):
  `has_behavior_init` — mirrors `has_behavior`'s proof structure but
  packages witnesses into `program_behavior_init` (fixing am to
  `ArrayMem.init`).
- In [PipelineCorrectness.lean](../CredibleCompilation/PipelineCorrectness.lean)
  ported three Fix B' primitives from probe files:
  - `arm_self_loop_diverges` (PF1')
  - `arm_diverges_of_prefix_reaches_self_loop` (PF1')
  - `tac_goto_self_loop_implies_arm_self_loop` (PF2')
- Proved Phase 7d (`arm_diverges_implies_while_diverges`) via case on
  `has_behavior_init`: halts/errors bins contradicted with
  `step_count_state_uniqueness` + `sentinel_stuck`; typeErrors via
  `pipelined_no_typeError`; diverges via
  `while_to_arm_divergence_preservation`.

### Plan deviation: Steps 7 and 8 deferred

The original plan ordered Phase B as Steps 6 → 7 → 8 → 9 → 10, with
Steps 7 (`tac_iftrue_self_loop_implies_arm_self_loop`) and 8
(`source_diverges_gives_ArmDiverges_init`) as Fix B' composition
infrastructure.

Session 3 deferred Steps 7, 8 because Phase 7d (Step 10) does NOT
consume them — its proof uses `step_count_state_uniqueness` +
`sentinel_stuck` + `while_to_arm_divergence_preservation` directly.
Steps 7, 8 are only needed for Phase C (7a/b/c) where source-
divergence must be contradicted at div/bounds sentinels.

**Structural concern with Step 7 raised during session 3**:
`.ifgoto be pc` (with `be.eval σ = true`) compiles to a **multi-
instruction** ARM sequence (evaluate `be` into regs/flags, then
conditional branch).  So `ArmStep r.bodyFlat s s` (single-step
self-loop) is **not directly provable** for the `.ifgoto` case —
intermediate ARM states have modified regs/flags.  The plan's
original framing ("similar to PF2'") needs revision for this case.

Recommended pivot in next session: generalize
`arm_diverges_of_prefix_reaches_self_loop` to accept an `ArmSteps s s'`
cycle (where `s'.pc = s.pc` but `s' ≠ s` is allowed) rather than a
single `ArmStep s s`.  Then the forward simulation for `.ifgoto` self-
loop produces this `ArmSteps` cycle directly, without needing a
dedicated `tac_iftrue_self_loop_implies_arm_self_loop` lemma.

### Current sorry count: 4 (post-session-4)

All in `CredibleCompilation/PipelineCorrectness.lean`:

| Line | Sorry | Phase | Status |
|---|---|---|---|
| 770 | `bodyFlat_branch_target_bounded` | 6 | Out of scope |
| 1022 | `arm_behavior_exhaustive` | 6 | Out of scope |
| 1324 | `source_diverges_gives_ArmDiverges_init` | 7 (Step 2) | Next session |
| 2115 | `verifiedGenInstr_ifgoto_branch_bounded` | 6 probe | Out of scope |

Closing the "Next session" sorry takes the count to **3** (Phase 7
fully done).  Closing the 3 "Out of scope" sorrys (Phase 6 exhaustion)
takes it to 0.

## Commits on `phase6-prep`

```
74f89ec Phase 7a/b/c close + source_diverges_gives_ArmDiverges_init placeholder
1ee116e Phase 7 Step 6: close halt_state_observables_deterministic
400dbbf Add LOC-over-time plots to plans/
72ace2f Phase 6/7 session 3 handoff: update plan + CHANGELOG
8524574 Phase B partial: Phase 7d closed + Fix B' primitives + has_behavior_init
d41636e Phase A: deterministic havoc pivot + state_uniqueness (9 → 8 sorrys)
632b130 Tune Livermore iteration counts and harden opt/C2 correctness check
0173762 Phase 6/7 handoff: consolidated next-session plan
4094678 Phase 6/7 micro-probe PF3: step_count_pc_uniqueness under nondet
166f873 Phase 6/7 pivot probes PF1', PF2': Fix B' validated
0732a55 Phase 6/7 pivot probes PE1, PE2, PE3: findings before starting pivot
75a47f8 Phase 6/7 pivot probes: PD1, PD2 passed; PD3 flags LOC blowup
ec91423 Phase 6/7 deterministic pivot implementation plan (SUPERSEDED by this doc)
eb899b9 Phase 6/7 session report: deterministic havoc pivot
63e88d3 Phase 6/7 Path B: infrastructure + P2/P3 probes validated
85cecb5 Bring main design doc into repo plans/
```

Branch is pushed to `origin/phase6-prep`.

## Next Session Work Plan (session 4, 2026-04-23+)

**Goal**: close Phase 7 fully by landing 7a, 7b, 7c + halt observables.
Target: 7 → 3 sorrys, ~280 LOC, ~80% confidence.

### Step order and estimates

**Step 1 (~40 LOC)** — Generalize `arm_diverges_of_prefix_reaches_self_loop`.

The current primitive requires a single `ArmStep s s` witness.  For the
`.ifgoto be pc` self-loop case, the ARM-level "loop" is a multi-step
sequence `ArmSteps s s'` with `s'.pc = s.pc` but `s' ≠ s`.  Generalize:

```lean
theorem arm_diverges_of_prefix_and_cycle
    {prog : ArmProg} {init s : ArmState}
    (hReach : ArmSteps prog init s)
    (hCycle : ArmSteps prog s s')
    (hCycleNonrefl : ∃ k, k ≥ 1 ∧ ArmStepsN prog s s' k)
    (hPcEq : s'.pc = s.pc)
    : ArmDiverges prog init
```

Wait — the new `s'` after a cycle isn't the same state, so we can't
"keep cycling" directly.  The right generalization uses ExtSimRel
forcing post-cycle state to satisfy the same source configuration:

```lean
theorem arm_diverges_of_source_self_loop_cycle
    {prog : ArmProg} {init : ArmState}
    (hReach : ∀ n, ∃ s, ArmStepsN prog init s n)  -- an infinite family
    : ArmDiverges prog init
```

This is definitionally `ArmDiverges`, so it's trivial.  The real lemma
we need: **forward sim of source TAC self-loop iterated n times gives
n distinct ArmSteps**.  Budget the first 40 LOC toward this.

**Step 2 (~120 LOC)** — `source_diverges_gives_ArmDiverges_init`.

Given `program_behavior_init p' σ_init .diverges` (i.e., an
`IsInfiniteExec f` with `f 0 = Cfg.run 0 σ_init ArrayMem.init`),
construct `ArmDiverges r.bodyFlat (Phase6.initArmState r)`.

Strategy: induction on step count n.  Use the forward simulation
(specifically `backward_simulation` / `tacToArm_correctness`'s
iterative version) to map each TAC step to a non-empty ARM step
sequence.  The cumulative ArmSteps give the ArmStepsN witness.

Expected tricky case: if the infinite TAC trace keeps returning to the
same TAC cfg (self-loop in source), ARM must still produce unboundedly
many states — this is guaranteed because each forward-sim of a
.goto/.ifgoto cycle is non-trivial (non-refl ArmSteps).

Two drafting approaches:
- **(a) Self-loop-aware**: case-split on whether any prefix ends in a
  source self-loop; use the helper from Step 1 if so.
- **(b) Uniform**: just prove each forward sim produces ≥ 1 ArmStep,
  then construct the ArmDiverges by induction without self-loop cases.

Approach (b) is cleaner if the forward-sim length is provably ≥ 1 for
every non-trivial TAC step.  Check `tacToArm_correctness` details.

**Step 3 (~60 LOC)** — Phase 7b (`arm_div_implies_while_unsafe_div`).

Case on `has_behavior_init` for source bin:
- halts σ': forward sim gives s' at haltFinal.  `step_count_state_
  uniqueness` ⇒ the ArmDiverges-implied state at length k matches s'.
  But here we're not given ArmDiverges — we're given an ARM reach at
  `divS`.  Contradict via sentinel distinctness: the divS-reach at
  some length m + the haltFinal-reach at length k both come from
  init; if m = k, state_uniqueness says they're the same state, but
  `haltFinal ≠ divS`; if m ≠ k, extend the shorter one or truncate
  the longer one to match lengths, same contradiction.
- errors σ' div: source is exactly what we want — return the witness.
- errors σ' bounds: forward sim gives s' at boundsS.  `step_count_
  state_uniqueness` at common length + `divS ≠ boundsS` → contradiction.
- typeErrors: excluded via `pipelined_no_typeError`.
- diverges: apply `source_diverges_gives_ArmDiverges_init` from Step 2
  → contradict via `sentinel_stuck` on divS (same technique as Phase
  7d's halts/errors branches).

**Step 4 (~60 LOC)** — Phase 7c (`arm_bounds_implies_while_unsafe_
bounds`).  Symmetric to Step 3 with boundsS instead of divS.

**Step 5 (~80 LOC)** — Phase 7a (`arm_halts_implies_while_halts`).

Case on `has_behavior_init`:
- halts σ': forward sim gives s'_fwd at haltFinal.  `step_count_state_
  uniqueness` at common length says s = s'_fwd (exact state equality
  under the pivot — stronger than PC-only uniqueness).  So observables
  match σ_src via the ExtStateRel in the forward sim.
- errors/typeErrors/diverges: all contradict via state_uniqueness +
  sentinel distinctness (`haltFinal ≠ divS`, `haltFinal ≠ boundsS`)
  or sentinel_stuck + Step 2's source_diverges_gives_ArmDiverges_init.

Phase 7a doesn't need `halt_state_observables_deterministic` as a
separate helper under the pivot — the state_uniqueness at common
length directly gives state equality, so observable match is inline.

**Step 6 (~15 LOC)** — Fill `halt_state_observables_deterministic`
sorry as a direct corollary of `step_count_state_uniqueness`.  Reach
init → s₁ in k₁ steps, init → s₂ in k₂ steps.  WLOG k₁ ≤ k₂ (take
min).  Truncate the longer; state_uniqueness at k = min says the
truncated equals the shorter.  But both end at haltFinal, so one of
them has an outgoing step from haltFinal — contradiction via
sentinel_stuck unless k₁ = k₂.  Then state_uniqueness gives s₁ = s₂
directly.

**Checkpoint after session 4**: 7 → 3 sorrys.  Commit as "Phase 7
complete."

### Checkpoint discipline

Commit after each step; `lake build` should be green with at most the
previously-remaining sorry count at each checkpoint.  If Step 2
exceeds 180 LOC, stop and reconsider — the composition might need
weaker intermediate conclusions.

### Still open after session 4

Phase 6 exhaustion (separate ~700 LOC deliverable):
- `bodyFlat_branch_target_bounded` (14-case sweep) — ~600 LOC
- `arm_behavior_exhaustive` (König) — ~100 LOC
- `verifiedGenInstr_ifgoto_branch_bounded` probe placeholder —
  subsumed by sweep

## Historical Work Plan (session 3, completed)

The plan below is the one session 3 followed.  Kept as historical
record for cross-referencing commit messages.

### Phase A — pivot (Steps 1–5 of old plan, ~450 LOC total) ✅ DONE

Goal: deterministic `ArmStep` + `step_count_state_uniqueness` + Phase 7d.

1. **Add opaque havoc functions** in
   [`CredibleCompilation/ArmDefs.lean`](../CredibleCompilation/ArmDefs.lean):

   ```lean
   opaque havocRegsFn : ArmState → ArmReg → BitVec 64
   opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64
   ```
   ~15 LOC including docstring.

2. **Refactor 5 `ArmStep` libcall constructors** in
   [`CredibleCompilation/ArmSemantics.lean`](../CredibleCompilation/ArmSemantics.lean):
   drop `(newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64)`
   arguments; use `havocRegsFn s`, `havocFRegsFn s` inline.
   Constructors: `printCall`, `callPrintI`, `callPrintB`, `callPrintF`,
   `callPrintS`, `callBinF`, `floatUnaryLibCall`.
   ~20 LOC.

3. **Update 19 call sites** (PE2 classified, see below):
   - `ArmSemantics.lean` (6 sites in `ArmStep_total_of_codeAt`): trivial,
     drop `(fun _ => 0) (fun _ => 0)` witnesses.
   - `ArmCorrectness.lean` (6 sites in forward sim): each has pattern
     `let newRegs := fun _ => 0; let newFregs := fun _ => 0; let s2 := ...
     .callPrintX newRegs newFregs hCodeCall`.  Update `s2` definition
     to use `havocRegsFn`/`havocFRegsFn`; drop args.  Standard proofs
     (e.g., `havocCallerSaved_preserved`) are generic — no proof rework.
   - `CodeGen.lean` (7 sites in `verifiedGenerateAsm_spec`): same
     pattern.  ~15 LOC per site.
   - `PipelineCorrectness.lean` § 10b: update `ArmStep.pc_eq_armNextPC`
     binder counts (remove `_ _` for havoc args in the 5 libcall
     cases).  ~20 LOC.

   **Total Step 3**: ~210 LOC mechanical.

   After Step 3, run `lake build` — should be green with same sorry
   count as before (9).

4. **Prove `arm_step_det`** via the projection trick validated in PD2:

   ```lean
   private def armStepResult (s : ArmState) (i : ArmInstr) : ArmState := ...
   private theorem ArmStep.eq_armStepResult (h : ArmStep prog s s') :
       ∃ i, prog[s.pc]? = some i ∧ s' = armStepResult s i := ...
   theorem arm_step_det {prog s s₁ s₂}
       (h1 : ArmStep prog s s₁) (h2 : ArmStep prog s s₂) : s₁ = s₂ := ...
   ```

   Clone `PivotProbePD2.lean`'s structure for 5 constructors.  Scaling
   to ~50 constructors is mechanical pattern-matching.  ~100 LOC.

5. **Prove `step_count_state_uniqueness`** in PipelineCorrectness.lean:
   direct induction via `arm_step_det`.  ~15 LOC (exact template in
   `PivotProbePD2.lean`).  Also fill the existing
   `step_count_pc_uniqueness` sorry as a 3-line corollary.

**Checkpoint after Phase A (landed ✅ in session 3, commit d41636e)**:
9 → 8 sorrys (`step_count_pc_uniqueness`
filled).  Commit as "Phase A: deterministic havoc + state_uniqueness
landed."

### Phase B — Fix B' + Phase 7d (~310 LOC) — PARTIAL ✅ (commit 8524574)

**Session 3 outcome**: Steps 6 (PF1/PF2 port), 9 (has_behavior_init),
and 10 (Phase 7d) landed.  Steps 7 (`tac_iftrue_self_loop_implies_arm_
self_loop`) and 8 (`source_diverges_gives_ArmDiverges_init`) deferred
— they are NOT needed for Phase 7d; consume them in Phase C instead.

Structural issue with Step 7 as originally framed: `.ifgoto`
compiles to multi-instruction ARM, so `ArmStep s s` (single-step self-
loop) is structurally not provable for the `.ifgoto` case.  The fix
for Phase C is to generalize Step 1's primitive to accept multi-step
cycles.  See § Next Session Work Plan Step 1 for the revised approach.


Goal: handle source-divergence bin for all Phase 7 theorems.

6. **Port probes to PipelineCorrectness.lean**: copy
   `arm_self_loop_diverges`, `arm_diverges_of_prefix_reaches_self_loop`,
   `tac_goto_self_loop_implies_arm_self_loop` from the probe files.
   ~80 LOC (already proven — transfer takes minimal effort).

7. **Prove `tac_iftrue_self_loop_implies_arm_self_loop`**
   (`.ifgoto be pc` with `be.eval = true`).  Similar to PF2' but
   navigates `.ifgoto`'s 3-arm be match.  ~60 LOC.  Reference the
   `.binop .div` / `.goto` probes in § 10 of PipelineCorrectness.lean
   and PE3 for the pattern.

8. **Prove `source_diverges_gives_ArmDiverges_init`** — the
   composition theorem.  Induction on TAC prefix length with case
   split: if any TAC step is a self-loop, apply
   `arm_diverges_of_prefix_reaches_self_loop`; else, use the fact that
   non-self-loop TAC steps produce non-refl ArmSteps (via ExtSimRel
   forcing state change).  ~120 LOC.

9. **Add `has_behavior_init` wrapper** in PropChecker.lean to
   strengthen `has_behavior`'s conclusion to `program_behavior_init`
   (fixing `am₀ = ArrayMem.init`).  Update `pipelined_has_behavior` to
   use it.  ~15 LOC.

10. **Phase 7d** — `arm_diverges_implies_while_diverges`:
    Case on `pipelined_has_behavior_init`:
    - halts/errors: forward sim → contradiction via
      `step_count_state_uniqueness` + `sentinel_stuck`.
    - typeErrors: `pipelined_no_typeError`.
    - diverges: existing `while_to_arm_divergence_preservation`.
    ~35 LOC.

**Checkpoint after Phase B (PARTIAL ✅ in session 3)**: 8 → 7 sorrys.
Phase 7d closed; Steps 7, 8 deferred to session 4.

### Phase C — Phase 7a/b/c (~220 LOC) — PENDING (session 4 target)

**Note**: session 4 should absorb Steps 7 and 8 (Fix B' composition)
into Phase C rather than treating them as Phase B leftovers — see the
"Next Session Work Plan (session 4)" above for the revised step order.


11. **Phase 7b** (`arm_div_implies_while_unsafe_div`): case on source
    behavior.  Halts/errors-bounds/typeErrors: contradict via state
    uniqueness + sentinel distinctness (`divS ≠ haltFinal`,
    `divS ≠ boundsS`).  Errors-div: direct via
    `while_to_arm_div_preservation`.  Diverges: contradict via Fix B'
    (`source_diverges_gives_ArmDiverges_init` gives `ArmDiverges`; then
    contradict with `sentinel_stuck` on `s.pc = divS`).  ~60 LOC.

12. **Phase 7c** — symmetric to 7b with `boundsS`.  ~60 LOC.

13. **Phase 7a** (`arm_halts_implies_while_halts`): case on source.
    Halts bin: forward sim gives `s_fwd` with `ExtStateRel σ_src s_fwd`
    and `s_fwd.pc = haltFinal`.  `step_count_state_uniqueness` gives
    `s = s_fwd`, so observables at `s` match `σ_src`.  Under the pivot,
    `halt_state_observables_deterministic` helper is subsumed by state
    uniqueness — close inline without a separate helper.  ~80 LOC.

14. **Close `halt_state_observables_deterministic` sorry**: becomes
    direct corollary of `step_count_state_uniqueness` applied at
    lengths k₁ = k₂ = min(k_fwd, k_hyp) or similar.  ~15 LOC (collapses
    from the design doc's 100 LOC estimate).

**Checkpoint after Phase C**: 7 → 3 sorrys (Phase 7a/b/c/d done +
halt observables).  Commit as "Phase 7 complete."

### Remaining after Next Session

Still open for full 0-sorry:
- `bodyFlat_branch_target_bounded` (Phase 6, 14-case sweep) — ~600 LOC
- `arm_behavior_exhaustive` (Phase 6 König) — ~100 LOC
- `verifiedGenInstr_ifgoto_branch_bounded` probe — subsumed by sweep

These are **Phase 6 exhaustion only** — not required for Phase 7
closure.  Do in a separate session if desired.

## Total budget summary

| Phase | LOC | Sorry change | Confidence |
|---|---|---|---|
| A — pivot + state_uniqueness | ~450 | 9 → 8 | 90% (probes validated) |
| B — Fix B' + 7d | ~310 | 8 → 7 | 80% |
| C — 7a/b/c + halt obs | ~220 | 7 → 3 | 80% |
| **Phase 7 total** | **~980** | **9 → 3** | **~75%** |
| D — Phase 6 exhaustion (optional) | ~700 | 3 → 0 | 65% |

Net: 6 sorrys closed for full Phase 7 in ~980 LOC.  9 sorrys closed in
~1680 LOC for full Phase 6/7.

## Risk tracker

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| Step 3 call-site rewrite has hidden non-mechanical sites | 20% | +50 LOC | PE2 enumerated all 19; spot-checked each pattern. |
| Step 4 `armStepResult` ~50-constructor enumeration hits compile-time | 15% | +1hr | Tier by structure: seq (~40), two-branch (~6), havoc (~5).  Clone PD2 pattern exactly. |
| Step 8 `source_diverges_gives_ArmDiverges_init` composition harder than estimated | 30% | +80 LOC | Well-defined induction; probe PF1' validates core primitives. |
| Step 13 Phase 7a's observable match needs more than state uniqueness | 25% | +30 LOC | State uniqueness is strictly stronger than PC uniqueness; observable-match inline via ExtStateRel. |
| `has_behavior_init` wrapper turns out >30 LOC | 20% | +20 LOC | Internal of `has_behavior` already gives `ArrayMem.init`; wrapper is just signature tightening. |

## Session prep checklist

Before starting:
- [ ] Read this document end-to-end.
- [ ] Skim [`CCTests/Tests/PivotProbePD2.lean`](../CCTests/Tests/PivotProbePD2.lean) (the `arm_step_det` blueprint).
- [ ] Skim [`CCTests/Tests/PivotProbePF1.lean`](../CCTests/Tests/PivotProbePF1.lean) and [`CCTests/Tests/PivotProbePF2.lean`](../CCTests/Tests/PivotProbePF2.lean) (Fix B' blueprints).
- [ ] Confirm `lake build` on commit `4094678` is green (baseline sanity).
- [ ] Have an enumeration of the 19 call sites handy (PE2 output in
      `phase6-7-pivot-probe-findings.md`).

## Key files and their purposes

| File | Purpose |
|---|---|
| [`CredibleCompilation/PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean) | Phase 6/7 theorems + infrastructure. Main workspace. |
| [`CredibleCompilation/ArmDefs.lean`](../CredibleCompilation/ArmDefs.lean) | Where opaque `havocRegsFn`/`havocFRegsFn` live. |
| [`CredibleCompilation/ArmSemantics.lean`](../CredibleCompilation/ArmSemantics.lean) | `ArmStep` inductive.  5 libcall constructors to refactor. |
| [`CredibleCompilation/ArmCorrectness.lean`](../CredibleCompilation/ArmCorrectness.lean) | Forward sim.  6 call sites need updating. |
| [`CredibleCompilation/CodeGen.lean`](../CredibleCompilation/CodeGen.lean) | Codegen + spec.  7 call sites need updating. |
| [`CredibleCompilation/PropChecker.lean`](../CredibleCompilation/PropChecker.lean) | `has_behavior`.  Add `has_behavior_init` wrapper. |
| [`CCTests/Tests/PivotProbe*.lean`](../CCTests/Tests/) | Probe files.  Blueprints to clone. |
| [`plans/phase6-7-NEXT-SESSION.md`](phase6-7-NEXT-SESSION.md) | This document. |
| [`plans/phase6-7-deterministic-pivot-plan.md`](phase6-7-deterministic-pivot-plan.md) | Original pivot plan.  SUPERSEDED — see header note. |
| [`plans/phase6-7-pivot-probe-findings.md`](phase6-7-pivot-probe-findings.md) | PD1/PD2/PD3 probe findings. |
| [`plans/phase6-7-session-report-2026-04-22.md`](phase6-7-session-report-2026-04-22.md) | Session 1 process report. |
| [`plans/backward-jumping-octopus.md`](backward-jumping-octopus.md) | Master plan doc.  Phase 6/7 checkpoints. |
| [`plans/backward-jumping-octopus-phase6-design.md`](backward-jumping-octopus-phase6-design.md) | Original Phase 6 design. |
| [`plans/backward-jumping-octopus-phase5b-design.md`](backward-jumping-octopus-phase5b-design.md) | Phase 5b design (not on critical path). |

## One-liner summary for fast handoff

**Pivot + Fix B', order: refactor ArmStep → arm_step_det → state_uniqueness → 7d → 7b → 7c → 7a.  Budget ~980 LOC.  All blueprints in `CCTests/Tests/PivotProbe*.lean`.  9 sorrys → 3 sorrys.  No changes needed to TAC, passes, ExtSimRel, or top-level theorems.**
