# Disjunction Elimination — Next Session Handoff

**Read this first.**  Follow-up to session-14's disjunction-elimination
refactor.  Last updated: 2026-04-24 after Stage 1 landed on `main`.

## Goal

Eliminate the `unsafeDiv ∨ unsafeBounds` disjunction from the conclusions
of the top-level cause-specific theorems, so that:

- `while_to_arm_div_preservation` concludes `∃ fuel, unsafeDiv fuel` (not
  the disjunction).
- `while_to_arm_bounds_preservation` concludes `∃ fuel, unsafeBounds fuel`.
- `arm_div_implies_while_unsafe_div` concludes `∃ fuel, unsafeDiv fuel`.
- `arm_bounds_implies_while_unsafe_bounds` concludes `∃ fuel, unsafeBounds fuel`.

Currently all four return `∃ fuel, unsafeDiv fuel ∨ unsafeBounds fuel`.

## TL;DR — state at end of previous session

**Stage 1 DONE and merged to main** (commit `c7d9b80`):
- `Behavior` type split: `.errors Store` replaced by `.errorDiv Store` +
  `.errorBounds Store`.
- `program_behavior`, `program_behavior_init`, `has_behavior`,
  `has_behavior_init`, `credible_compilation_soundness`,
  `credible_compilation_total`, `trans_has_behavior`,
  `exec_checker_correct`, `exec_checker_total`, `whileToTAC_refinement`,
  `while_to_arm_error_source_side`, and 3 backward Phase 7 theorems
  updated to the new constructor split.
- Cert-level cause-preservation (`errorDiv_preservation`,
  `errorBounds_preservation`) wired through instead of the cause-agnostic
  `error_preservation` wrapper.
- Build green, 0 sorries, no new axioms, end-to-end chain unaffected.

**Stages 2–5 REMAINING** (~1000–1200 LOC, 1.5–2 focused sessions):
cause-faithful forward compilation plus downstream tightening.

## Bottleneck

`whileToTAC_refinement`'s two error cases (`.errorDiv`, `.errorBounds`)
each currently prove the disjunction `∃ fuel, unsafeDiv ∨ unsafeBounds`
via `compileStmt_unsafe`, which is **cause-agnostic** — it only promises
the compiled code reaches some `c_err.isError` state, not which specific
cause.

To tighten, we need cause-faithful clauses in the forward-compilation
theorems: "if the source has `unsafeDiv`, the emitted error state is
specifically `Cfg.errorDiv`; if `unsafeBounds`, `Cfg.errorBounds`."

## Critical helper that already exists

`SExpr.unsafeDiv_unsafeBounds_disjoint` at
[CompilerCorrectness.lean:975](../CredibleCompilation/CompilerCorrectness.lean#L975),
and parallel theorems for `SBool` (line 1047) and `Stmt` (line 1203).
These prove `¬ (s.unsafeDiv ∧ s.unsafeBounds)` — the two source-level
predicates are **mutually exclusive**. This means the cause-faithful
clauses don't need extra exclusion hypotheses.

## Recommended approach (cleanest structurally)

**Strengthen the existing theorems in-place** rather than duplicating
into `_unsafeDiv` / `_unsafeBounds` variants. Add these two clauses to
each of `compileExpr_stuck`, `compileBool_stuck`, `compileExprs_unsafe`,
`compileStmt_unsafe`:

```lean
∧ (e.unsafeDiv σ am decls → ∃ σ' am', c_err = Cfg.errorDiv σ' am')
∧ (e.unsafeBounds σ am decls → ∃ σ' am', c_err = Cfg.errorBounds σ' am')
```

Each exit point of these theorems must now supply the two extra clauses.
The structure of each exit point makes this easy:

- **Emission producing `errorDiv`** (`.bin .div` / `.bin .mod`
  `unsafe_binop_errors`): unsafeDiv clause is `fun _ => ⟨_, _, rfl⟩`;
  unsafeBounds clause is vacuous via disjointness (the case's
  preconditions imply `unsafeDiv`, so by disjointness `¬unsafeBounds`).
- **Emission producing `errorBounds`** (`.arrRead` / `.farrRead` with
  `Step.arrLoad_boundsError`): symmetric.
- **Recursive case** (all non-emission cases): unpack the IH's two new
  clauses, pass them through.

## Scope

LOC estimate per file (rough):

| File | Existing | New (cause-faithful) |
|---|---|---|
| `compileExpr_stuck` ([ErrorHandling.lean:19](../CredibleCompilation/RefCompiler/ErrorHandling.lean#L19)) | 247 LOC | ~30 LOC additions |
| `compileBool_stuck` ([line 266](../CredibleCompilation/RefCompiler/ErrorHandling.lean#L266)) | 564 LOC | ~80 LOC additions |
| `compileExprs_unsafe` ([line 830](../CredibleCompilation/RefCompiler/ErrorHandling.lean#L830)) | 69 LOC | ~20 LOC additions |
| `compileStmt_unsafe` ([line 899](../CredibleCompilation/RefCompiler/ErrorHandling.lean#L899)) | 802 LOC | ~200 LOC additions |
| `whileToTAC_refinement` errorDiv/errorBounds cases | ~50 LOC each | drop disjunction — replace by_contra argument |
| 4 top-level theorems (`while_to_arm_*_preservation`, `arm_*_implies_*`) | ~50 LOC each | tighten conclusion, ~10 LOC change each |

**Total:** ~350 LOC of strengthening + ~200 LOC of downstream updates =
**~550 LOC.**

(Earlier estimates of 1000-2000 LOC were pessimistic; the per-case
additions are small because disjointness closes the "other cause"
clauses vacuously. Real effort is probably 1 focused session.)

## Proof skeleton for a typical emission case

For `compileExpr_stuck`'s `.bin .div a b` emission case (both a and b
safe, b.eval = 0 forcing errorDiv):

```lean
-- Before: returns ⟨..., 7-tuple⟩
-- After: returns ⟨..., 7-tuple ∧ cause-div-clause ∧ cause-bounds-clause⟩
refine ⟨offset + codeA.length + codeB.length, σ_b, _,
  FragExec.trans' hexec_a hexec_b,
  unsafe_binop_errors hbinop hva hvb hop,
  by simp [Cfg.isError],
  by simp [List.length_append]; omega,
  ?_, ?_⟩
· -- unsafeDiv clause: fires, c_err = errorDiv σ_b am
  intro _
  exact ⟨σ_b, am, rfl⟩
· -- unsafeBounds clause: vacuous via disjointness
  intro hbounds
  exfalso
  have hunsafe_div : e.unsafeDiv σ am p.arrayDecls := by
    simp [SExpr.unsafeDiv]; exact Or.inr (Or.inr ⟨ha, hb, hop_is_zero⟩)
  exact SExpr.unsafeDiv_unsafeBounds_disjoint e σ am p.arrayDecls
    ⟨hunsafe_div, hbounds⟩
```

## `whileToTAC_refinement` tightening

After `compileStmt_unsafe` has cause-faithful clauses, replace the
`errorDiv σ_e` case's body with direct cause tracking:

```lean
| errorDiv σ_e =>
  simp only [program_behavior_init] at hbeh
  obtain ⟨am_e, herr⟩ := hbeh
  -- goal (new strengthened): ∃ fuel, unsafeDiv fuel
  by_contra hall
  push_neg at hall  -- ∀ fuel, ¬ unsafeDiv fuel
  -- classical: either ∀ fuel, safe (handled by existing div/halt dichotomy)
  -- or ∃ fuel, unsafeBounds (handled via cause-faithful compileStmt + stuck_det)
  by_cases hub : ∃ fuel, prog.body.unsafeBounds fuel prog.initStore ArrayMem.init prog.arrayDecls
  · -- unsafeBounds at fuel → compileStmt_unsafe + cause-faithful clause →
    --   compiled reaches Cfg.errorBounds. But herr reaches Cfg.errorDiv.
    --   By stuck_det, errorBounds = errorDiv. Cfg.noConfusion. ∎
    obtain ⟨fuel, hub⟩ := hub
    have hunsafe : ¬ prog.body.safe fuel ... := ...
    obtain ⟨..., _, _, hBoundsClause⟩ := compileStmt_unsafe ... hunsafe ...
    obtain ⟨σ', am', heq_bounds⟩ := hBoundsClause hub
    -- stuck_det: c_err from compileStmt = c_err from herr = errorDiv σ_e am_e
    -- but heq_bounds says c_err = errorBounds σ' am' — Cfg.noConfusion.
    ...
  · push_neg at hub
    -- ∀ fuel, ¬ unsafeBounds fuel ∧ ¬ unsafeDiv fuel → ∀ fuel, safe fuel
    -- Then existing halt-or-diverge argument closes.
    ...
| errorBounds σ_e => ...  -- symmetric
```

## Top-level theorem tightening

Once `whileToTAC_refinement` gives specific causes, the following chain
becomes straightforward:

```lean
theorem while_to_arm_div_preservation ... :
    (∃ fuel, prog.body.unsafeDiv fuel ...) ∧    -- tightened (was disjunction)
    (∃ s', ArmSteps ... s' ∧ s'.pc = r.divS) := ...
```

And in `arm_div_implies_while_unsafe_div`, the cases now collapse —
the sentinel argument already fingers the source bin as `errorDiv`,
so the conclusion tightens directly.

## Don't

- Don't duplicate into `_unsafeDiv` / `_unsafeBounds` theorem pairs —
  that's ~2× the LOC with no structural benefit.
- Don't redefine `unsafeDiv` / `unsafeBounds` — they're already
  mutually exclusive (see `SExpr.unsafeDiv_unsafeBounds_disjoint`).
- Don't touch the existing Stage 1 `Behavior` split — it's landed on
  main and any further work goes **on top** of it.

## Where everything lives

| Artifact | Location |
|---|---|
| `Behavior` split + core definitions | [PropChecker.lean:560-573](../CredibleCompilation/PropChecker.lean#L560) |
| `program_behavior_init` (Behavior-valued) | [Refinement.lean:224](../CredibleCompilation/RefCompiler/Refinement.lean#L224) |
| `whileToTAC_refinement` (contains the stuck disjunction) | [Refinement.lean:313](../CredibleCompilation/RefCompiler/Refinement.lean#L313) |
| Forward compilation unsafe theorems | [ErrorHandling.lean](../CredibleCompilation/RefCompiler/ErrorHandling.lean) |
| Disjointness theorems | [CompilerCorrectness.lean:975](../CredibleCompilation/CompilerCorrectness.lean#L975), 1047, 1203 |
| Top-level forward theorems | [PipelineCorrectness.lean:432,453](../CredibleCompilation/PipelineCorrectness.lean#L432) |
| Top-level backward theorems | [PipelineCorrectness.lean:1454,1516](../CredibleCompilation/PipelineCorrectness.lean#L1454) |
| `while_to_arm_error_source_side` (currently dispatches Or) | [PipelineCorrectness.lean:402](../CredibleCompilation/PipelineCorrectness.lean#L402) |

## Checkpointing

The refactor splits naturally into commit-able chunks:

1. Strengthen `compileExpr_stuck` alone (closest to self-contained).
   Build green, commit.
2. Strengthen `compileBool_stuck`. Commit.
3. Strengthen `compileExprs_unsafe`. Commit.
4. Strengthen `compileStmt_unsafe` (largest; split into batches if
   needed). Commit.
5. Tighten `whileToTAC_refinement`. Commit.
6. Tighten top-level theorems. Commit.

## Stop conditions

- If any of Stages 2–5 fails to close after 2 hours on that stage:
  commit what's green, document the blocker, continue or defer.
- If `lake build` breaks with errors unresolvable in 30 minutes:
  revert the in-progress stage to the last green state.
