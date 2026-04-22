# Phase 6/7 Session Report — Deterministic Havoc Pivot (2026-04-22)

## Summary

Session started with the goal of landing the literal Phase 6 and Phase 7
theorems from `plans/backward-jumping-octopus.md` at 0 sorrys.  Ended
with a pivot: we stopped trying to prove `step_count_pc_uniqueness`
under the existing nondeterministic ARM semantics and decided to change
the ARM model to be deterministic-with-opaque-havoc-functions instead.
This document records the full process — probes, infrastructure that
landed, dead ends explored, and the reasoning that led to the pivot — so
the next session starts with the full context.

## Starting state

- Branch: `phase6-prep`, commit `85cecb5`.
- 11 sorrys in `PipelineCorrectness.lean`.
- Phase 6/7 skeleton in place from prep session (`1206945`).
- Probes validated: `.goto` and `.binop .div` branch-target-bounded
  cases in § 10 of `PipelineCorrectness.lean`.
- Design doc estimate: ~965 LOC, 1.5–2 focused days.

## Initial risk assessment

Before writing code, I graded the three pieces the design doc flagged as
risky:

1. **14-case `verifiedGenInstr_branch_target_bounded` sweep** — mechanical
   but voluminous.  Phase 5b history showed 3-nest cases (`.binop`)
   landed at 312 LOC vs. ~40 optimistic estimate.  `.ifgoto` is the
   main unknown.
2. **`step_count_pc_uniqueness`** — design estimated ~80 LOC via direct
   induction using per-ArmStep-rule PC determinism.  I flagged moderate
   risk around havoc interaction.
3. **`halt_state_observables_deterministic`** for 7a — design warned
   >200 LOC means the halt-save block semantics are more tangled than
   assumed.

Given these, I chose **Path B** over Path A: land the low-risk
infrastructure tier + validate the two highest-risk assumptions with
probes, then commit and hand off if the probes flagged issues.

## Derisk probes

### P3 — `type_safety` shape check

Quick grep to confirm `TypeSystem.lean:560`'s `type_safety` has the
exact shape `pipelined_no_typeError` needs.

**Result**: PASSED.  Confirmed `pipelined_no_typeError` is a ~20 LOC
wrapper.

### P2 — `arm_step_pc_det`

Goal: prove `ArmStep prog s s₁ ∧ ArmStep prog s s₂ → s₁.pc = s₂.pc`.
Input to `step_count_pc_uniqueness`'s induction.

**First attempt**: naive `cases h1 <;> cases h2 <;> simp_all`.
Timed out at `maximum number of heartbeats (200000)`.  The 50×50
ArmStep constructor pairing is too much for `simp_all` to close
unguided.

**Second attempt** (successful): defined a projection function
`armNextPC : ArmState → ArmInstr → Nat` that computes the next PC from
state + instruction as a pure function.  Cased on all ~50 ArmStep
constructors once to prove `ArmStep.pc_eq_armNextPC`:

```lean
theorem ArmStep.pc_eq_armNextPC (h : ArmStep prog s s') :
    ∃ i, prog[s.pc]? = some i ∧ s'.pc = armNextPC s i
```

Then `arm_step_pc_det` falls out in 4 lines via projection matching
(both steps project through same PC via the same instruction).

**Result**: PASSED (~70 LOC).  The `ArmState.havocCallerSaved_pc` simp
lemma (havoc doesn't touch PC) made the havoc cases one-liners.

**Key takeaway**: the projection trick avoids the constructor-pairing
explosion entirely for this kind of "input determines X" property.

### P1 — `.ifgoto` branch-target-bounded

Goal: prove `verifiedGenInstr_ifgoto_branch_bounded`.  Validates the
three-nest case pattern (`.not (.cmp)`, `.not (.fcmp)`, fallback)
needed for `bodyFlat_branch_target_bounded`.

**Attempted**: the proof structure matches the design doc's outline.
But Lean's elaborator choked on nested-match type signatures in helper
`have` blocks:

```lean
have loadA_nb : ∀ i ∈ (match a with
    | .var v => vLoadVar layout v (match a with | .var v => ... | _ => .x1)
    | .lit n => ...
    | _ => []),
    ...
```

Error: `Unknown constant False.var`.  Root cause is the nested `match a
with` inside the type signature re-references the outer `a` variable
confusingly during elaboration.

**Fix known** (inline the helpers, no `have` blocks), but deferred —
this probe confirmed the case is mechanically tractable but fiddly.
Helpers `formalLoadImm64_no_branches`, `vLoadVarFP_no_branches`,
`verifiedGenBoolExpr_no_branches` landed separately and are reusable.

**Result**: PARTIAL.  The `.ifgoto` theorem is left as `sorry` with the
attempt preserved in a comment block.  The 14-case sweep will revisit.

## Infrastructure landed (11 → 9 sorrys)

All in [`PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean):

### Phase 6 helpers
- `sentinel_stuck` — sentinel PC ⇒ `bodyFlat[pc]? = none` via
  `spec.haltFinal_eq` + `spec.haltS_eq` rewrite, then
  `ArmStep_stuck_of_none`.
- `pcMap_le_haltS` — every live TAC PC maps to ARM PC ≤ haltS.  Uses
  newly un-privatized `buildPcMap_eq_take_length` from CodeGen.lean.
- `checkBranchTargets_to_labels_in_bounds` — bridges the decidable
  check `checkBranchTargets` to the propositional "goto/ifgoto targets
  < p.size" form.
- `haltFinal_ne_divS`, `haltFinal_ne_boundsS`, `divS_ne_boundsS` —
  sentinel distinctness, trivial `omega` over spec equalities.

### Phase 7 helpers
- `stepClosed_of_checkCertificateExec` — extracts condition 6
  (`checkSuccessorsInBounds`) from a validated certificate.
- `applyPass_preserves_stepClosedInBounds` /
  `applyPassesPure_preserves_stepClosedInBounds` — Prop-form
  preservation of `StepClosedInBounds` through certified passes.
- `pipelined_has_behavior` — wrapper: `has_behavior` applied to the
  pipelined TAC, with `StepClosedInBounds` threaded via the pass
  preservation above.
- `pipelined_no_typeError` — wrapper over existing `type_safety` in
  TypeSystem.lean.

### Probe scaffolding (Phase6Probes2)
- `armNextPC`, `ArmStep.pc_eq_armNextPC`, `arm_step_pc_det` (P2).
- `formalLoadImm64_no_branches`, `vLoadVarFP_no_branches`,
  `verifiedGenBoolExpr_no_branches` (helpers for the 14-case sweep).

All 3137 jobs build green.  Commit `63e88d3` on `phase6-prep`.

## The `step_count_pc_uniqueness` roadblock

After landing the above, I attempted `step_count_pc_uniqueness`:

```lean
theorem step_count_pc_uniqueness {prog : ArmProg} {s₀ : ArmState} :
    ∀ n (s₁ s₂ : ArmState),
      ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n → s₁.pc = s₂.pc
```

**The issue**: the naive direct induction doesn't close.

- Base case (n=0): trivial, `s₁ = s₂ = s₀`.
- Successor step (n+1): obtain intermediate states `m₁, m₂` with
  `ArmStep prog s₀ m₁` and `ArmStep prog s₀ m₂`.  By `arm_step_pc_det`
  (probe P2), `m₁.pc = m₂.pc`.  But for the inductive hypothesis, we
  need `m₁ = m₂` (or at least equi-reachability), which is **false in
  general**: havoc rules take arbitrary `newRegs`/`newFregs` arguments,
  so two witnesses of `ArmStep prog s₀ m_i` can produce different
  register contents.

At the next step, `ArmStep prog m₁ m₂'` and `ArmStep prog m₂ m₂''`:
since `m₁.regs ≠ m₂.regs` is possible, a subsequent `cbz rn _` on a
havoc'd reg could branch differently, yielding different next PCs.

So `step_count_pc_uniqueness` **only holds because of spec-guaranteed
save/restore structure** around every havoc, ensuring no branch reads a
havoc'd reg without intervening restore.  Proving that requires
traversing `spec.callSiteSaveRestore` + `spec.printSaveRestore` +
`callerSaveSpec`.

**Revised estimate**: ~200+ LOC, not ~80.

## Design exploration: four alternatives

I stepped back to consider paths to prove `step_count_pc_uniqueness` cleanly.

### Option 1 — Chunk structural invariant (rejected)

"Every `bodyPerPC[pc]` chunk has either no branches or no havoc."

Initially thought ~250 LOC.  The idea: if a chunk has havoc, it must be
a libcall chunk (per `spec.callSiteSaveRestore`), which structurally
has no branches — just `saves ++ [single havoc instr] ++ restores`.
If a chunk has branches, it must be a non-libcall chunk, which
structurally has no havoc.

**Rejected when user pointed out**: havoc persists across chunks until
overwritten.  A subsequent chunk reading a caller-saved reg that
was havoc'd by a prior chunk without being restored would still be
unsafe.  The invariant needs to span chunks, not just be intra-chunk.

### Option 2 — Safe-branch-register check (considered)

Decidable check `checkBranchRegsSafe : ArmProg → Bool` that for every
`.cbz`/`.cbnz`/`.bCond`, verifies the operand register is either (a)
callee-saved, or (b) freshly written within the same chunk via a
deterministic instruction (`ldr`, `movR`, `mov`, etc.).

LOC estimate: ~400–500.  Still spec-dependent because caller-saved
var-holding regs need cross-chunk save/restore reasoning.

### Option 3 — Uninit-reads abstract interpretation (considered)

Abstract interp over a "may be uninitialized" set `U : Set ArmReg × Set
ArmFReg` per PC.  Transfer function:
- Writes (any `mov`/`ldr`/etc.): `U \ {rd}`.
- Havoc instructions: `U ∪ callerSavedRegs`.
- Reads: side condition `operand ∉ U`.

Chunk-local analysis exploits the spec property "branches only jump to
chunk starts, never mid-chunk" — so no CFG dataflow fixpoint needed,
just a structural linear scan per chunk with `U_canonical` at chunk
boundaries.

LOC estimate: ~440.  Clean framework, but:

**User raised the liveness-optimization concern**: if codegen later
adopts "save only live caller-saved vars" instead of saving all var-
holding ones, different libcall chunks have different save sets, so
`U` at chunk boundaries varies — either fixpoint dataflow (needs
fuel/termination infrastructure) or liveness-info-dependent analysis
(~700–900 LOC).

### Option 4 — Deterministic ARM semantics (PIVOT)

User proposal: change `ArmStep` so havoc is **deterministic** given
state.  Same state in ⇒ same state out.  Use opaque globally-fixed
havoc functions:

```lean
opaque havocRegsFn : ArmState → ArmReg → BitVec 64
opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64

inductive ArmStep (prog : ArmProg) : ArmState → ArmState → Prop where
  ...
  | printCall (lines : List String) :
      prog[s.pc]? = some (.printCall lines) →
      ArmStep prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
        |>.nextPC)
  ...
```

Consequences:
- `arm_step_det : ArmStep prog s s₁ ∧ ArmStep prog s s₂ → s₁ = s₂`
  becomes provable directly (~50 LOC).
- `step_count_state_uniqueness` (stronger than PC-uniqueness): ~15
  LOC induction via full state determinism.
- Phase 7a/b/c/d collapse: ~30 LOC each.

**Cost**: ~200–300 LOC mechanical refactor (ArmStep definition + ~50–100
call sites dropping `newRegs`/`newFregs` arguments) + ~150 LOC new
theorems (`arm_step_det`, `step_count_state_uniqueness`, Phase 7a/b/c/d).

**Soundness**: the opaque function is a universally-quantified witness —
"for any deterministic havoc function, correctness holds" —
equivalent expressive power to the nondeterministic model for this
codebase's needs.  We're not giving up anything real: our libcalls
(print, sin, cos, exp, pow) are all deterministic given state
(stdout side effects are observable output, not modeled state).

## Pivot decision

**Option 4 chosen.**  Rationale:

1. **Conceptual simplicity.**  "Same state in, same state out" is
   trivially testable and matches how pure libcalls actually behave.
2. **Unblocks all of Phase 7 cheaply.**  Once `arm_step_det` lands,
   7a/b/c/d collapse via full state determinism — no
   `halt_state_observables_deterministic` helper needed for 7a because
   state equality subsumes observable matching.
3. **No expressive loss for this codebase.**  All our libcalls are
   functionally deterministic given input state.  If that changes
   (e.g., `bl _rand()`), we can revisit on a per-call basis.

### Comparison of options

| Approach | LOC | Conceptual cost | Blockers |
|---|---|---|---|
| Direct proof under nondet havoc | ~300 | High (spec traversal) | Bespoke, fragile |
| Option 2 (safe-branch-reg check) | ~450 | High | Same spec traversal in disguise |
| Option 3 (uninit-reads analysis) | ~440 | High | Liveness optimization makes it worse |
| **Option 4 (deterministic havoc)** | **~400** | **Low** | **ArmStep refactor ripples** |

## Next-session work plan

Order:

1. **Refactor `ArmStep`** — add two `opaque` declarations for the havoc
   functions; remove `newRegs`/`newFregs` args from the 5 libcall
   constructors (`printCall`, `callPrintI/B/F/S`, `callBinF`,
   `floatUnaryLibCall`).  ~20 LOC in ArmSemantics.lean.

2. **Update call sites** — every existing use of
   `ArmStep.printCall _ _ _ _`, etc.  Mostly in `ArmCorrectness.lean`'s
   forward sim proofs and in `ArmStep_total_of_codeAt`.  ~100–150 LOC
   of mechanical argument removal.

3. **Prove `arm_step_det`** — case analysis on both ArmSteps at same
   state; each case closes by determinism of the rule's target state
   now that havoc args are fixed.  ~50 LOC.

4. **Prove `step_count_state_uniqueness`** — direct induction using
   `arm_step_det`.  ~15 LOC.  Supersedes
   `step_count_pc_uniqueness` (which the skeleton has as a sorry).

5. **Land Phase 7d** (simplest) — case on `pipelined_has_behavior`,
   rule out halt/error/typeError bins via state determinism + sentinel
   distinctness + `sentinel_stuck`; diverges case uses existing
   `while_to_arm_divergence_preservation`.  ~30 LOC.

6. **Land Phase 7a/b/c** — same schema as 7d.  7a needs observable
   matching, which follows from state determinism (no separate helper
   needed).  ~30 LOC each.

7. **(Separate track)** The 14-case
   `verifiedGenInstr_branch_target_bounded` sweep + lift +
   `arm_behavior_exhaustive` König construction for Phase 6 exhaustion.
   This is independent of `step_count_pc_uniqueness` — it's about
   "ARM always lands in one of four bins".  ~600 LOC, separate session.

Budget: Phase 7 closure ~400 LOC; Phase 6 exhaustion ~600 LOC.
Combined next-session target: Phase 7 (steps 1–6).

### Prereqs for the refactor

- Read this report for context.
- Decide: truly opaque (`opaque havocRegsFn ...`) vs. parameterized
  (ArmStep takes havoc functions as implicit parameters, theorems
  universally quantify).  Opaque is simpler call-site-wise; parameterized
  is more explicit about universality.  Recommend opaque for
  cleanliness; the meta-level "∀ havoc function" property can be
  documented in a comment rather than encoded in types.
- Checkpoint before step 5: full build green, `arm_step_det` closed,
  `step_count_state_uniqueness` closed.  If any fails, stop and
  re-plan.

## Lessons for future sessions

1. **Run derisk probes before the heavy sweep.**  P2 and P3 landed in
   <2 hours combined and saved misaligned work later.  P1's failure
   surfaced Lean elaboration quirks that would have eaten 2–3 hours in
   the middle of the full sweep.

2. **The design doc's LOC estimates trend optimistic for novel proofs.**
   `step_count_pc_uniqueness` at ~80 LOC was off by 2.5×.  `.binop` at
   ~40 LOC landed at 312.  For per-case sweeps, multiply the
   "optimistic" estimate by 4–8× for realistic budgeting.

3. **Semantic model choice is a design lever, not a constraint.**  When
   a theorem becomes hard to prove under the current model, consider
   whether a different (still sound) model makes it easy.  The
   nondeterministic ArmStep was chosen for generality, but that
   generality isn't used by any existing correctness theorem in this
   codebase — making the determinization essentially free.

4. **Chunk-local reasoning beats CFG dataflow when available.**  The
   `pcMap` property "branches only jump to chunk starts" turns
   ostensibly global analyses into local ones.  Worth documenting as a
   spec invariant so future analyses can rely on it.

## Files modified

- [`CredibleCompilation/PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean)
  — landed infrastructure, probes, broken P1 preserved in comment.
- [`CredibleCompilation/CodeGen.lean`](../CredibleCompilation/CodeGen.lean)
  — `buildPcMap_eq_take_length` un-privatized.
- [`CHANGELOG.md`](../CHANGELOG.md) — session summary.
- [`plans/backward-jumping-octopus.md`](backward-jumping-octopus.md) —
  checkpoint status updated.

## Commits

- `63e88d3` on `phase6-prep` — Path B infrastructure + P2/P3 probes.
