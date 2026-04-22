/-
# PD3 — Forward-sim composability probe

Tests whether we can compose `tacToArm_refinement` over prefixes of an
`IsInfiniteExec` to get `ArmStepsN init s K` with `K` bounded below by
the TAC prefix length.

This is the core ingredient for `source_diverges_arm_pc_in_bodyFlat`
(Step 6 of the pivot plan), which in turn unblocks Phase 7a/b/c's
"source diverges" case.

**Goal of this probe**: identify which sub-lemmas are actually needed
and whether they're available or require new work.
-/

import CredibleCompilation.PipelineCorrectness

namespace PivotProbePD3

open ArmState

/-!
## The target lemma (Step 6 of the pivot plan)

```lean
theorem source_diverges_arm_pc_in_bodyFlat
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok r)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPassesPure prog.tyCtx passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init)
    (k : Nat) {s : ArmState}
    (hArm : ArmStepsN r.bodyFlat (Phase6.initArmState r) s k) :
    s.pc < r.haltFinal
```

## Dependency graph

To prove the target:

1. **Need**: given IsInfiniteExec + prefix length n, extract an ArmStepsN
   witness of length ≥ n whose state is at some TAC-configuration-corresponding
   PC.
2. **Have**: `tacToArm_refinement` gives `ArmSteps init s'` from a
   finite `Steps` chain.
3. **Have**: `ArmSteps_to_ArmStepsN` gives an existential length.
4. **Missing**: a way to LOWER-BOUND the extracted length by the
   number of TAC steps.

The bound comes from `bodyPerPC_length_pos` (each chunk ≥ 1 ARM
instruction).  But `ArmSteps_to_ArmStepsN` loses this information.

**Two routes**:

- Route A: **refactor** tacToArm_refinement to return
  `ArmStepsN init s' K` with an explicit length parameter.  This is
  the Phase 5b `step_simulation` refactor.  ~150 LOC.

- Route B: **under the deterministic model**, rely on determinism to
  conclude state uniqueness at each step count, sidestepping the
  length-bound issue.
-/

/-!
## Route B sketch: deterministic model bypass

Key insight: under deterministic havoc (arm_step_det), the ARM
trajectory from init is unique.  Define:

```lean
def armTrace (prog : ArmProg) (init : ArmState) : Nat → ArmState
  | 0 => init
  | n + 1 => (armStepResult (armTrace prog init n) (prog[(armTrace prog init n).pc]?.getD default))
```

Any ArmStepsN init s K satisfies `s = armTrace prog init K`.  So PC
determinism becomes a pure function of init and step count.

BUT this requires total `armTrace`, which requires `armStepResult` to
be total over all (state, instr) pairs — including the case where
`prog[pc]? = none`.  We'd handle this with a "stuck" marker.

**Simpler alternative**: rather than defining armTrace, directly use
`ArmStepsN_trans` to compose forward sim with `bodyPerPC_length_pos`
at the proof level.  Track length symbolically in a refined forward
sim chain.
-/

/-!
## What the direct proof shape looks like

```lean
-- Helper (Step 6's real shape): forward sim over n TAC steps gives
-- ArmStepsN of length ≥ n.
theorem forward_sim_over_tac_prefix
    {prog ...} (hGen ...) (f : Nat → Cfg) (hinf ...) (hf0 ...)
    (n : Nat) :
    ∃ s K, K ≥ n ∧ ArmStepsN r.bodyFlat init s K ∧
           (∀ k ≤ K, ∃ s_k, ArmStepsN r.bodyFlat init s_k k ∧
              s_k.pc < r.haltFinal)
```

**Size estimate by stages**:
1. Induction on n, accumulating ArmStepsN: ~30 LOC.
2. Per-step extension via tacToArm_refinement + ArmSteps_to_ArmStepsN + trans: ~40 LOC.
3. The "for all k ≤ K, intermediate state has PC < haltFinal" part:
   requires tracking what happens INSIDE each chunk.  Each chunk's
   PCs are in `[pcMap pc_i, pcMap pc_i + |chunk_i|)`.  For all such
   PCs, PC < haltS < haltFinal.  This needs a new lemma:
   `chunk_internal_pc_le_haltS` ~40 LOC.
4. Composing these: ~30 LOC.

Total: ~140 LOC — at the higher end of the 80-150 budget, but
tractable.

**Obstacle: the "for all k ≤ K" intermediate states claim** requires
the forward sim to track EACH intermediate ARM state, not just the
endpoint.  Current tacToArm_refinement only gives the endpoint.

This is where we run into Phase 5b territory.  We'd need a refined
variant of `step_simulation` that exposes its intermediate ArmStepsN
structure.
-/

/-!
## Sketch: what would the refined step_simulation need?

Current (returns opaque ArmSteps):
```lean
step_simulation spec hStep hRel hPC hTS_cur hInv_cur :
    ∃ s_mid, ArmSteps prog s s_mid ∧ ExtSimRel cfg' s_mid ∧ ...
```

Refined (returns ArmStepsN with intermediate PC bounds):
```lean
step_simulation_bounded spec hStep hRel hPC hTS_cur hInv_cur :
    ∃ s_mid K, K ≥ 1 ∧ ArmStepsN prog s s_mid K ∧
               ExtSimRel cfg' s_mid ∧ ... ∧
               (∀ k < K, ∃ s_k, ArmStepsN prog s s_k k ∧
                  s_k.pc < r.haltFinal)
```

Adapting step_simulation to this shape: requires threading step counts
through every one of its internal cases (normal, lib-call, print,
halt-intercept).  This is precisely the Phase 5b refactor — ~150 LOC
per phase5b-design estimate.

**Conclusion**: without the Phase 5b refactor, Step 6 is not ~80 LOC —
it's ~200 LOC at minimum (80 for the outer induction + 120 for
rolling our own step-count-tracking forward sim).  With the Phase 5b
refactor available, Step 6 drops to ~60 LOC.
-/

/-!
## Alternative: weaker conclusion sufficient for 7a/b/c

What 7a/b/c ACTUALLY need: given ArmStepsN init s K (from our
hypothesis + ArmSteps_to_ArmStepsN), show s.pc ∉ sentinels IF source
diverges.  Equivalently, for the CURRENT K (not all k ≤ K), s.pc <
haltFinal.

This is weaker than "for all k ≤ K, intermediate PC is in bodyFlat."
It's just a single-state claim.

Can we prove the weaker version without full Phase 5b?

Attempt: given K and source diverges (via IsInfiniteExec), find n TAC
steps such that the cumulative ARM length exceeds K.  Then extract a
prefix ArmStepsN of length K (via ArmStepsN_prefix).  By
step_count_state_uniqueness, this prefix's endpoint = our s.  Show
the prefix endpoint has PC < haltFinal: it's INSIDE the forward-sim
chain for the first n TAC steps, at some ARM step K ≤ cumulative
length, i.e., PC is at `pcMap(pc_i) + j` for some i and j ≤
|chunk_i|, which is < haltS < haltFinal.

Yes — this works.  The key is that we still need:
- A way to say "cumulative ARM length ≥ K for some finite TAC prefix."
- A way to identify the state at any intermediate ARM step count.

This CAN be formalized without the full Phase 5b refactor, but it's
moderately intricate.  Estimate ~100 LOC.
-/

/-!
## PD3 verdict

- Step 6 as currently scoped (~80 LOC) is optimistic.  Realistic
  estimate: **~150 LOC** under deterministic model, assuming we don't
  do the full Phase 5b `step_simulation` refactor.
- Step 6's proof is tractable but depends on infrastructure that's
  similar-in-kind to Phase 5b pieces (just narrower in scope).
- The critical sub-lemma is "forward sim over n TAC steps gives
  cumulative ARM step count ≥ n".  This requires either:
    (a) Walking through tacToArm_refinement's induction and counting
        each sub-chunk's contribution.
    (b) Using `bodyPerPC_length_pos` + `ArmSteps_to_ArmStepsN` + a
        structural argument.

**Recommendation**: budget Step 6 at 150 LOC (not 80).  Plan accordingly.

**Alternative**: if Step 6 threatens to exceed 200 LOC, drop 7a/b/c's
"source diverges" case.  Their conclusions are weakened to e.g.
"source halts with matching observables OR source diverges" — still a
meaningful theorem but less clean.
-/

/-!
## Sanity check: can we at least state the target lemma without any
   proof?  If the statement alone has issues, there's a deeper problem.
-/

-- Include minimal infrastructure to state the target signature
-- (can be copy-paste'd into the real file later).

-- Verify the signature compiles.  Actual proof left as `sorry`.
theorem source_diverges_arm_pc_in_bodyFlat_SIGNATURE_CHECK
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok r)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPassesPure prog.tyCtx passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init)
    (k : Nat) {s : ArmState}
    (hArm : ArmStepsN r.bodyFlat
      { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
        pc := r.pcMap 0, flags := ⟨0, 0⟩ } s k) :
    s.pc < r.haltFinal := by
  sorry

end PivotProbePD3
