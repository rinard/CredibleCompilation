# Flavor A Signature Spec

**Purpose:** exact signatures for the length-tracked refactor that closes
`source_diverges_gives_ArmDiverges_init` at [PipelineCorrectness.lean:1324](../CredibleCompilation/PipelineCorrectness.lean#L1324).
Supersedes the ad-hoc descriptions in `plans/phase6-7-NEXT-SESSION.md § Session 5 work plan`.

**Estimated scope:** ~1000 LOC across 2–3 focused sessions.

## Core principle

Replace `∃ s', ArmSteps prog s s' ∧ P s'` return types with
`∃ s' k, ArmStepsN prog s s' k ∧ K(k) ∧ P s'` where `K(k)` is a case-
appropriate length claim. The length `k` becomes observable at destructure,
breaking the Lean 4 proof-irrelevance barrier that defeats post-hoc extraction.

## Length-claim forms used

| Form | When to use |
|---|---|
| `k = <list>.length` | Helpers emitting a fixed list of instructions, full traversal. |
| `(∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length)` | `verifiedGenInstr_correct`: full block traversal on `.run` targets. |
| `n ≤ k` | Multi-step composition (`tacToArm_refinement`, `tacToArm_correctness`): at least `n` ARM steps for `n` source steps. |

## Infrastructure (already in place)

- `ArmStepsN`, `ArmStepsN.single`, `ArmStepsN_trans`, `ArmStepsN_prefix`,
  `ArmStepsN_extend`, `ArmSteps_to_ArmStepsN` — in ArmSemantics.lean:299–353.
- `ArmStepsN_to_ArmSteps` (added session 5) — bridges new-signature callers
  to any residual `ArmSteps`-typed consumers without requiring full cascade.
- `StepsN`, `Steps_to_StepsN`, `StepsN_trans`, `StepsN_prefix` — TAC-side
  counted closure in PropChecker.lean:371–412.
- `verifiedGenInstr_output_pos` at ArmSemantics.lean:2615 — gives
  `1 ≤ instrs.length` under full spec invariants.
- `bodyPerPC_length_pos` in CodeGen.lean — per-PC block has length ≥ 1.
- `arm_step_det` in PipelineCorrectness.lean — deterministic ARM successor.

## Execution strategy — READ BEFORE STARTING

**Two procedural rules govern the refactor:**

### Rule 1: Sorry-ratchet within each phase

For each phase (A, B, C, ...), do it in two sub-steps:

**Sub-step X.0 (signatures + cascade)**: Update ALL the phase's theorem
signatures in one pass. Update ALL caller destructure patterns to match
the new signatures (e.g., `obtain ⟨s, hSteps, ...⟩ := foo ...` becomes
`obtain ⟨s, k, hStepsN, hk, ...⟩ := foo ...`). Replace each theorem body
with `sorry` (at the finest case granularity possible — e.g., per `|
case =>` arm in `verifiedGenInstr_correct`). Replace any caller proof
that uses `.trans` / `.single` in a non-trivially-composing way with
`sorry`. **Build must be green with temporarily bloated sorry count.**

**Sub-step X.1+ (fill sorrys)**: Fill each sorry individually, one at a
time. Commit per case or per logical group. Sorry count monotonically
decreases through this sub-step.

**Why this works:** destructure updates are cascade-sensitive (must be
right at signature-change time) but mechanical; proofs are intellectual
but case-local once signatures are fixed. Separating them avoids the
"break-everything-then-scramble" failure mode.

**Peak sorry count projection:** 4 (starting) → ~30 after A.0 → ~90
after B.0 → back down through A.1+, B.1+ → 3 at end.

### Rule 2: Hard cases first within each sub-step

De-risk the signature by attempting the hardest case before the easy
ones. If the hard case exposes a signature flaw, you fix it once; if
you'd done easy cases first, all their proofs would need re-doing.

**Specific hard-first ordering per phase:**

**Phase A fill order** (dependencies permitting):
1. `verifiedGenBoolExpr_correct` — most complex (recursive over BoolExpr
   AST), exercises layer-2 helpers. Validates Phase A signatures.
2. `fp_exec_and_store` — composite, variable-length sub-chunk composition.
3. `loadFloatExpr_exec` — match-based length claim on expression form.
4. `loadImm64_fregs_preserved` — 4-chunk composition via `optional_movk_step'`.
5. Remaining helpers in any order (simpler).

**Phase B fill order**:
1. `.binop` normal case — 4-chunk composition (load lv, load rv, op,
   store). Exercises `vLoadVar_eff_exec` × 2, `vStoreVar_exec`, direct
   ArmStep. Validates the `k = instrs.length` claim over a concatenated
   block.
2. `.ifgoto_true` case — integrates `verifiedGenBoolExpr_correct` +
   conditional branch. Validates bool-expr integration with the length
   claim.
3. `.floatUnary` case — exercises `fp_exec_and_store` composition.
4. `.arrLoad` normal + `.arrStore` normal — bounds-check integration.
5. `.goto` normal, `.goto` self-loop, `.halt`, `.const`, `.copy` (self-
   and non-self) — simple cases, pure mechanical.
6. typeError and dead injectivity cases — vacuous discharge via
   `cfg' ≠ .run` implication, ~5 min each.

**Phase C–H fill order**: one-pass, no per-case sorry required. Complete
each phase in a single sitting. Phase H (`source_diverges_gives_
ArmDiverges_init`) is the final target — its proof sketch is in § Phase H
below and should be ~40 LOC once A–G are done.

### Build discipline

- `lake build` after each signature change (confirm cascade is complete).
- `lake build` after each sorry fill (confirm no regression).
- `grep -c "sorry" CredibleCompilation/*.lean` to track progress per
  sub-step.
- Commit per case or per logical group. Never commit with broken build.
- If a hard case fails to close: FIX THE SIGNATURE first (may require
  re-doing other sorrys). Do not paper over with weaker claims.

### Entry point for every session

1. Read this doc end-to-end first.
2. `git log --oneline -5` to see current state.
3. `lake build 2>&1 | grep "declaration uses \`sorry\`"` to see current
   sorry list.
4. Compare to expected sorry count for current phase (in Checkpoints
   table below). Resume from the next unchecked item.
5. Follow Rule 1 + Rule 2 above for whatever phase is active.

## Phase A — Helpers in ArmCorrectness.lean lines 81–1000

15 theorems. For each, the return type picks up `∃ ... k, ArmStepsN ... k ∧ k = <list>.length ∧ ...`.

### A.1 `optional_movk_step` (line 29, already updated session 5)

```lean
private theorem optional_movk_step (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      <other conjuncts unchanged>
```

### A.2 `loadImm64_correct` (line 81, already updated session 5)

```lean
theorem loadImm64_correct (prog : ArmProg) (rd : ArmReg) (n : BitVec 64) ... :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (formalLoadImm64 rd n).length ∧
      <other conjuncts unchanged>
```

### A.3 `optional_movk_step'` (line 250) — fregs-preserving variant

Mirror A.1 plus the fregs conjunct. Length identical to A.1.

### A.4 `loadImm64_fregs_preserved` (line 272)

Mirror A.2 plus fregs conjunct. Length identical to A.2.

### A.5 `vStoreVar_x0_correct` (line 488)

Current length = 1 (single `.str .x0 off`). Add:
```lean
∃ s' k, ArmStepsN ... k ∧ k = 1 ∧ <other conjuncts>
```

### A.6 `vStoreVar_x0_ireg_correct` (line 508)

Current length = 1 (single `.movR r .x0`). Same form as A.5.

### A.7 `vLoadVar_exec` (line 527)

Length = `(vLoadVar layout v tmp).length`. Case analysis on layout:
- stack: length 1 (`.ldr tmp off`).
- ireg same as tmp: length 0 (empty list, `.refl`).
- ireg diff from tmp: length 1 (`.movR tmp r`).
- freg: ruled out by `hNotFreg`.
- none: ruled out by `hMapped`.

Add `k = (vLoadVar layout v tmp).length` to return.

### A.8 `vLoadVar_eff_exec` (line 590)

Same form as A.7 with `eff` instead of `tmp`.

### A.9 `vStoreVar_exec` (line 618)

Length = `(vStoreVar layout v .x0).length`. Has a length-0 case when
`layout v = none` (silent-drop). Add `k = (vStoreVar layout v .x0).length`.

### A.10 `vStoreVarFP_exec` (line 659)

Length = `(vStoreVarFP layout v .d0).length`. Has length-0 cases
(silent-drop when layout v = none or freg matches .d0). Add the equality.

### A.11 `fp_exec_and_store` (line 701)

Composite helper: executes one FP op (1 step) then `vStoreVarFP` (0 or 1
step). Length = `1 + (vStoreVarFP layout x dst_reg).length`.

Return:
```lean
∃ s' k, ArmStepsN ... k ∧ k = 1 + (vStoreVarFP layout x dst_reg).length ∧
    ExtSimRel layout pcMap divS boundsS (.run (pc + 1) (σ[x ↦ resultVal]) am) s'
```

### A.12 `vLoadVarFP_exec` (line 762)

Mirror A.7 for float side. Length = `(vLoadVarFP layout v tmp).length`.

### A.13 `vLoadVarFP_eff_exec` (line 824)

Mirror A.8 for float side.

### A.14 `loadFloatExpr_exec` (line 859)

Length depends on `e`:
- `.var v`: `(vLoadVarFP layout v dst).length`.
- `.flit n`: `(formalLoadImm64 .x0 n).length + 1` (for trailing `fmovToFP`).

Add match-based length claim.

### A.15 `verifiedGenBoolExpr_correct` (line 925)

Composite: boolean expression evaluation. Length = `(verifiedGenBoolExpr
layout be).length` on the `.run` case. Note that `verifiedGenBoolExpr`
output has fixed length given `be.hasSimpleOps = true` — track via
structural induction on `be`.

Return includes:
```lean
∃ s' k, ArmStepsN ... k ∧ k = (verifiedGenBoolExpr layout be).length ∧
    <existing conjuncts for x0 = be.eval encoded, ExtStateRel, etc.>
```

### Phase A caller-update burden

When a helper's signature gains `k` + `k = ...` fields, every `obtain
⟨..., hSteps, ...⟩ := helper ...` callsite gains two slots:

```lean
-- Before:
obtain ⟨s1, hSteps1, <rest>⟩ := helper ...
-- After:
obtain ⟨s1, k1, hStepsN1, hk1, <rest>⟩ := helper ...
```

Downstream `.trans` compositions become `ArmStepsN_trans`. Downstream
`.single` constructions become `ArmStepsN.single`.

Caller-update counts (mechanical):
- `loadImm64_fregs_preserved` (line 272): ~15 callsites in verifiedGenBoolExpr_correct + verifiedGenInstr_correct.
- `optional_movk_step'` (line 250): 3 callsites in loadImm64_fregs_preserved.
- `vLoadVar_exec` (line 527): ~20+ callsites in verifiedGenInstr_correct.
- `vStoreVar_exec` (line 618): ~15+ callsites.
- Other helpers: ~5–15 callsites each.

Total Phase A caller updates: ~150–200 destructure patterns, all mechanical.

## Phase B — `verifiedGenInstr_correct` (ArmCorrectness.lean:1748)

New return type:
```lean
theorem verifiedGenInstr_correct ... :
    ∃ s' k, ArmStepsN prog s s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
      ExtSimRel layout pcMap divLabel boundsLabel cfg' s'
```

Rationale: the `.run` case is the only one we need for divergence; other
cases (halt/errorDiv/errorBounds/typeError) don't need length constraints.
For `.run` cases, the full block is traversed so `k = instrs.length`.

### Per-case proof pattern

For `.run` target cases (~15 cases: goto non-self, goto self, ifgoto_true,
ifgoto_false, const, copy, binop normal, boolop, arrLoad normal, arrStore
normal, fbinop normal, intToFloat, floatToInt, floatUnary, fternop,
printInt/B/F/S):

```lean
-- Internal chain via ArmStepsN.single and ArmStepsN_trans, matching the
-- helper outputs. Each k tracks the sub-chunk length; total k matches
-- instrs.length.
refine ⟨s_final, k_total, hArmN_total, ?_, hExtSimRel⟩
· intro pc' σ' am' hCfg
  -- Sub-in the concrete block structure, use helper k-equalities + list.length algebra.
  unfold <relevant block>
  omega  -- or simp + omega depending on structure
```

For terminal cases (halt, errorDiv, errorBounds): block is partially
fired (k < instrs.length). The implication `cfg' = .run ... → k = ...`
is vacuous.

For typeError cases (lines 1881–1895): `refine ⟨s, 0, rfl, ?_, trivial⟩`
plus vacuous `cfg' = .run → k = instrs.length` (typeError ≠ .run, so
implication vacuous).

For dead injectivity branches (lines 2438, 2462): `refine ⟨s, 0, rfl, ?_,
⟨...⟩⟩` with the `cfg' = .run` implication discharged by `instrs.length = 0`
(from `hCode = []` in these branches).

### Length-claim proofs per case

Mechanical: given helper-level `k_i = <helper_list>.length` and the
concrete `instrs = <helper lists concatenated>`, compute via:
```lean
rw [hk1, hk2, ..., hkN]
simp [List.length_append, List.length_cons, List.length_nil]
omega
```

Most proofs are 2–5 LOC of linear arithmetic.

### Scope for Phase B

~60 cases × 5–15 LOC per case = ~300–900 LOC of destructure + length
arithmetic. Keep build green by completing all cases before commit —
do not commit partial Phase B.

### Session 6 technique patterns that transfer to Phase B

From the A.15 `verifiedGenBoolExpr_correct` fill (~500 LOC, 11 sub-cases,
chains of length 1–6), the following patterns proved robust and should
be reused in Phase B:

1. **Intermediate state lets** — `let s3 := { s2 with flags := ..., pc := ... }`.
   Include `s3` in simp sets (e.g. `simp [s3, ArmState.setReg, ...]`)
   to unfold when goals need the field-update form expanded.

2. **Explicit ArmStepsN chain construction** — bind each step's
   `hStepN : ArmStepsN prog sPrev sNext 1` separately, then chain
   via `ArmStepsN_trans` with visible arithmetic:
   ```lean
   have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
   have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
   have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
   have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
   have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
     ArmStepsN_trans h23 hStepCsetN
   ```
   Avoid "`.step h1 (.step h2 (.single h3))`" chains written inline —
   they work for ArmSteps but require type annotations in ArmStepsN that
   quickly get messy. Explicit `ArmStepsN_trans` chains are clearer.

3. **k-equality proof pattern** — after the main refine:
   ```lean
   · rw [hk1, hk2]; simp [verifiedGenInstr, List.length_append]; omega
   ```

4. **Surgical `simp only` for flag-handling cases** — when a chain
   ends with `Flags.condHolds_correct` / `_float_correct`, over-
   unfolding with plain `simp` breaks the expected normal form
   `{ lhs := a, rhs := b }.condHolds`. Workaround:
   ```lean
   simp only [sN, ArmState.setReg, ArmState.nextPC, hD1_s4, hD2_s4]
   simp [BoolExpr.eval, Expr.eval, Value.toFloat]
   exact congrArg ... (Flags.condHolds_float_correct ...)
   ```
   First `simp only` stages the form; second `simp` simplifies remaining
   non-flag bits; `exact` closes.

5. **Python cascade script for mechanical destructure migration** —
   session 6's script (`grep` + regex-based transform) handled 102 of
   106 cascade sites correctly. Edge cases that tripped the regex:
   - apostrophe-named variables (`s'`, `hSteps'`) — regex used `\w+`
     which doesn't match apostrophe; fix: use `[\w']+`.
   - same-line obtains (`obtain ⟨...⟩ := helper ...` on one line) —
     regex required `:= ...\n$`; fix: allow optional same-line content.
   - complex destructure patterns with multiple `_` wildcards — in
     one site (`CodeGen.lean:5540`), Lean misinterpreted the field
     positions when `_` was used; fix: name the wildcards (`k1_U`,
     `hFregsD0_U`, etc.) to disambiguate.

   Phase B has its own cascade (verifiedGenInstr_correct's callers:
   `ext_backward_simulation`, `step_simulation`, `tacToArm_*`,
   `while_to_arm_*`). Reuse the script with these fixes.

## Phase C — `ext_backward_simulation` (ArmCorrectness.lean:5433)

Trivial re-export. New signature mirrors verifiedGenInstr_correct:

```lean
theorem ext_backward_simulation (p : Prog) (armProg : ArmProg) ... :
    ∃ s' k, ArmStepsN armProg s s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
      ExtSimRel layout pcMap divLabel boundsLabel cfg' s' :=
  verifiedGenInstr_correct ... -- same args
```

~10 LOC.

## Phase D — `step_simulation` (CodeGen.lean:4182)

step_simulation wraps ext_backward_simulation and adds save/restore logic
for lib-call and print cases. Three internal cases:

1. **Lib-call**: block = `caller_saves ++ body ++ caller_restores`.
   Total k = `save_count + k_body + restore_count`. For `.run` target,
   k = `instrs.length` where `instrs` is the full save/body/restore list.

2. **Print**: block = `caller_saves ++ [.printCall label] ++ caller_restores`.
   Similar to lib-call with fixed body length = 1.

3. **Normal**: block = verifiedGenInstr output directly. Delegate to ext_backward_simulation.

New signature:
```lean
private theorem step_simulation {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r) ...
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg') ... :
    ∃ s' k, ArmStepsN r.bodyFlat s s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → 1 ≤ k) ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)
```

Note: we weaken to `1 ≤ k` (rather than equality with a specific length)
because the lib-call/print cases have variable save/restore counts
dependent on `spec`. `1 ≤ k` is all the divergence proof needs, and is
derivable from `bodyPerPC_length_pos` + full block traversal on `.run`.

~80–120 LOC depending on how smoothly the internal composition threads.

## Phase E — `tacToArm_refinement` (CodeGen.lean:6044)

Current signature accepts `Steps`, returns `ArmSteps`. Switch to accept
`StepsN ... n` and return `ArmStepsN ... k` with `n ≤ k`.

New signature:
```lean
theorem tacToArm_refinement {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm tyCtx p = .ok r)
    {pc : Nat} {σ : Store} {am : ArrayMem}
    (s : ArmState)
    (hRel : ExtSimRel r.layout r.pcMap r.divS r.boundsS (.run pc σ am) s)
    (hTS : TypedStore tyCtx σ)
    (hInv : buildVerifiedInvMap p pc σ am)
    {n : Nat} (cfg' : Cfg) (hStepsN : StepsN p (.run pc σ am) cfg' n) :
    ∃ s' k, ArmStepsN r.bodyFlat s s' k ∧
      (∀ pc' σ' am', cfg' = .run pc' σ' am' → n ≤ k) ∧
      ExtSimRel r.layout r.pcMap r.divS r.boundsS cfg' s' ∧
      (∀ σ' am', cfg' = .halt σ' am' → s'.pc = r.haltFinal)
```

Proof: induction on `hStepsN`.
- `zero` case: `n = 0`, `cfg' = .run pc σ am`. Return `⟨s, 0, rfl, by
  intros; omega, hRel, ...⟩`.
- `succ n` case: one TAC step plus StepsN of length `n`. Apply
  `step_simulation` for the first step (gives `k_1 ≥ 1`), IH for the
  remaining `n` steps (gives `n ≤ k_rest`). Total `k = k_1 + k_rest ≥ 1 + n > n`.

~40–60 LOC.

## Phase F — `tacToArm_correctness` (CodeGen.lean:6135)

Mirror Phase E. Takes `Steps` from initial config; converts to `StepsN`
via `Steps_to_StepsN` and delegates to `tacToArm_refinement`.

Alternatively, accept `StepsN` directly at this level.

~20 LOC.

## Phase G — `while_to_arm_*` callers (PipelineCorrectness.lean)

Three callers of `tacToArm_correctness`:
- `while_to_arm_correctness` (around line 349)
- `while_to_arm_div_preservation` (around line 443)
- `while_to_arm_bounds_preservation` (around line 470)

Each destructures: `obtain ⟨s', hArm, hRel, hPC⟩ := tacToArm_correctness ...`.
Update to: `obtain ⟨s', k, hArmN, _, hRel, hPC⟩ := tacToArm_correctness ...`
then `have hArm : ArmSteps ... := ArmStepsN_to_ArmSteps hArmN` to preserve
downstream proof unchanged.

~15 LOC total.

## Phase H — `source_diverges_gives_ArmDiverges_init` (PipelineCorrectness.lean:1324)

```lean
private theorem source_diverges_gives_ArmDiverges_init
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok r)
    {f : Nat → Cfg}
    (hinf : IsInfiniteExec (applyPassesPure prog.tyCtx passes prog.compileToTAC) f)
    (hf0 : f 0 = Cfg.run 0 prog.initStore ArrayMem.init) :
    ArmDiverges r.bodyFlat (Phase6.initArmState r) := by
  intro N
  -- All `f i` are .run configs (else trace can't continue)
  have hAllRun : ∀ i, ∃ pc_i σ_i am_i, f i = .run pc_i σ_i am_i := ...
  -- Extract StepsN of length N+1 from IsInfiniteExec
  have hStepsN : StepsN _ (f 0) (f (N+1)) (N+1) := ...
  -- Rewrite f 0
  rw [hf0] at hStepsN
  obtain ⟨pc_end, σ_end, am_end, hfend⟩ := hAllRun (N+1)
  rw [hfend] at hStepsN
  -- Apply enhanced tacToArm_correctness (Phase F output):
  obtain ⟨s_fwd, k, hArmN, hk_bound, _⟩ :=
    tacToArm_correctness hGen _ _ hStepsN
  -- k ≥ N+1 by hk_bound applied to .run ending config
  have hN1_le_k : N+1 ≤ k := hk_bound _ _ _ rfl
  have hN_le_k : N ≤ k := by omega
  -- Truncate via ArmStepsN_prefix
  obtain ⟨d, hd⟩ : ∃ d, k = N + d := ⟨k - N, by omega⟩
  rw [hd] at hArmN
  obtain ⟨s_prefix, hPrefix⟩ := ArmStepsN_prefix hArmN
  exact ⟨s_prefix, hPrefix⟩
```

~40 LOC.

## Checkpoints

With the sorry-ratchet procedure (Rule 1), sorry count temporarily
balloons during X.0 sub-steps and monotonically decreases during X.1+
fills. Commit frequently.

| Checkpoint | Sorry count (expected) | Actual | Green build |
|---|---|---|---|
| start of session 6 | 4 | 4 | yes |
| A.0 complete (helper sigs + cascade + sorried bodies) | ~19 (4 + 15 helper sorries) | 17 (4 + 13 new sorries; A.1/A.2 were already filled session 5) | yes |
| A.1+ fills through `verifiedGenBoolExpr_correct` | ~18 | tracked descent to 4 | yes |
| **A complete (all helper sorries filled)** | 4 | **4 ✅ session 6** | yes |
| B.0 complete (verifiedGenInstr_correct sig + per-case sorries) | ~64 (4 + 60) | — session 7 target | — |
| B.1 fill `.binop` normal | ~63 | | |
| B.2 fill `.ifgoto_true` | ~62 | | |
| B complete | 4 | | |
| C complete (ext_backward_simulation) | 4 | | |
| D complete (step_simulation) | 4 | | |
| E complete (tacToArm_refinement) | 4 | | |
| F complete (tacToArm_correctness) | 4 | | |
| G complete (while_to_arm_*) | 4 | | |
| **H complete (source_diverges closed)** | **3** | | |

**Sorry count regression check**: after each sub-step, the running total
of sorrys should be monotone non-increasing (or the expected bump from a
fresh X.0 sub-step). Any unexpected new sorry = investigate immediately.

### Session 6 actuals vs estimate

| Metric | Spec estimate | Session 6 actual |
|---|---|---|
| Phase A total LOC | ~150 | ~850 (includes full 500-LOC A.15 fill + 102-site cascade) |
| Phase A caller updates | ~150–200 destructure patterns | 102 automated + 4 hand-fixed (3 apostrophe-var sites + 1 named-wildcard site) |
| Phase A sessions | 1 day / across 2-3 sessions | 1 session |
| Remaining session 6 budget allocated to Phase B | optional | 0 (scope consumed by A) |

Phase A took ~5× the LOC estimate. Main driver: A.15 verifiedGenBoolExpr_
correct had 11 sub-cases (bexpr/lit/bvar/not + cmp×4 + fcmp×4), each
requiring 4–6 step ArmStepsN chains with explicit k arithmetic.
Takeaway for Phase B: the ~60-case `verifiedGenInstr_correct` cascade
likely runs 500–1500 LOC, probably 2 sessions not 1.

## Risks and mitigations

1. **Helper length equality proofs trip on non-trivial list algebra.**
   ~~Mitigation: each helper's length is `concrete_list.length`, omega
   handles linear combinations.~~ **Resolved session 6**: all 13 helper
   length proofs closed cleanly with `rw [hk_i]; simp [..., List.length_append]; omega`.

2. **Phase B destructure cascades touch more callers than enumerated.**
   Mitigation: build after each ~10 case updates to catch drift.
   Session 6 note: the Python cascade script is the fastest route;
   see § "Session 6 technique patterns" above for edge cases.

3. **Some callsite uses the old `hArm : ArmSteps` by composition
   (`hArm1.trans hArm2`).** ~~Mitigation: `ArmStepsN_trans` is a drop-in
   replacement.~~ **Session 6 preferred alternative**: keep the old
   `hArm : ArmSteps` name via `have hArm := ArmStepsN_to_ArmSteps hArmN`
   bridge, leaving downstream `.trans` / `.single` usages intact.
   Phase B case rewrites can remove bridges per-case as they adopt
   length-tracked chains. Session 6 applied this at 102+ sites.

4. **Phase D step_simulation's lib-call save/restore math.**
   Mitigation: `1 ≤ k` is the minimal claim; don't pursue tighter
   equalities here.

5. **Phase G while_to_arm_* might need deeper updates if internal
   reasoning relied on specific ArmSteps structure.** Mitigation: the
   bridging lemma preserves ArmSteps view; internal reasoning unchanged.

6. **NEW: Phase B complex cases may have 4-6-step chains like A.15's
   flit+flit fcmp case.** Mitigation: use the surgical `simp only`
   pattern (see § Session 6 technique patterns #4). For cases with
   mixed FP/integer ops (e.g., `.floatUnary` → `fp_exec_and_store`),
   lean on the helper's k-equality rather than inlining.

7. **NEW: Phase B `verifiedGenInstr_correct` has ~60 cases but only
   ~15 are `.run` targets requiring the length claim.** The terminal
   cases (halt, errorDiv, errorBounds, typeError, dead injectivity)
   discharge `(cfg' = .run → k = instrs.length)` vacuously. Mitigation:
   group cases by target kind for efficiency — tackle all `.run` cases
   first, then batch the vacuous-discharge cases.

## What to do if Phase B stalls mid-session

Phases B and D are atomic — mixed signatures within these functions don't
compose. If blocked past a reasonable threshold (e.g., 4 hours on Phase B),
revert to last green commit rather than commit partial.

## Success criteria (unchanged from plan doc)

- `lake build` green.
- Sorry count: 4 → 3. Remaining sorrys at PipelineCorrectness.lean:770,
  :1022, :2115 (Phase 6 out-of-scope).
- `grep -rE "axiom\s" CredibleCompilation/` shows only the two pre-existing
  float-op axioms (`Flags.condHolds_float_correct`, `FloatBinOp.fadd_comm`).
