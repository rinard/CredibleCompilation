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

Per-phase commits recommended:

| Commit | Sorry count | Green build |
|---|---|---|
| A complete | 4 | yes |
| B complete | 4 | yes |
| C complete | 4 | yes |
| D complete | 4 | yes |
| E complete | 4 | yes |
| F complete | 4 | yes |
| G complete | 4 | yes |
| H complete | **3** | yes |

## Risks and mitigations

1. **Helper length equality proofs trip on non-trivial list algebra.**
   Mitigation: each helper's length is `concrete_list.length`, omega
   handles linear combinations. If a case resists, relax equality to
   inequality (`k ≤ list.length`) — this works as long as Phase F can
   still derive `n ≤ k` from cumulative bounds.

2. **Phase B destructure cascades touch more callers than enumerated.**
   Mitigation: build after each ~10 case updates to catch drift.

3. **Some callsite uses the old `hArm : ArmSteps` by composition
   (`hArm1.trans hArm2`).** Mitigation: `ArmStepsN_trans` is a drop-in
   replacement. If the caller also consumes it as plain ArmSteps
   elsewhere, use `ArmStepsN_to_ArmSteps` to bridge.

4. **Phase D step_simulation's lib-call save/restore math.**
   Mitigation: `1 ≤ k` is the minimal claim; don't pursue tighter
   equalities here.

5. **Phase G while_to_arm_* might need deeper updates if internal
   reasoning relied on specific ArmSteps structure.** Mitigation: the
   bridging lemma preserves ArmSteps view; internal reasoning unchanged.

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
