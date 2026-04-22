# Phase 6/7 Design Note — Backward Theorems Over Verified ARM

Context for a focused 1–2 day session landing the literal Phase 6 / Phase 7 theorems from `plans/backward-jumping-octopus.md` at 0 sorrys. Written 2026-04-22 after the foundational session that shipped commit `94f4fe6` (sdivR precondition removal + `ArmStep_total_of_codeAt` + `ArmStep_stuck_of_none`).

## Goal (literal, not weakened)

Land in `CredibleCompilation/PipelineCorrectness.lean`:

```lean
theorem arm_behavior_exhaustive (prog …) (hGen : verifiedGenerateAsm … = .ok r) :
    let init := { regs := fun _ => 0, fregs := fun _ => 0, stack := fun _ => 0,
                  pc := r.pcMap 0, flags := ⟨0, 0⟩ }
    (∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.haltFinal) ∨
    (∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.divS) ∨
    (∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.boundsS) ∨
    ArmDiverges r.bodyFlat init
```

Plus the four backward theorems `arm_halts_implies_while_halts`, `arm_div_implies_while_unsafe_div`, `arm_bounds_implies_while_unsafe_bounds`, `arm_diverges_implies_while_diverges`.

The 4th bin must be literal `ArmDiverges`, not a weaker surrogate like `∀ fuel, prog.interp fuel = none`.

## State of the foundation (commit `94f4fe6`, already on `main`)

- **sdivR rule**: `ArmStep.sdivR` no longer requires `s.regs rm ≠ 0`. `BitVec.sdiv` is total; the verified trace still goes through `cbz rm, divS` so `rm ≠ 0` holds whenever `sdivR` runs, but the rule itself is unconstrained. Matches `plans/backward-jumping-octopus.md` line 27.
- **`ArmStep_total_of_codeAt`**: `prog[s.pc]? = some i → ∃ s', ArmStep prog s s'`. Case analysis on `ArmInstr`. After the sdivR change every rule's only precondition is `prog[s.pc]? = some _`; two-branch rules (`cbz`/`cbnz`/`bCond`) exhaust via `by_cases`, `floatUnaryInstr` exhausts via `by_cases op.isNative`.
- **`ArmStep_stuck_of_none`**: `prog[s.pc]? = none → ¬ ∃ s', ArmStep prog s s'`.
- **`bodyPerPC_length_pos`** (commit `124d582`, older): every live TAC PC's ARM block is ≥ 1 instruction.
- **`ArmStepsN.single` / `ArmStepsN.refl_zero`** (commit `2930ef8`, older): step-count helpers.

Missing for Phase 6/7.

## The single load-bearing missing lemma: `branchTargetsBounded`

**Claim**: for any successful `verifiedGenerateAsm` output `r`, every branch instruction in `r.bodyFlat` targets a PC ≤ `r.boundsS`.

```lean
theorem bodyFlat_branch_target_bounded
    {tyCtx p r} (spec : GenAsmSpec tyCtx p r) :
    ∀ pc lbl,
      (r.bodyFlat[pc]? = some (.b lbl) ∨
       (∃ rn, r.bodyFlat[pc]? = some (.cbz rn lbl)) ∨
       (∃ rn, r.bodyFlat[pc]? = some (.cbnz rn lbl)) ∨
       (∃ c,  r.bodyFlat[pc]? = some (.bCond c lbl))) →
      lbl ≤ r.boundsS
```

### Why this is the only missing piece

The König step for `ArmDiverges` at the no-sentinel-reached contrapositive: given `ArmStepsN init s n` with `s.pc ≤ r.boundsS ∧ s.pc ∉ {haltFinal, divS, boundsS}`, we want `ArmStepsN init s' (n+1)` with the same invariant on `s'`. Step:
1. `s.pc ≤ r.boundsS` and `s.pc` non-sentinel ⇒ `s.pc < r.haltFinal` (the three sentinels occupy exactly `[haltFinal, haltFinal+2]`).
2. `s.pc < r.haltFinal = r.bodyFlat.size` ⇒ `r.bodyFlat[s.pc]? = some _`.
3. `ArmStep_total_of_codeAt` gives `s'`.
4. Show `s'.pc ≤ r.boundsS`: sequential rules advance `pc → pc+1`, so `s'.pc ≤ r.bodyFlat.size = r.haltFinal ≤ r.boundsS` (with `boundsS_eq : r.boundsS = r.haltFinal + 2`). Branch rules set `s'.pc := lbl`; **`branchTargetsBounded` gives `lbl ≤ r.boundsS`**.
5. Show `s'.pc ∉ {haltFinal, divS, boundsS}`: ruled out by the no-sentinel-reached contrapositive hypothesis (if `s'.pc` were a sentinel, `ArmStepsN init s' (n+1)` would witness `ArmSteps init s'` with `s'.pc = sentinel`).

Without `branchTargetsBounded`, step 4 leaks: a branch could land outside `[0, boundsS]`, no instruction there, stuck, König fails at that `n`.

### Formulation choices

**Option A — new `GenAsmSpec` clause.** Add a field to `GenAsmSpec` and discharge in `verifiedGenerateAsm_spec`. Clean consumer side; invasive producer side (touches the big `verifiedGenerateAsm_spec` proof).

**Option B — standalone theorem taking `GenAsmSpec` as input.** The field-free version above. Self-contained. Default recommendation unless something makes Option A naturally simpler.

### Discharge strategy (Option B)

Two sub-claims:

**(B.1) Per-instruction claim on `verifiedGenInstr` output.**

```lean
theorem verifiedGenInstr_branch_target_bounded
    (layout : VarLayout) (pcMap : Nat → Nat) (instr : TAC)
    (haltS divS boundsS : Nat) (arrayDecls : _) (safe : Bool)
    (instrs : List ArmInstr)
    (hGen : verifiedGenInstr layout pcMap instr haltS divS boundsS arrayDecls safe = some instrs)
    (hPc : ∀ l, instr = .goto l ∨ instr = .ifgoto _ l → l < p.size)  -- from checkBranchTargets
    (hMono : ∀ l, l < p.size → pcMap l ≤ haltS)                      -- from spec.pcMapLengths
    (hHaltLe : haltS ≤ boundsS)                                      -- from haltS_eq/boundsS_eq
    (hDivLe : divS ≤ boundsS)
    (hBoundsLe : boundsS ≤ boundsS := le_refl _) :
    ∀ instr' ∈ instrs, ∀ lbl,
      (instr' = .b lbl ∨ (∃ rn, instr' = .cbz rn lbl) ∨
       (∃ rn, instr' = .cbnz rn lbl) ∨ (∃ c, instr' = .bCond c lbl)) →
      lbl ≤ boundsS
```

Proven by case analysis on `instr`. Per-case breakdown:

| TAC constructor | Branches emitted? | Target |
|---|---|---|
| `.const _ _` | no (`formalLoadImm64` has no branches) | — |
| `.copy _ _` | no (only `mov`/`ldr`/`str`/`fmov`) | — |
| `.binop _ op _ _` with `op ∈ {.div, .mod}` | `.cbz rv_reg divLabel` | `divLabel = divS ≤ boundsS` |
| `.binop _ _ _ _` (other ops) | no | — |
| `.boolop _ be` | depends on `verifiedGenBoolExpr be` | **none** (inner generator has no branches — verify) |
| `.goto l` | `.b (pcMap l)` | `pcMap l ≤ haltS ≤ boundsS` |
| `.ifgoto be l` | depends on `be` shape: `.bCond cond.negate (pcMap l)` (one of three arms) or `.cbnz .x0 (pcMap l)` (fallback) | `pcMap l ≤ haltS ≤ boundsS` |
| `.halt` | `.b haltLabel` | `haltLabel = haltS ≤ boundsS` |
| `.arrLoad _ _ _ _` | `.bCond .hs boundsLabel` (unless `boundsSafe`) | `boundsLabel = boundsS ≤ boundsS` |
| `.arrStore _ _ _ _` | same as `.arrLoad` | `boundsLabel = boundsS` |
| `.fbinop _ _ _ _` | no | — |
| `.intToFloat _ _` | no | — |
| `.floatToInt _ _` | no | — |
| `.floatUnary _ _ _` | no | — |
| `.fternop _ _ _ _ _` | no | — |
| `.print _ _` | vacuous (`verifiedGenInstr` returns `none`) | — |
| `.printInt _` / `.printBool _` / `.printFloat _` | no (call-prints are not control-flow branches, PC advances by 1) | — |
| `.printString _` | no | — |

**Verify before starting**: `verifiedGenBoolExpr` output contains no branch instructions. Grep for `ArmInstr.b`, `.cbz`, `.cbnz`, `.bCond` inside the function body — expected result: none. If it does, `.boolop` and the `.ifgoto` arms need additional inner analysis.

14 non-vacuous cases. Probable LOC breakdown:
- No-branch cases (const, copy, fbinop, intToFloat, floatToInt, floatUnary, fternop, printInt/B/F/S, boolop if no inner branches): ~5 LOC each × 10 = 50 LOC. For each, unfold `verifiedGenInstr`, case-split on layout, show the output `instrs` is a concatenation of `vLoadVar`/`vStoreVar`/`formalLoadImm64`/fixed instruction lists that contain no `.b`/`.cbz`/`.cbnz`/`.bCond`.
- `.goto` / `.halt`: ~10 LOC each = 20 LOC.
- `.binop`: ~40 LOC (handles the `op ∈ {.div, .mod}` split).
- `.ifgoto`: ~80 LOC (3-arm `match be` + fallback, each arm emits a branch).
- `.arrLoad` / `.arrStore`: ~30 LOC each = 60 LOC (type case + `boundsSafe` branch).
- Helper about `verifiedGenBoolExpr` emitting no branches: ~15 LOC.

Subtotal (B.1): ~265 LOC.

**(B.2) Lift to `bodyFlat`.**

```lean
theorem bodyFlat_branch_target_bounded (spec : GenAsmSpec …) …
```

`r.bodyFlat = bodyPerPC.toList.flatMap id ++ haltSaveBlock.toList` (from `VerifiedAsmResult.bodyFlat`). Case split on whether `pc` falls in the `bodyPerPC` prefix or the `haltSaveBlock` suffix:

- `pc` in `haltSaveBlock`: `haltSaveBlock` is `genHaltSave ...`, a flat sequence of `str`/`fstr` (no branches — confirmed in Phase 2a design). So the branch-ness hypothesis is vacuous. ~15 LOC.
- `pc` in `bodyPerPC[k]` for some `k < p.size`: the block at index `k` is either (i) from `verifiedGenInstr` directly (via `spec.instrGen`), (ii) wrapped via `spec.callSiteSaveRestore` (saves ++ `verifiedGenInstr` output ++ restores — saves/restores are `str`/`ldr` only, no branches), or (iii) the print-wrapper from `spec.printSaveRestore` (saves ++ `[.printCall _]` ++ restores — `printCall` is not in our branch set). In cases (i) and (ii) the interesting instructions come from `verifiedGenInstr` output; apply (B.1). ~40 LOC.

Subtotal (B.2): ~55 LOC.

**Required existing facts** (to feed into B.1):
- `∀ l, l < p.size → pcMap l ≤ haltS`. From `spec.pcMapLengths` + `spec.haltS_eq` + monotonicity of `buildPcMap`. Maybe 20 LOC of helper.
- `spec.haltS_eq`, `spec.haltFinal_eq`, `spec.divS_eq`, `spec.boundsS_eq` — all in spec, all `rfl` or close.
- `spec.wellTypedProg p` → `checkBranchTargets p.code = none` → `∀ pc l, p[pc] = .goto l ∨ p[pc] = .ifgoto _ l → l < p.size`. Bridge lemma ~20 LOC.

Subtotal (B): ~360 LOC total.

## Phase 6 main theorem on top of branchTargetsBounded

Two routes.

### Route 1 — classical em + König (the task's intended structure)

```lean
theorem arm_behavior_exhaustive (prog …) (hGen …) : … := by
  classical
  by_cases h1 : ∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.haltFinal
  · left; exact h1
  by_cases h2 : ∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.divS
  · right; left; exact h2
  by_cases h3 : ∃ s', ArmSteps r.bodyFlat init s' ∧ s'.pc = r.boundsS
  · right; right; left; exact h3
  right; right; right
  -- Build ArmDiverges: ∀ n, ∃ s, ArmStepsN init s n.
  -- Inductive invariant: s.pc ≤ boundsS ∧ s.pc ∉ {haltFinal, divS, boundsS}.
  -- Base: init.pc = pcMap 0 ≤ haltS < haltFinal ≤ boundsS; not a sentinel since pcMap 0 ≤ haltS < haltFinal.
  -- Step: stuck-free (via ArmStep_total_of_codeAt since s.pc < haltFinal) gives s'.
  --       s'.pc ≤ boundsS via sequential-or-branch case split + branchTargetsBounded.
  --       s'.pc ∉ sentinels via h1/h2/h3 applied to ArmStepsN init s' (n+1).
  …
```

~100 LOC for this proof given the helpers.

### Route 2 — source totality

Apply `has_behavior` (extended to the pipelined TAC via `applyPassesPure_preserves_stepClosed` — a new ~30 LOC helper). Cases:
- TAC halts → forward sim → bin 1.
- TAC errorDiv → forward sim → bin 2.
- TAC errorBounds → forward sim → bin 3.
- TAC typeErrors → excluded via `checkWellTypedProg` preservation + `typeError_excluded_of_wellTyped`.
- TAC diverges → build `ArmDiverges` via König using the same infrastructure as Route 1.

Route 2 doesn't avoid the König step in bin 4; it just sharpens the proof obligation ("no sentinel reached" → "source diverges" → König). Pure König with the em contrapositive (Route 1) is cleaner.

**Recommendation**: Route 1.

## Phase 7 theorems on top of Phase 6

Given `arm_behavior_exhaustive` plus **sentinel exclusivity** (`haltFinal`, `divS`, `boundsS` are pairwise distinct — all three `rfl`/`omega` from the spec equations), the four theorems fall into a near-mechanical schema.

### Sentinel exclusivity lemmas

```lean
theorem haltFinal_ne_divS (spec : GenAsmSpec …) : r.haltFinal ≠ r.divS := by
  rw [spec.divS_eq]; omega

theorem haltFinal_ne_boundsS (spec : GenAsmSpec …) : r.haltFinal ≠ r.boundsS := by
  rw [spec.boundsS_eq]; omega

theorem divS_ne_boundsS (spec : GenAsmSpec …) : r.divS ≠ r.boundsS := by
  rw [spec.divS_eq, spec.boundsS_eq]; omega
```

Trivially ~3 LOC each.

### Bin-exclusivity via forward sim

If `arm_behavior_exhaustive` returns bin 1 (halt reached) and simultaneously the source is `unsafeDiv`, then `while_to_arm_div_preservation` (existing) gives another `ArmSteps init s''` with `s''.pc = r.divS`. Key question: does this contradict bin 1?

**Not directly** — ARM is nondeterministic at havoc sites, so two `ArmSteps` traces from `init` reaching different final states is consistent. Exclusivity needs PC determinism (which the design doc asserts holds modulo havoc — havoc doesn't affect PC sequence for verified code).

Two paths to handle exclusivity:

**Path X — ARM PC determinism**. New lemma: `ArmSteps init s₁ ∧ ArmSteps init s₂ ∧ s₁.pc = p₁ ∧ s₂.pc = p₂ ∧ p₁ ∉ {haltFinal, divS, boundsS} ∧ p₂ ∈ {haltFinal, divS, boundsS} → p₁ can't be reached after p₂ is reached`. Essentially: sentinels are stuck (from `ArmStep_stuck_of_none`), so once the trace reaches one, it's over.

Formally easiest: `ArmSteps init s ∧ s.pc ∈ sentinels → ¬ ∃ s', ArmSteps s s' ∧ s' ≠ s`. Since sentinel PCs are stuck, `ArmSteps s s'` must be `refl`, so `s' = s`.

Then: if source is `unsafeDiv`, forward → `ArmSteps init s_div`, `s_div.pc = divS`. Our hypothesis: `ArmSteps init s_halt`, `s_halt.pc = haltFinal`. Both traces start from `init`. The question: can both exist?

This is where ARM PC determinism bites. Without it, yes both could exist (hypothetically). **With** it: the unique PC trajectory from init hits a sentinel at some step `m`; after step `m` the trace is stuck. So either both traces agree on PC (same sentinel reached) or one is an initial segment of the other. Two traces to two different sentinels ⇒ contradiction.

PC determinism is a separate ~200 LOC lemma. Substantial.

**Path Y — avoid exclusivity via uniqueness of source behavior**. Source has a unique behavior (TAC is deterministic, Prog is deterministic, pipeline is deterministic). So source is in exactly one of {halts, unsafeDiv, unsafeBounds, diverges} (typeErrors excluded). Forward sim from the actual source behavior places ARM in exactly one specific bin. Thus the backward theorem is: "given ARM is in bin X, source must be in the bin that forward-sims to X".

Implementation:
```lean
theorem arm_halts_implies_while_halts (hArm : ArmSteps init s) (hPC : s.pc = haltFinal) :
    source halts with match := by
  obtain ⟨b, hbeh⟩ := pipelined_has_behavior prog htcs passes  -- source totality
  cases b with
  | halts σ =>
    -- Source halts. Apply forward halt theorem to get matching σ_src + am_src.
    -- Match s to the forward-derived s_fwd on observables. REQUIRES matching observables between s and s_fwd.
    -- s is our hypothesis. s_fwd is what forward sim produces.
    …
  | errors _ => …
  | typeErrors _ => absurd (typeErrors_excluded …) hbeh
  | diverges => …
```

The tricky part: for the `halts σ` case, we need to show `s` (our hypothesized ARM halt state) has observables matching `σ`. Forward sim gives `s_fwd` with `s_fwd.pc = haltFinal ∧ ExtStateRel σ s_fwd ∧ s_fwd.arrayMem = am_src`. We need `ExtStateRel σ s ∧ s.arrayMem = am_src`.

This requires determinism of observable contents of the final ARM state. The halt-save block at the end of `bodyFlat` spills observable variables to deterministic stack slots (independent of havoc — havoc preceded by save/restore). So **observable content of the state at haltFinal is determined by source semantics** — not by the ARM trace taken.

Formalizing this: ~100 LOC. Path Y avoids full PC determinism but still needs observable determinism at haltFinal. Similar shape to PC determinism proof, smaller scope.

**Recommendation**: Path Y for `arm_halts_implies_while_halts`. For the error/bounds theorems, the `observables` requirement is weaker (just `∃ fuel, unsafeDiv/unsafeBounds`, no observable content match) — Path Y requires only excluding the other three source bins via forward-sim-places-ARM-in-a-different-sentinel + PC-based uniqueness-of-sentinel-reach (weaker than full PC determinism: just "can reach at most one sentinel from init").

### Four theorem outlines

**7a — `arm_halts_implies_while_halts`** (hardest — observable content match): Path Y. ~80 LOC given Phase 6 + observable-determinism helper (~100 LOC).

**7b — `arm_div_implies_while_unsafe_div`**: Path Y lite. Given `s.pc = divS`, source totality + "ARM reaches at most one sentinel from init" excludes halts/unsafeBounds. typeErrors excluded via well-typedness. Remaining: unsafeDiv or diverges. Diverges excluded via forward divergence theorem's contrapositive (TAC diverges → source diverges; but we want to argue ARM can reach `divS` ⇒ source doesn't diverge — needs a small additional argument). ~60 LOC.

**7c — `arm_bounds_implies_while_unsafe_bounds`**: symmetric to 7b. ~60 LOC.

**7d — `arm_diverges_implies_while_diverges`**: `ArmDiverges` taken as hypothesis. Source totality. For each non-`diverges` source bin, forward sim gives `ArmSteps init s_sentinel`. Use `ArmDiverges` at step `(ArmSteps_to_ArmStepsN s_sentinel).length + 1` to get a state at step (m+1); apply `ArmStepsN_split_last` to get an `ArmStep` from a step-m state. **If** that step-m state has PC = sentinel (needs PC determinism OR a uniqueness-of-sentinel-reach argument), `ArmStep_stuck_of_none` contradicts the existence of the outgoing `ArmStep`. So source is `diverges`. ~40 LOC given the helper.

### Shared helper: "ARM reaches at most one sentinel"

```lean
theorem at_most_one_sentinel_reach
    (spec : GenAsmSpec …) (s₁ s₂ : ArmState)
    (h₁ : ArmSteps r.bodyFlat init s₁) (h₂ : ArmSteps r.bodyFlat init s₂)
    (hS₁ : s₁.pc ∈ ({r.haltFinal, r.divS, r.boundsS} : Set Nat))
    (hS₂ : s₂.pc ∈ ({r.haltFinal, r.divS, r.boundsS} : Set Nat)) :
    s₁.pc = s₂.pc
```

Proof idea: WLOG (ArmSteps → ArmStepsN) assume s₁ reached at step m₁, s₂ at step m₂. By PC determinism (along the unique-up-to-havoc PC trajectory, considering havoc doesn't affect PCs that matter for branches in verified code), the sentinel reached is the one hit first. Either m₁ = m₂ (same sentinel) or the later trace is stuck at the earlier sentinel (contradiction with the later reach).

**Substantial** — this is the heart of the exclusivity argument. ~150–200 LOC including havoc-determinism reasoning.

Alternative **weaker** formulation that suffices for 7b/7c/7d:

```lean
theorem sentinel_stuck (spec : GenAsmSpec …) (s : ArmState)
    (hS : s.pc ∈ {r.haltFinal, r.divS, r.boundsS}) :
    ¬ ∃ s', ArmStep r.bodyFlat s s'
```

This is immediate: `r.bodyFlat.size = r.haltFinal`, and the three sentinels are `haltFinal`, `haltFinal+1`, `haltFinal+2`, all ≥ `bodyFlat.size`, so `r.bodyFlat[s.pc]? = none`, invoke `ArmStep_stuck_of_none`. ~10 LOC.

With `sentinel_stuck` alone, 7d goes through cleanly: `ArmDiverges` + source-in-non-diverges-bin + forward sim → `ArmStepsN init s_sent n` for some n and sentinel; `ArmDiverges (n+1)` + `ArmStepsN_split_last` gives outgoing `ArmStep` from a step-n state; by ARM step-count uniqueness-of-PC-at-step-count (weaker than trace PC determinism), the step-n state has `s.pc = sentinel`, which `sentinel_stuck` rules out.

Question for next session: is "step-count uniqueness of PC" (∀ n s₁ s₂, `ArmStepsN init s₁ n → ArmStepsN init s₂ n → s₁.pc = s₂.pc`) provable more cheaply than full trace PC determinism? The answer is probably **yes** — it's a direct induction on `n` using PC-determinism of individual `ArmStep` transitions (which holds for non-havoc sites; at havoc sites, PC advances by 1 regardless of the havoc values, so PC is still deterministic). Havoc affects `regs`/`fregs` not `pc`. ~80 LOC.

## Pipelined `has_behavior` helper

Needed for Route 2 Phase 6 proof AND for Path Y in Phase 7. Missing right now because `applyPassesPure_preserves_invariants` extracts 4 invariants but not `checkStepClosed`.

```lean
theorem applyPassesPure_preserves_stepClosed (tyCtx : TyCtx)
    (passes : List (String × (Prog → ECertificate)))
    (p : Prog) (h : checkStepClosed p = true) :
    checkStepClosed (applyPassesPure tyCtx passes p) = true
```

Follow the same pattern as `applyPassesPure_preserves_invariants`. Each cert check extracts `checkSuccessorsInBounds cert = checkStepClosed cert.trans` (via `invariants_of_checkCertificateExec`); propagate through `applyPass_preserves_stepClosed`. ~30 LOC.

Then:

```lean
theorem pipelined_has_behavior (prog …) (htcs …) (passes …) (σ₀ : Store) :
    ∃ b, program_behavior (applyPassesPure prog.tyCtx passes prog.compileToTAC) σ₀ b := by
  have hsc := applyPassesPure_preserves_stepClosed prog.tyCtx passes prog.compileToTAC
    (checkStepClosed_complete (prog.compileToTAC_stepClosed _))
  exact has_behavior _ σ₀ (checkStepClosed_sound hsc)
```

~5 LOC.

## typeError exclusion

For the Phase 7 theorems' source-totality case split, we need to exclude the `typeErrors` branch. Needed helper:

```lean
theorem typeErrors_excluded
    (prog : Program) (htcs : prog.typeCheckStrict = true) (passes …)
    (σ' : Store) (am' : ArrayMem) :
    ¬ ((applyPassesPure prog.tyCtx passes prog.compileToTAC) ⊩
        Cfg.run 0 (Store.typedInit prog.tyCtx) ArrayMem.init ⟶* Cfg.typeError σ' am')
```

Proof: well-typed programs don't reach typeError (standard type safety). The pipelined program is well-typed by `applyPassesPure_preserves_invariants`. `type_safety` in `CredibleCompilation/TypeSystem.lean` gives the standard no-typeError-at-runtime lemma. ~25 LOC.

## Total LOC and time budget

| Piece | LOC | Confidence |
|---|---|---|
| `verifiedGenInstr_branch_target_bounded` (14 cases, helper for `verifiedGenBoolExpr`) | 265 | 80% |
| `bodyFlat_branch_target_bounded` (lift to bodyFlat) | 55 | 85% |
| Feeder lemmas (`pcMap l ≤ haltS`, `checkBranchTargets` bridge) | 40 | 90% |
| `sentinel_stuck` + sentinel distinctness | 25 | 99% |
| `step_count_pc_uniqueness` | 80 | 70% |
| `applyPassesPure_preserves_stepClosed` + `pipelined_has_behavior` | 35 | 95% |
| `typeErrors_excluded` | 25 | 90% |
| `arm_behavior_exhaustive` main proof (Route 1 König) | 100 | 80% |
| Observable-determinism helper for 7a | 100 | 60% |
| `arm_halts_implies_while_halts` (7a) | 80 | 75% |
| `arm_div_implies_while_unsafe_div` (7b) | 60 | 80% |
| `arm_bounds_implies_while_unsafe_bounds` (7c) | 60 | 80% |
| `arm_diverges_implies_while_diverges` (7d) | 40 | 85% |
| **Total** | **~965 LOC** | **~75% first attempt, ~85% with one iteration** |

**Time estimate**: 1.5–2 focused days. Biggest risks:
1. `verifiedGenInstr_branch_target_bounded.ifgoto` — 3-arm match × branch extraction; mirrors phase5b's `.ifgoto` complexity. Maybe macroable.
2. `step_count_pc_uniqueness` — havoc semantics may surface edge cases.
3. Observable-determinism for 7a — interacts with halt-save block semantics in non-obvious ways.

## Critical path and derisk order

1. **Land probes first** (already ordered for next session in the skeleton branch `phase6-prep`):
   - `.goto` case — simplest, validates the overall pattern.
   - `.binop .div` case — validates the "branch targets `divLabel`" pattern.
2. Once probes compile, fan out to remaining `verifiedGenInstr_branch_target_bounded` cases.
3. Lift to bodyFlat.
4. Feeder lemmas + sentinel_stuck + step_count_pc_uniqueness.
5. `arm_behavior_exhaustive`.
6. Phase 7 theorems in order 7d → 7b → 7c → 7a (easiest → hardest given observable-determinism sits only in 7a).

## Session prep checklist

Before the actual session:

- [x] `94f4fe6` on `main` — sdivR + ArmStep_total_of_codeAt (committed + pushed).
- [x] Design note (this file).
- [ ] Skeleton file with all theorem statements + sorry — on branch `phase6-prep`. **Next step.**
- [ ] `.goto` + `.binop .div` probes — on branch `phase6-prep`. **Next step.**
- [ ] Confirm `verifiedGenBoolExpr` has no branches (one grep).

## Out of scope for this design

- `while_to_arm_divergence_preservation` strengthening to conclude `ArmDiverges` (Phase 5b). Separate effort, ~1500 LOC per the phase-5b design note. Not needed for Phase 6/7 since `ArmDiverges` is constructed in Phase 6 via König (using the material in this note) rather than derived forward.
- PC determinism of full ARM traces. We only need step-count PC uniqueness, which is strictly weaker.
