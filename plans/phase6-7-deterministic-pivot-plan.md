# Phase 6/7 Deterministic Havoc Pivot — Implementation Plan

Concrete next-session plan for pivoting the ARM semantics to
deterministic havoc and closing Phase 7 theorems.  Budget ~1–2 focused
sessions depending on how clean the refactor goes.  Companion to
`plans/phase6-7-session-report-2026-04-22.md`.

## Entry state

- Branch: `phase6-prep`, head `eb899b9` (session report) preceded by
  `63e88d3` (Path B infrastructure).
- 9 sorrys, full build green.
- Landed: `sentinel_stuck`, feeder lemmas, `pipelined_has_behavior`,
  `pipelined_no_typeError`, sentinel distinctness, P2 probe
  (`arm_step_pc_det` via `armNextPC` projection), reusable no-branch
  helpers.
- Phase 5a's `bodyPerPC_length_pos` already landed (commit `124d582`).
  Used by the 7a/b/c diverges case.

## Critical-path ordering

```
Step 1 (ArmStep refactor)
    ↓
Step 2 (call-site updates) — high LOC, mechanical
    ↓
Step 3 (arm_step_det)
    ↓
Step 4 (step_count_state_uniqueness)
    ↓
Step 5 (Phase 7d) — simplest, doesn't need forward-sim extension
    ↓
Step 6 (forward-sim PC-in-bodyFlat helper) — needed by 7a/b/c
    ↓
Step 7 (Phase 7b + 7c) — symmetric
    ↓
Step 8 (Phase 7a) — observable matching via state determinism
    ↓
Step 9 (commit + CHANGELOG + plan update)
```

Each step's output is the next step's precondition.  **Checkpoint after
Steps 1–4**: full build green, `arm_step_det` and
`step_count_state_uniqueness` landed.  If stalled, stop and reassess —
everything after depends on these.

## Step 1: refactor `ArmStep` (~30 LOC)

**Files**: [`CredibleCompilation/ArmDefs.lean`](../CredibleCompilation/ArmDefs.lean),
[`CredibleCompilation/ArmSemantics.lean`](../CredibleCompilation/ArmSemantics.lean).

**Add to `ArmDefs.lean`** (near the bottom of the ArmState section,
before `ArmStep` is introduced):

```lean
/-- Opaque havoc functions for library calls.  Models "the callee
    returns some specific (but unknown) value for each caller-saved
    register, deterministic in the caller's state."  This makes
    `ArmStep` a function of the starting state — two `ArmStep`s from
    the same state produce the same successor.

    Soundness: the opaque function is a universally-quantified
    witness; any concrete havoc behavior of real libcalls is
    accommodated by an appropriate choice.  For our libcalls
    (print*, sin, cos, exp, pow) the return-value garbage is
    deterministic given state; stdout side effects are modeled
    as observable output, not ArmState. -/
opaque havocRegsFn : ArmState → ArmReg → BitVec 64
opaque havocFRegsFn : ArmState → ArmFReg → BitVec 64
```

**Modify `ArmStep` in `ArmSemantics.lean`** for the 5 libcall
constructors — remove the `newRegs`, `newFregs` arguments, replace
with `havocRegsFn s`, `havocFRegsFn s`:

```lean
| printCall (lines : List String) :
    prog[s.pc]? = some (.printCall lines) →
    ArmStep prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC)
| callPrintI :
    prog[s.pc]? = some .callPrintI →
    ArmStep prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC)
| callPrintB : ...  -- similar
| callPrintF : ...
| callPrintS (lit : String) : ...
| callBinF (fop : FloatBinOp) (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.callBinF fop fd fn fm) →
    ArmStep prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
      |>.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC)
| floatUnaryLibCall (op : FloatUnaryOp) (fd fn : ArmFReg) :
    prog[s.pc]? = some (.floatUnaryInstr op fd fn) →
    op.isNative = false →
    ArmStep prog s (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
      |>.setFReg fd (op.eval (s.fregs fn)) |>.nextPC)
```

Note: `callBinF` and `floatUnaryLibCall` still compute their result
deterministically from input fregs (via `FloatBinOp.eval` or
`op.eval`); the havoc only affects caller-saved regs *other than* the
result register, which `havocCallerSaved` then overwrites before
`setFReg fd` writes the result on top.  The existing semantics are
preserved; only the havoc parameter is reified.

**Checkpoint after Step 1**: file might not build until Step 2 updates
all call sites.  That's expected.

## Step 2: update call sites (~100–150 LOC)

**Files affected** (greppable via `ArmStep.printCall`,
`ArmStep.callPrintI`, etc., and via `ArmStep_total_of_codeAt` /
`ArmStep_stuck_of_none`):

### [`ArmSemantics.lean`](../CredibleCompilation/ArmSemantics.lean)

- `ArmStep_total_of_codeAt` — currently has lines like:
  ```lean
  | printCall lines => exact ⟨_, .printCall lines (fun _ => 0) (fun _ => 0) h⟩
  ```
  Change to:
  ```lean
  | printCall lines => exact ⟨_, .printCall lines h⟩
  ```
  Same pattern for `callPrintI`, `callPrintB`, `callPrintF`,
  `callPrintS`, `callBinF`, `floatUnaryInstr` (the libcall case).
  ~10 lines touched.

### [`ArmCorrectness.lean`](../CredibleCompilation/ArmCorrectness.lean)

The forward-sim proofs for TAC print/libcall instructions construct
specific ArmSteps.  Grep for the six constructor names.  Expected:
~10–30 sites.  Each site currently picks specific havoc values (often
`fun _ => 0` or the current-state regs); with the refactor, those
picks disappear — the constructor no longer accepts them.

Watch for:
- `exact ArmStep.callBinF fop fd fn fm _ _ h`  →  `exact ArmStep.callBinF fop fd fn fm h`
- Any explicit destructuring that binds `newRegs`, `newFregs` —
  remove the bindings.
- Goal-state equalities that reference `havocCallerSaved newRegs
  newFregs` — these now reference `havocCallerSaved (havocRegsFn s)
  (havocFRegsFn s)`, which is a specific (opaque) term.  `rfl` should
  still close most of them because the change is definitional.

Where proofs previously "picked witnesses" (e.g., `exact ⟨fun _ => 0,
fun _ => 0, h_further_goals⟩`), the witnesses are gone — the proof
becomes more direct.

Budget ~50–100 LOC of mechanical edits here.

### [`PipelineCorrectness.lean`](../CredibleCompilation/PipelineCorrectness.lean)

- `ArmStep.pc_eq_armNextPC` in § 10b (P2 probe) — the match cases for
  `printCall`, `callPrintI`, etc. need updating to the new constructor
  arity.  ~10 lines.

### Any file using `havocCallerSaved` directly

Shouldn't need changes — the function signature is unchanged.

## Step 3: prove `arm_step_det` (~100 LOC)

**File**: `PipelineCorrectness.lean` (in § 10b Phase6Probes2 alongside
`arm_step_pc_det`), or a new section.

**Strategy**: use the projection trick that worked for P2 — define a
pure function `armStepResult : ArmState → ArmInstr → ArmState` that
computes the deterministic successor, prove every `ArmStep` reduces to
it, pair via `Option.some.inj` to conclude determinism.

```lean
private def armStepResult (s : ArmState) (i : ArmInstr) : ArmState :=
  match i with
  | .mov rd imm => s.setReg rd imm |>.nextPC
  | .movR rd rn => s.setReg rd (s.regs rn) |>.nextPC
  -- ... all ~50 instruction constructors
  | .cbz rn lbl => if s.regs rn = (0 : BitVec 64) then { s with pc := lbl } else s.nextPC
  | .cbnz rn lbl => if s.regs rn = (0 : BitVec 64) then s.nextPC else { s with pc := lbl }
  | .bCond c lbl => if s.flags.condHolds c = true then { s with pc := lbl } else s.nextPC
  | .printCall _ => s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s) |>.nextPC
  | .callBinF fop fd fn fm =>
      s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
        |>.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC
  | .floatUnaryInstr op fd fn =>
      if op.isNative
      then s.setFReg fd (op.eval (s.fregs fn)) |>.nextPC
      else s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)
             |>.setFReg fd (op.eval (s.fregs fn)) |>.nextPC
  -- ...

private theorem ArmStep.eq_armStepResult (h : ArmStep prog s s') :
    ∃ i, prog[s.pc]? = some i ∧ s' = armStepResult s i := by
  cases h with
  | mov rd imm hi => exact ⟨_, hi, rfl⟩
  | cbz_taken rn lbl hi hz =>
      exact ⟨_, hi, by simp only [armStepResult, if_pos hz]⟩
  | cbz_fall rn lbl hi hnz =>
      exact ⟨_, hi, by simp only [armStepResult, if_neg hnz]⟩
  -- ... analogous to pc_eq_armNextPC, ~50 rules
  | printCall lines hi => exact ⟨_, hi, rfl⟩
  -- ...

theorem arm_step_det {prog s s₁ s₂}
    (h1 : ArmStep prog s s₁) (h2 : ArmStep prog s s₂) : s₁ = s₂ := by
  obtain ⟨i1, hi1, he1⟩ := ArmStep.eq_armStepResult h1
  obtain ⟨i2, hi2, he2⟩ := ArmStep.eq_armStepResult h2
  have : i1 = i2 := Option.some.inj (hi1 ▸ hi2)
  rw [he1, he2, this]
```

**Tricky cases**: `.floatUnaryInstr` has two ArmStep rules
(`floatUnaryNative` and `floatUnaryLibCall`) split on `op.isNative`.
`armStepResult`'s definition uses `if op.isNative`, matching the rule
dispatch.  The two rules' premises (`op.isNative = true` vs `= false`)
are syntactically inverses, so `simp` closes via `if_pos`/`if_neg`.

**Tempting shortcut**: `cases h1 <;> cases h2 <;> simp_all`.  This
will timeout (same reason as P2 failed).  Use the projection approach.

## Step 4: prove `step_count_state_uniqueness` (~15 LOC)

**File**: `PipelineCorrectness.lean`.

Direct induction using `arm_step_det`:

```lean
theorem step_count_state_uniqueness {prog : ArmProg} {s₀ : ArmState} :
    ∀ n (s₁ s₂ : ArmState),
      ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n → s₁ = s₂ := by
  intro n
  induction n generalizing s₀ with
  | zero =>
      intro s₁ s₂ h1 h2
      change s₀ = s₁ at h1; change s₀ = s₂ at h2
      subst h1; subst h2; rfl
  | succ n ih =>
      intro s₁ s₂ h1 h2
      obtain ⟨m₁, hs₁, hr₁⟩ := h1
      obtain ⟨m₂, hs₂, hr₂⟩ := h2
      have hmid : m₁ = m₂ := arm_step_det hs₁ hs₂
      subst hmid
      exact ih _ _ hr₁ hr₂
```

Then fill in the skeleton's `step_count_pc_uniqueness` as a corollary:

```lean
theorem step_count_pc_uniqueness {prog : ArmProg} {s₀ : ArmState} :
    ∀ n (s₁ s₂ : ArmState),
      ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n → s₁.pc = s₂.pc := by
  intros n s₁ s₂ h1 h2
  rw [step_count_state_uniqueness n s₁ s₂ h1 h2]
```

**Checkpoint after Step 4**: 9 → 8 sorrys (`step_count_pc_uniqueness`
closed).  Full build green.  If stalled on Step 3, stop and re-plan.

## Step 5: Phase 7d (~30 LOC)

**File**: `PipelineCorrectness.lean`, § 9 Phase7Skeleton.

Case analysis on source behavior via `pipelined_has_behavior`:

```lean
theorem arm_diverges_implies_while_diverges
    (prog : Program) (htcs : prog.typeCheckStrict = true)
    (passes : List (String × (Prog → ECertificate)))
    {r : VerifiedAsmResult}
    (hGen : verifiedGenerateAsm prog.tyCtx
      (applyPassesPure prog.tyCtx passes prog.compileToTAC) = .ok r)
    (hDiv : ArmDiverges r.bodyFlat (Phase6.initArmState r)) :
    ∀ fuel, prog.interp fuel = none := by
  intro fuel
  -- Get source behavior
  obtain ⟨b, hbeh⟩ := pipelined_has_behavior prog htcs passes
    (Store.typedInit prog.tyCtx)
  have spec := verifiedGenerateAsm_spec hGen
  cases b with
  | halts σ' =>
      -- forward sim to haltFinal; ArmDiverges implies stepping past it; contradict via sentinel_stuck
      obtain ⟨am₀, am', hhalt⟩ := hbeh
      -- This case requires am₀ = ArrayMem.init to apply the existing forward theorem.
      -- See "sub-issue: program_behavior vs program_behavior_init" below.
      sorry
  | errors σ' =>
      -- similar for divS or boundsS
      sorry
  | typeErrors σ' =>
      obtain ⟨am₀, am', hte⟩ := hbeh
      exact absurd hte (pipelined_no_typeError prog htcs passes σ' am')
      -- NOTE: pipelined_no_typeError currently assumes am₀ = ArrayMem.init;
      -- check if generalizing it for any am₀ is needed.
  | diverges =>
      obtain ⟨f, hinf, hf0⟩ := hbeh
      have htc := prog.typeCheckStrict_typeCheck htcs
      have hInitEq := prog.typedInit_eq_initStore htc
      exact while_to_arm_divergence_preservation prog htcs passes hinf
        (by rw [hInitEq] at hf0; exact hf0) fuel
```

**Sub-issue**: `program_behavior` has `∃ am am'` for each non-diverges
bin, making the initial `am` existential.  The forward theorems
(`while_to_arm_correctness` etc.) require `am₀ = ArrayMem.init`.
Resolution options:

1. **Strengthen `pipelined_has_behavior` to `program_behavior_init`**:
   add a wrapper theorem `has_behavior_init` in PropChecker that gives
   `program_behavior_init` (witnesses all have `am₀ = ArrayMem.init`).
   `has_behavior`'s proof internally builds exactly this, so the
   wrapper is ~10 LOC.
2. **Generalize the forward theorems** to accept arbitrary `am₀`.
   More invasive.

Go with (1).  Add `has_behavior_init` in PropChecker.lean, update
`pipelined_has_behavior` to return `program_behavior_init`.

### For the halts case specifically

```lean
| halts σ' =>
    obtain ⟨am', hhalt⟩ := hbeh  -- with _init form, am₀ is fixed
    obtain ⟨s_fwd, hArm, hSimRel, hHaltPC⟩ := tacToArm_correctness hGen
      -- need hHalt in shape haltsWithResult applyPassesPure 0 (typedInit) σ' ArrayMem.init am'
      (by ...)
    have hHPC : s_fwd.pc = r.haltFinal := hHaltPC _ _ rfl
    obtain ⟨k, hStepsN⟩ := ArmSteps_to_ArmStepsN hArm
    obtain ⟨s_extra, hExtra⟩ := hDiv (k + 1)
    obtain ⟨s_mid, hMid, hStep⟩ := ArmStepsN_split_last hExtra
    have hEq : s_mid = s_fwd :=
      step_count_state_uniqueness k s_mid s_fwd hMid hStepsN
    rw [hEq] at hStep
    exact absurd ⟨s_extra, hStep⟩
      (sentinel_stuck spec (Or.inl hHPC))
```

Similar for errors case (use `while_to_arm_div_preservation` or
`_bounds_preservation` to get forward-sim ARM state at divS/boundsS,
then contradict via step_count_state_uniqueness + sentinel_stuck).

**Estimate**: 7d fills in at ~30 LOC once the `has_behavior_init`
wrapper lands (+ ~10 LOC for the wrapper).

**Checkpoint after Step 5**: 7d closed, 8 → 7 sorrys.

## Step 6: forward-sim PC-in-bodyFlat helper (~80 LOC)

**Needed for**: Phase 7a/b/c's "source diverges" case.

Under the deterministic model, forward sim of a divergent source
produces ArmStepsN traces of unbounded length that never reach
sentinels.  Specifically:

```lean
/-- Under source divergence, every ArmStepsN witness reaches a state
    whose PC is inside `bodyFlat`, never at a sentinel.  Used by
    7a/b/c to contradict "ARM trace ends at sentinel" vs "source
    diverges". -/
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

**Proof sketch**:

1. Run forward sim over the first `n` TAC steps of `f` to produce
   `ArmStepsN init s_fwd K(n)` where `K(n) = Σᵢ₌₀ⁿ⁻¹ |bodyPerPC[pcᵢ]|`.
   Since each `|bodyPerPC[pcᵢ]| ≥ 1` (from `bodyPerPC_length_pos`),
   `K(n) ≥ n`.
2. Pick `n` such that `K(n) ≥ k`.  Since `K` is unbounded as `n → ∞`,
   such `n` exists.
3. Extract `ArmStepsN init s_prefix k` from `ArmStepsN init s_fwd K(n)`
   via `ArmStepsN_prefix`.
4. Apply `step_count_state_uniqueness` to conclude `s = s_prefix`.
5. Show `s_prefix.pc < r.haltFinal`: the state at any intermediate ARM
   step within the forward-sim chain has PC `pcMap pcᵢ + j` for some
   `pcᵢ < p.size` and `j ≤ |bodyPerPC[pcᵢ]|`.  This is bounded above
   by `pcMap p.size = haltS < haltFinal`.

**Auxiliary lemma needed**: "forward sim of n TAC steps gives ArmStepsN
of length ≥ n, and at any intermediate step, the state's PC is < haltS."

This is essentially Phase 5b's forward divergence theorem, specialized
to "PC stays in bodyFlat" rather than constructing the full
`ArmDiverges`.  Less work than Phase 5b because we don't need the
`ArmDiverges` reachability form.

**Proof infrastructure to lean on**:

- `tacToArm_refinement` or `tacToArm_correctness` (forward sim over
  halting prefixes).  For infinite traces, iterate over halting
  prefixes.
- `step_simulation` (single-TAC-step ARM correspondence).
- `bodyPerPC_length_pos` (each TAC step ≥ 1 ARM step).
- `spec.pcMapLengths` (`pcMap pc + |bodyPerPC[pc]| ≤ haltS` for
  `pc < p.size`).

**Budget**: ~80 LOC.  Risk medium — this is partial Phase 5b, so it
inherits some of Phase 5b's complexity.  If it exceeds ~150 LOC,
consider dropping to 7d-only delivery and revisiting 7a/b/c in a later
session.

**Checkpoint after Step 6**: helper closed, ready for 7a/b/c.

## Step 7: Phase 7b + 7c (~60 LOC each = 120 LOC)

**File**: `PipelineCorrectness.lean`.

7b and 7c are symmetric (div vs bounds sentinel).  Shared schema:

```lean
theorem arm_div_implies_while_unsafe_div
    ... (hArm : ArmSteps r.bodyFlat init s) (hPC : s.pc = r.divS) :
    ∃ fuel, unsafeDiv fuel ∨ unsafeBounds fuel := by
  obtain ⟨b, hbeh⟩ := pipelined_has_behavior_init prog htcs passes
    (Store.typedInit prog.tyCtx)
  have spec := verifiedGenerateAsm_spec hGen
  obtain ⟨k, hStepsN⟩ := ArmSteps_to_ArmStepsN hArm
  cases b with
  | halts σ' =>
      -- forward gives ArmSteps to haltFinal, step_count_state_uniqueness
      -- pins s_halt.pc = s.pc = divS, but haltFinal ≠ divS.
      obtain ⟨am', hhalt⟩ := hbeh
      obtain ⟨s_fwd, hArmF, _, hHaltPC⟩ := tacToArm_correctness hGen hhalt
      obtain ⟨k', hStepsN_fwd⟩ := ArmSteps_to_ArmStepsN hArmF
      -- Match lengths: if k = k', direct conflict.  Else, use prefix.
      -- Easiest: use max(k, k') via ArmStepsN_prefix on the longer.
      sorry  -- ~15 LOC of PC arithmetic
  | errors σ' =>
      obtain ⟨am', herr⟩ := hbeh
      -- Source reached errorDiv OR errorBounds.
      rcases herr with hed | heb
      · -- errorDiv → while_to_arm_div_preservation gives s.pc = divS (matches!)
        have ⟨hUnsafe, _⟩ := while_to_arm_div_preservation prog htcs passes hGen hed
        exact hUnsafe
      · -- errorBounds → while_to_arm_bounds_preservation gives s.pc = boundsS (contradicts divS)
        have ⟨hUnsafe, ⟨s_b, hArmB, hBPC⟩⟩ :=
          while_to_arm_bounds_preservation prog htcs passes hGen heb
        -- Contradict divS = boundsS
        obtain ⟨kb, hStepsN_b⟩ := ArmSteps_to_ArmStepsN hArmB
        -- step_count_state_uniqueness at min k, kb
        sorry  -- ~20 LOC
  | typeErrors σ' =>
      obtain ⟨am', hte⟩ := hbeh
      exact absurd hte (pipelined_no_typeError prog htcs passes σ' am')
  | diverges =>
      obtain ⟨f, hinf, hf0⟩ := hbeh
      have := source_diverges_arm_pc_in_bodyFlat prog htcs passes hGen hinf hf0 k hStepsN
      -- this : s.pc < r.haltFinal.  But hPC : s.pc = r.divS = haltFinal + 1.
      rw [hPC, spec.divS_eq] at this
      omega
```

For the "forward gives different sentinel than our hypothesis"
sub-cases (halts case in 7b, bounds case in 7b, div case in 7c), the
pattern is:

1. Get ArmStepsN of lengths k (our trace) and k' (forward trace).
2. If k = k': direct `step_count_state_uniqueness` contradicts
   different PCs.
3. If k < k': our trace is a prefix of forward.  Forward's state at k
   has PC < haltFinal (if intermediate) or haltFinal/divS/boundsS (if
   endpoint).  Match via state uniqueness, contradict.
4. If k > k': symmetric.

This merge-by-length pattern can factor into a helper lemma:

```lean
/-- If two traces both reach sentinels, they reach the same sentinel. -/
theorem unique_sentinel_reach
    {s₁ s₂ : ArmState} (hP₁ : s₁.pc ∈ sentinels) (hP₂ : s₂.pc ∈ sentinels)
    (h1 : ArmSteps init s₁) (h2 : ArmSteps init s₂) :
    s₁.pc = s₂.pc
```

~30 LOC via length comparison + state uniqueness.

**Budget**: ~60 LOC each for 7b and 7c, shared ~30 LOC helper.  Total
~150 LOC.  Assumes Step 6 is stable.

**Checkpoint after Step 7**: 7b, 7c closed, 7 → 5 sorrys.

## Step 8: Phase 7a (~80 LOC)

**File**: `PipelineCorrectness.lean`.

Observable matching: given ArmSteps init s with s.pc = haltFinal, show
source halts with σ_src, and `ArmMatchesWhile r.layout
compileToTAC.observable σ_src s.arrayMem s`.

Under deterministic model, `s` is fully determined by init state and
step count.  Forward sim's s_fwd for source halt is the same state s.
So observable matching follows from forward sim's `ExtSimRel` without
a separate `halt_state_observables_deterministic` helper.

Schema:

```lean
theorem arm_halts_implies_while_halts
    ... (hArm : ArmSteps r.bodyFlat init s) (hPC : s.pc = r.haltFinal) :
    ∃ fuel σ_src am_src, prog.interp fuel = some (σ_src, am_src) ∧
      ArmMatchesWhile r.layout prog.compileToTAC.observable σ_src am_src s := by
  obtain ⟨b, hbeh⟩ := pipelined_has_behavior_init prog htcs passes
    (Store.typedInit prog.tyCtx)
  cases b with
  | halts σ' =>
      -- This matches the hypothesis; apply while_to_arm_correctness
      obtain ⟨am', hhalt⟩ := hbeh
      obtain ⟨fuel, σ_src, am_src, s_fwd, hinterp, hArmF, hMatch, hHaltPC⟩ :=
        while_to_arm_correctness prog htcs passes hGen hhalt
      obtain ⟨k, hStepsN⟩ := ArmSteps_to_ArmStepsN hArm
      obtain ⟨k', hStepsN_fwd⟩ := ArmSteps_to_ArmStepsN hArmF
      -- hPC and hHaltPC both give pc = haltFinal, so by unique_sentinel_reach-style
      -- reasoning, k = k' and s = s_fwd.  Then ArmMatchesWhile transfers.
      sorry  -- ~30 LOC
  | errors σ' =>
      -- forward gives divS or boundsS, contradicts haltFinal via spec distinctness
      sorry  -- ~15 LOC
  | typeErrors σ' =>
      obtain ⟨am', hte⟩ := hbeh
      exact absurd hte (pipelined_no_typeError prog htcs passes σ' am')
  | diverges =>
      obtain ⟨f, hinf, hf0⟩ := hbeh
      have := source_diverges_arm_pc_in_bodyFlat prog htcs passes hGen hinf hf0 k hStepsN
      rw [hPC] at this; spec.haltFinal_eq at this; omega
```

The halts-sub-case needs matching forward trace length with our trace
length.  Both end at `haltFinal`, both are deterministic (state
uniqueness), so the final states are equal.  `ArmMatchesWhile`
transfers.

**Budget**: ~80 LOC.  Moderate risk — the length-matching argument is
the new wrinkle.

**Checkpoint after Step 8**: 7a closed, 5 → 4 sorrys (remaining: Phase
6 pieces — `bodyFlat_branch_target_bounded`, P1, `arm_behavior_exhaustive`,
`halt_state_observables_deterministic`).

## Step 9: commit + docs (~0 LOC)

- Commit `eb899bN` "Phase 7a/b/c/d closure via deterministic havoc".
- Update CHANGELOG.md with session summary.
- Update `plans/backward-jumping-octopus.md`: mark 7a-d complete.
- If Phase 6 is still open, note next step (the 14-case sweep +
  `arm_behavior_exhaustive` König).

## Remaining after this plan

After Phase 7 closes, still open for full 0-sorry:

- `bodyFlat_branch_target_bounded` (the 14-case sweep + lift).
- `arm_behavior_exhaustive` — depends on
  `bodyFlat_branch_target_bounded`.
- P1 probe (the `.ifgoto` case) — subsumed by the 14-case sweep.
- `halt_state_observables_deterministic` — may not be needed if 7a
  closes via state determinism (likely unused).

These are the Phase 6 exhaustion work.  Separate ~600 LOC session.

## LOC budget summary

| Step | LOC | Confidence | Cumulative sorrys |
|---|---|---|---|
| 1. ArmStep refactor | 30 | 95% | (not counted — mid-refactor) |
| 2. Call-site updates | 150 | 85% | 9 (re-green) |
| 3. `arm_step_det` | 100 | 85% | 9 |
| 4. `step_count_state_uniqueness` + use | 20 | 95% | 8 |
| 5. Phase 7d + `has_behavior_init` | 50 | 85% | 7 |
| 6. `source_diverges_arm_pc_in_bodyFlat` | 80 | 65% | 7 |
| 7. Phase 7b, 7c + helper | 180 | 75% | 5 |
| 8. Phase 7a | 80 | 70% | 4 |
| **Total** | **~690** | | **9 → 4** |

Compared to original design estimate for Phase 7 (~240 LOC from the
design doc's pre-pivot accounting): ~3× larger, but buys full state
determinism rather than just PC determinism, and closes 5 sorrys
instead of partial progress.

## Risks

1. **Step 2 call-site update ripples farther than expected.**  If
   ArmCorrectness.lean has ~100 constructor call sites instead of
   ~30, budget doubles.  Mitigation: grep exhaustively before
   starting, list every site in advance.

2. **Step 3 `ArmStep.eq_armStepResult` explodes.**  ~50 constructors
   × ~5 LOC each = ~250 LOC, not 100.  Mitigation: the existing
   `ArmStep.pc_eq_armNextPC` is the blueprint — clone its structure.

3. **Step 6 is partial Phase 5b.**  Forward sim over n TAC steps +
   PC-in-bounds invariant could balloon to 200 LOC if the
   tacToArm-refinement composition isn't as clean as expected.
   Mitigation: if Step 6 exceeds 150 LOC, stop; land 7d and defer
   7a/b/c to a follow-up session.

4. **Step 7/8 length-matching argument.**  The "if k = k' / k < k' /
   k > k'" case split repeats across 7a/b/c.  Mitigation: factor
   `unique_sentinel_reach` helper early, use it uniformly.

5. **Semantic change breaks unrelated downstream proofs.**  Refactoring
   `ArmStep` could expose latent assumptions in proofs that use its
   nondeterminism implicitly.  Mitigation: after Step 2, run full
   `lake build`.  Every new failure signals a proof that relied on
   picking specific havoc witnesses; update in place.

## Fallback: partial delivery

If we stall at Step 6, the useful partial result is Steps 1–5 +
Phase 7d.  That's:

- Full deterministic ARM semantics.
- `arm_step_det` and `step_count_state_uniqueness` proven.
- `step_count_pc_uniqueness` closed (was sorry).
- Phase 7d closed.
- 9 → 7 sorrys (net reduction of 2 + model change).

This is a meaningful milestone even without 7a/b/c.  Worth committing
as a checkpoint before continuing.

## Escape hatches

If the pivot turns out to have hidden complications:

- **Opaque vs parameterized**: if opaque havoc functions cause
  unexpected issues (e.g., `simp`/`decide` refusing to unfold them
  under some simp sets), switch to parameterized: pass
  `havocRegsFn`, `havocFRegsFn` as implicit parameters to `ArmStep`,
  quantify universally in theorems.  More ceremony, same effect.

- **Deterministic via Classical.choice**: if `opaque` misbehaves, use
  `noncomputable def havocRegsFn := Classical.choice _`.  Equivalent
  to opaque for proof purposes; may interact better with existing
  tactics.

- **Revert if truly broken**: the refactor is self-contained to ArmStep
  and call sites.  If Step 3 is blocked after thorough investigation,
  `git reset --hard 63e88d3` returns to the pre-pivot state and we
  pursue the uninit-reads analysis (Option 3) instead.

## Session prep checklist

Before starting:

- [ ] Read `plans/phase6-7-session-report-2026-04-22.md` (process
      context).
- [ ] Read this plan end to end.
- [ ] Confirm `lake build` on `eb899b9` is green (sanity check state).
- [ ] Decide: opaque vs parameterized havoc (default: opaque).
- [ ] Run `grep -n "ArmStep.printCall\|ArmStep.callPrint\|ArmStep.callBinF\|ArmStep.floatUnaryLibCall"`
      across the repo to enumerate Step 2 call sites.
