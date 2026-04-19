# Last Sorry: hBaseExists in step_simulation (CodeGen.lean:1836)

## Goal
Close the last sorry in CodeGen.lean — the only sorry in the entire codebase.

## Completed
- layoutComplete, callSiteSaveRestore, pcMapLengths (GenAsmSpec fields)
- step_simulation: non-lib-call cases, print case, lib-call infrastructure
  (saves/restores stepping, hDstOnly, hEIU, hEFU, hCfgRun)
- verifiedGenInstr_correct: all cases including bool arrLoad

## The Sorry

**Location:** CodeGen.lean:1836, inside `step_simulation`, lib-call branch.

**Goal:** Given `s_saved` (post-caller-save state), prove:
```
∃ s_mid, ArmSteps r.bodyFlat s_saved s_mid ∧
  s_mid.pc = s_saved.pc + baseInstrs.length ∧
  s_mid.arrayMem = am ∧
  (∀ e ∈ entries, s_mid.stack e.off = (applyCallerSaves entries s).stack e.off) ∧
  (∀ v ir, layout v = .ireg ir → (∀ off, .ireg ir off ∉ entries) → s_mid.regs ir = (σ' v).encode) ∧
  (∀ v fr, layout v = .freg fr → (∀ off, .freg fr off ∉ entries) → s_mid.fregs fr = (σ' v).encode) ∧
  (∀ v off, layout v = .stack off → s_mid.stack off = (σ' v).encode)
```

**Context available at sorry site:**
- `hGenInstr`: `verifiedGenInstr ... p[pc] ... = some baseInstrs`
- `hLib`: `isLibCallTAC p[pc] = true`
- `hCodeBase`: `CodeAt r.bodyFlat (pcMap pc + saves.length) baseInstrs`
- `hStateRel`: `ExtStateRel r.layout σ s`
- `hDstOnly`: `∀ v, DAEOpt.instrDef p[pc] ≠ some v → σ' v = σ v`
- `s_saved = {applyCallerSaves entries s with pc := s.pc + entries.length}`
- `hSavedPC`: `s_saved.pc = pcMap pc + (entriesToSaves entries).length`

## Approach

### Step 0: Establish ExtStateRel for s_saved (DONE)
Derive `hEntriesSub'` (entries sublist of genCallerSaveAll) inline — `hSubset`
is not in scope yet (defined at line 1874). Then use
`ExtStateRel.applyCallerSaves_preserved` with freshness from
`callerSaveSpec.1` composed through `hEntriesSub'.subset`.
ExtStateRel ignores PC so this covers s_saved.

Proven pattern:
```lean
have hEntriesSub' : entries.Sublist (genCallerSaveAll r.layout r.varMap) := by
  show (callerSaveEntries r.layout r.varMap (DAEOpt.instrDef p[pc])).Sublist _
  unfold callerSaveEntries
  cases DAEOpt.instrDef p[pc] with
  | none => exact List.Sublist.refl _
  | some _ => exact List.filter_sublist
have hRelSaved : ExtStateRel r.layout σ s_saved := by
  show ExtStateRel r.layout σ {applyCallerSaves entries s with pc := s.pc + entries.length}
  intro v loc hv
  exact ExtStateRel.applyCallerSaves_preserved hStateRel entries
    (fun e he v' => spec.callerSaveSpec.1 e (hEntriesSub'.subset he) v') v loc hv
```

### Step 1: Case-split on p[pc] (DONE)
`cases hInstr : p.code[pc]` + `cases fop` for fbinop.

### Step 2: Unfold verifiedGenInstr (DONE)
In each case, derives: hSS, hII, hScratch, hInjective, hNotIregY/Z/X, hInstrs.

**Lessons learned:**
- hNotIreg proofs: `simp [verifiedGenInstr, hSS, hII, h] at this` works for
  all three (Y, Z, X) in both floatUnary (two-way match) and fbinop (three-way
  match). Simp collapses the nested match when one discriminant is concrete ireg.
- hInstrs for floatUnary (two-way match): `split at hSome` approach from
  ArmCorrectness.lean works (`split` + `simp_all` + `Option.some.inj`).
- hInstrs for fbinop (three-way match): `split` produces too many sub-cases
  with auto-generated names. Use `rcases` on all three layouts instead:
  ```lean
  rcases hly : r.layout y with _ | ⟨ir | fr | off⟩
  all_goals rcases hlz : r.layout z with _ | ⟨ir | fr | off⟩
  all_goals rcases hlx : r.layout x with _ | ⟨ir | fr | off⟩
  all_goals (try { exact absurd hly (hNotIregY _) })
  all_goals (try { exact absurd hlz (hNotIregZ _) })
  all_goals (try { exact absurd hlx (hNotIregX _) })
  all_goals (simp [hly, hlz, hlx, lv_reg, rv_reg, dst_reg] at h ⊢; exact h.symm)
  ```
- **Let binding trap:** `lv_reg`/`rv_reg`/`dst_reg` are let bindings in the
  proof context. `simp at ⊢` doesn't unfold them. Must pass them explicitly
  to simp: `simp [..., lv_reg, rv_reg, dst_reg] at h ⊢`.

### Steps 3-4: Step through instructions + prove 7 properties (DONE for floatUnary)
floatUnary case is fully closed (~250 lines). Pattern established:

**Shared facts (before rcases on layout x):**
- `hPC1'` — normalized alias for hPC1 (avoids let-binding mismatch)
- `hSR1'` — normalized alias for hSR1
- `hAM2, hAMChain` — arrayMem chain from s2 to am
- `hStack2` — `s2.stack = (applyCallerSaves entries s).stack`
- `hNEI_shared` — non-entry ireg (uniform, store doesn't touch iregs)
- `hLibStep` / `hLibStepBin` — TAC result extraction (proved BEFORE subst hCfg
  to avoid am-dependency in `cases hStep`)
- `hArmResult` — `s2.fregs dst_reg = (σ' x).encode` (connecting TAC to ARM)

**Per layout-x sub-case (rcases hlx):**
- `none` / `freg==dst`: s_mid = s2, all 7 properties straightforward
- `stack off`: s_mid = s3 (fstr step), save slots need freshness, stack vars
  need by_cases on v=x (injectivity)
- `freg≠dst`: s_mid = s3 (fmovRR step), non-entry freg needs by_cases fr'=fr

**Key patterns discovered:**
- `VarLoc` constructor order is `stack | ireg | freg` (not ireg|freg|stack)
- `Store.update_self` (not `Store.update`) for `(σ[x ↦ val]) x = val`
- `cases hCfg` needed inside `hLibStep` proof to connect `σ'` to `σ[x ↦ ...]`
- Non-entry freg callerSaveEntries membership: `refine ⟨hMem, ?_⟩; simp [hlx, hff]`
  (filter passes because layout x doesn't match the entry's register type)
- `v ≠ x` from layout type mismatch: `intro h; subst h; rw [hlx] at hLoc; cases hLoc`

## Remaining: fbinop fpow case (1 sorry at line ~2273)

Same structure as floatUnary but with TWO loads (y then z) before the havoc.
Use `ArmStep.callBinF` instead of `floatUnaryLibCall`. The `hLibStepBin`
fact is already proved.

Differences from floatUnary:
- Phase A: two `vLoadVarFP_eff_exec` calls, chained with ArmSteps.trans
  - First load: same as floatUnary (uses hRelSaved, hSavedPC)
  - Second load: uses hRel1 (ExtStateRel after first load), hPC1 for startPC
- dst_reg defaults to `.d0`, lv_reg to `.d1`, rv_reg to `.d2` (different scratches)
- `hNotIregZ` additionally needed for the second load

The 7 properties proof is identical in structure — copy from floatUnary
with minor adjustments (two load steps composed, different register names).

Estimated: ~250 more lines (mirroring floatUnary).
Consider extracting a helper if shared structure emerges, but likely
easier to just do both inline given the slight differences (1 vs 2 loads,
different havoc constructors).

## Probe Results

All probes verified (lake build passes with only the expected sorry warning).

1. **ExtStateRel for s_saved:** WORKS. Must derive `hEntriesSub'` inline
   (hSubset not in scope). Pattern above in Step 0.
2. **Case-split on p[pc]:** WORKS. `cases hInstr : p.code[pc]` + simp
   eliminates non-lib-call cases. For fbinop, need `cases fop` to
   isolate fpow from native fbinops.
3. **havocCallerSaved lemmas:** Only `_stack` and `_pc` simp lemmas.
   For regs/fregs must unfold `ArmState.havocCallerSaved` and reason
   about `if r.isCallerSaved`. No setFReg/havocCallerSaved composition
   lemma — unfold both.

## Prompt for fbinop fpow case

floatUnary is done. One sorry remains: fbinop fpow (line ~2273).

Mirror the floatUnary proof with these changes:
1. **Two loads** instead of one: `vLoadVarFP_eff_exec` for y (fallback .d1),
   then for z (fallback .d2, uses hRel1/hPC1 from first load). Compose steps.
2. **`ArmStep.callBinF`** instead of `floatUnaryLibCall`.
3. **`hLibStepBin`** instead of `hLibStep` for TAC result.
4. **hNotIregZ** additionally needed.
5. CodeAt splitting: `hCodeBase.append_left.append_left.append_left` for first
   load, `.append_left.append_right` for second, etc. (one deeper level).

All shared infrastructure (hEntriesSub', hRelSaved, hPC1', hAM2, hAMChain,
hStack2, hNEI_shared, hArmResult) follows the same pattern.
The 7 properties proof is identical structure — copy from floatUnary.

Build and verify with `lake build` — expect 0 sorrys total.
