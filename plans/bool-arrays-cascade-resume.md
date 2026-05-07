# Resume prompt: bool-arrays cascade

> Paste the body of this file into a fresh Claude Code session in
> `/Users/mr/CredibleCompilation` to continue the work.

---

## Your task

You are picking up a partial Lean 4 refactor in the CredibleCompilation project.
The goal is end-to-end source-level boolean arrays:
the source statement `arr[i] := true` (where `arr` is declared
`array X[N] : bool`) should typecheck, lower to TAC instructions
that use `.bool` element type, and have a clean correctness proof.

The build is currently broken with ~100+ errors. All of them are in three
files; all of them follow the same mechanical pattern that has already
been applied successfully to a fourth file. **Your job is to apply that
pattern to the remaining three files until `lake build` is clean and 0
sorrys are introduced.**

The hard design work is done. What's left is template-matching.

## What's already done (do not redo)

- `CredibleCompilation/WhileLang.lean` — `barrRead`/`barrWrite` typecheck
  now requires `arrayElemTy = .bool`; lowering emits TAC `arrLoad/arrStore _ _ _ .bool`
  using a new `btmpName` (`__bt`-prefixed) tmp namespace; `tyCtx_btmp_wt`,
  `defaultVarTy_of_isBTmp`, etc. added.
- `CredibleCompilation/CodeGen.lean` — `noRegVar` proofs updated for the
  new `barrWrite` lowering shape.
- `CredibleCompilation/RefCompiler/Defs.lean` — added `btmpName_ne`,
  `tmpName_ne_btmpName`, `ftmpName_ne_btmpName`, `Store.update_btmpName_ne`,
  `Store.update_isBTmp_ne`, `tmpName_not_isBTmp`, `ftmpName_not_isBTmp`,
  plus three `FragExec.single_*` helpers (`single_arrLoad_bool`,
  `single_arrStore_bool`, `single_boolop`).
- `CredibleCompilation/CompilerCorrectness.lean` — `Stmt.btmpFree`,
  `noTmpDecls_not_btmp`, `Program.typeCheck_btmpFree`.
- `CredibleCompilation/RefCompiler/Correctness.lean` — **fully cascaded**:
  `compileExpr_correct`, `compileBool_correct` (including the new
  `barrRead` case), `compileExprs_correct`, `compileStmt_correct`
  (including the rewritten `barrWrite` refinement), and
  `compileStmtToProg_correct`. `compileExpr_result_isBTmp_false` helper added.

This file is your **template**. Every transformation you'll apply elsewhere
has already been applied here. Use `git diff` to see exactly the shape.

## What you need to do

In order:

1. **`CredibleCompilation/RefCompiler/ErrorHandling.lean`** (~1300 LoC,
   biggest remaining file). Theorems `compileExpr_stuck`,
   `compileBool_stuck`, `compileStmt_stuck` already have updated
   signatures (taking `htbf` / `hbtmpfree` and the ternary `hagree`).
   Their internal proofs and call sites still need the cascade.

2. **`CredibleCompilation/RefCompiler/Refinement.lean`** (~31 hagree
   references). Top-level wrappers. They construct `htmpfree` /
   `hftmpfree` via `Program.typeCheck_tmpFree` / `_ftmpFree`; you need to
   add `hbtmpfree` from `Program.typeCheck_btmpFree`. Update each call
   to `compileStmt_correct` / `compileStmtToProg_correct` to pass
   `hbtmpfree` and use the ternary `hagree`.

3. **`CredibleCompilation/RefCompiler/Metatheory.lean`** (~52 hagree
   references). Same shape as Refinement.

4. Final: `lake build` clean, 0 sorrys, commit.

## The cascade pattern (cheat-sheet)

The refactor adds a third dimension (`btmp`) to the existing `tmp` /
`ftmp` infrastructure. Every transformation is one of these:

### Signature changes

```diff
  (htf  : ∀ v ∈ X.freeVars, v.isTmp  = false)
  (hftf : ∀ v ∈ X.freeVars, v.isFTmp = false)
+ (htbf : ∀ v ∈ X.freeVars, v.isBTmp = false)
  …
- (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
+ (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
```

For statement-level theorems, instead of `htbf` add `hbtmpfree : s.btmpFree`.

### Call site changes

```diff
- compileExpr_correct e off nT σ σ_tac am p htf_e hftf_e htv_e hsafe_e hagree hcodeE
+ compileExpr_correct e off nT σ σ_tac am p htf_e hftf_e htbf_e htv_e hsafe_e hagree hcodeE
```

(insert `htbf_e` between `hftf_e` and `htv_e`)

```diff
- compileStmt_correct s fuel σ σ' am am' off nT p σ_tac hinterp htmpfree hftmpfree hNoGoto …
+ compileStmt_correct s fuel σ σ' am am' off nT p σ_tac hinterp htmpfree hftmpfree hbtmpfree hNoGoto …
```

### Obtain pattern changes

```diff
- obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e⟩ := compileExpr_correct …
+ obtain ⟨σ_e, hexec_e, hval_e, hntmp_e, hprev_e, hfprev_e, hbprev_e⟩ := compileExpr_correct …
```

(one extra `_` or named binder for the new `hbprev_X` clause)

For `compileBool_correct`, same shape (one extra binder).

### Intro / hntmp / hagree application changes

```diff
- intro v hv1 hv2; rw [hntmp_e v hv1 hv2]; exact hagree v hv1 hv2
+ intro v hv1 hv2 hv3; rw [hntmp_e v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
```

### Projecting `htbf` for sub-expressions

When the expression has `freeVars = a.freeVars ++ b.freeVars`:

```lean
have htbf_a := fun v hv => htbf v (List.mem_append_left _ hv)
have htbf_b := fun v hv => htbf v (List.mem_append_right _ hv)
```

When the statement is `assign x e` and we want `htbf_e` over `e.freeVars`:

```lean
have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
  fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
```

For `compileStmt_correct`'s recursive sub-statements (seq/ite/loop):

```lean
have hbtf1 : s1.btmpFree := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact …)
have hbtf2 : s2.btmpFree := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact …)
```

(The ellipsis matches whatever `htf1`/`htf2` use for membership: `List.mem_append_left`, `_right`, etc.)

### When you need `va.isBTmp = false` for a result var

If the proof needs `va.isBTmp = false` where `va` is the result variable of `compileExpr a`:

```lean
have h3 : va.isBTmp = false := by
  have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
  rw [hra] at this; simpa using this
```

This helper is defined in `Correctness.lean` right before § 9.

### Identity agreement at the top level (Refinement.lean)

```diff
- (fun _ _ _ => rfl)
+ (fun _ _ _ _ => rfl)
```

(four binders for the four-argument identity hagree)

## How to start

1. `cd /Users/mr/CredibleCompilation`
2. `lake build 2>&1 | grep -E "^error" | head -10` — see current errors
3. `git log --oneline -3` — confirm you're on `main` with the rename commit
4. `git status` — confirm working tree has the partial cascade (M on
   `WhileLang.lean`, `CodeGen.lean`, `RefCompiler/Correctness.lean`,
   `RefCompiler/Defs.lean`, `RefCompiler/ErrorHandling.lean`,
   `CompilerCorrectness.lean`, plus pre-existing unrelated changes
   to `.claude/settings.json`, `lakefile.toml`, `scripts/optimizer_history.sh`,
   and untracked `Experiments/`, `instr.txt`, `parser.txt`)
5. Look at `Correctness.lean`'s changes for the template:
   `git diff HEAD -- CredibleCompilation/RefCompiler/Correctness.lean | head -300`
6. Apply the cascade to `ErrorHandling.lean` first. Iterate
   `lake build 2>&1 | grep ^error | head` after each pattern application.
7. After ErrorHandling clean: do `Refinement.lean`, then `Metatheory.lean`.

## Verification when done

```bash
lake build  # should print "Build completed successfully"
grep -rIn --include='*.lean' "sorry" CredibleCompilation/ | grep -v "/-" | grep -v "// " | wc -l   # should be 0 (all "sorry" mentions are in comments)
```

## Commit

When the build is clean:

1. Stage **only** the cascade-related files (do NOT stage the pre-existing
   in-flight modifications to `.claude/settings.json`, `lakefile.toml`,
   `scripts/optimizer_history.sh`, or the untracked `Experiments/`,
   `instr.txt`, `parser.txt`):

   ```bash
   git add CredibleCompilation/WhileLang.lean \
           CredibleCompilation/CodeGen.lean \
           CredibleCompilation/CompilerCorrectness.lean \
           CredibleCompilation/RefCompiler/Defs.lean \
           CredibleCompilation/RefCompiler/Correctness.lean \
           CredibleCompilation/RefCompiler/ErrorHandling.lean \
           CredibleCompilation/RefCompiler/Refinement.lean \
           CredibleCompilation/RefCompiler/Metatheory.lean
   ```

2. Then also remove this resume note (cascade is done):

   ```bash
   git rm plans/bool-arrays-cascade-resume.md
   ```

3. Commit with a message describing the substantive change (bool arrays
   typed end-to-end, three-dimensional agreement relation, btmpName
   infrastructure, etc.) and push to `origin/main`.

## Notes

- This entire refactor was originally estimated at 2-4 hours; the actual
  cost was much higher (5-7+ hours by the end of the previous session,
  with another 3-5 hours estimated for the remaining cascade). The
  pattern, however, is fully fixed at this point — no design decisions
  remain.

- Bool array runtime semantics are unchanged at the bit level: a bool is
  still encoded as 0/1 in a `BitVec 64` cell. The refactor is about
  which TAC ops carry the .bool tag and which variables hold the
  intermediate values.

- The `compileExpr_result_isBTmp_false` helper exists in `Correctness.lean`
  right before § 9 ("Expression compilation correctness"). Don't try to
  re-derive `va.isBTmp = false` by case-splitting; just use the helper.

- For the `barrRead` and `barrWrite` cases in `compileBool_correct` /
  `compileStmt_correct`: those proofs were entirely rewritten (the old
  ones lowered to `.int`-encoded bool arrays through 4 conversion
  instructions; the new ones use a single `boolop` + `arrStore _ _ _ .bool`).
  Don't try to apply the cascade pattern to them — the existing rewrites
  in `Correctness.lean` are already final. Just thread the new
  parameters through any sites that *call* them.
