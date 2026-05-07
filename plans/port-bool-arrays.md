# Port: source-level bool arrays + parser routing fix

You are porting two related changes from this CredibleCompilation repo to a
**derivative codebase** (a fork/sibling system that diverged from this one).
The changes have already landed here — your job is to apply equivalent
edits over there.

The user will tell you the path of the derivative repo when they invoke
this prompt; if they don't, ask. This file describes **what** to change
and **why**, not the exact line-edits — the derivative may have drifted,
so you must read its current state and translate the change shape onto it.

---

## What the changes do

### Change A — End-to-end source-level bool arrays

Source programs like

```
var i : int;
array flags[8] : bool;
flags[0] := true;
i := 0;
while (i < 8) { printBool(flags[i]); printString("\n"); i := i + 1 }
```

now typecheck, lower to TAC, codegen to ARM, and run.

Before: `array X[N] : bool` parsed but `barrRead`/`barrWrite` typechecking
demanded `arrayElemTy = .int` and lowering went through `.int`-encoded
bools (a 5-instruction `ifgoto`/`const`/`goto`/`const`/`arrStore _ _ _ .int`
sequence). After: `barrRead`/`barrWrite` demand `.bool`; lowering uses a
single `arrLoad _ _ _ .bool` and a single `boolop` + `arrStore _ _ _ .bool`
(2 instructions for write). Bit-level runtime semantics are unchanged
(0/1 in a `BitVec 64` cell); the refactor is about which TAC ops carry
the `.bool` tag and which variables hold intermediates.

The proof side adds a **third dimension** to the existing tmp/ftmp
infrastructure:

- New temp namespace `btmpName` (`__bt`-prefixed) for compiler-generated
  bool intermediates, parallel to existing `tmpName` (`__t`) and
  `ftmpName` (`__ft`).
- The agreement relation between source store `σ` and TAC store `σ_tac`
  becomes ternary: preserved on vars that are not `isTmp`, not `isFTmp`,
  **and** not `isBTmp`.
- Every `compile{Expr,Bool,Exprs,Stmt,*}_{correct,stuck,unsafe,diverges}`
  signature gains a parallel `htbf : ∀ v ∈ X.freeVars, v.isBTmp = false`
  (or, at statement level, `hbtmpfree : s.btmpFree`).
- Every conclusion's `hntmp_X` / agree-postcondition gains a parallel
  `hbprev_X : ∀ k < nextTmp, σ' (btmpName k) = σ_tac (btmpName k)` clause.
- `Program.noTmpDecls` is extended to also reject `isBTmp` source decls
  so that default typing (in `tyCtx`) stays coherent for bool temps.

### Change B — Parser bool-routing fix

The grammar commits to `Stmt.assign x e` (int-typed) before knowing the
declared type of `x`, and to `Stmt.arrWrite arr idx val` before knowing
the array's element type. After type resolution, `t := flags[i]` (with
`t : bool` and `flags` a `bool` array) was failing well-formedness
because `assign x e` requires `e` to be int-typed. Same for
`flags[0] := flags[3]` (bool array element copy).

The fix lives in the type-resolution pass: when the destination is
bool, attempt to re-view the parser-emitted SExpr value as a SBool.
The conversion is partial (only `.var x` ↦ `.bvar x` and
`.arrRead arr idx` ↦ `.barrRead arr idx` are handled) — other forms
are left to well-formedness to reject. This is parallel to the
existing int→float reroute (`.assign` → `.fassign` when LHS is float).

---

## Reference commits in this repo

The changes are squashed across two commits on `origin/main`:

- **`2ef09ab`** — "Bool arrays: type end-to-end, three-dimensional
  agreement relation" — the main cascade. 10 files,
  +1095 / −893.
- **`<latest>`** — the parser routing fix in
  `CredibleCompilation/Parser.lean` `sExprToSBool` + `resolveStmt`
  rewrite. ~25 lines.
- A set of 8 bool-array end-to-end tests under
  `tests/programs/bool_*.{while,c}` that both compile + run identically.

To inspect the diffs:
```
git show 2ef09ab -- '*.lean'                   # the cascade
git log --oneline origin/main -- CredibleCompilation/Parser.lean   # find the parser-fix commit
git show <parser-fix-sha> -- CredibleCompilation/Parser.lean
git diff 2ef09ab^..HEAD -- tests/programs/bool_*               # the new tests
```

Use these as your source of truth.

---

## Files touched (this repo)

In dependency order. The derivative will likely have files with the same
or similar names; map them across.

1. `CredibleCompilation/WhileLang.lean` — typecheck rules for
   `barrRead`/`barrWrite` (now require `.bool`), lowering through
   `btmpName` namespace, supporting helpers (`btmpName_isBTmp_wt`,
   `lookup_none_of_isBTmp_wt`, `defaultVarTy_of_isBTmp`, `tyCtx_btmp_wt`,
   `noTmpDecls` rejecting `isBTmp`).
2. `CredibleCompilation/CodeGen.lean` — `noRegVar` proofs updated for
   the new `barrWrite` lowering shape.
3. `CredibleCompilation/RefCompiler/Defs.lean` — name-disjointness lemmas
   (`btmpName_ne`, `tmpName_ne_btmpName`, `ftmpName_ne_btmpName`),
   store-update lemmas (`Store.update_btmpName_ne`,
   `Store.update_isBTmp_ne`), filtering lemmas (`tmpName_not_isBTmp`,
   `ftmpName_not_isBTmp`), and three new `FragExec.single_*` helpers
   (`single_arrLoad_bool`, `single_arrStore_bool`, `single_boolop`).
4. `CredibleCompilation/CompilerCorrectness.lean` — `Stmt.btmpFree`
   predicate, `noTmpDecls_not_btmp`, `Program.typeCheck_btmpFree`.
5. `CredibleCompilation/RefCompiler/Correctness.lean` — **the cascade
   template**. Every kind of edit you'll need to make appears here:
   signature updates, `obtain` pattern extensions, `htbf_X` projections,
   ternary-agreement applications, the new `compileExpr_result_isBTmp_false`
   helper. The `barrRead` and `barrWrite` correctness cases are
   rewritten end-to-end for the new lowering — copy these directly,
   don't try to derive them from the old shape.
6. `CredibleCompilation/RefCompiler/ErrorHandling.lean` — same cascade
   applied to `_stuck` and `_unsafe` variants.
7. `CredibleCompilation/RefCompiler/Refinement.lean` — top-level
   wrappers thread `hbtmpfree` from `Program.typeCheck_btmpFree`; the
   identity agreement becomes `(fun _ _ _ _ => rfl)`.
8. `CredibleCompilation/RefCompiler/Metatheory.lean` — same shape as
   Refinement.
9. `CredibleCompilation/PipelineCorrectness.lean` — one call site that
   consumes the now-ternary agreement gains a third arg (`hntw.2`).
10. `CredibleCompilation/Parser.lean` — Change B (`sExprToSBool`,
    extended `resolveStmt`).

---

## The cascade pattern (cheat-sheet for Change A)

### Signature changes
```diff
  (htf  : ∀ v ∈ X.freeVars, v.isTmp  = false)
  (hftf : ∀ v ∈ X.freeVars, v.isFTmp = false)
+ (htbf : ∀ v ∈ X.freeVars, v.isBTmp = false)
  …
- (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → σ_tac v = σ v)
+ (hagree : ∀ v, v.isTmp = false → v.isFTmp = false → v.isBTmp = false → σ_tac v = σ v)
```

For statement-level theorems use `hbtmpfree : s.btmpFree` instead of
`htbf`.

### Conclusions (when extending the existential return type)
Add one more conjunct after `hfprev_X`:
```
∧ (∀ k, k < nextTmp → σ' (btmpName k) = σ_tac (btmpName k))
```

### Call sites
```diff
- compileExpr_correct e off nT σ σ_tac am p htf_e hftf_e htv_e hsafe hagree hcode
+ compileExpr_correct e off nT σ σ_tac am p htf_e hftf_e htbf_e htv_e hsafe hagree hcode
```
Insert `htbf_e` between `hftf_e` and `htv_e`. Same pattern for
`compileBool_correct`, `compileExprs_correct`, the `_stuck` / `_unsafe`
variants, and `compileStmt_correct` (which inserts `hbtmpfree` between
`hftmpfree` and `hNoGoto`).

### Obtain patterns
```diff
- obtain ⟨σ_e, hexec, hval, hntmp, hprev, hfprev⟩ := compileExpr_correct …
+ obtain ⟨σ_e, hexec, hval, hntmp, hprev, hfprev, hbprev⟩ := compileExpr_correct …
```
One extra `_` or named binder (the new `hbprev_X`).

### Ternary application
```diff
- intro v hv1 hv2; rw [hntmp_e v hv1 hv2]; exact hagree v hv1 hv2
+ intro v hv1 hv2 hv3; rw [hntmp_e v hv1 hv2 hv3]; exact hagree v hv1 hv2 hv3
```

### Identity agreement at top level
```diff
- (fun _ _ _ => rfl)
+ (fun _ _ _ _ => rfl)
```

### Projecting `htbf` for sub-expressions / sub-statements
When `freeVars = a.freeVars ++ b.freeVars`:
```lean
have htbf_a : ∀ v ∈ a.freeVars, v.isBTmp = false :=
  fun v hv => htbf v (List.mem_append_left _ hv)
have htbf_b : ∀ v ∈ b.freeVars, v.isBTmp = false :=
  fun v hv => htbf v (List.mem_append_right _ hv)
```

For statement `assign x e`:
```lean
have htbf_e : ∀ v ∈ e.freeVars, v.isBTmp = false :=
  fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact List.mem_cons_of_mem x hv)
```

For seq/ite/loop sub-statements:
```lean
have hbtf1 : s1.btmpFree := fun v hv => hbtmpfree v (by simp only [Stmt.allVars]; exact …)
```

### When you need `va.isBTmp = false` for an expression-result variable
Use the new helper `compileExpr_result_isBTmp_false` (defined in
`Correctness.lean` immediately before § 9):
```lean
have h3 : va.isBTmp = false := by
  have := compileExpr_result_isBTmp_false a offset nextTmp htbf_a
  rw [hra] at this; simpa using this
```
Then any use of `hntmp_b va h h2` becomes `hntmp_b va h h2 h3`.

---

## Parser fix (Change B) — exact shape

In whatever module does post-parse type resolution (in this repo it's
`CredibleCompilation/Parser.lean`'s `resolveStmt`), add a SExpr-to-SBool
view:

```lean
private def sExprToSBool (lookupVar : Var → Option VarTy)
    (lookupArr : ArrayName → Option VarTy) : SExpr → Option SBool
  | .var x => if lookupVar x == some .bool then some (.bvar x) else none
  | .arrRead arr idx => if lookupArr arr == some .bool then some (.barrRead arr idx) else none
  | _ => none
```

Then extend `resolveStmt` so that:

- `.assign x e` with `lookupVar x == some .bool` → try `sExprToSBool` on
  the resolved value; if `some b`, emit `.bassign x b`; otherwise leave
  as `.assign x e'` (well-formedness will reject).
- `.arrWrite arr idx val` with `lookupArr arr == some .bool` → try
  `sExprToSBool` on resolved val; if `some bval`, emit
  `.barrWrite arr idx' bval`; otherwise leave as `.arrWrite`.

The parallel structure to the existing int→float reroute is intentional —
keep the new branch as the second `else if`, after the float check and
before the fall-through.

---

## What NOT to do

- **Don't** try to apply the cascade pattern to the `barrRead` /
  `barrWrite` proof cases — those are rewritten end-to-end (the old
  proofs lowered through 4-5 conversion instructions; the new ones use
  1-2 typed instructions). Copy the new versions from
  `Correctness.lean` directly.
- **Don't** add `barrRead` / `barrWrite` support to `sExprToSBool`'s
  `_ => none` fallback by reverse-engineering from the SExpr side —
  the parser already routes pure-bool expressions via `parseBOr`. The
  helper exists strictly to recover from the parser's *commit-to-int*
  for two specific shapes (var, arrRead).
- **Don't** introduce sorrys. The cascade is mechanical; if a case
  won't close with the standard pattern, look at the corresponding case
  in `Correctness.lean` — that's the template.

---

## Verification checklist

After porting:

1. `lake build` (or the derivative's equivalent) is clean — no `error:`
   lines.
2. Sorry count is unchanged from before your edits:
   `grep -rIn --include='*.lean' '\bsorry\b' <src> | grep -vE '^[^:]+:[0-9]+:\s*--'`
   should show only doc-comment occurrences (text like
   "0 sorrys from..." inside `/-! ... -/` blocks).
3. End-to-end smoke test: copy `tests/programs/bool_001_basic.{while,c}`
   through `bool_008_negation.{while,c}` from this repo into the
   derivative, run them through the derivative's compiler + a `cc`-built
   reference, and diff outputs. All eight should pass.

If the derivative has its own test harness, integrate the bool tests
into it instead of running them ad-hoc.

---

## Reporting back

When done, report:

- which files in the derivative ended up touched (mapped from this
  repo's file list),
- the final sorry delta (should be 0),
- a one-line summary of any cases where the cascade pattern needed
  adapting because the derivative's proof structure differed,
- the bool_001..bool_008 pass/fail status.
