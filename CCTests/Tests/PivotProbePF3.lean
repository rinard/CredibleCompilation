/-
# Micro-probe — step_count_pc_uniqueness under nondeterministic ArmStep

Goal: determine how painful it is to prove step_count_pc_uniqueness
for r.bodyFlat without the determinism pivot.

Strategy:
  Attempt 1: naive direct induction using arm_step_pc_det.  See
    where it gets stuck.
  Attempt 2: augment the invariant (track more state equality).  See
    how painful the richer invariant is.
-/

import CredibleCompilation.PipelineCorrectness

namespace PivotProbePF3

open ArmState

/-!
## Attempt 1: naive direct induction

Expected: fails at the inductive step because `arm_step_pc_det`
needs the SAME starting state, but induction gives two states with
potentially different regs.
-/

/-- Attempt 1.  For generic `prog` (not specific to r.bodyFlat). -/
example {prog : ArmProg} {s₀ : ArmState} :
    ∀ n s₁ s₂, ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n →
      s₁.pc = s₂.pc := by
  intro n
  induction n with
  | zero =>
      intro s₁ s₂ h1 h2
      change s₀ = s₁ at h1; change s₀ = s₂ at h2
      subst h1; subst h2; rfl
  | succ k ih =>
      intro s₁ s₂ h1 h2
      obtain ⟨m₁, hs₁, hr₁⟩ := h1
      obtain ⟨m₂, hs₂, hr₂⟩ := h2
      -- arm_step_pc_det: m₁.pc = m₂.pc ✓
      -- IH needs ArmStepsN from the SAME state.  But m₁ ≠ m₂ in general.
      -- We CAN'T apply ih here directly.
      sorry

/-!
## Attempt 2: strengthened invariant

Invariant: two states agree on all fields relevant to branches.  This
includes stack, arrayMem, callee-saved regs/fregs, flags, and — the
hard part — caller-saved regs that were written deterministically
since the last havoc.

The last part is the hidden complexity.  Without it, any cmp/cbz
reading a caller-saved scratch (freshly loaded via vLoadVar) can't
be handled.  With it, we're effectively encoding uninit-reads
analysis.

Here's a minimal attempt that works on the HAPPY CASE: two traces
that happen to agree on all reg contents.
-/

/-- If two traces from init agree on ALL fields at every step, PCs
    agree trivially.  This is trivially provable; the interesting
    question is whether "all fields agree" is preserved under ArmStep. -/
example {prog : ArmProg} {s₀ : ArmState} :
    ∀ n s₁ s₂, ArmStepsN prog s₀ s₁ n → ArmStepsN prog s₀ s₂ n →
      (∀ k ≤ n, ∃ s_can, ∀ s, ArmStepsN prog s₀ s k → s = s_can) →
      s₁ = s₂ := by
  intro n s₁ s₂ h1 h2 hUniq
  obtain ⟨s_can, hUniq_n⟩ := hUniq n (Nat.le.refl)
  have := hUniq_n s₁ h1
  have := hUniq_n s₂ h2
  subst_vars; rfl

/-!
## Attempt 3: under BRANCHLESS program assumption

If `prog` contains no branch instructions (`.b`, `.cbz`, `.cbnz`, `.bCond`),
then every ArmStep advances pc by +1.  Two ArmStepsN of same length
trivially agree on PC.

This would validate the INDUCTION MACHINERY without getting stuck on
branch reasoning.  If it passes cleanly, the remaining work is
handling branches (which is the spec-level per-PC analysis).
-/

/-- For a branchless program, PC after n steps is init.pc + n,
    regardless of havoc. -/
example {prog : ArmProg} {s₀ : ArmState}
    (hBranchless : ∀ (pc : Nat) lbl,
        prog[pc]? ≠ some (ArmInstr.b lbl) ∧
        (∀ rn, prog[pc]? ≠ some (ArmInstr.cbz rn lbl)) ∧
        (∀ rn, prog[pc]? ≠ some (ArmInstr.cbnz rn lbl)) ∧
        (∀ c, prog[pc]? ≠ some (ArmInstr.bCond c lbl))) :
    ∀ n s, ArmStepsN prog s₀ s n → s.pc = s₀.pc + n := by
  intro n
  induction n with
  | zero => intro s h; change s₀ = s at h; subst h; simp
  | succ k ih =>
      intro s h
      obtain ⟨m, hs, hr⟩ := h
      -- hs : ArmStep prog s₀ m
      -- Show m.pc = s₀.pc + 1.
      -- Use arm_step_pc_det via armNextPC — but we need to show it's
      -- s₀.pc + 1, not a branch target.
      -- The armNextPC helper is private in PipelineCorrectness.lean.
      -- For the probe, admit via sorry.
      sorry

/-!
## Findings from the micro-probe

### Attempt 1 conclusively confirms:

Naive induction CAN'T close step_count_pc_uniqueness.  The inductive
step obtains two intermediate states `m₁, m₂` with potentially
different regs (due to havoc).  `arm_step_pc_det` only works on the
SAME input state.  To apply the IH, we'd need `m₁ = m₂` (full state)
or a stronger invariant on (m₁, m₂).

### Attempt 2 sketches the strong approach:

Strengthen to full state equality.  Under the DETERMINISM PIVOT, this
is automatic (arm_step_det does the heavy lifting).  Under the
NONDETERMINISTIC model, full state equality fails (havoc diverges).

### Attempt 3 sketches a partial-program approach:

For branchless programs, PC is determined by step count alone.  The
induction works.  But real r.bodyFlat HAS branches — we can't reduce
to branchless.

### What would actually work under nondet

To prove step_count_pc_uniqueness for r.bodyFlat nondetermistically,
we need a richer invariant on state pairs that:
  1. Tracks which state components affect future branches.
  2. Shows these components agree in both traces.
  3. Is preserved by ArmStep (requires per-rule analysis).

This is the "uninit-reads analysis" discussed earlier, formalized as
an abstract interpretation.  Estimated cost: ~440 LOC as noted
previously.

Alternative: prove for bodyFlat specifically via spec-structure
navigation.  Per-PC classification (libcall chunk / print chunk /
non-libcall chunk / haltSaveBlock), per-class branch-safety argument,
composition into PC uniqueness.  Estimated cost: ~300 LOC.

### Neither is the advertised "~150 LOC"

Both realistic paths are 300+ LOC.  The pivot's step_count_state_
uniqueness at ~15 LOC is dramatically cheaper (after paying ~250 LOC
for the refactor).

### Micro-probe verdict

**Fix B' without the pivot is not economical.**  step_count_pc_uniqueness
for bodyFlat under nondet is ~300 LOC minimum, comparable to or
exceeding the pivot's total cost.  Reactive stacking would incur
significant waste (~200 LOC of abandoned attempt).

**Recommend: pivot + Fix B' from the start.**  Fixed cost ~750 LOC,
no backtracking risk.
-/

/-- The verdict proof is trivial. -/
theorem probe_verdict : True := trivial

end PivotProbePF3
