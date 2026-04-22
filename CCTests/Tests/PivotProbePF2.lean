/-
# PF2' — TAC self-loop → ARM self-loop

Probes the second key piece of Fix B': given a TAC-level self-loop
(`.goto pc` at PC pc), show that the corresponding ARM instruction
produces an ArmStep that self-loops at the ARM level
(`ArmStep prog s s`).

If this lands, combined with PF1's `arm_self_loop_diverges`, we have
the full Fix B' pipeline: self-loop TAC step → ARM self-loop →
ArmDiverges.
-/

import CredibleCompilation.PipelineCorrectness

namespace PivotProbePF2

open ArmState

/-- **PF2' — TAC self-loop → ARM self-loop.**

    Given a TAC instruction `.goto pc` at PC pc (self-loop) and an
    ARM state s matching via ExtSimRel, the ARM code at pcMap pc is
    `.b (pcMap pc)` (from spec.instrGen + verifiedGenInstr unfolding),
    and executing it from state s (which has s.pc = pcMap pc) yields
    state s again (target = current PC).  Hence ArmStep s s. -/
theorem tac_goto_self_loop_implies_arm_self_loop
    {tyCtx : TyCtx} {p : Prog} {r : VerifiedAsmResult}
    (spec : GenAsmSpec tyCtx p r)
    {pc : Nat} {σ : Store} {am : ArrayMem} {s : ArmState}
    (hRel : ExtSimRel r.layout r.pcMap r.divS r.boundsS (.run pc σ am) s)
    (hPC : pc < p.size)
    (hGoto : p[pc] = TAC.goto pc) :
    ArmStep r.bodyFlat s s := by
  -- Step 1: from ExtSimRel.run, s.pc = r.pcMap pc.
  have hsPc : s.pc = r.pcMap pc := by
    -- ExtSimRel for .run cfg is ⟨ExtStateRel, PcRel, arrayMem⟩.
    exact hRel.2.1
  -- Step 2: spec.instrGen at pc.  Need to show .goto pc is not a libcall or print.
  have hNotLib : isLibCallTAC p[pc] = false := by rw [hGoto]; rfl
  have hNotPrint : ∀ fmt vs, p[pc] ≠ .print fmt vs := by
    intro fmt vs h; rw [hGoto] at h; exact TAC.noConfusion h
  have hGenInstr := spec.instrGen pc hPC hNotLib hNotPrint
  -- Step 3: compute verifiedGenInstr for .goto pc = some [.b (pcMap pc)]
  -- Substitute p[pc] = .goto pc in hGenInstr.
  rw [hGoto] at hGenInstr
  -- hGenInstr : verifiedGenInstr r.layout r.pcMap (.goto pc) ... = some bodyPerPC[pc]
  -- Now show bodyPerPC[pc] = [.b (pcMap pc)] by unfolding verifiedGenInstr on .goto pc.
  have hBodyEq : r.bodyPerPC[pc]'(spec.bodySize ▸ hPC) = [ArmInstr.b (r.pcMap pc)] := by
    simp only [verifiedGenInstr] at hGenInstr
    -- The outer guard `!regConv || !inj`: if true, returns none; else matches.
    -- Since hGenInstr = some (...), the guard must be false.
    split at hGenInstr
    · exact absurd hGenInstr (by intro h; cases h)
    · -- Guard false; the match on .goto pc gives some [.b (pcMap pc)].
      simp only [Option.some.injEq] at hGenInstr
      exact hGenInstr.symm
  -- Step 4: lift to bodyFlat via codeAt_of_bodyFlat'.
  obtain ⟨lengths, hLSz, hPcMap, hLenEq⟩ := spec.pcMapLengths
  have hCodeAt0 :=
    codeAt_of_bodyFlat' r lengths hLSz hLenEq pc (spec.bodySize ▸ hPC)
  -- hCodeAt0 : CodeAt r.bodyFlat (buildPcMap lengths pc) r.bodyPerPC[pc]
  rw [← hPcMap] at hCodeAt0
  rw [hBodyEq] at hCodeAt0
  -- hCodeAt0 : CodeAt r.bodyFlat (r.pcMap pc) [ArmInstr.b (r.pcMap pc)]
  have hCodeAt := hCodeAt0
  -- Step 5: extract r.bodyFlat[r.pcMap pc]? = some (.b (r.pcMap pc))
  have hCode : r.bodyFlat[r.pcMap pc]? = some (ArmInstr.b (r.pcMap pc)) :=
    hCodeAt.head
  -- Step 6: apply ArmStep.branch.  Target = r.pcMap pc = s.pc, so next state = s.
  have hCode' : r.bodyFlat[s.pc]? = some (ArmInstr.b (r.pcMap pc)) := by
    rw [hsPc]; exact hCode
  have hStep := ArmStep.branch (r.pcMap pc) hCode'
  -- hStep : ArmStep r.bodyFlat s { s with pc := r.pcMap pc }
  -- { s with pc := r.pcMap pc } = s since s.pc = r.pcMap pc
  have hsEq : { s with pc := r.pcMap pc } = s := by
    rw [← hsPc]
  rw [hsEq] at hStep
  exact hStep

end PivotProbePF2
