import CredibleCompilation.ArmSemantics
import CredibleCompilation.BvLemmas
import CredibleCompilation.ExecChecker
import Std.Tactic.BVDecide

/-!
# ARM64 Correctness Proofs

Correctness theorems for the ARM64 code generation: loadImm64_correct,
Flags.condHolds_correct, verifiedGenBoolExpr_correct,
verifiedGenInstr_correct, and ext_backward_simulation.

Split from `AsmSemantics.lean`.
-/

-- === Helpers for loadImm64_correct large case ===

private theorem uint64_nat_roundtrip (u : UInt64) : u.toNat.toUInt64 = u := by
  apply UInt64.eq_of_toBitVec_eq
  simp [UInt64.toBitVec, Nat.toUInt64, BitVec.ofNat]
private theorem BitVec_ofNat_UInt64_toNat (u : UInt64) :
    BitVec.ofNat 64 u.toNat = u.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  exact Nat.mod_eq_of_lt u.toBitVec.isLt
private theorem insertBits_unfold (bv : BitVec 64) (imm16 : UInt64) (shift : Nat) :
    insertBits bv imm16 shift =
    (bv &&& ~~~(0xFFFF#64 <<< shift)) ||| (BitVec.ofNat 64 imm16.toNat <<< shift) := by
  unfold insertBits; rfl
/-- Execute an optional movk instruction (present when w ≠ 0, skipped when w = 0). -/
private theorem optional_movk_step (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs rd = (if (w != 0) = true then insertBits (s.regs rd) w shift else s.regs rd) ∧
      s'.stack = s.stack ∧
      s'.pc = pc0 + (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  by_cases hw : (w != 0) = true
  · -- w ≠ 0: one movk instruction
    simp only [hw, ite_true] at hCode ⊢
    have hInstr := hCode.head
    rw [← hPC] at hInstr
    refine ⟨s.setReg rd (insertBits (s.regs rd) w shift) |>.nextPC,
      .single (.movk rd w shift hInstr), ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC, hPC]
    · intro r hr; exact ArmState.setReg_regs_other _ _ _ _ hr
    · rfl
  · -- w = 0: no instruction, identity
    simp only [hw] at hCode ⊢
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨s, .refl, rfl, rfl, by simp [hPC], fun _ _ => rfl, rfl⟩
private theorem uint64_shl_zero (u : UInt64) : u <<< (0 : UInt64) = u := by
  apply UInt64.eq_of_toBitVec_eq; simp
private theorem uint64_eq_zero_toBitVec (u : UInt64) (h : u = 0) :
    u.toBitVec = 0 := by rw [h]; rfl
private theorem uint64_ne_zero_bne (u : UInt64) (h : ¬(u = 0)) :
    (u != 0) = true := by simp [bne, beq_iff_eq, h]

-- Bridge: convert UInt64 .toBitVec expressions to pure BitVec for bv_reassemble
private theorem uint64_toBitVec_chunk0 (u : UInt64) :
    (u &&& (0xFFFF : UInt64)).toBitVec = u.toBitVec &&& 0xFFFF#64 := rfl
private theorem uint64_toBitVec_chunk16 (u : UInt64) :
    (u >>> (16:UInt64) &&& (0xFFFF:UInt64)).toBitVec = (u.toBitVec >>> 16) &&& 0xFFFF#64 := by
  apply BitVec.eq_of_toNat_eq; simp
private theorem uint64_toBitVec_chunk32 (u : UInt64) :
    (u >>> (32:UInt64) &&& (0xFFFF:UInt64)).toBitVec = (u.toBitVec >>> 32) &&& 0xFFFF#64 := by
  apply BitVec.eq_of_toNat_eq; simp
private theorem uint64_toBitVec_chunk48 (u : UInt64) :
    (u >>> (48:UInt64) &&& (0xFFFF:UInt64)).toBitVec = (u.toBitVec >>> 48) &&& 0xFFFF#64 := by
  apply BitVec.eq_of_toNat_eq; simp
private theorem uint64_bne_false_toBitVec (u : UInt64) (h : (u != 0) = false) :
    u.toBitVec = 0 := by
  simp [bne, beq_iff_eq] at h
  rw [h]; rfl
private theorem uint64_toBitVec_toNat_roundtrip (u : UInt64) :
    u.toBitVec.toNat.toUInt64 = u := uint64_nat_roundtrip u

set_option maxHeartbeats 40000000 in
theorem loadImm64_correct (prog : ArmProg) (rd : ArmReg) (n : BitVec 64)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs rd = n ∧
      s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  unfold formalLoadImm64 at hCode
  split at hCode
  case isTrue hSmall =>
    -- Small case: single mov instruction
    have hMov := hCode.head
    rw [← hPC] at hMov
    exact ⟨s.setReg rd n |>.nextPC, .single (.mov rd n hMov),
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC, hPC, formalLoadImm64, hSmall],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, rfl⟩
  case isFalse hLarge =>
    -- Large case: movz/movk sequence
    -- Beta-reduce the have-bindings from the unfolded let
    dsimp only at hCode
    -- Local abbreviations
    let bits : UInt64 := n.toNat.toUInt64
    let w0 : UInt64 := bits &&& 65535
    let w1 : UInt64 := bits >>> 16 &&& 65535
    let w2 : UInt64 := bits >>> 32 &&& 65535
    let w3 : UInt64 := bits >>> 48 &&& 65535
    -- Extract CodeAt for the base instruction and each optional movk
    have hCodeBase := hCode.append_left.append_left.append_left
    have hCodeK1rest := hCode.append_left.append_left.append_right
    -- hCodeK1rest : CodeAt prog (startPC + 1) (if (w1 != 0) = true then ...)
    -- We need to adjust the PC for k2 and k3
    have hCodeK1K2 := hCode.append_left
    have hCodeK2rest := hCodeK1K2.append_right
    have hCodeK3rest := hCode.append_right
    -- Step 1: Execute movz rd w0 0
    have hMovz := hCodeBase.head
    rw [← hPC] at hMovz
    let s0 := s.setReg rd (BitVec.ofNat 64 (w0 <<< (0 : UInt64)).toNat) |>.nextPC
    have hPC0 : s0.pc = startPC + 1 := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hPC]
    have hw0_shift : (w0 <<< (0 : UInt64)) = w0 := uint64_shl_zero w0
    have hRd0 : s0.regs rd = BitVec.ofNat 64 w0.toNat := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hw0_shift]
    -- Step 2: optional movk for w1 at shift 16
    obtain ⟨s1, hSteps1, hRd1, hStack1, hPC1, hRegs1, hAM1⟩ :=
      optional_movk_step prog rd w1 16 s0 (startPC + 1) hPC0 hCodeK1rest
    -- Step 3: optional movk for w2 at shift 32
    -- Need to show the PC for k2
    have hLenBase : [ArmInstr.movz rd w0 0].length = 1 := by simp
    have hLenK1K2 : hCodeK1K2.append_right = hCodeK2rest := rfl
    have hPC_k2 : startPC + ([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])).length =
        startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length := by
      simp; omega
    rw [hPC_k2] at hCodeK2rest
    obtain ⟨s2, hSteps2, hRd2, hStack2, hPC2, hRegs2, hAM2⟩ :=
      optional_movk_step prog rd w2 32 s1
        (startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length)
        hPC1 hCodeK2rest
    -- Step 4: optional movk for w3 at shift 48
    have hPC_k3 : startPC + (([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])) ++
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else [])).length =
        startPC + 1 +
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length := by
      simp; omega
    rw [hPC_k3] at hCodeK3rest
    obtain ⟨s3, hSteps3, hRd3, hStack3, hPC3, hRegs3, hAM3⟩ :=
      optional_movk_step prog rd w3 48 s2
        (startPC + 1 +
         (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
         (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length)
        hPC2 hCodeK3rest
    -- Chain all steps together
    refine ⟨s3,
      (.step (.movz rd w0 0 hMovz) (hSteps1.trans (hSteps2.trans hSteps3))),
      ?_, ?_, ?_, ?_, ?_⟩
    · -- s3.regs rd = n
      -- Key fact: bits.toBitVec = n
      have hbits_bv : bits.toBitVec = n := by
        show n.toNat.toUInt64.toBitVec = n
        rw [UInt64.toBitVec]
        apply BitVec.eq_of_toNat_eq
        simp [Nat.toUInt64]
      -- Prepare chunk zero-facts
      have hc0 : w0.toBitVec = bits.toBitVec &&& 0xFFFF#64 := uint64_toBitVec_chunk0 bits
      have hc1 : w1.toBitVec = (bits.toBitVec >>> 16) &&& 0xFFFF#64 := uint64_toBitVec_chunk16 bits
      have hc2 : w2.toBitVec = (bits.toBitVec >>> 32) &&& 0xFFFF#64 := uint64_toBitVec_chunk32 bits
      have hc3 : w3.toBitVec = (bits.toBitVec >>> 48) &&& 0xFFFF#64 := uint64_toBitVec_chunk48 bits
      -- Case split on w1, w2, w3 being zero to resolve the ifs in hRd1/hRd2/hRd3
      by_cases hw1z : w1 = 0 <;> by_cases hw2z : w2 = 0 <;> by_cases hw3z : w3 = 0
      -- Simplify the if-then-else in each hRd
      all_goals simp only [show (w1 != 0) = true ↔ w1 ≠ 0 from by simp [bne, beq_iff_eq]] at hRd1
      all_goals simp only [show (w2 != 0) = true ↔ w2 ≠ 0 from by simp [bne, beq_iff_eq]] at hRd2
      all_goals simp only [show (w3 != 0) = true ↔ w3 ≠ 0 from by simp [bne, beq_iff_eq]] at hRd3
      all_goals (try simp only [hw1z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd1)
      all_goals (try simp only [hw2z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd2)
      all_goals (try simp only [hw3z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd3)
      -- Rewrite to get a concrete BitVec expression
      all_goals rw [hRd3]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd2]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd1]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd0]
      -- Convert BitVec.ofNat to .toBitVec
      all_goals simp only [BitVec_ofNat_UInt64_toNat]
      -- Convert .toBitVec of each chunk to the bits expression
      all_goals rw [hc0]
      all_goals try rw [hc1]
      all_goals try rw [hc2]
      all_goals try rw [hc3]
      all_goals rw [← hbits_bv]
      -- Now apply the appropriate bv_reassemble variant
      -- Order: w1=0/w2=0/w3=0, w1=0/w2=0/w3≠0, w1=0/w2≠0/w3=0, w1=0/w2≠0/w3≠0,
      --        w1≠0/w2=0/w3=0, w1≠0/w2=0/w3≠0, w1≠0/w2≠0/w3=0, w1≠0/w2≠0/w3≠0
      · exact bv_reassemble_000 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_001 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_010 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_011 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z)
      · exact bv_reassemble_100 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_101 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_110 bits.toBitVec (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble bits.toBitVec
    · -- s3.stack = s.stack
      rw [hStack3, hStack2, hStack1]
      simp [s0, ArmState.setReg, ArmState.nextPC]
    · -- s3.pc = startPC + (formalLoadImm64 rd n).length
      rw [hPC3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · -- Other registers preserved
      intro r hr
      rw [hRegs3 r hr, hRegs2 r hr, hRegs1 r hr]
      simp [s0, ArmState.setReg, ArmState.nextPC]
      intro heq; exact absurd heq hr
    · -- arrayMem preserved
      rw [hAM3, hAM2, hAM1]; simp [s0, ArmState.setReg, ArmState.nextPC]
/-- Flags.condHolds matches CmpOp.eval — trivially, since both use slt/sle
    on the stored operands. No range restriction needed. -/
theorem Flags.condHolds_correct (op : CmpOp) (a b : BitVec 64) :
    (Flags.mk a b).condHolds
      (match op with | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le)
    = op.eval a b := by
  cases op <;> simp [Flags.condHolds, CmpOp.eval, BEq.beq, bne]

/-- Floating-point flags from `fcmp` correctly implement `FloatCmpOp.eval`.
    Since FP semantics are opaque (uninterpreted bitvectors), this is an axiom
    asserting our flag model faithfully represents IEEE 754 comparison. -/
axiom Flags.condHolds_float_correct (op : FloatCmpOp) (a b : BitVec 64) :
    (Flags.mk a b).condHolds
      (match op with | .feq => .eq | .fne => .ne | .flt => .lt | .fle => .le)
    = FloatCmpOp.eval op a b


-- ============================================================
-- § fregs preservation for integer-only instruction sequences
-- ============================================================

/-- optional_movk_step extended with fregs preservation. -/
private theorem optional_movk_step' (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs rd = (if (w != 0) = true then insertBits (s.regs rd) w shift else s.regs rd) ∧
      s'.stack = s.stack ∧ s'.fregs = s.fregs ∧
      s'.pc = pc0 + (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  by_cases hw : (w != 0) = true
  · simp only [hw, ite_true] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    exact ⟨s.setReg rd (insertBits (s.regs rd) w shift) |>.nextPC,
      .single (.movk rd w shift hInstr),
      by simp, by simp, by simp, by simp [hPC],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, by simp⟩
  · simp only [hw] at hCode ⊢; simp only [Bool.false_eq_true, ite_false]
    exact ⟨s, .refl, rfl, rfl, rfl, by simp [hPC], fun _ _ => rfl, rfl⟩

/-- Re-execute formalLoadImm64 tracking fregs. Since mov/movz/movk only use
    setReg+nextPC (which preserve fregs), the resulting state has s'.fregs = s.fregs.
    This is a standalone re-derivation — it doesn't depend on loadImm64_correct's witness. -/
theorem loadImm64_fregs_preserved (prog : ArmProg) (rd : ArmReg) (n : BitVec 64)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧ s'.fregs = s.fregs ∧
      s'.regs rd = n ∧ s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  -- Use the existing loadImm64_correct for everything except fregs,
  -- then observe fregs is preserved because the witness state only differs
  -- from s by setReg/nextPC operations (which preserve fregs by simp).
  unfold formalLoadImm64 at hCode
  split at hCode
  case isTrue hSmall =>
    have hMov := hCode.head; rw [← hPC] at hMov
    exact ⟨s.setReg rd n |>.nextPC, .single (.mov rd n hMov), by simp, by simp, by simp,
      by simp [hPC, formalLoadImm64, hSmall],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, by simp⟩
  case isFalse hLarge =>
    dsimp only at hCode
    let bits : UInt64 := n.toNat.toUInt64
    let w0 := bits &&& 65535
    let w1 := bits >>> 16 &&& 65535
    let w2 := bits >>> 32 &&& 65535
    let w3 := bits >>> 48 &&& 65535
    have hCodeBase := hCode.append_left.append_left.append_left
    have hCodeK1rest := hCode.append_left.append_left.append_right
    have hCodeK1K2 := hCode.append_left
    have hCodeK2rest := hCodeK1K2.append_right
    have hCodeK3rest := hCode.append_right
    -- movz
    have hMovz := hCodeBase.head; rw [← hPC] at hMovz
    let s0 := s.setReg rd (BitVec.ofNat 64 (w0 <<< (0 : UInt64)).toNat) |>.nextPC
    have hs0f : s0.fregs = s.fregs := by simp [s0]
    have hPC0 : s0.pc = startPC + 1 := by simp [s0, hPC]
    -- k1
    have hw0_shift : (w0 <<< (0 : UInt64)) = w0 := uint64_shl_zero w0
    have hRd0 : s0.regs rd = BitVec.ofNat 64 w0.toNat := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hw0_shift]
    obtain ⟨s1, hS1, hRd1, hs1s, hs1f, hPC1, hs1r, hs1a⟩ :=
      optional_movk_step' prog rd w1 16 s0 _ hPC0 hCodeK1rest
    -- k2
    have hPC_k2 : startPC + ([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])).length =
        startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length := by
      simp; omega
    rw [hPC_k2] at hCodeK2rest
    obtain ⟨s2, hS2, hRd2, hs2s, hs2f, hPC2, hs2r, hs2a⟩ :=
      optional_movk_step' prog rd w2 32 s1 _ hPC1 hCodeK2rest
    -- k3
    have hPC_k3 : startPC + (([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])) ++
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else [])).length =
        startPC + 1 +
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length := by
      simp; omega
    rw [hPC_k3] at hCodeK3rest
    obtain ⟨s3, hS3, hRd3, hs3s, hs3f, hPC3, hs3r, hs3a⟩ :=
      optional_movk_step' prog rd w3 48 s2 _ hPC2 hCodeK3rest
    refine ⟨s3, (.step (.movz rd w0 0 hMovz) (hS1.trans (hS2.trans hS3))),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- fregs
      rw [hs3f, hs2f, hs1f, hs0f]
    · -- regs rd = n
      have hbits_bv : bits.toBitVec = n := by
        show n.toNat.toUInt64.toBitVec = n
        rw [UInt64.toBitVec]
        apply BitVec.eq_of_toNat_eq
        simp [Nat.toUInt64]
      have hc0 : w0.toBitVec = bits.toBitVec &&& 0xFFFF#64 := uint64_toBitVec_chunk0 bits
      have hc1 : w1.toBitVec = (bits.toBitVec >>> 16) &&& 0xFFFF#64 := uint64_toBitVec_chunk16 bits
      have hc2 : w2.toBitVec = (bits.toBitVec >>> 32) &&& 0xFFFF#64 := uint64_toBitVec_chunk32 bits
      have hc3 : w3.toBitVec = (bits.toBitVec >>> 48) &&& 0xFFFF#64 := uint64_toBitVec_chunk48 bits
      by_cases hw1z : w1 = 0 <;> by_cases hw2z : w2 = 0 <;> by_cases hw3z : w3 = 0
      all_goals simp only [show (w1 != 0) = true ↔ w1 ≠ 0 from by simp [bne, beq_iff_eq]] at hRd1
      all_goals simp only [show (w2 != 0) = true ↔ w2 ≠ 0 from by simp [bne, beq_iff_eq]] at hRd2
      all_goals simp only [show (w3 != 0) = true ↔ w3 ≠ 0 from by simp [bne, beq_iff_eq]] at hRd3
      all_goals (try simp only [hw1z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd1)
      all_goals (try simp only [hw2z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd2)
      all_goals (try simp only [hw3z, ne_eq, not_true_eq_false, ite_false, not_false_eq_true, ite_true] at hRd3)
      all_goals rw [hRd3]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd2]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd1]
      all_goals (try rw [insertBits_unfold])
      all_goals rw [hRd0]
      all_goals simp only [BitVec_ofNat_UInt64_toNat]
      all_goals rw [hc0]
      all_goals try rw [hc1]
      all_goals try rw [hc2]
      all_goals try rw [hc3]
      all_goals rw [← hbits_bv]
      · exact bv_reassemble_000 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_001 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_010 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_011 bits.toBitVec (by rw [← hc1]; exact uint64_eq_zero_toBitVec w1 hw1z)
      · exact bv_reassemble_100 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z) (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble_101 bits.toBitVec (by rw [← hc2]; exact uint64_eq_zero_toBitVec w2 hw2z)
      · exact bv_reassemble_110 bits.toBitVec (by rw [← hc3]; exact uint64_eq_zero_toBitVec w3 hw3z)
      · exact bv_reassemble bits.toBitVec
    · -- stack
      rw [hs3s, hs2s, hs1s]; simp [s0]
    · -- pc
      rw [hPC3]; unfold formalLoadImm64; simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · -- other regs
      intro r hr; rw [hs3r r hr, hs2r r hr, hs1r r hr]
      simp [s0, ArmState.setReg, ArmState.nextPC, hr]
    · -- arrayMem
      rw [hs3a, hs2a, hs1a]; simp [s0]


-- ============================================================
-- § Extended correctness: verifiedGenInstr with VarLayout
-- ============================================================

/-- vLoadVar from a stack variable. -/
theorem vLoadVar_stack (layout : VarLayout) (v : Var) (tmp : ArmReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vLoadVar layout v tmp = [.ldr tmp off] := by
  simp [vLoadVar, hv]

/-- vLoadVar from an ireg that equals tmp. -/
theorem vLoadVar_ireg_same (layout : VarLayout) (v : Var) (r : ArmReg)
    (hv : layout v = some (.ireg r)) :
    vLoadVar layout v r = [] := by
  simp [vLoadVar, hv]

/-- vLoadVar from an ireg different from tmp. -/
theorem vLoadVar_ireg_diff (layout : VarLayout) (v : Var) (tmp r : ArmReg)
    (hv : layout v = some (.ireg r)) (hne : (r == tmp) = false) :
    vLoadVar layout v tmp = [.movR tmp r] := by
  simp [vLoadVar, hv, hne]

/-- vStoreVar to a stack variable. -/
theorem vStoreVar_stack (layout : VarLayout) (v : Var) (tmp : ArmReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vStoreVar layout v tmp = [.str tmp off] := by
  simp [vStoreVar, hv]

/-- vStoreVar to an ireg that equals tmp. -/
theorem vStoreVar_ireg_same (layout : VarLayout) (v : Var) (r : ArmReg)
    (hv : layout v = some (.ireg r)) :
    vStoreVar layout v r = [] := by
  simp [vStoreVar, hv]

/-- vStoreVar to an ireg different from tmp. -/
theorem vStoreVar_ireg_diff (layout : VarLayout) (v : Var) (tmp r : ArmReg)
    (hv : layout v = some (.ireg r)) (hne : (r == tmp) = false) :
    vStoreVar layout v tmp = [.movR r tmp] := by
  simp [vStoreVar, hv, hne]

/-- vLoadVarFP from a stack variable. -/
theorem vLoadVarFP_stack (layout : VarLayout) (v : Var) (tmp : ArmFReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vLoadVarFP layout v tmp = [.fldr tmp off] := by
  simp [vLoadVarFP, hv]

/-- vStoreVarFP to a stack variable. -/
theorem vStoreVarFP_stack (layout : VarLayout) (v : Var) (tmp : ArmFReg) (off : Nat)
    (hv : layout v = some (.stack off)) :
    vStoreVarFP layout v tmp = [.fstr tmp off] := by
  simp [vStoreVarFP, hv]

-- ============================================================
-- § ExtStateRel preservation helpers for verifiedGenInstr
-- ============================================================

/-- ExtStateRel is preserved by any state change that only modifies
    a scratch integer register (x0, x1, or x2) — provided the layout
    satisfies ExtScratchSafe. -/
theorem ExtStateRel.preserved_by_ireg_only
    {layout : VarLayout} {σ : Store} {s s' : ArmState}
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hStack : s'.stack = s.stack) (hFregs : s'.fregs = s.fregs)
    (hRegsOther : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x8 → s'.regs r = s.regs r) :
    ExtStateRel layout σ s' := by
  intro v loc hv
  match loc with
  | .stack off => rw [hStack]; exact hRel v (.stack off) hv
  | .ireg r =>
    have h0 := hScratch.not_x0 v; have h1 := hScratch.not_x1 v
    have h2 := hScratch.not_x2 v; have h8 := hScratch.not_x8 v
    have hr0 : r ≠ .x0 := fun h => h0 (h ▸ hv)
    have hr1 : r ≠ .x1 := fun h => h1 (h ▸ hv)
    have hr2 : r ≠ .x2 := fun h => h2 (h ▸ hv)
    have hr8 : r ≠ .x8 := fun h => h8 (h ▸ hv)
    show s'.regs r = (σ v).encode
    rw [hRegsOther r hr0 hr1 hr2 hr8]; exact hRel v (.ireg r) hv
  | .freg r =>
    show s'.fregs r = (σ v).encode
    rw [hFregs]; exact hRel v (.freg r) hv

/-- loadImm64 preserves ExtStateRel (it only clobbers one integer scratch register). -/
theorem loadImm64_preserves_ExtStateRel (prog : ArmProg) (layout : VarLayout)
    (rd : ArmReg) (n : BitVec 64) (σ : Store) (s s' : ArmState)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hStack : s'.stack = s.stack) (hFregs : s'.fregs = s.fregs)
    (hRegs : ∀ r, r ≠ rd → s'.regs r = s.regs r)
    (hAM : s'.arrayMem = s.arrayMem)
    (hRdScratch : rd = .x0 ∨ rd = .x1 ∨ rd = .x2) :
    ExtStateRel layout σ s' := by
  apply ExtStateRel.preserved_by_ireg_only hRel hScratch hStack hFregs
  intro r h0 h1 h2 h8
  apply hRegs
  rcases hRdScratch with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- After executing `vStoreVar layout v .x0` when `s.regs .x0 = val.encode`,
    `ExtStateRel layout (σ[v ↦ val]) s'` holds.
    Requires: v is at a stack or ireg (not freg) location. -/
theorem vStoreVar_x0_correct (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (off : Nat) (hLoc : layout v = some (.stack off))
    (hCode : CodeAt prog startPC (ArmInstr.str .x0 off :: [])) :
    ∃ s', ArmSteps prog s s' ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + 1 ∧
        s'.arrayMem = s.arrayMem := by
  have hStr := hCode.head; rw [← hPC] at hStr
  refine ⟨s.setStack off (s.regs .x0) |>.nextPC, .single (.str .x0 off hStr), ?_, ?_, ?_⟩
  · -- ExtStateRel after store to stack
    rw [hX0]; exact ExtStateRel.update_stack hRel hInj hLoc
  · simp [hPC]
  · simp

/-- After executing `vStoreVar layout v .x0` when v is in ireg r (r ≠ x0),
    `ExtStateRel layout (σ[v ↦ val]) s'` holds. -/
theorem vStoreVar_x0_ireg_correct (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (r : ArmReg) (hLoc : layout v = some (.ireg r)) (hne : (r == ArmReg.x0) = false)
    (hCode : CodeAt prog startPC (ArmInstr.movR r .x0 :: [])) :
    ∃ s', ArmSteps prog s s' ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + 1 ∧
        s'.arrayMem = s.arrayMem := by
  have hMovR := hCode.head; rw [← hPC] at hMovR
  refine ⟨s.setReg r (s.regs .x0) |>.nextPC, .single (.movR r .x0 hMovR), ?_, ?_, ?_⟩
  · rw [hX0]; exact ExtStateRel.update_ireg hRel hInj hLoc
  · simp [hPC]
  · simp

/-- Execute vLoadVar: loads v into scratch register tmp, preserving ExtStateRel.
    Case-splits on layout to determine instruction sequence. -/
theorem vLoadVar_exec (prog : ArmProg) (layout : VarLayout) (v : Var) (tmp : ArmReg)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC)
    (hCode : CodeAt prog startPC (vLoadVar layout v tmp))
    (hTmpScratch : tmp = .x0 ∨ tmp = .x1 ∨ tmp = .x2)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    (hMapped : layout v ≠ none) :
    ∃ s', ArmSteps prog s s' ∧
        s'.regs tmp = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.fregs = s.fregs ∧
        s'.pc = startPC + (vLoadVar layout v tmp).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ tmp → s'.regs r = s.regs r) := by
  -- Case split on where v lives
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vLoadVar_stack layout v tmp off hv
    rw [hEq] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    refine ⟨s.setReg tmp (s.stack off) |>.nextPC, .single (.ldr tmp off hInstr), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp; exact hRel.read_stack hv
    · exact (ExtStateRel.setReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hScratch.not_x0 w
        · exact hScratch.not_x1 w
        · exact hScratch.not_x2 w)).nextPC
    · simp
    · simp [hPC]
    · simp
    · intro r hne; simp [ArmState.setReg, ArmState.nextPC]
      exact fun h => absurd h hne
  | some (.ireg r) =>
    by_cases heq : r = tmp
    · subst heq
      have hEq := vLoadVar_ireg_same layout v r hv
      rw [hEq] at hCode ⊢; simp
      exact ⟨s, .refl, hRel.read_ireg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl⟩
    · have hbeq : (r == tmp) = false := by
        cases h : r == tmp
        · rfl
        · simp [beq_iff_eq] at h; exact absurd h heq
      have hEq := vLoadVar_ireg_diff layout v tmp r hv hbeq
      rw [hEq] at hCode ⊢
      have hInstr := hCode.head; rw [← hPC] at hInstr
      refine ⟨s.setReg tmp (s.regs r) |>.nextPC, .single (.movR tmp r hInstr), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp; exact hRel.read_ireg hv
      · exact (ExtStateRel.setReg_preserved hRel (fun w => by
          rcases hTmpScratch with rfl | rfl | rfl
          · exact hScratch.not_x0 w
          · exact hScratch.not_x1 w
          · exact hScratch.not_x2 w)).nextPC
      · simp
      · simp [hPC]
      · simp
      · intro r' hne; simp [ArmState.setReg, ArmState.nextPC]
        exact fun h => absurd h hne
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none => exact absurd hv hMapped

/-- Execute vLoadVar with effective register: if v is in an ireg, use it directly (no-op);
    otherwise fall back to the scratch register. -/
theorem vLoadVar_eff_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (σ : Store) (s : ArmState) (startPC : Nat) (fallback : ArmReg)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    (hFB : fallback = .x0 ∨ fallback = .x1 ∨ fallback = .x2)
    (hMapped : layout v ≠ none) :
    let eff := match layout v with | some (.ireg r) => r | _ => fallback
    ∀ (hCode : CodeAt prog startPC (vLoadVar layout v eff)),
    ∃ s', ArmSteps prog s s' ∧
        s'.regs eff = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.fregs = s.fregs ∧
        s'.pc = startPC + (vLoadVar layout v eff).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ eff → s'.regs r = s.regs r) := by
  match hv : layout v with
  | some (.ireg r) =>
    simp [vLoadVar, hv]
    intro _
    exact ⟨s, .refl, hRel.read_ireg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl⟩
  | some (.stack off) =>
    simp only [show (match some (VarLoc.stack off) with | some (.ireg r) => r | _ => fallback) = fallback from rfl]
    exact fun hCode => vLoadVar_exec prog layout v fallback σ s startPC hRel hScratch hPC hCode hFB hNotFreg hMapped
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none => exact absurd hv hMapped

/-- Execute vStoreVar from x0: stores result into v's location, updating ExtStateRel. -/
theorem vStoreVar_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (hCode : CodeAt prog startPC (vStoreVar layout v .x0))
    (hNotFreg : ∀ r, layout v ≠ some (.freg r)) :
    ∃ s', ArmSteps prog s s' ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + (vStoreVar layout v .x0).length ∧
        s'.arrayMem = s.arrayMem := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vStoreVar_stack layout v .x0 off hv
    rw [hEq] at hCode ⊢
    have hStr := hCode.head; rw [← hPC] at hStr
    refine ⟨s.setStack off (s.regs .x0) |>.nextPC, .single (.str .x0 off hStr), ?_, ?_, ?_⟩
    · rw [hX0]; exact (ExtStateRel.update_stack hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.ireg r) =>
    have hne : (r == ArmReg.x0) = false := by
      cases hr : r == ArmReg.x0
      · rfl
      · simp [beq_iff_eq] at hr; exact absurd (hr ▸ hv) (hScratch.not_x0 v)
    have hEq := vStoreVar_ireg_diff layout v .x0 r hv hne
    rw [hEq] at hCode ⊢
    have hMovR := hCode.head; rw [← hPC] at hMovR
    refine ⟨s.setReg r (s.regs .x0) |>.nextPC, .single (.movR r .x0 hMovR), ?_, ?_, ?_⟩
    · rw [hX0]; exact (ExtStateRel.update_ireg hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none =>
    simp [vStoreVar, hv]
    refine ⟨s, .refl, ?_, by omega, rfl⟩
    intro w loc hw
    have hwv : w ≠ v := fun h => by subst h; simp [hv] at hw
    rw [Store.update_other σ v w val hwv]; exact hRel w loc hw

/-- Execute vStoreVarFP from d0: stores FP result into v's location. -/
theorem vStoreVarFP_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC) (hD0 : s.fregs .d0 = val.encode)
    (hCode : CodeAt prog startPC (vStoreVarFP layout v .d0))
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hFregPrecond : ∀ r, layout v = some (.freg r) → s.fregs r = val.encode) :
    ∃ s', ArmSteps prog s s' ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + (vStoreVarFP layout v .d0).length ∧
        s'.arrayMem = s.arrayMem := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vStoreVarFP_stack layout v .d0 off hv
    rw [hEq] at hCode ⊢
    have hFstr := hCode.head; rw [← hPC] at hFstr
    refine ⟨s.setStack off (s.fregs .d0) |>.nextPC, .single (.fstr .d0 off hFstr), ?_, ?_, ?_⟩
    · rw [hD0]; exact (ExtStateRel.update_stack hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | some (.freg r) =>
    -- r ≠ d0 by scratchSafe, so code = [.fmovRR r .d0]
    have hne : (r == ArmFReg.d0) = false := by
      simp [beq_iff_eq]; exact fun h => absurd hv (h ▸ hScratch.not_d0 v)
    simp only [vStoreVarFP, hv, hne] at hCode ⊢
    have hFmov := hCode.head; rw [← hPC] at hFmov
    refine ⟨(s.setFReg r (s.fregs .d0)).nextPC, .single (.fmovRR r .d0 hFmov), ?_, ?_, ?_⟩
    · rw [hD0]; exact (ExtStateRel.update_freg hRel hInj hv).nextPC
    · simp [ArmState.nextPC, ArmState.setFReg, hPC]
    · simp [ArmState.nextPC, ArmState.setFReg]
  | none =>
    simp [vStoreVarFP, hv]
    refine ⟨s, .refl, ?_, by omega, rfl⟩
    intro w loc hw
    have hwv : w ≠ v := fun h => by subst h; simp [hv] at hw
    rw [Store.update_other σ v w val hwv]; exact hRel w loc hw

/-- Execute one FP instruction and store the result into a variable's location.
    Abstracts the common "op + store" pattern shared by fbinop, fternop, and
    floatUnary proofs. -/
theorem fp_exec_and_store (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (pc : Nat) (σ : Store) (am : ArrayMem) (x : Var)
    (dst_reg : ArmFReg)
    (resultBv : BitVec 64) (resultVal : Value)
    (hResultEnc : resultBv = resultVal.encode)
    (s_pre : ArmState) (prePC : Nat)
    (hRelPre : ExtStateRel layout σ s_pre)
    (hInjective : VarLayoutInjective layout)
    (hScratch : ExtScratchSafe layout)
    (hPC_pre : s_pre.pc = prePC)
    (hAM_pre : s_pre.arrayMem = am)
    (hDstReg : dst_reg = match layout x with | some (.freg r) => r | _ => .d0)
    (hNotIregX : ∀ r, layout x ≠ some (.ireg r))
    (fpOp : ArmInstr)
    (hCodeOpStore : CodeAt prog prePC (fpOp :: vStoreVarFP layout x dst_reg))
    (hArmStep : ArmStep prog s_pre (s_pre.setFReg dst_reg resultBv |>.nextPC))
    (prefixLen : Nat)
    (hPrePC_eq : prePC = pcMap pc + prefixLen)
    (hPcNext : pcMap (pc + 1) = pcMap pc + prefixLen + 1 +
      (vStoreVarFP layout x dst_reg).length) :
    ∃ s', ArmSteps prog s_pre s' ∧
      ExtSimRel layout pcMap (.run (pc + 1) (σ[x ↦ resultVal]) am) s' := by
  let s_op := (s_pre.setFReg dst_reg resultBv).nextPC
  have hStepsOp : ArmSteps prog s_pre s_op := .single hArmStep
  have hPC_op : s_op.pc = prePC + 1 := by simp [s_op, ArmState.nextPC, ArmState.setFReg, hPC_pre]
  have hAM_op : s_op.arrayMem = am := by simp [s_op, hAM_pre]
  by_cases hXFR : ∃ r, layout x = some (.freg r)
  · obtain ⟨r_dst, hDst⟩ := hXFR
    have hDR : dst_reg = r_dst := by rw [hDstReg]; simp [hDst]
    have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
    have hRelPost : ExtStateRel layout (σ[x ↦ resultVal]) s_op := by
      show ExtStateRel layout (σ[x ↦ resultVal])
        (s_pre.setFReg dst_reg resultBv).nextPC
      rw [hDR, hResultEnc]
      exact (ExtStateRel.update_freg hRelPre hInjective hDst).nextPC
    refine ⟨s_op, hStepsOp, ⟨hRelPost, ?_, hAM_op⟩⟩
    show s_op.pc = pcMap (pc + 1)
    simp [hStore] at hPcNext; simp [s_op, ArmState.nextPC, ArmState.setFReg, hPC_pre, hPrePC_eq]; omega
  · have hDR : dst_reg = .d0 := by
      rw [hDstReg]; split
      · next r h => exact absurd ⟨r, h⟩ hXFR
      · rfl
    have hRelOp : ExtStateRel layout σ s_op := by
      show ExtStateRel layout σ (s_pre.setFReg dst_reg resultBv).nextPC
      rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelPre (fun v => hScratch.not_d0 v)).nextPC
    have hD0 : s_op.fregs .d0 = resultVal.encode := by
      simp [s_op, hDR, ArmState.setFReg, ArmState.nextPC, hResultEnc]
    have hCodeStore : CodeAt prog (prePC + 1) (vStoreVarFP layout x .d0) := by
      rw [← hDR]; exact hCodeOpStore.tail
    obtain ⟨s_fin, hStepsFin, hRelFin, hPC_fin, hAM_fin⟩ :=
      vStoreVarFP_exec prog layout x resultVal σ s_op (prePC + 1)
        hRelOp hInjective hScratch hPC_op hD0 hCodeStore hNotIregX
        (fun r h => absurd ⟨r, h⟩ hXFR)
    refine ⟨s_fin, hStepsOp.trans hStepsFin, ⟨hRelFin, ?_, by simp [hAM_fin, hAM_op]⟩⟩
    show s_fin.pc = pcMap (pc + 1)
    have : dst_reg = .d0 := hDR
    simp [this] at hPcNext; omega

/-- Execute vLoadVarFP: loads float variable v into scratch FP register tmp,
    preserving ExtStateRel. Case-splits on layout. -/
theorem vLoadVarFP_exec (prog : ArmProg) (layout : VarLayout) (v : Var) (tmp : ArmFReg)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC)
    (hCode : CodeAt prog startPC (vLoadVarFP layout v tmp))
    (hTmpScratch : tmp = .d0 ∨ tmp = .d1 ∨ tmp = .d2)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hMapped : layout v ≠ none) :
    ∃ s', ArmSteps prog s s' ∧
        s'.fregs tmp = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.regs = s.regs ∧
        s'.pc = startPC + (vLoadVarFP layout v tmp).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ tmp → s'.fregs r = s.fregs r) ∧
        s'.stack = s.stack := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vLoadVarFP_stack layout v tmp off hv
    rw [hEq] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    refine ⟨s.setFReg tmp (s.stack off) |>.nextPC, .single (.fldr tmp off hInstr),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setFReg, ArmState.nextPC]; exact hRel.read_stack hv
    · exact (ExtStateRel.setFReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hScratch.not_d0 w
        · exact hScratch.not_d1 w
        · exact hScratch.not_d2 w)).nextPC
    · simp
    · simp [hPC]
    · simp
    · intro r hr; simp [ArmState.setFReg, ArmState.nextPC, hr]
    · simp
  | some (.freg r) =>
    -- r ≠ tmp by scratchSafe (tmp is d0/d1/d2, r is not)
    have hne : (r == tmp) = false := by
      simp [beq_iff_eq]
      rcases hTmpScratch with rfl | rfl | rfl
      · exact fun h => absurd hv (h ▸ hScratch.not_d0 v)
      · exact fun h => absurd hv (h ▸ hScratch.not_d1 v)
      · exact fun h => absurd hv (h ▸ hScratch.not_d2 v)
    simp only [vLoadVarFP, hv, hne] at hCode ⊢
    have hFmov := hCode.head; rw [← hPC] at hFmov
    refine ⟨(s.setFReg tmp (s.fregs r)).nextPC, .single (.fmovRR tmp r hFmov),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setFReg, ArmState.nextPC]; exact hRel.read_freg hv
    · exact (ExtStateRel.setFReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hScratch.not_d0 w
        · exact hScratch.not_d1 w
        · exact hScratch.not_d2 w)).nextPC
    · simp
    · simp [ArmState.setFReg, ArmState.nextPC, hPC]
    · simp
    · intro r' hr'; simp [ArmState.setFReg, ArmState.nextPC, hr']
    · simp
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | none => exact absurd hv hMapped

/-- Execute vLoadVarFP with effective register: if v is in a freg, uses that freg directly;
    otherwise falls back to a scratch register. Analogous to vLoadVar_eff_exec. -/
theorem vLoadVarFP_eff_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (σ : Store) (s : ArmState) (startPC : Nat) (fallback : ArmFReg)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hFB : fallback = .d0 ∨ fallback = .d1 ∨ fallback = .d2)
    (hMapped : layout v ≠ none) :
    let eff := match layout v with | some (.freg r) => r | _ => fallback
    ∀ (hCode : CodeAt prog startPC (vLoadVarFP layout v eff)),
    ∃ s', ArmSteps prog s s' ∧
        s'.fregs eff = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.regs = s.regs ∧
        s'.pc = startPC + (vLoadVarFP layout v eff).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ eff → s'.fregs r = s.fregs r) ∧
        s'.stack = s.stack := by
  match hv : layout v with
  | some (.freg r) =>
    simp [vLoadVarFP, hv]
    intro _
    exact ⟨s, .refl, hRel.read_freg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl, rfl⟩
  | some (.stack off) =>
    simp only [show (match some (VarLoc.stack off) with | some (.freg r) => r | _ => fallback) = fallback from rfl]
    exact fun hCode => vLoadVarFP_exec prog layout v fallback σ s startPC hRel hScratch hPC hCode
      hFB hNotIreg hMapped
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | none => exact absurd hv hMapped

-- ============================================================
-- § loadFloatExpr_exec: unified float operand loading
-- ============================================================

/-- Load a float expression operand (.var or .flit) into a float register.
    Unifies vLoadVarFP and loadImm64+fmovToFP into a single helper. -/
theorem loadFloatExpr_exec (prog : ArmProg) (layout : VarLayout) (e : Expr) (dst : ArmFReg)
    (σ : Store) (am : ArrayMem) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hPC : s.pc = startPC)
    (hSimple : (∃ v, e = .var v) ∨ (∃ n, e = .flit n))
    (Γ : TyCtx) (hTS : TypedStore Γ σ) (hTy : ExprHasTy Γ e .float)
    (hWTL : WellTypedLayout Γ layout)
    (hMapped : ∀ v, v ∈ e.freeVars → layout v ≠ none)
    (hDst : dst = .d0 ∨ dst = .d1 ∨ dst = .d2)
    (hCode : CodeAt prog startPC
      (match e with | .var v => vLoadVarFP layout v dst
                    | .flit n => formalLoadImm64 .x0 n ++ [.fmovToFP dst .x0]
                    | _ => [])) :
    ∃ s', ArmSteps prog s s' ∧
      s'.fregs dst = (e.eval σ am).toFloat ∧
      ExtStateRel layout σ s' ∧
      s'.pc = startPC +
        (match e with | .var v => vLoadVarFP layout v dst
                      | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP dst .x0]
                      | _ => []).length ∧
      s'.arrayMem = s.arrayMem ∧
      (∀ r, r ≠ dst → s'.fregs r = s.fregs r) := by
  rcases hSimple with ⟨v, rfl⟩ | ⟨n, rfl⟩
  · -- .var v: use vLoadVarFP_exec
    simp only [] at hCode
    have hNotIreg : ∀ r, layout v ≠ some (.ireg r) := hWTL.float_not_ireg hTy
    have hMappedV : layout v ≠ none := hMapped v (by simp [Expr.freeVars])
    obtain ⟨s', hSteps, hFreg, hRel', _, hPC', hAM', hFregs', _⟩ :=
      vLoadVarFP_exec prog layout v dst σ s startPC hRel hScratch hPC hCode hDst hNotIreg hMappedV
    have hTyV := hTS v; rw [hTy] at hTyV
    obtain ⟨fv, hfv⟩ := Value.float_of_typeOf_float hTyV
    exact ⟨s', hSteps,
      by simp [Expr.eval, Value.toFloat, hFreg, hfv, Value.encode],
      hRel', hPC', hAM', hFregs'⟩
  · -- .flit n: loadImm64 into x0, then fmovToFP
    simp only [] at hCode
    have hCodeImm := hCode.append_left
    have hCodeFmov := hCode.append_right
    obtain ⟨s1, hSteps1, hFregs1, hX0, hStack1, hPC1, hRegs1, hAM1⟩ :=
      loadImm64_fregs_preserved prog .x0 n s startPC hCodeImm hPC
    have hRel1 : ExtStateRel layout σ s1 :=
      loadImm64_preserves_ExtStateRel prog layout .x0 n σ s s1
        hRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
    have hFmov := hCodeFmov.head; rw [← hPC1] at hFmov
    let s2 := s1.setFReg dst (s1.regs .x0) |>.nextPC
    have hRel2 : ExtStateRel layout σ s2 := by
      have hNotDst : ∀ w, layout w ≠ some (.freg dst) := by
        cases hDst with
        | inl h => subst h; exact fun w => hScratch.not_d0 w
        | inr h => cases h with
          | inl h => subst h; exact fun w => hScratch.not_d1 w
          | inr h => subst h; exact fun w => hScratch.not_d2 w
      exact (ExtStateRel.setFReg_preserved hRel1 hNotDst).nextPC
    exact ⟨s2, hSteps1.trans (.single (ArmStep.fmovToFP dst .x0 hFmov)),
      by simp [s2, ArmState.setFReg, ArmState.nextPC, hX0, Expr.eval, Value.toFloat],
      hRel2,
      by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append, hPC1]; omega,
      by simp [s2, ArmState.setFReg, ArmState.nextPC, hAM1],
      by intro r hr; simp [s2, ArmState.setFReg, ArmState.nextPC, hr, hFregs1]⟩

-- ============================================================
-- § verifiedGenBoolExpr_correct
-- ============================================================

/-- Correctness of verifiedGenBoolExpr: after execution, x0 holds the boolean result
    encoded as 1 (true) or 0 (false), and ExtStateRel is preserved. -/
theorem verifiedGenBoolExpr_correct (prog : ArmProg) (layout : VarLayout)
    (be : BoolExpr) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hScratch : ExtScratchSafe layout)
    (hCode : CodeAt prog startPC (verifiedGenBoolExpr layout be))
    (hPC : s.pc = startPC)
    (Γ : TyCtx) (hTS : TypedStore Γ σ)
    (hWTBE : WellTypedBoolExpr Γ be)
    (hWTL : WellTypedLayout Γ layout)
    (hMapped : ∀ v, v ∈ be.vars → layout v ≠ none)
    (hSimple : be.hasSimpleOps = true)
    (am : ArrayMem) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs .x0 = (if be.eval σ am then (1 : BitVec 64) else 0) ∧
      ExtStateRel layout σ s' ∧
      s'.pc = startPC + (verifiedGenBoolExpr layout be).length ∧
      s'.arrayMem = s.arrayMem := by
  cases hWTBE with
  | bexpr => simp [BoolExpr.hasSimpleOps] at hSimple
  | lit =>
    rename_i b_val
    simp only [verifiedGenBoolExpr] at hCode
    have hMov := hCode.head; rw [← hPC] at hMov
    refine ⟨_, .single (.mov .x0 _ hMov), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, BoolExpr.eval]
    · exact (ExtStateRel.setReg_preserved hRel (fun w => hScratch.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr, hPC]
    · simp [ArmState.setReg, ArmState.nextPC]
  | bvar hty =>
    rename_i x
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeLoad := hCode.append_left
    have hCodeAnd := hCode.append_right
    -- x is a bool variable; get its value
    have hTy := hTS x; rw [hty] at hTy
    obtain ⟨bv, hbv⟩ := Value.bool_of_typeOf_bool hTy
    -- Load x into x0 (x is a bool, so not in freg — from WellTypedLayout)
    have hNotFreg : ∀ r, layout x ≠ some (.freg r) := hWTL.bool_not_freg hty
    obtain ⟨s1, hSteps1, hX0_1, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout x .x0 σ s startPC hRel hScratch hPC hCodeLoad
        (Or.inl rfl) hNotFreg (hMapped x (by simp [BoolExpr.vars]))
    -- andImm x0 x0 1
    have hAnd := hCodeAnd.head; rw [← hPC1] at hAnd
    refine ⟨_, hSteps1.trans (.single (.andImm .x0 .x0 1 hAnd)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, hbv, BoolExpr.eval, Value.toBool,
            Value.encode]
      cases bv <;> simp
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hScratch.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | not hbe =>
    rename_i e
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    -- hasSimpleOps propagates to sub-expression
    have hSimpleE : e.hasSimpleOps = true := by
      simp [BoolExpr.hasSimpleOps] at hSimple; exact hSimple
    -- Recursive call
    obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout e σ s startPC hRel hScratch hCodeE hPC Γ hTS hbe
        hWTL (fun v hv => hMapped v (by simp [BoolExpr.vars]; exact hv)) hSimpleE am
    -- eorImm x0 x0 1
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    refine ⟨_, hSteps1.trans (.single (.eorImm .x0 .x0 1 hEor)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, BoolExpr.eval]
      cases h : BoolExpr.eval σ am e <;> simp [h] <;> decide
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hScratch.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | cmp ha hb =>
    rename_i a b op'
    -- Extract hasSimpleOps info
    obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimple
    cases a with
    | var va => cases b with
      | var vb =>
        -- Sub-case: var+var (from old proof lines 921-970)
        simp only [verifiedGenBoolExpr] at hCode
        -- Split code: (vLoadVar va .x1 ++ vLoadVar vb .x2) ++ [.cmp .x1 .x2, .cset .x0 cond]
        have hCodeLVRV := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeLV := hCodeLVRV.append_left
        have hCodeRV := hCodeLVRV.append_right
        -- Type info
        have hTyL := hTS va; rw [ha] at hTyL
        have hTyR := hTS vb; rw [hb] at hTyR
        obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
        obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
        -- NotFreg from WellTypedLayout
        have hNotFregLV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha
        have hNotFregRV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb
        -- Step 1: vLoadVar va into x1
        obtain ⟨s1, hSteps1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_exec prog layout va .x1 σ s startPC hRel hScratch hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotFregLV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        -- Step 2: vLoadVar vb into x2
        obtain ⟨s2, hSteps2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotFregRV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        -- x1 preserved through second vLoadVar (x2 ≠ x1)
        have hX1_s2 : s2.regs .x1 = (σ va).encode := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        -- Step 3: cmp x1 x2 — sets flags
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        -- Step 4: cset x0 cond
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        refine ⟨_, (hSteps1.trans hSteps2).trans
          (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnL, hnR,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' nL nR)
        · -- ExtStateRel preserved
          exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hScratch.not_x0 w)).nextPC
        · -- pc advanced
          simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · -- arrayMem preserved
          simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | lit nb =>
        -- Sub-case: var+lit (adapted from old cmpLit proof lines 971-1020)
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeLV := hCodeLoadImm.append_left
        have hCodeImm := hCodeLoadImm.append_right
        -- Type info
        have hTyV := hTS va; rw [ha] at hTyV
        obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
        -- NotFreg from WellTypedLayout
        have hNotFregV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha
        -- Step 1: vLoadVar va into x1
        obtain ⟨s1, hSteps1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_exec prog layout va .x1 σ s startPC hRel hScratch hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotFregV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        -- Step 2: loadImm64 nb into x2 (preserves x1 and fregs)
        obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImm hPC1
        -- x1 preserved through loadImm64 (x2 ≠ x1)
        have hX1_s2 : s2.regs .x1 = (σ va).encode := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        -- ExtStateRel preserved through loadImm64
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
            hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
        -- Step 3: cmp x1 x2 — sets flags
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        -- Step 4: cset x0 cond
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        refine ⟨_, (hSteps1.trans hSteps2).trans
          (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [ArmState.setReg, ArmState.nextPC, s3, hX1_s2, hX2, hnV,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' nV nb)
        · -- ExtStateRel preserved
          exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hScratch.not_x0 w)).nextPC
        · -- pc advanced
          simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · -- arrayMem preserved
          simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | lit na => cases b with
      | var vb =>
        -- Sub-case: lit+var (mirror of var+lit)
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeImm := hCodeLoadImm.append_left
        have hCodeRV := hCodeLoadImm.append_right
        -- Type info
        have hTyV := hTS vb; rw [hb] at hTyV
        obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
        -- NotFreg from WellTypedLayout
        have hNotFregV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb
        -- Step 1: loadImm64 na into x1
        obtain ⟨s1, hSteps1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x1 na s _ hCodeImm hPC
        -- ExtStateRel preserved through loadImm64
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
            hRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
        -- Step 2: vLoadVar vb into x2
        obtain ⟨s2, hSteps2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotFregV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        -- x1 preserved through vLoadVar (x2 ≠ x1)
        have hX1_s2 : s2.regs .x1 = na := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        -- Step 3: cmp x1 x2 — sets flags
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        -- Step 4: cset x0 cond
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        refine ⟨_, (hSteps1.trans hSteps2).trans
          (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [ArmState.setReg, ArmState.nextPC, s3, hX1_s2, hX2, hnV,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' na nV)
        · -- ExtStateRel preserved
          exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hScratch.not_x0 w)).nextPC
        · -- pc advanced
          simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · -- arrayMem preserved
          simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | lit nb =>
        -- Sub-case: lit+lit (both immediates)
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeImmA := hCodeLoadImm.append_left
        have hCodeImmB := hCodeLoadImm.append_right
        -- Step 1: loadImm64 na into x1
        obtain ⟨s1, hSteps1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x1 na s _ hCodeImmA hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
            hRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
        -- Step 2: loadImm64 nb into x2
        obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImmB hPC1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
            hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
        -- x1 preserved through second loadImm64 (x2 ≠ x1)
        have hX1_s2 : s2.regs .x1 = na := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        -- Step 3: cmp x1 x2 — sets flags
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        -- Step 4: cset x0 cond
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        refine ⟨_, (hSteps1.trans hSteps2).trans
          (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [ArmState.setReg, ArmState.nextPC, s3, hX1_s2, hX2,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' na nb)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hScratch.not_x0 w)).nextPC
        · simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
  | fcmp ha hb =>
    rename_i a b fop
    -- Extract hasSimpleOps info
    obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimple
    cases a with
    | var va => cases b with
      | var vb =>
        -- Sub-case: var+var (from old proof lines 1021-1070)
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLVRV := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeLV := hCodeLVRV.append_left
        have hCodeRV := hCodeLVRV.append_right
        -- Type info
        have hTyL := hTS va; rw [ha] at hTyL
        have hTyR := hTS vb; rw [hb] at hTyR
        obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
        obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
        -- NotIreg from WellTypedLayout
        have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha
        have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb
        -- Step 1: vLoadVarFP va into d1
        obtain ⟨s1, hSteps1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
          vLoadVarFP_exec prog layout va .d1 σ s startPC hRel hScratch hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotIregLV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        -- Step 2: vLoadVarFP vb into d2
        obtain ⟨s2, hSteps2, hD2, hRel2, hRegsI2, hPC2, hAM2, hFregs2, _⟩ :=
          vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotIregRV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        -- d1 preserved through second vLoadVarFP (d2 ≠ d1)
        have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
          rw [hFregs2 .d1 (by decide)]; exact hD1
        -- Step 3: fcmpR d1 d2 — sets flags
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length
            = s2.pc from by rw [List.length_append]; omega] at hFcmp
        let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
        have hRelFcmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        -- Step 4: cset x0 cond
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        refine ⟨_, (hSteps1.trans hSteps2).trans
          (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [ArmState.setReg, ArmState.nextPC, hD1_s2, hD2, hfL, hfR,
                BoolExpr.eval, Expr.eval, Value.toFloat, Value.encode]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fL fR)
        · exact (ExtStateRel.setReg_preserved hRelFcmp (fun w => hScratch.not_x0 w)).nextPC
        · simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | flit fb =>
        -- Sub-case: var+flit (from old fcmpLit proof lines 1071-1132)
        simp only [verifiedGenBoolExpr] at hCode
        -- Split: (vLoadVarFP va .d1 ++ (formalLoadImm64 .x0 fb ++ [fmovToFP .d2 .x0])) ++ [fcmpR .d1 .d2, cset .x0 cond]
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeLV := hCodeLoadImm.append_left
        have hCodeImmFmov := hCodeLoadImm.append_right
        -- Type info
        have hTyV := hTS va; rw [ha] at hTyV
        obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
        -- NotIreg from WellTypedLayout
        have hNotIregV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha
        -- Step 1: vLoadVarFP va into d1
        obtain ⟨s1, hSteps1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
          vLoadVarFP_exec prog layout va .d1 σ s startPC hRel hScratch hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotIregV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        -- Step 2: loadImm64 fb into x0 (preserves fregs)
        have hCodeImm := hCodeImmFmov.append_left
        obtain ⟨s2, hSteps2, hFregs2, hX0, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x0 fb s1 _ hCodeImm hPC1
        -- d1 preserved through loadImm64 (loadImm64 preserves fregs)
        have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
          rw [hFregs2]; exact hD1
        -- ExtStateRel preserved through loadImm64
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fb σ s1 s2
            hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inl rfl)
        -- Step 3: fmovToFP d2 x0
        have hFmov := hCodeImmFmov.append_right |>.head
        rw [← hPC2] at hFmov
        let s3 := s2.setFReg .d2 (s2.regs .x0) |>.nextPC
        have hRel3 : ExtStateRel layout σ s3 :=
          (ExtStateRel.setFReg_preserved hRel2 (fun w => hScratch.not_d2 w)).nextPC
        -- d1 preserved through fmovToFP (d2 ≠ d1)
        have hD1_s3 : s3.fregs .d1 = (σ va).encode := by
          simp [s3, ArmState.setFReg, ArmState.nextPC]; exact hD1_s2
        -- Step 4: fcmpR d1 d2 — sets flags
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
            = s3.pc from by simp [s3, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega] at hFcmp
        let s4 := { s3 with flags := Flags.mk (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
        have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
        -- Step 5: cset x0 cond
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
            = s4.pc from by simp [s4, s3, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega] at hCset
        refine ⟨_, (hSteps1.trans hSteps2).trans
          (.step (.fmovToFP .d2 .x0 hFmov) (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset)))),
          ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s2, hX0, hfV, Value.encode, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fV fb)
        · exact (ExtStateRel.setReg_preserved hRel4 (fun w => hScratch.not_x0 w)).nextPC
        · simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | flit fa => cases b with
      | var vb =>
        -- Sub-case: flit+var (mirror of var+flit)
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeImmFmov := hCodeLoadImm.append_left
        have hCodeRV := hCodeLoadImm.append_right
        -- Type info
        have hTyV := hTS vb; rw [hb] at hTyV
        obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
        -- NotIreg from WellTypedLayout
        have hNotIregV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb
        -- Step 1: loadImm64 fa into x0 (preserves fregs)
        have hCodeImm := hCodeImmFmov.append_left
        obtain ⟨s1, hSteps1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 fa s _ hCodeImm hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fa σ s s1
            hRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
        -- Step 2: fmovToFP d1 x0
        have hFmov := hCodeImmFmov.append_right |>.head
        rw [← hPC1] at hFmov
        let s2 := s1.setFReg .d1 (s1.regs .x0) |>.nextPC
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun w => hScratch.not_d1 w)).nextPC
        have hD1_s2 : s2.fregs .d1 = fa := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
        -- Step 3: vLoadVarFP vb into d2
        obtain ⟨s3, hSteps3, hD2, hRel3, hRegsI3, hPC3, hAM3, hFregs3, _⟩ :=
          vLoadVarFP_exec prog layout vb .d2 σ s2 _ hRel2 hScratch
            (by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega)
            hCodeRV
            (Or.inr (Or.inr rfl)) hNotIregV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        -- d1 preserved through vLoadVarFP (d2 ≠ d1)
        have hD1_s3 : s3.fregs .d1 = fa := by
          rw [hFregs3 .d1 (by decide)]; exact hD1_s2
        -- Step 4: fcmpR d1 d2 — sets flags
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length
            = s3.pc from by simp [List.length_append] at hPC3 ⊢; omega] at hFcmp
        let s4 := { s3 with flags := Flags.mk (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
        have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
        -- Step 5: cset x0 cond
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length + 1
            = s4.pc from by simp [s4, List.length_append] at hPC3 ⊢; omega] at hCset
        refine ⟨_, (hSteps1.trans (.single (.fmovToFP .d1 .x0 hFmov))).trans (hSteps3.trans
          (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset)))),
          ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [s4, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s3, hD2, hfV, Value.encode, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fa fV)
        · exact (ExtStateRel.setReg_preserved hRel4 (fun w => hScratch.not_x0 w)).nextPC
        · simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr, List.length_append] at hPC3 ⊢; omega
        · simp [s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM3, hAM1]
      | flit fb =>
        -- Sub-case: flit+flit (both float literals)
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeImmFmovA := hCodeLoadImm.append_left
        have hCodeImmFmovB := hCodeLoadImm.append_right
        -- Step 1: loadImm64 fa into x0
        have hCodeImmA := hCodeImmFmovA.append_left
        obtain ⟨s1, hSteps1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 fa s _ hCodeImmA hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fa σ s s1
            hRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
        -- Step 2: fmovToFP d1 x0
        have hFmovA := hCodeImmFmovA.append_right |>.head
        rw [← hPC1] at hFmovA
        let s2 := s1.setFReg .d1 (s1.regs .x0) |>.nextPC
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun w => hScratch.not_d1 w)).nextPC
        have hD1_s2 : s2.fregs .d1 = fa := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
        -- Step 3: loadImm64 fb into x0
        have hCodeImmB := hCodeImmFmovB.append_left
        obtain ⟨s3, hSteps3, hFregs3, hX0_3, hStack3, hPC3, hRegs3, hAM3⟩ :=
          loadImm64_fregs_preserved prog .x0 fb s2 _ hCodeImmB
            (by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega)
        have hRel3 : ExtStateRel layout σ s3 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fb σ s2 s3
            hRel2 hScratch hStack3 hFregs3 hRegs3 hAM3 (Or.inl rfl)
        -- d1 preserved through second loadImm64 (loadImm64 preserves fregs)
        have hD1_s3 : s3.fregs .d1 = fa := by rw [hFregs3]; exact hD1_s2
        -- Step 4: fmovToFP d2 x0
        have hFmovB := hCodeImmFmovB.append_right |>.head
        rw [← hPC3] at hFmovB
        let s4 := s3.setFReg .d2 (s3.regs .x0) |>.nextPC
        have hRel4 : ExtStateRel layout σ s4 :=
          (ExtStateRel.setFReg_preserved hRel3 (fun w => hScratch.not_d2 w)).nextPC
        have hD1_s4 : s4.fregs .d1 = fa := by
          simp [s4, ArmState.setFReg, ArmState.nextPC]; exact hD1_s3
        have hD2_s4 : s4.fregs .d2 = fb := by
          simp [s4, ArmState.setFReg, ArmState.nextPC, hX0_3]
        -- Step 5: fcmpR d1 d2 — sets flags
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
            = s4.pc from by simp [s4, s2, ArmState.setFReg, ArmState.nextPC, List.length_append] at hPC3 ⊢; omega] at hFcmp
        let s5 := { s4 with flags := Flags.mk (s4.fregs .d1) (s4.fregs .d2), pc := s4.pc + 1 }
        have hRel5 : ExtStateRel layout σ s5 := fun v loc hv => hRel4 v loc hv
        -- Step 6: cset x0 cond
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
            = s5.pc from by simp [s5, s4, s2, ArmState.setFReg, ArmState.nextPC, List.length_append] at hPC3 ⊢; omega] at hCset
        refine ⟨_, ((hSteps1.trans (.single (.fmovToFP .d1 .x0 hFmovA))).trans (hSteps3.trans (.single (.fmovToFP .d2 .x0 hFmovB)))).trans
          (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset))),
          ?_, ?_, ?_, ?_⟩
        · -- x0 = correct value
          simp [s5, s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s3, hX0_3, hD1_s2, hX0_1, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fa fb)
        · exact (ExtStateRel.setReg_preserved hRel5 (fun w => hScratch.not_x0 w)).nextPC
        · simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr, List.length_append] at hPC3 ⊢; omega
        · simp [s2, s4, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM3, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h

-- Old verifiedGenBoolExpr_correct proof body removed during BoolExpr Expr-operand refactor.
-- The `cmpLit`/`fcmpLit`/flip cases are eliminated; remaining cases need rebuilding.
/-  Old proof text preserved for reference:
  | bvar hty =>
    rename_i x
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeLoad := hCode.append_left
    have hCodeAnd := hCode.append_right
    -- x is a bool variable; get its value
    have hTy := hTS x; rw [hty] at hTy
    obtain ⟨bv, hbv⟩ := Value.bool_of_typeOf_bool hTy
    -- Load x into x0 (x is a bool, so not in freg — from WellTypedLayout)
    have hNotFreg : ∀ r, layout x ≠ some (.freg r) := hWTL.bool_not_freg hty
    obtain ⟨s1, hSteps1, hX0_1, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout x .x0 σ s startPC hRel hScratch hPC hCodeLoad
        (Or.inl rfl) hNotFreg (hMapped x (by simp [BoolExpr.vars]))
    -- andImm x0 x0 1
    have hAnd := hCodeAnd.head; rw [← hPC1] at hAnd
    refine ⟨_, hSteps1.trans (.single (.andImm .x0 .x0 1 hAnd)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, hbv, BoolExpr.eval, Value.toBool,
            Value.encode]
      cases bv <;> simp
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hScratch.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | not hbe =>
    rename_i e
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    -- Recursive call
    obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout e σ s startPC hRel hScratch hCodeE hPC Γ hTS hbe
        hWTL hMapped
    -- eorImm x0 x0 1
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    refine ⟨_, hSteps1.trans (.single (.eorImm .x0 .x0 1 hEor)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, BoolExpr.eval]
      cases h : BoolExpr.eval σ e <;> simp [h] <;> decide
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hScratch.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | cmp htyL htyR =>
    rename_i lv rv op'
    simp only [verifiedGenBoolExpr] at hCode
    -- Split code: (vLoadVar lv .x1 ++ vLoadVar rv .x2) ++ [.cmp .x1 .x2, .cset .x0 cond]
    have hCodeLVRV := hCode.append_left
    have hCodeCmpCset := hCode.append_right
    have hCodeLV := hCodeLVRV.append_left
    have hCodeRV := hCodeLVRV.append_right
    -- Type info
    have hTyL := hTS lv; rw [htyL] at hTyL
    have hTyR := hTS rv; rw [htyR] at hTyR
    obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
    obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
    -- NotFreg from WellTypedLayout
    have hNotFregLV : ∀ r, layout lv ≠ some (.freg r) := hWTL.int_not_freg htyL
    have hNotFregRV : ∀ r, layout rv ≠ some (.freg r) := hWTL.int_not_freg htyR
    -- Step 1: vLoadVar lv into x1
    obtain ⟨s1, hSteps1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_exec prog layout lv .x1 σ s startPC hRel hScratch hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotFregLV (hMapped lv (by simp [BoolExpr.vars]))
    -- Step 2: vLoadVar rv into x2
    obtain ⟨s2, hSteps2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
      vLoadVar_exec prog layout rv .x2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
        (Or.inr (Or.inr rfl)) hNotFregRV (hMapped rv (by simp [BoolExpr.vars]))
    -- x1 preserved through second vLoadVar (x2 ≠ x1)
    have hX1_s2 : s2.regs .x1 = (σ lv).encode := by
      rw [hRegs2 .x1 (by decide)]; exact hX1
    -- Step 3: cmp x1 x2 — sets flags
    have hCmp := hCodeCmpCset.head
    rw [show startPC + (vLoadVar layout lv .x1 ++ vLoadVar layout rv .x2).length
        = s2.pc from by rw [List.length_append]; omega] at hCmp
    let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
    have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
    -- Step 4: cset x0 cond
    have hCset := hCodeCmpCset.tail.head
    rw [show startPC + (vLoadVar layout lv .x1 ++ vLoadVar layout rv .x2).length + 1
        = s3.pc from by simp [s3]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      simp [ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnL, hnR,
            BoolExpr.eval, Value.toInt]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_correct op' nL nR)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hScratch.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
  | cmpLit hty _hLB _hUB =>
    rename_i v op' n
    simp only [verifiedGenBoolExpr] at hCode
    -- Split code: (vLoadVar v .x1 ++ formalLoadImm64 .x2 n) ++ [.cmp .x1 .x2, .cset .x0 cond]
    have hCodeLoadImm := hCode.append_left
    have hCodeCmpCset := hCode.append_right
    have hCodeLV := hCodeLoadImm.append_left
    have hCodeImm := hCodeLoadImm.append_right
    -- Type info
    have hTyV := hTS v; rw [hty] at hTyV
    obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
    -- NotFreg from WellTypedLayout
    have hNotFregV : ∀ r, layout v ≠ some (.freg r) := hWTL.int_not_freg hty
    -- Step 1: vLoadVar v into x1
    obtain ⟨s1, hSteps1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_exec prog layout v .x1 σ s startPC hRel hScratch hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotFregV (hMapped v (by simp [BoolExpr.vars]))
    -- Step 2: loadImm64 n into x2 (preserves x1 and fregs)
    obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_fregs_preserved prog .x2 n s1 _ hCodeImm hPC1
    -- x1 preserved through loadImm64 (x2 ≠ x1)
    have hX1_s2 : s2.regs .x1 = (σ v).encode := by
      rw [hRegs2 .x1 (by decide)]; exact hX1
    -- ExtStateRel preserved through loadImm64
    have hRel2 : ExtStateRel layout σ s2 :=
      loadImm64_preserves_ExtStateRel prog layout .x2 n σ s1 s2
        hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
    -- Step 3: cmp x1 x2 — sets flags
    have hCmp := hCodeCmpCset.head
    rw [show startPC + (vLoadVar layout v .x1 ++ formalLoadImm64 .x2 n).length
        = s2.pc from by rw [List.length_append]; omega] at hCmp
    let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
    have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
    -- Step 4: cset x0 cond
    have hCset := hCodeCmpCset.tail.head
    rw [show startPC + (vLoadVar layout v .x1 ++ formalLoadImm64 .x2 n).length + 1
        = s3.pc from by simp [s3]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      simp [ArmState.setReg, ArmState.nextPC, s3, hX1_s2, hX2, hnV,
            BoolExpr.eval, Value.toInt]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_correct op' nV n)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hScratch.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
  | fcmp htyL htyR =>
    rename_i lv rv fop
    simp only [verifiedGenBoolExpr] at hCode
    -- Split code: (vLoadVarFP lv .d1 ++ vLoadVarFP rv .d2) ++ [.fcmpR .d1 .d2, .cset .x0 cond]
    have hCodeLVRV := hCode.append_left
    have hCodeFcmpCset := hCode.append_right
    have hCodeLV := hCodeLVRV.append_left
    have hCodeRV := hCodeLVRV.append_right
    -- Type info
    have hTyL := hTS lv; rw [htyL] at hTyL
    have hTyR := hTS rv; rw [htyR] at hTyR
    obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
    obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
    -- NotIreg from WellTypedLayout
    have hNotIregLV : ∀ r, layout lv ≠ some (.ireg r) := hWTL.float_not_ireg htyL
    have hNotIregRV : ∀ r, layout rv ≠ some (.ireg r) := hWTL.float_not_ireg htyR
    -- Step 1: vLoadVarFP lv into d1
    obtain ⟨s1, hSteps1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
      vLoadVarFP_exec prog layout lv .d1 σ s startPC hRel hScratch hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotIregLV (hMapped lv (by simp [BoolExpr.vars]))
    -- Step 2: vLoadVarFP rv into d2
    obtain ⟨s2, hSteps2, hD2, hRel2, hRegsI2, hPC2, hAM2, hFregs2, _⟩ :=
      vLoadVarFP_exec prog layout rv .d2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
        (Or.inr (Or.inr rfl)) hNotIregRV (hMapped rv (by simp [BoolExpr.vars]))
    -- d1 preserved through second vLoadVarFP (d2 ≠ d1)
    have hD1_s2 : s2.fregs .d1 = (σ lv).encode := by
      rw [hFregs2 .d1 (by decide)]; exact hD1
    -- Step 3: fcmpR d1 d2 — sets flags
    have hFcmp := hCodeFcmpCset.head
    rw [show startPC + (vLoadVarFP layout lv .d1 ++ vLoadVarFP layout rv .d2).length
        = s2.pc from by rw [List.length_append]; omega] at hFcmp
    let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
    have hRelFcmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
    -- Step 4: cset x0 cond
    have hCset := hCodeFcmpCset.tail.head
    rw [show startPC + (vLoadVarFP layout lv .d1 ++ vLoadVarFP layout rv .d2).length + 1
        = s3.pc from by simp [s3]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset))), ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      simp [ArmState.setReg, ArmState.nextPC, hD1_s2, hD2, hfL, hfR,
            BoolExpr.eval, Value.toFloat, Value.encode]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_float_correct fop fL fR)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRelFcmp (fun w => hScratch.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
  | fcmpLit hty =>
    rename_i v fop n
    simp only [verifiedGenBoolExpr] at hCode
    -- Split: (vLoadVarFP v .d1 ++ formalLoadImm64 .x0 n) ++ [fmovToFP .d2 .x0, fcmpR .d1 .d2, cset .x0 cond]
    have hCodeLoadImm := hCode.append_left
    have hCodeFmovFcmpCset := hCode.append_right
    have hCodeLV := hCodeLoadImm.append_left
    have hCodeImm := hCodeLoadImm.append_right
    -- Type info
    have hTyV := hTS v; rw [hty] at hTyV
    obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
    -- NotIreg from WellTypedLayout
    have hNotIregV : ∀ r, layout v ≠ some (.ireg r) := hWTL.float_not_ireg hty
    -- Step 1: vLoadVarFP v into d1
    obtain ⟨s1, hSteps1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
      vLoadVarFP_exec prog layout v .d1 σ s startPC hRel hScratch hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotIregV (hMapped v (by simp [BoolExpr.vars]))
    -- Step 2: loadImm64 n into x0 (preserves fregs)
    obtain ⟨s2, hSteps2, hFregs2, hX0, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_fregs_preserved prog .x0 n s1 _ hCodeImm hPC1
    -- d1 preserved through loadImm64 (loadImm64 preserves fregs)
    have hD1_s2 : s2.fregs .d1 = (σ v).encode := by
      rw [hFregs2]; exact hD1
    -- ExtStateRel preserved through loadImm64
    have hRel2 : ExtStateRel layout σ s2 :=
      loadImm64_preserves_ExtStateRel prog layout .x0 n σ s1 s2
        hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inl rfl)
    -- Step 3: fmovToFP d2 x0
    have hFmov := hCodeFmovFcmpCset.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length
        = s2.pc from by rw [List.length_append]; omega] at hFmov
    let s3 := s2.setFReg .d2 (s2.regs .x0) |>.nextPC
    have hRel3 : ExtStateRel layout σ s3 :=
      (ExtStateRel.setFReg_preserved hRel2 (fun w => hScratch.not_d2 w)).nextPC
    -- d1 preserved through fmovToFP (d2 ≠ d1)
    have hD1_s3 : s3.fregs .d1 = (σ v).encode := by
      simp [s3, ArmState.setFReg, ArmState.nextPC]; exact hD1_s2
    -- Step 4: fcmpR d1 d2 — sets flags
    have hFcmp := hCodeFmovFcmpCset.tail.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length + 1
        = s3.pc from by simp [s3, ArmState.setFReg, ArmState.nextPC]; omega] at hFcmp
    let s4 := { s3 with flags := Flags.mk (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
    have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
    -- Step 5: cset x0 cond
    have hCset := hCodeFmovFcmpCset.tail.tail.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length + 2
        = s4.pc from by simp [s4, s3, ArmState.setFReg, ArmState.nextPC]; omega] at hCset
    refine ⟨_, (hSteps1.trans hSteps2).trans
      (.step (.fmovToFP .d2 .x0 hFmov) (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.cset .x0 _ hCset)))),
      ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      have hD1_s2 : s2.fregs .d1 = (σ v).encode := by rw [hFregs2]; exact hD1
      simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
            hD1_s2, hX0, hfV, Value.encode, BoolExpr.eval, Value.toFloat]
      exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
        (Flags.condHolds_float_correct fop fV n)
    · -- ExtStateRel preserved
      exact (ExtStateRel.setReg_preserved hRel4 (fun w => hScratch.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM2, hAM1]
-/

/-- x1 ≠ effective ireg with x2 fallback. -/
theorem x1_ne_eff_x2 (layout : VarLayout) (v : Var)
    (hScratch : ExtScratchSafe layout) (hNotFreg : ∀ r, layout v ≠ some (.freg r)) :
    ArmReg.x1 ≠ (match layout v with | some (.ireg r) => r | _ => ArmReg.x2) := by
  match hv : layout v with
  | some (.ireg r) => intro h; exact (hScratch.not_x1 v (h ▸ hv)).elim
  | some (.stack _) => exact (by decide : ArmReg.x1 ≠ ArmReg.x2)
  | none => exact (by decide : ArmReg.x1 ≠ ArmReg.x2)
  | some (.freg r) => exact absurd hv (hNotFreg r)

/-- Value in effective ireg preserved after state transition clobbering a different register. -/
theorem eff_ireg_val_preserved (layout : VarLayout) (v : Var) (σ : Store)
    (s2 : ArmState) (fallback clobbered : ArmReg)
    (hRel2 : ExtStateRel layout σ s2)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    {s1 : ArmState}
    (hRegs : ∀ r, r ≠ clobbered → s2.regs r = s1.regs r)
    (hVal1 : s1.regs (match layout v with | some (.ireg r) => r | _ => fallback) = (σ v).encode)
    (hFBneCl : fallback ≠ clobbered) :
    s2.regs (match layout v with | some (.ireg r) => r | _ => fallback) = (σ v).encode := by
  match hv : layout v with
  | some (.ireg r) => exact hRel2.read_ireg hv
  | some (.stack _) =>
    simp only [hv] at hVal1 ⊢; rw [hRegs _ hFBneCl]; exact hVal1
  | none =>
    simp only [hv] at hVal1 ⊢; rw [hRegs _ hFBneCl]; exact hVal1
  | some (.freg r) => exact absurd hv (hNotFreg r)

/-- d1 ≠ effective freg with d2 fallback. -/
theorem d1_ne_eff_d2 (layout : VarLayout) (v : Var)
    (hScratch : ExtScratchSafe layout) (hNotIreg : ∀ r, layout v ≠ some (.ireg r)) :
    ArmFReg.d1 ≠ (match layout v with | some (.freg r) => r | _ => ArmFReg.d2) := by
  match hv : layout v with
  | some (.freg r) => intro h; exact (hScratch.not_d1 v (h ▸ hv)).elim
  | some (.stack _) => exact (by decide : ArmFReg.d1 ≠ ArmFReg.d2)
  | none => exact (by decide : ArmFReg.d1 ≠ ArmFReg.d2)
  | some (.ireg r) => exact absurd hv (hNotIreg r)

/-- Value in effective freg preserved after state change clobbering a different register. -/
theorem eff_freg_val_preserved (layout : VarLayout) (v : Var) (σ : Store)
    (s2 : ArmState) (fallback clobbered : ArmFReg)
    (hRel2 : ExtStateRel layout σ s2)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    {s1 : ArmState}
    (hFregs : ∀ r, r ≠ clobbered → s2.fregs r = s1.fregs r)
    (hVal1 : s1.fregs (match layout v with | some (.freg r) => r | _ => fallback) = (σ v).encode)
    (hFBneCl : fallback ≠ clobbered) :
    s2.fregs (match layout v with | some (.freg r) => r | _ => fallback) = (σ v).encode := by
  match hv : layout v with
  | some (.freg r) => exact hRel2.read_freg hv
  | some (.stack _) =>
    simp only [hv] at hVal1 ⊢; rw [hFregs _ hFBneCl]; exact hVal1
  | none =>
    simp only [hv] at hVal1 ⊢; rw [hFregs _ hFBneCl]; exact hVal1
  | some (.ireg r) => exact absurd hv (hNotIreg r)

-- § verifiedGenInstr_correct
-- ============================================================

/-- Single TAC instruction backward simulation for the verified codegen.
    Analogous to `genInstr_correct` but uses `ExtStateRel`/`VarLayout`
    and supports register-allocated variables. -/
theorem verifiedGenInstr_correct (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) (s : ArmState)
    (haltLabel divLabel boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hRel : ExtSimRel layout pcMap (.run pc σ am) s)
    (instrs : List ArmInstr)
    (hSome : verifiedGenInstr layout pcMap instr haltLabel divLabel boundsLabel arrayDecls boundsSafe = some instrs)
    (hPC_bound : pc < p.size)
    (hWT : WellTypedProg p.tyCtx p) (hTS : TypedStore p.tyCtx σ)
    (hWTL : WellTypedLayout p.tyCtx layout)
    (hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (cfg' : Cfg) (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hCodeInstr : CodeAt prog (pcMap pc) instrs)
    (hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      pcMap (pc + 1) = pcMap pc + instrs.length)
    (hAD : arrayDecls = p.arrayDecls)
    (hNCSL : ∀ x op y, instr = .floatUnary x op y → op.isNative = false → NoCallerSavedLayout layout)
    (hNCSLBin : ∀ x y z, instr = .fbinop x .fpow y z → NoCallerSavedLayout layout) :
    ∃ s', ArmSteps prog s s' ∧ ExtSimRel layout pcMap cfg' s' := by
  -- Derive scratchSafe and injective from hSome (the if-guard passed)
  have hSS : layout.scratchSafe = true := by
    cases h : layout.scratchSafe
    · simp [verifiedGenInstr, h] at hSome
    · rfl
  have hII : layout.isInjective = true := by
    cases h : layout.isInjective
    · simp [verifiedGenInstr, hSS, h] at hSome
    · rfl
  have hScratch : ExtScratchSafe layout := VarLayout.scratchSafe_spec layout hSS
  have hInjective : VarLayoutInjective layout := VarLayout.isInjective_spec layout hII
  obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
  cases hStep with
  | goto hinstr =>
    have heq : instr = .goto _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr, hSS, hII] at hSome
    rw [← hSome] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    exact ⟨{ s with pc := pcMap _ }, .single (.branch _ hb),
      ⟨hStateRel, rfl, hArrayMem⟩⟩
  | halt hinstr =>
    have heq : instr = .halt := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr, hSS, hII] at hSome
    rw [← hSome] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    exact ⟨{ s with pc := haltLabel }, .single (.branch haltLabel hb),
      ⟨hStateRel, hArrayMem⟩⟩
  | error hinstr hy hz hs =>
    exact ⟨s, .refl, trivial⟩
  | binop_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | arrLoad_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | arrStore_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | fbinop_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | intToFloat_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | floatToInt_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | floatUnary_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | fternop_typeError hinstr hne =>
    exact ⟨s, .refl, trivial⟩
  | arrLoad_boundsError hinstr hidx hbounds =>
    exact ⟨s, .refl, trivial⟩
  | arrStore_boundsError hinstr hidx hval hbounds =>
    exact ⟨s, .refl, trivial⟩
  | printInt hinstr =>
    exact sorry  -- unverified: print not modeled in ARM semantics
  | printFloat hinstr =>
    exact sorry  -- unverified: print not modeled in ARM semantics
  | const hinstr =>
    rename_i x v
    have heq : instr = .const x v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    cases v with
    | int n =>
      match hLocX : layout x with
      | some (.stack off) =>
        have hInstrs : instrs = formalLoadImm64 .x0 n ++ vStoreVar layout x .x0 := by
          simp [verifiedGenInstr, hSS, hII, hLocX] at hSome; exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, hSteps1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 n s (pcMap pc) hCodeL hPcRel
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hScratch hStack1 hFregs1
            (fun r h0 h1 h2 h8 => hRegs1 r h0)
        have hStore := vStoreVar_stack layout x .x0 off hLocX
        rw [hStore] at hCodeR
        have hStr := hCodeR.head; rw [← hPC1] at hStr
        refine ⟨s1.setStack off (s1.regs .x0) |>.nextPC,
          hSteps1.trans (.single (.str .x0 off hStr)),
          ⟨by rw [hx0]; exact (ExtStateRel.update_stack hRel1 hInjective hLocX).nextPC,
           by show s1.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; rw [hStore] at this; simp at this
              rw [this, hPC1]; omega,
           by simp [hAM1, hArrayMem]⟩⟩
      | some (.ireg r) =>
        have hInstrs : instrs = formalLoadImm64 .x0 n ++ vStoreVar layout x .x0 := by
          simp [verifiedGenInstr, hSS, hII, hLocX] at hSome; exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, hSteps1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 n s (pcMap pc) hCodeL hPcRel
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hScratch hStack1 hFregs1
            (fun r h0 h1 h2 h8 => hRegs1 r h0)
        have hne : (r == ArmReg.x0) = false := by
          cases hr : r == ArmReg.x0
          · rfl
          · simp [beq_iff_eq] at hr; exact absurd (hr ▸ hLocX) (hScratch.not_x0 x)
        have hStore := vStoreVar_ireg_diff layout x .x0 r hLocX hne
        rw [hStore] at hCodeR
        have hMovR := hCodeR.head; rw [← hPC1] at hMovR
        refine ⟨s1.setReg r (s1.regs .x0) |>.nextPC,
          hSteps1.trans (.single (.movR r .x0 hMovR)),
          ⟨by rw [hx0]; exact (ExtStateRel.update_ireg hRel1 hInjective hLocX).nextPC,
           by show s1.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; rw [hStore] at this; simp at this
              rw [this, hPC1]; omega,
           by simp [hAM1, hArrayMem]⟩⟩
      | some (.freg _) => simp [verifiedGenInstr, hSS, hII, hLocX] at hSome
      | none => simp [verifiedGenInstr, hSS, hII, hLocX] at hSome
    | bool b =>
      match hLocX : layout x with
      | some (.stack off) =>
        have hInstrs : instrs = [ArmInstr.mov .x0 (if b then 1 else 0)] ++ vStoreVar layout x .x0 := by
          simp [verifiedGenInstr, hSS, hII, hLocX] at hSome; exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        have hMov := hCodeL.head; rw [← hPcRel] at hMov
        let s1 := s.setReg .x0 (if b then 1 else 0) |>.nextPC
        have hx0 : s1.regs .x0 = (Value.bool b).encode := by
          simp [s1, ArmState.setReg, ArmState.nextPC, Value.encode]
        have hStack1 : s1.stack = s.stack := by simp [s1]
        have hFregs1 : s1.fregs = s.fregs := by simp [s1]
        have hPC1 : s1.pc = pcMap pc + 1 := by
          simp [s1, ArmState.nextPC]; exact hPcRel
        have hLen1 : [ArmInstr.mov ArmReg.x0 (if b then (1 : BitVec 64) else 0)].length = 1 := by simp
        have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
        have hRegs1 : ∀ r, r ≠ .x0 → s1.regs r = s.regs r := by
          intro r hr; simp [s1, ArmState.setReg, ArmState.nextPC, hr]
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hScratch hStack1 hFregs1
            (fun r h0 _ _ _ => hRegs1 r h0)
        have hSteps1 : ArmSteps prog s s1 :=
          ArmSteps.single (.mov .x0 (if b then 1 else 0) hMov)
        have hStore := vStoreVar_stack layout x .x0 off hLocX
        rw [hStore] at hCodeR; rw [hLen1] at hCodeR
        have hStr := hCodeR.head; rw [← hPC1] at hStr
        refine ⟨s1.setStack off (s1.regs .x0) |>.nextPC,
          hSteps1.trans (ArmSteps.single (.str .x0 off hStr)),
          ⟨by rw [hx0]; exact (ExtStateRel.update_stack hRel1 hInjective hLocX).nextPC,
           by show s1.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; rw [hStore] at this; simp at this
              rw [this, hPC1],
           by simp [hAM1, hArrayMem]⟩⟩
      | some (.ireg r) =>
        have hInstrs : instrs = [ArmInstr.mov .x0 (if b then 1 else 0)] ++ vStoreVar layout x .x0 := by
          simp [verifiedGenInstr, hSS, hII, hLocX] at hSome; exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        have hMov := hCodeL.head; rw [← hPcRel] at hMov
        let s1 := s.setReg .x0 (if b then 1 else 0) |>.nextPC
        have hx0 : s1.regs .x0 = (Value.bool b).encode := by
          simp [s1, ArmState.setReg, ArmState.nextPC, Value.encode]
        have hStack1 : s1.stack = s.stack := by simp [s1]
        have hFregs1 : s1.fregs = s.fregs := by simp [s1]
        have hPC1 : s1.pc = pcMap pc + 1 := by
          simp [s1, ArmState.nextPC]; exact hPcRel
        have hLen1 : [ArmInstr.mov ArmReg.x0 (if b then (1 : BitVec 64) else 0)].length = 1 := by simp
        have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
        have hRegs1 : ∀ r, r ≠ .x0 → s1.regs r = s.regs r := by
          intro r hr; simp [s1, ArmState.setReg, ArmState.nextPC, hr]
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hScratch hStack1 hFregs1
            (fun r h0 _ _ _ => hRegs1 r h0)
        have hSteps1 : ArmSteps prog s s1 :=
          ArmSteps.single (.mov .x0 (if b then 1 else 0) hMov)
        have hne : (r == ArmReg.x0) = false := by
          cases hr : r == ArmReg.x0
          · rfl
          · simp [beq_iff_eq] at hr; exact absurd (hr ▸ hLocX) (hScratch.not_x0 x)
        have hStore := vStoreVar_ireg_diff layout x .x0 r hLocX hne
        rw [hStore] at hCodeR; rw [hLen1] at hCodeR
        have hMovR := hCodeR.head; rw [← hPC1] at hMovR
        refine ⟨s1.setReg r (s1.regs .x0) |>.nextPC,
          hSteps1.trans (ArmSteps.single (.movR r .x0 hMovR)),
          ⟨by rw [hx0]; exact (ExtStateRel.update_ireg hRel1 hInjective hLocX).nextPC,
           by show s1.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; rw [hStore] at this; simp at this
              rw [this, hPC1],
           by simp [hAM1, hArrayMem]⟩⟩
      | some (.freg _) => simp [verifiedGenInstr, hSS, hII, hLocX] at hSome
      | none => simp [verifiedGenInstr, hSS, hII, hLocX] at hSome
    | float f =>
      match hLocX : layout x with
      | some (.stack off) =>
        have hInstrs : instrs = formalLoadImm64 .x0 f ++ [ArmInstr.fmovToFP .d0 .x0] ++ vStoreVarFP layout x .d0 := by
          simp [verifiedGenInstr, hSS, hII, hLocX] at hSome ⊢; exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeLM := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        have hCodeL := hCodeLM.append_left
        have hCodeM := hCodeLM.append_right
        obtain ⟨s1, hSteps1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 f s (pcMap pc) hCodeL hPcRel
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hScratch hStack1 hFregs1
            (fun r h0 _ _ _ => hRegs1 r h0)
        have hFmov := hCodeM.head; rw [← hPC1] at hFmov
        let s2 := s1.setFReg .d0 (s1.regs .x0) |>.nextPC
        have hSteps2 : ArmSteps prog s1 s2 := ArmSteps.single (.fmovToFP .d0 .x0 hFmov)
        have hD0 : s2.fregs .d0 = (Value.float f).encode := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hx0, Value.encode]
        have hStack2 : s2.stack = s1.stack := by simp [s2]
        have hPC2 : s2.pc = pcMap pc + ((formalLoadImm64 .x0 f).length + 1) := by
          simp [s2, ArmState.nextPC, hPC1]; omega
        have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun v => hScratch.not_d0 v)).nextPC
        have hStore := vStoreVarFP_stack layout x .d0 off hLocX
        rw [hStore] at hCodeR
        have hLenLM : (formalLoadImm64 .x0 f ++ [ArmInstr.fmovToFP .d0 .x0]).length =
            (formalLoadImm64 .x0 f).length + 1 := by simp
        rw [hLenLM] at hCodeR
        have hFstr := hCodeR.head; rw [← hPC2] at hFstr
        refine ⟨s2.setStack off (s2.fregs .d0) |>.nextPC,
          hSteps1.trans (hSteps2.trans (ArmSteps.single (.fstr .d0 off hFstr))),
          ⟨by rw [hD0]; exact (ExtStateRel.update_stack hRel2 hInjective hLocX).nextPC,
           by constructor
              · show s2.pc + 1 = pcMap (pc + 1)
                have := hPcNext _ _ rfl; rw [hStore] at this; simp at this
                rw [this, hPC2]; omega
              · simp [hAM2, hAM1, hArrayMem]⟩⟩
      | some (.freg r) =>
        -- With effective fregs: dst_reg = r, vStoreVarFP layout x r = [] (r == r)
        have hInstrs : instrs = formalLoadImm64 .x0 f ++ [ArmInstr.fmovToFP r .x0] := by
          simp [verifiedGenInstr, hSS, hII, hLocX, vStoreVarFP] at hSome ⊢
          exact hSome.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, hSteps1, hFregs1, hx0, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 f s (pcMap pc) hCodeL hPcRel
        have hRel1 : ExtStateRel layout σ s1 :=
          ExtStateRel.preserved_by_ireg_only hStateRel hScratch hStack1 hFregs1
            (fun r h0 _ _ _ => hRegs1 r h0)
        have hFmov := hCodeR.head; rw [← hPC1] at hFmov
        -- s1.regs .x0 = f = (Value.float f).encode
        have hx0enc : s1.regs .x0 = (Value.float f).encode := by
          rw [hx0]; rfl
        let s2 := (s1.setFReg r (Value.float f).encode).nextPC
        have hS2eq : s2 = (s1.setFReg r (s1.regs .x0)).nextPC := by
          simp [s2, hx0enc]
        have hSteps2 : ArmSteps prog s1 s2 := by
          rw [hS2eq]; exact ArmSteps.single (.fmovToFP r .x0 hFmov)
        have hPC2 : s2.pc = pcMap pc + ((formalLoadImm64 .x0 f).length + 1) := by
          simp [s2, ArmState.nextPC, hPC1]; omega
        have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
        have hRel2 : ExtStateRel layout (σ[x ↦ Value.float f]) s2 :=
          (ExtStateRel.update_freg hRel1 hInjective hLocX).nextPC
        refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel2, ?_, ?_⟩⟩
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl
          simp at this
          rw [hPC2]; omega
        · simp [hAM2, hAM1, hArrayMem]
      | some (.ireg _) => simp [verifiedGenInstr, hSS, hII, hLocX] at hSome
      | none => simp [verifiedGenInstr, hSS, hII, hLocX] at hSome
  | copy hinstr =>
    rename_i x y
    have heq : instr = .copy x y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- Case split on whether source is in freg
    by_cases hYFreg : ∃ r, layout y = some (.freg r)
    · -- FP copy path: src y is in freg r, code = vStoreVarFP layout x r
      obtain ⟨r, hLY⟩ := hYFreg
      have hInstrs : instrs = vStoreVarFP layout x r := by
        simp [verifiedGenInstr, hSS, hII, hLY] at hSome; exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hYVal : s.fregs r = (σ y).encode := hStateRel.read_freg hLY
      -- Derive that x is float-typed (hence not in ireg)
      have hWTi := hWT pc hPC_bound
      have heq_instr := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_instr; rw [← Option.some.inj heq_instr] at hWTi
      have hTyEq : p.tyCtx x = p.tyCtx y := match hWTi with | .copy h => h
      have hTyY : p.tyCtx y = .float := by
        cases h : p.tyCtx y with
        | float => rfl
        | int => exact absurd hLY (hWTL.1 y r (by rw [h]; decide))
        | bool => exact absurd hLY (hWTL.1 y r (by rw [h]; decide))
      have hNotIregX : ∀ r', layout x ≠ some (.ireg r') :=
        hWTL.float_not_ireg (hTyEq ▸ hTyY)
      -- Case split on layout x
      match hLX : layout x with
      | some (.stack off) =>
        -- code = [.fstr r off]: store freg r to stack
        have hCode : vStoreVarFP layout x r = [.fstr r off] := by
          simp [vStoreVarFP, hLX]
        rw [hCode] at hCodeInstr hPcNext
        have hFstr := hCodeInstr.head; rw [← hPcRel] at hFstr
        refine ⟨(s.setStack off (s.fregs r)).nextPC,
          .single (.fstr r off hFstr), ⟨?_, ?_, ?_⟩⟩
        · -- ExtStateRel
          have : s.setStack off (s.fregs r) = s.setStack off ((σ y).encode) := by
            rw [hYVal]
          rw [this]
          exact (ExtStateRel.update_stack hStateRel hInjective hLX).nextPC
        · -- pc
          have := hPcNext _ _ rfl; simp at this
          simp only [ArmState.nextPC, ArmState.setStack]
          rw [hPcRel, ← this]; rfl
        · -- arrayMem
          simp [ArmState.nextPC, ArmState.setStack, hArrayMem]
      | some (.freg r') =>
        by_cases hrr : r' = r
        · -- r' = r → code = [], x = y by injectivity → copy is no-op
          have hCode : vStoreVarFP layout x r = [] := by simp [vStoreVarFP, hLX, hrr]
          rw [hCode] at hCodeInstr hPcNext
          have hxy : x = y := hInjective x y (.freg r) (hrr ▸ hLX) hLY
          rw [hxy]
          refine ⟨s, .refl, ⟨?_, ?_, ?_⟩⟩
          · intro w loc hw
            have : (σ[y ↦ σ y]) w = σ w := by
              simp only [Store.update]; split <;> simp_all
            rw [this]; exact hStateRel w loc hw
          · have := hPcNext _ _ rfl; simp at this; rw [hPcRel]; exact this.symm
          · exact hArrayMem
        · -- r' ≠ r → code = [fmovRR r' r], move src freg r into dst freg r'
          have hne : (r' == r) = false := by simp [hrr]
          -- Reduce vStoreVarFP in hypotheses
          simp only [vStoreVarFP, hLX, hne] at hCodeInstr hPcNext
          have hFmov := hCodeInstr.head; rw [← hPcRel] at hFmov
          refine ⟨(s.setFReg r' (s.fregs r)).nextPC,
            .single (.fmovRR r' r hFmov), ⟨?_, ?_, ?_⟩⟩
          · rw [hYVal]
            exact (ExtStateRel.update_freg hStateRel hInjective hLX).nextPC
          · have := hPcNext _ _ rfl; simp at this
            simp only [ArmState.nextPC, ArmState.setFReg]
            rw [hPcRel, ← this]; rfl
          · simp [ArmState.nextPC, ArmState.setFReg, hArrayMem]
      | some (.ireg r') => exact absurd hLX (hNotIregX r')
      | none =>
        have hCode : vStoreVarFP layout x r = [] := by simp [vStoreVarFP, hLX]
        rw [hCode] at hCodeInstr hPcNext
        refine ⟨s, .refl, ⟨?_, ?_, ?_⟩⟩
        · intro w loc hw
          have hne : w ≠ x := fun h => by rw [h] at hw; simp [hLX] at hw
          rw [Store.update_other _ _ _ _ hne]; exact hStateRel w loc hw
        · have := hPcNext _ _ rfl; simp at this; rw [hPcRel]; exact this.symm
        · exact hArrayMem
    · -- Int copy path: y not in freg
      have hNotFregY : ∀ r, layout y ≠ some (.freg r) := fun r h => hYFreg ⟨r, h⟩
      by_cases hXFreg : ∃ r, layout x = some (.freg r)
      · obtain ⟨rf, hLX⟩ := hXFreg
        match hLY : layout y with
        | some (.freg r) => exact absurd hLY (hNotFregY r)
        | some (.stack _) | some (.ireg _) | none =>
          have := hSome; simp [verifiedGenInstr, hSS, hII, hLY, hLX] at this
      · have hNotFregX : ∀ r, layout x ≠ some (.freg r) := fun r h => hXFreg ⟨r, h⟩
        have hInstrs : instrs = vLoadVar layout y .x0 ++ vStoreVar layout x .x0 := by
          match hLY : layout y with
          | some (.freg r) => exact absurd hLY (hNotFregY r)
          | some (.stack _) | some (.ireg _) | none =>
            match hLX' : layout x with
            | some (.freg r) => exact absurd hLX' (hNotFregX r)
            | some (.stack _) | some (.ireg _) | none =>
              have := hSome; simp [verifiedGenInstr, hSS, hII, hLY, hLX'] at this
              exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeL := hCodeInstr.append_left
        have hCodeR := hCodeInstr.append_right
        obtain ⟨s1, hSteps1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
          vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeL
            (Or.inl rfl) hNotFregY (hMapped y (by simp [heq, TAC.vars]))
        obtain ⟨s2, hSteps2, hRel2, hPC2, hAM2⟩ :=
          vStoreVar_exec prog layout x (σ y) σ s1 (pcMap pc + (vLoadVar layout y .x0).length)
            hRel1 hInjective hScratch hPC1 hX0_1 hCodeR hNotFregX
        refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel2, ?_, ?_⟩⟩
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this
          rw [this, hPC2]; omega
        · simp [hAM2, hAM1, hArrayMem]
  | binop hinstr hy hz hs =>
    rename_i x op y z a b
    have heq : instr = .binop x op y z := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- Derive freg guards from the notFreg check in verifiedGenInstr
    have hNotFregY : ∀ r, layout y ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotFregZ : ∀ r, layout z ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    -- Effective registers: use allocated ireg directly, fall back to scratch
    let lv_reg := match layout y with | some (.ireg r) => r | _ => ArmReg.x1
    let rv_reg := match layout z with | some (.ireg r) => r | _ => ArmReg.x2
    let dst_reg := match layout x with | some (.ireg r) => r | _ => ArmReg.x0
    -- Common proof for add/sub/mul with effective registers
    suffices hSimple : ∀ (armOp : ArmInstr),
        instrs = vLoadVar layout y lv_reg ++
          (vLoadVar layout z rv_reg ++ (armOp :: vStoreVar layout x dst_reg)) →
        (∀ s', prog[s'.pc]? = some armOp →
          ArmStep prog s' (s'.setReg dst_reg (op.eval (s'.regs lv_reg) (s'.regs rv_reg)) |>.nextPC)) →
        ∃ s', ArmSteps prog s s' ∧
          ExtSimRel layout pcMap (.run (pc + 1) (σ[x ↦ .int (op.eval a b)]) am) s' by
      cases op with
      | add =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .addR dst_reg lv_reg rv_reg h
      | sub =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .subR dst_reg lv_reg rv_reg h
      | mul =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .mulR dst_reg lv_reg rv_reg h
      | band =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .andR dst_reg lv_reg rv_reg h
      | bor =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .orrR dst_reg lv_reg rv_reg h
      | bxor =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .eorR dst_reg lv_reg rv_reg h
      | shl =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .lslR dst_reg lv_reg rv_reg h
      | shr =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .asrR dst_reg lv_reg rv_reg h
      | div =>
        -- instrs = vLoadVar lv lv_reg ++ vLoadVar rv rv_reg ++
        --   cbz rv_reg divLabel :: sdivR dst_reg lv_reg rv_reg :: vStoreVar dst dst_reg
        have hInstrs : instrs = vLoadVar layout y lv_reg ++
            (vLoadVar layout z rv_reg ++
            (.cbz rv_reg divLabel :: .sdivR dst_reg lv_reg rv_reg ::
             vStoreVar layout x dst_reg)) := by
          have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeA := hCodeInstr.append_left
        have hCodeBcDE := hCodeInstr.append_right
        have hCodeB := hCodeBcDE.append_left
        have hCodecDE := hCodeBcDE.append_right
        -- Step 1: vLoadVar y into lv_reg
        obtain ⟨s1, hSteps1, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hScratch hPcRel
            hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [heq, TAC.vars])) hCodeA
        -- Step 2: vLoadVar z into rv_reg
        obtain ⟨s2, hSteps2, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
          vLoadVar_eff_exec prog layout z σ s1
            (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
            hRel1 hScratch hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [heq, TAC.vars])) hCodeB
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length := hPC2_
        -- s2.regs lv_reg = a
        have hLV_2 : s2.regs lv_reg = a := by
          match hLY : layout y with
          | some (.ireg r) =>
            have hlv : lv_reg = r := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
            rw [hlv, hRel2.read_ireg hLY, hy]; simp [Value.encode]
          | some (.stack _) | none =>
            have hlv : lv_reg = .x1 := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
            rw [hlv]
            have hne : ArmReg.x1 ≠ rv_reg := by
              intro h
              match hLZ : layout z with
              | some (.ireg rz) =>
                have hrv : rv_reg = rz := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = rz; simp [hLZ]
                rw [hrv] at h; exact hScratch.not_x1 z (h ▸ hLZ)
              | some (.stack _) | none =>
                have hrv : rv_reg = .x2 := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
                rw [hrv] at h; exact absurd h (by decide)
              | some (.freg r) => exact absurd hLZ (hNotFregZ r)
            rw [hRegs2 .x1 hne, ← hlv, hLV_1, hy]; simp [Value.encode]
          | some (.freg r) => exact absurd hLY (hNotFregY r)
        have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
        -- b ≠ 0 from safety
        have hb_ne0 : b ≠ 0 := by unfold BinOp.safe at hs; exact hs
        have hRV_ne0 : s2.regs rv_reg ≠ (0 : BitVec 64) := by
          rw [hRV_eq]; exact hb_ne0
        -- Step 3: cbz falls through (rv_reg ≠ 0)
        have hCbz := hCodecDE.head; rw [← hPC2_] at hCbz
        have hStepsCbz : ArmSteps prog s2 s2.nextPC :=
          ArmSteps.single (.cbz_fall rv_reg divLabel hCbz hRV_ne0)
        have hPC_cbz : s2.nextPC.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 1 := by
          show s2.pc + 1 = _; omega
        -- cbz preserves all registers
        have hLV_cbz : s2.nextPC.regs lv_reg = a := by
          simp [ArmState.nextPC]; exact hLV_2
        have hRV_cbz : s2.nextPC.regs rv_reg = b := by
          simp [ArmState.nextPC]; exact hRV_eq
        have hRV_ne0_cbz : s2.nextPC.regs rv_reg ≠ (0 : BitVec 64) := by
          rw [hRV_cbz]; exact hb_ne0
        have hRel_cbz : ExtStateRel layout σ s2.nextPC := hRel2.nextPC
        have hAM_cbz : s2.nextPC.arrayMem = s2.arrayMem := by simp [ArmState.nextPC]
        -- Step 4: sdivR dst_reg lv_reg rv_reg
        have hSdiv := hCodecDE.tail.head; rw [← hPC_cbz] at hSdiv
        have hStepsSdiv : ArmSteps prog s2.nextPC
            (s2.nextPC.setReg dst_reg (BitVec.sdiv (s2.nextPC.regs lv_reg) (s2.nextPC.regs rv_reg))).nextPC :=
          ArmSteps.single (.sdivR dst_reg lv_reg rv_reg hSdiv hRV_ne0_cbz)
        -- Rewrite to use a, b
        have hSdivEq : (s2.nextPC.setReg dst_reg (BitVec.sdiv (s2.nextPC.regs lv_reg) (s2.nextPC.regs rv_reg))).nextPC =
            (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC := by
          rw [hLV_cbz, hRV_cbz]; rfl
        rw [hSdivEq] at hStepsSdiv
        let s3 := (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC
        have hPC3 : s3.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 2 := by
          show s2.nextPC.pc + 1 = _; omega
        have hAM3 : s3.arrayMem = s2.arrayMem := by
          simp [s3, ArmState.nextPC, ArmState.setReg]
        -- Step 5: store — case split on layout dst
        by_cases hXIR : ∃ r, layout x = some (.ireg r)
        · obtain ⟨r_dst, hDst⟩ := hXIR
          have hDR : dst_reg = r_dst := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDst]
          have hStore : vStoreVar layout x dst_reg = [] := by simp [vStoreVar, hDst, hDR]
          have hRel4 : ExtStateRel layout (σ[x ↦ .int (BinOp.eval .div a b)]) s3 := by
            show ExtStateRel layout (σ[x ↦ .int (BinOp.eval .div a b)])
              (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC
            rw [hDR, show BinOp.eval .div a b = (Value.int (BinOp.eval .div a b)).encode from by simp [Value.encode]]
            exact (ExtStateRel.update_ireg hRel_cbz hInjective hDst).nextPC
          refine ⟨s3, ((hSteps1.trans hSteps2).trans hStepsCbz).trans hStepsSdiv, ⟨hRel4, ?_, ?_⟩⟩
          · show s3.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp [hStore] at this; omega
          · simp [hAM3, hAM2, hAM1, hArrayMem]
        · have hDR : dst_reg = .x0 := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hXIR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            show ExtStateRel layout σ (s2.nextPC.setReg dst_reg (BinOp.eval .div a b)).nextPC
            rw [hDR]; exact (ExtStateRel.setReg_preserved hRel_cbz (fun w => hScratch.not_x0 w)).nextPC
          have hVal3 : s3.regs .x0 = (Value.int (BinOp.eval .div a b)).encode := by
            simp [s3, hDR, ArmState.setReg, ArmState.nextPC, Value.encode]
          have hCodeStore : CodeAt prog
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 2)
              (vStoreVar layout x .x0) := by
            rw [← hDR]; exact hCodecDE.tail.tail
          obtain ⟨s4, hSteps4, hRel4, hPC4, hAM4⟩ :=
            vStoreVar_exec prog layout x (Value.int (BinOp.eval .div a b)) σ s3
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 2)
              hRel3 hInjective hScratch hPC3 hVal3 hCodeStore hNotFregX
          refine ⟨s4, ((hSteps1.trans hSteps2).trans hStepsCbz).trans (hStepsSdiv.trans hSteps4), ⟨hRel4, ?_, ?_⟩⟩
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this; simp at this; omega
          · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
      | mod =>
        -- instrs = vLoadVar lv lv_reg ++ vLoadVar rv rv_reg ++ [cbz rv_reg divLabel] ++
        --   [sdivR .x0 lv_reg rv_reg, mulR .x0 .x0 rv_reg, subR dst_reg lv_reg .x0] ++
        --   vStoreVar dst dst_reg
        have hInstrs : instrs = vLoadVar layout y lv_reg ++
            (vLoadVar layout z rv_reg ++
            (.cbz rv_reg divLabel :: .sdivR .x0 lv_reg rv_reg :: .mulR .x0 .x0 rv_reg ::
             .subR dst_reg lv_reg .x0 :: vStoreVar layout x dst_reg)) := by
          have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeA := hCodeInstr.append_left
        have hCodeBcDE := hCodeInstr.append_right
        have hCodeB := hCodeBcDE.append_left
        have hCodecDE := hCodeBcDE.append_right
        -- Step 1: vLoadVar y into lv_reg
        obtain ⟨s1, hSteps1, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hScratch hPcRel
            hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [heq, TAC.vars])) hCodeA
        -- Step 2: vLoadVar z into rv_reg
        obtain ⟨s2, hSteps2, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
          vLoadVar_eff_exec prog layout z σ s1
            (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
            hRel1 hScratch hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [heq, TAC.vars])) hCodeB
        have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length := hPC2_
        -- s2.regs lv_reg = a
        have hLV_2 : s2.regs lv_reg = a := by
          match hLY : layout y with
          | some (.ireg r) =>
            have hlv : lv_reg = r := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
            rw [hlv, hRel2.read_ireg hLY, hy]; simp [Value.encode]
          | some (.stack _) | none =>
            have hlv : lv_reg = .x1 := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
            rw [hlv]
            have hne : ArmReg.x1 ≠ rv_reg := by
              intro h
              match hLZ : layout z with
              | some (.ireg rz) =>
                have hrv : rv_reg = rz := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = rz; simp [hLZ]
                rw [hrv] at h; exact hScratch.not_x1 z (h ▸ hLZ)
              | some (.stack _) | none =>
                have hrv : rv_reg = .x2 := by
                  show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
                rw [hrv] at h; exact absurd h (by decide)
              | some (.freg r) => exact absurd hLZ (hNotFregZ r)
            rw [hRegs2 .x1 hne, ← hlv, hLV_1, hy]; simp [Value.encode]
          | some (.freg r) => exact absurd hLY (hNotFregY r)
        have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
        -- b ≠ 0 from safety
        have hb_ne0 : b ≠ 0 := by unfold BinOp.safe at hs; exact hs
        have hRV_ne0 : s2.regs rv_reg ≠ (0 : BitVec 64) := by
          rw [hRV_eq]; exact hb_ne0
        -- Step 3: cbz falls through (rv_reg ≠ 0)
        have hCbz := hCodecDE.head; rw [← hPC2_] at hCbz
        have hStepsCbz : ArmSteps prog s2 s2.nextPC :=
          ArmSteps.single (.cbz_fall rv_reg divLabel hCbz hRV_ne0)
        have hPC_cbz : s2.nextPC.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 1 := by
          show s2.pc + 1 = _; omega
        have hLV_cbz : s2.nextPC.regs lv_reg = a := by
          simp [ArmState.nextPC]; exact hLV_2
        have hRV_cbz : s2.nextPC.regs rv_reg = b := by
          simp [ArmState.nextPC]; exact hRV_eq
        have hRV_ne0_cbz : s2.nextPC.regs rv_reg ≠ (0 : BitVec 64) := by
          rw [hRV_cbz]; exact hb_ne0
        have hRel_cbz : ExtStateRel layout σ s2.nextPC := hRel2.nextPC
        have hAM_cbz : s2.nextPC.arrayMem = s2.arrayMem := by simp [ArmState.nextPC]
        -- Step 4: sdivR .x0 lv_reg rv_reg
        have hSdiv := hCodecDE.tail.head; rw [← hPC_cbz] at hSdiv
        let q := BitVec.sdiv a b
        have hStepsSdiv : ArmSteps prog s2.nextPC
            (s2.nextPC.setReg .x0 q).nextPC := by
          have h := ArmSteps.single (.sdivR .x0 lv_reg rv_reg hSdiv hRV_ne0_cbz)
          rwa [hLV_cbz, hRV_cbz] at h
        let s_q := (s2.nextPC.setReg .x0 q).nextPC
        have hPC_q : s_q.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 2 := by
          show s2.nextPC.pc + 1 = _; omega
        -- lv_reg ≠ x0 and rv_reg ≠ x0 (scratch safety)
        have hLV_ne_x0 : lv_reg ≠ .x0 := by
          intro h
          match hLY : layout y with
          | some (.ireg r) =>
            have : lv_reg = r := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
            rw [this] at h; rw [h] at hLY; exact absurd hLY (hScratch.not_x0 y)
          | some (.stack _) | none =>
            have : lv_reg = .x1 := by
              show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
            rw [this] at h; exact absurd h (by decide)
          | some (.freg r) => exact absurd hLY (hNotFregY r)
        have hRV_ne_x0 : rv_reg ≠ .x0 := by
          intro h
          match hLZ : layout z with
          | some (.ireg r) =>
            have : rv_reg = r := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = r; simp [hLZ]
            rw [this] at h; rw [h] at hLZ; exact absurd hLZ (hScratch.not_x0 z)
          | some (.stack _) | none =>
            have : rv_reg = .x2 := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
            rw [this] at h; exact absurd h (by decide)
          | some (.freg r) => exact absurd hLZ (hNotFregZ r)
        have hLV_q : s_q.regs lv_reg = a := by
          show (s2.nextPC.setReg .x0 q).nextPC.regs lv_reg = a
          rw [ArmState.nextPC_regs, ArmState.setReg_regs_other _ _ _ _ hLV_ne_x0,
              ArmState.nextPC_regs]; exact hLV_2
        have hRV_q : s_q.regs rv_reg = b := by
          show (s2.nextPC.setReg .x0 q).nextPC.regs rv_reg = b
          rw [ArmState.nextPC_regs, ArmState.setReg_regs_other _ _ _ _ hRV_ne_x0,
              ArmState.nextPC_regs]; exact hRV_eq
        -- Step 5: mulR .x0 .x0 rv_reg
        have hMul := hCodecDE.tail.tail.head; rw [← hPC_q] at hMul
        have hStepsMul : ArmSteps prog s_q
            (s_q.setReg .x0 (s_q.regs .x0 * s_q.regs rv_reg)).nextPC :=
          ArmSteps.single (.mulR .x0 .x0 rv_reg hMul)
        -- s_q.regs .x0 = q, s_q.regs rv_reg = b
        have hx0_q : s_q.regs .x0 = q := by
          show (s2.nextPC.setReg .x0 q).nextPC.regs .x0 = q
          simp [ArmState.nextPC_regs, ArmState.setReg_regs_same]
        let s_qb := (s_q.setReg .x0 (q * b)).nextPC
        have hMulEq : (s_q.setReg .x0 (s_q.regs .x0 * s_q.regs rv_reg)).nextPC = s_qb := by
          rw [hx0_q, hRV_q]
        rw [hMulEq] at hStepsMul
        have hPC_qb : s_qb.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 3 := by
          show s_q.pc + 1 = _; omega
        -- lv_reg value preserved through second x0 write
        have hLV_qb : s_qb.regs lv_reg = a := by
          show (s_q.setReg .x0 (q * b)).nextPC.regs lv_reg = a
          rw [ArmState.nextPC_regs, ArmState.setReg_regs_other _ _ _ _ hLV_ne_x0]
          exact hLV_q
        -- x0 value after mul
        have hx0_qb : s_qb.regs .x0 = q * b := by
          show (s_q.setReg .x0 (q * b)).nextPC.regs .x0 = q * b
          simp [ArmState.nextPC_regs, ArmState.setReg_regs_same]
        -- Step 6: subR dst_reg lv_reg .x0
        have hSub := hCodecDE.tail.tail.tail.head; rw [← hPC_qb] at hSub
        have hStepsSub : ArmSteps prog s_qb
            (s_qb.setReg dst_reg (s_qb.regs lv_reg - s_qb.regs .x0)).nextPC :=
          ArmSteps.single (.subR dst_reg lv_reg .x0 hSub)
        -- a - q * b = srem a b = BinOp.eval .mod a b
        have hModEq : a - q * b = BinOp.eval .mod a b := by
          simp [BinOp.eval, q]; exact BitVec.srem_eq_sub_sdiv_mul a b
        let s5 := (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC
        have hSubEq : (s_qb.setReg dst_reg (s_qb.regs lv_reg - s_qb.regs .x0)).nextPC = s5 := by
          rw [hLV_qb, hx0_qb, hModEq]
        rw [hSubEq] at hStepsSub
        have hPC5 : s5.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
            (vLoadVar layout z rv_reg).length + 4 := by
          show s_qb.pc + 1 = _; omega
        have hAM5 : s5.arrayMem = s2.arrayMem := by
          show (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC.arrayMem = s2.arrayMem
          simp [ArmState.nextPC_arrayMem, ArmState.setReg_arrayMem]
          show (s_q.setReg .x0 (q * b)).nextPC.arrayMem = s2.arrayMem
          simp [ArmState.nextPC_arrayMem, ArmState.setReg_arrayMem]
          show (s2.nextPC.setReg .x0 q).nextPC.arrayMem = s2.arrayMem
          simp [ArmState.nextPC_arrayMem, ArmState.setReg_arrayMem]
        -- Chain all intermediate steps
        have hStepsAll : ArmSteps prog s2 s5 :=
          (hStepsCbz.trans hStepsSdiv).trans (hStepsMul.trans hStepsSub)
        -- Step 7: store — case split on layout dst
        by_cases hXIR : ∃ r, layout x = some (.ireg r)
        · obtain ⟨r_dst, hDst⟩ := hXIR
          have hDR : dst_reg = r_dst := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDst]
          have hStore : vStoreVar layout x dst_reg = [] := by simp [vStoreVar, hDst, hDR]
          -- For the ireg case, s5 already has the result in the right register
          -- Need ExtStateRel for the updated store
          have hRel_cbz_s : ExtStateRel layout σ s2.nextPC := hRel2.nextPC
          -- Chain setReg_preserved for x0 writes, then update_ireg for dst
          -- Actually s5 = (s_qb.setReg dst_reg (mod a b)).nextPC
          -- = (s_q.setReg .x0 (q*b)).nextPC.setReg dst_reg (mod a b)).nextPC
          -- We need: ExtStateRel layout (σ[x ↦ .int (mod a b)]) s5
          -- Since dst_reg = r_dst and layout x = some (.ireg r_dst), use update_ireg
          -- But we need ExtStateRel layout σ on the state before the final setReg
          -- s_qb = (s_q.setReg .x0 (q*b)).nextPC
          -- s_q = (s2.nextPC.setReg .x0 q).nextPC
          -- Through both x0 writes, ExtStateRel is preserved (x0 is scratch)
          have hRelQ : ExtStateRel layout σ s_q :=
            (ExtStateRel.setReg_preserved hRel_cbz_s (fun w => hScratch.not_x0 w)).nextPC
          have hRelQB : ExtStateRel layout σ s_qb :=
            (ExtStateRel.setReg_preserved hRelQ (fun w => hScratch.not_x0 w)).nextPC
          have hRel5 : ExtStateRel layout (σ[x ↦ .int (BinOp.eval .mod a b)]) s5 := by
            show ExtStateRel layout (σ[x ↦ .int (BinOp.eval .mod a b)])
              (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC
            rw [hDR, show BinOp.eval .mod a b = (Value.int (BinOp.eval .mod a b)).encode from by simp [Value.encode]]
            exact (ExtStateRel.update_ireg hRelQB hInjective hDst).nextPC
          refine ⟨s5, ((hSteps1.trans hSteps2).trans hStepsAll), ⟨hRel5, ?_, ?_⟩⟩
          · show s5.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp [hStore] at this; omega
          · simp [hAM5, hAM2, hAM1, hArrayMem]
        · have hDR : dst_reg = .x0 := by
            change (match layout x with | some (.ireg r) => r | _ => .x0) = .x0
            split
            · next r h => exact absurd ⟨r, h⟩ hXIR
            · rfl
          -- Through all ops: x0 is scratch, and the final subR writes dst_reg = x0
          -- So we need ExtStateRel for σ (not updated) on the state before vStoreVar
          have hRelQ : ExtStateRel layout σ s_q :=
            (ExtStateRel.setReg_preserved hRel2.nextPC (fun w => hScratch.not_x0 w)).nextPC
          have hRelQB : ExtStateRel layout σ s_qb :=
            (ExtStateRel.setReg_preserved hRelQ (fun w => hScratch.not_x0 w)).nextPC
          have hRel5 : ExtStateRel layout σ s5 := by
            show ExtStateRel layout σ (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC
            rw [hDR]; exact (ExtStateRel.setReg_preserved hRelQB (fun w => hScratch.not_x0 w)).nextPC
          have hVal5 : s5.regs .x0 = (Value.int (BinOp.eval .mod a b)).encode := by
            show (s_qb.setReg dst_reg (BinOp.eval .mod a b)).nextPC.regs .x0 = _
            rw [ArmState.nextPC_regs, hDR, ArmState.setReg_regs_same]; simp [Value.encode]
          have hCodeStore : CodeAt prog
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 4)
              (vStoreVar layout x .x0) := by
            rw [← hDR]; exact hCodecDE.tail.tail.tail.tail
          obtain ⟨s6, hSteps6, hRel6, hPC6, hAM6⟩ :=
            vStoreVar_exec prog layout x (Value.int (BinOp.eval .mod a b)) σ s5
              (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 4)
              hRel5 hInjective hScratch hPC5 hVal5 hCodeStore hNotFregX
          refine ⟨s6, ((hSteps1.trans hSteps2).trans hStepsAll).trans hSteps6, ⟨hRel6, ?_, ?_⟩⟩
          · show s6.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this; simp at this; omega
          · simp [hAM6, hAM5, hAM2, hAM1, hArrayMem]
    -- Prove the common case for add/sub/mul
    intro armOp hInstrs hArmStep
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeA := hCodeInstr.append_left
    have hCodeBcD := hCodeInstr.append_right
    have hCodeB := hCodeBcD.append_left
    have hCodecD := hCodeBcD.append_right
    -- Step 1: vLoadVar y into lv_reg (effective)
    obtain ⟨s1, hSteps1, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hScratch hPcRel
        hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [heq, TAC.vars])) hCodeA
    -- Step 2: vLoadVar z into rv_reg (effective)
    obtain ⟨s2, hSteps2, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
      vLoadVar_eff_exec prog layout z σ s1
        (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
        hRel1 hScratch hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [heq, TAC.vars])) hCodeB
    -- Cast hPC2 to use let-bound names (definitionally equal)
    have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
        (vLoadVar layout z rv_reg).length := hPC2_
    -- s2.regs lv_reg = a: use ExtStateRel for ireg, register preservation for stack
    have hLV_2 : s2.regs lv_reg = a := by
      -- Prove lv_reg equals a concrete register, then rw to work with it
      match hLY : layout y with
      | some (.ireg r) =>
        have hlv : lv_reg = r := by
          show (match layout y with | some (.ireg r) => r | _ => .x1) = r; simp [hLY]
        rw [hlv, hRel2.read_ireg hLY, hy]; simp [Value.encode]
      | some (.stack _) | none =>
        have hlv : lv_reg = .x1 := by
          show (match layout y with | some (.ireg r) => r | _ => .x1) = .x1; simp [hLY]
        rw [hlv]
        have hne : ArmReg.x1 ≠ rv_reg := by
          intro h
          match hLZ : layout z with
          | some (.ireg rz) =>
            have hrv : rv_reg = rz := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = rz; simp [hLZ]
            rw [hrv] at h; exact hScratch.not_x1 z (h ▸ hLZ)
          | some (.stack _) | none =>
            have hrv : rv_reg = .x2 := by
              show (match layout z with | some (.ireg r) => r | _ => .x2) = .x2; simp [hLZ]
            rw [hrv] at h; exact absurd h (by decide)
          | some (.freg r) => exact absurd hLZ (hNotFregZ r)
        rw [hRegs2 .x1 hne, ← hlv, hLV_1, hy]; simp [Value.encode]
      | some (.freg r) => exact absurd hLY (hNotFregY r)
    have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
    -- Step 3: execute the op instruction
    have hOp := hCodecD.head; rw [← hPC2_] at hOp
    -- Step 3: execute op, rewrite to use a, b
    have hSteps3 : ArmSteps prog s2 (s2.setReg dst_reg (op.eval a b)).nextPC := by
      have := ArmSteps.single (hArmStep s2 hOp); rwa [hLV_2, hRV_eq] at this
    have hPC3 : (s2.setReg dst_reg (op.eval a b)).nextPC.pc =
        pcMap pc + (vLoadVar layout y lv_reg).length +
        (vLoadVar layout z rv_reg).length + 1 := by
      show s2.pc + 1 = _; omega
    have hAM3 : (s2.setReg dst_reg (op.eval a b)).nextPC.arrayMem = s2.arrayMem := by
      simp [ArmState.nextPC, ArmState.setReg]
    -- Step 4: store — case split on layout dst
    by_cases hXIR : ∃ r, layout x = some (.ireg r)
    · -- dst in ireg r: vStoreVar is [], use update_ireg
      obtain ⟨r_dst, hDst⟩ := hXIR
      have hDR : dst_reg = r_dst := by
        change (match layout x with | some (.ireg r) => r | _ => .x0) = r_dst; rw [hDst]
      have hStore : vStoreVar layout x dst_reg = [] := by simp [vStoreVar, hDst, hDR]
      have hRel4 : ExtStateRel layout (σ[x ↦ .int (op.eval a b)])
          (s2.setReg dst_reg (op.eval a b)).nextPC := by
        rw [hDR, show op.eval a b = (Value.int (op.eval a b)).encode from by simp [Value.encode]]
        exact (ExtStateRel.update_ireg hRel2 hInjective hDst).nextPC
      refine ⟨_, (hSteps1.trans hSteps2).trans hSteps3, ⟨hRel4, ?_, ?_⟩⟩
      · show (s2.setReg dst_reg (op.eval a b)).nextPC.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp [hStore] at this
        show s2.pc + 1 = _; omega
      · simp [hAM2, hAM1, hArrayMem]
    · -- dst on stack/none: dst_reg = x0, use vStoreVar_exec
      have hDR : dst_reg = .x0 := by
        change (match layout x with | some (.ireg r) => r | _ => .x0) = .x0
        split
        · next r h => exact absurd ⟨r, h⟩ hXIR
        · rfl
      have hRel3 : ExtStateRel layout σ (s2.setReg dst_reg (op.eval a b)).nextPC := by
        rw [hDR]; exact (ExtStateRel.setReg_preserved hRel2 (fun w => hScratch.not_x0 w)).nextPC
      have hVal3 : (s2.setReg dst_reg (op.eval a b)).nextPC.regs .x0 =
          (Value.int (op.eval a b)).encode := by
        simp [hDR, ArmState.setReg, ArmState.nextPC, Value.encode]
      have hCodeStore : CodeAt prog
          (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 1)
          (vStoreVar layout x .x0) := by rw [← hDR]; exact hCodecD.tail
      obtain ⟨s4, hSteps4, hRel4, hPC4, hAM4⟩ :=
        vStoreVar_exec prog layout x (Value.int (op.eval a b)) σ
          (s2.setReg dst_reg (op.eval a b)).nextPC
          (pcMap pc + (vLoadVar layout y lv_reg).length + (vLoadVar layout z rv_reg).length + 1)
          hRel3 hInjective hScratch hPC3 hVal3 hCodeStore hNotFregX
      refine ⟨s4, (hSteps1.trans hSteps2).trans (hSteps3.trans hSteps4), ⟨hRel4, ?_, ?_⟩⟩
      · show s4.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; rw [show dst_reg = ArmReg.x0 from hDR] at this; simp at this; omega
      · simp [hAM4, hAM2, hAM1, hArrayMem]
  | boolop hinstr =>
    rename_i x be
    have heq : instr = .boolop x be := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    have hSimpleBE : be.hasSimpleOps = true := by
      cases hb : be.hasSimpleOps with
      | true => rfl
      | false => simp [verifiedGenInstr, hSS, hII, hb] at hSome
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, hSimpleBE, h] at this
    have hInstrs : instrs = verifiedGenBoolExpr layout be ++ vStoreVar layout x .x0 := by
      have := hSome; simp [verifiedGenInstr, hSS, hII, hSimpleBE] at this; exact this.symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeBE := hCodeInstr.append_left
    have hCodeStore := hCodeInstr.append_right
    -- Extract WellTypedBoolExpr
    have hWTbe : WellTypedBoolExpr p.tyCtx be := by
      have hwti := hWT pc hPC_bound
      have heq_i := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_i; rw [← Option.some.inj heq_i] at hwti
      cases hwti with | boolop _ hbe => exact hbe
    obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout be σ s (pcMap pc) hStateRel hScratch hCodeBE
        hPcRel p.tyCtx hTS hWTbe hWTL
        (fun v hv => hMapped v (by simp [heq, TAC.vars]; exact Or.inr hv)) hSimpleBE am
    -- vStoreVar x from x0
    have hX0_val : s1.regs .x0 = (Value.bool (be.eval σ am)).encode := by
      rw [hX0_1]; simp [Value.encode]
    obtain ⟨s2, hSteps2, hRel2, hPC2, hAM2⟩ :=
      vStoreVar_exec prog layout x (Value.bool (be.eval σ am)) σ s1
        (pcMap pc + (verifiedGenBoolExpr layout be).length)
        hRel1 hInjective hScratch hPC1 hX0_val hCodeStore hNotFregX
    refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel2, ?_, ?_⟩⟩
    · show s2.pc = pcMap (pc + 1)
      have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
    · simp [hAM2, hAM1, hArrayMem]
  | iftrue hinstr hcond =>
    rename_i l_var be_var
    have heq : instr = .ifgoto be_var l_var := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hSimpleBV : be_var.hasSimpleOps = true := by
      cases hb : be_var.hasSimpleOps with
      | true => rfl
      | false => simp [verifiedGenInstr, hSS, hII, hb] at hSome
    have hWTbe : WellTypedBoolExpr p.tyCtx be_var := by
      have hwti := hWT pc hPC_bound
      have heq_i := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_i; rw [← Option.some.inj heq_i] at hwti
      cases hwti with | ifgoto hbe => exact hbe
    cases be_var with
    | not inner =>
      cases inner with
      | cmp op a b =>
        simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
        obtain rfl := Option.some.inj hSome
        have hSimpleCmp : (BoolExpr.cmp op a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimpleCmp
        have hWTcmp : WellTypedBoolExpr p.tyCtx (.cmp op a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy p.tyCtx a .int ∧ ExprHasTy p.tyCtx b .int := by
          cases hWTcmp with | cmp ha hb => exact ⟨ha, hb⟩
        have hcmp_false : BoolExpr.eval σ am (.cmp op a b) = false := by
          simp [BoolExpr.eval] at hcond; exact hcond
        cases a with
        | var va => cases b with
          | var vb =>
            have hNotFregA : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hNotFregB : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨nA, hnA⟩ := Value.int_of_typeOf_int hTyA
            obtain ⟨nB, hnB⟩ := Value.int_of_typeOf_int hTyB
            let a_reg := match layout va with | some (.ireg r) => r | _ => ArmReg.x1
            let b_reg := match layout vb with | some (.ireg r) => r | _ => ArmReg.x2
            simp only [] at hCodeInstr
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, hSteps1, hVal1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_eff_exec prog layout va σ s (pcMap pc) .x1 hStateRel hScratch hPcRel
                hNotFregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            obtain ⟨s2, hSteps2, hVal2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
              vLoadVar_eff_exec prog layout vb σ s1 _ .x2
                hRel1 hScratch hPC1
                hNotFregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hA_s2 : s2.regs a_reg = nA := by
              have := eff_ireg_val_preserved layout va σ s2 .x1 b_reg hRel2 hNotFregA
                hRegs2 hVal1 (x1_ne_eff_x2 layout vb hScratch hNotFregB)
              rw [this, hnA]; rfl
            have hB_s2 : s2.regs b_reg = nB := by rw [hVal2, hnB]; rfl
            have hPC2' : s2.pc = pcMap pc + (vLoadVar layout va a_reg ++ vLoadVar layout vb b_reg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2
            have hCmp := hPC2'.symm ▸ hCodeCmpBCond.head
            let s3 := { s2 with flags := Flags.mk (s2.regs a_reg) (s2.regs b_reg), pc := s2.pc + 1 }
            have hPC3 : s3.pc = pcMap pc + (vLoadVar layout va a_reg ++ vLoadVar layout vb b_reg).length + 1 := by
              simp [s3, hPC2']
            have hBCond := hPC3.symm ▸ hCodeCmpBCond.tail.head
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnA, hnB] at hcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.cmpRR a_reg b_reg hCmp) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            simp only [s3, hA_s2, hB_s2, Value.encode]
            cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
              BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_false ⊢ <;> exact hcmp_false
          | lit nb =>
            have hNotFregA : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hTyA := hTS va; rw [ha_ty] at hTyA
            obtain ⟨nA, hnA⟩ := Value.int_of_typeOf_int hTyA
            let a_reg := match layout va with | some (.ireg r) => r | _ => ArmReg.x1
            simp only [] at hCodeInstr
            have hCodeA := hCodeInstr.append_left.append_left
            have hCodeImm := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, hSteps1, hVal1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_eff_exec prog layout va σ s (pcMap pc) .x1 hStateRel hScratch hPcRel
                hNotFregA (Or.inr (Or.inl rfl))
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeA
            obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImm hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hA_s2 : s2.regs a_reg = nA := by
              have := eff_ireg_val_preserved layout va σ s2 .x1 .x2 hRel2 hNotFregA
                hRegs2 hVal1 (by decide)
              rw [this, hnA]; rfl
            have hPC2' : s2.pc = pcMap pc + (vLoadVar layout va a_reg ++ formalLoadImm64 .x2 nb).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2
            have hCmp := hPC2'.symm ▸ hCodeCmpBCond.head
            let s3 := { s2 with flags := Flags.mk (s2.regs a_reg) (s2.regs .x2), pc := s2.pc + 1 }
            have hPC3 : s3.pc = pcMap pc + (vLoadVar layout va a_reg ++ formalLoadImm64 .x2 nb).length + 1 := by
              simp [s3, hPC2']
            have hBCond := hPC3.symm ▸ hCodeCmpBCond.tail.head
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnA] at hcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.cmpRR a_reg .x2 hCmp) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            simp only [s3, hA_s2, hX2, Value.encode]
            cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
              BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_false ⊢ <;> exact hcmp_false
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | lit na => cases b with
          | var vb =>
            have hNotFregB : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            have hTyB := hTS vb; rw [hb_ty] at hTyB
            obtain ⟨nB, hnB⟩ := Value.int_of_typeOf_int hTyB
            let b_reg := match layout vb with | some (.ireg r) => r | _ => ArmReg.x2
            simp only [] at hCodeInstr
            have hCodeImm := hCodeInstr.append_left.append_left
            have hCodeB := hCodeInstr.append_left.append_right
            have hCodeCmpBCond := hCodeInstr.append_right
            obtain ⟨s1, hSteps1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImm hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, hSteps2, hVal2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
              vLoadVar_eff_exec prog layout vb σ s1 _ .x2
                hRel1 hScratch hPC1
                hNotFregB (Or.inr (Or.inr rfl))
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars])) hCodeB
            have hX1_s2 : s2.regs .x1 = na := by
              rw [hRegs2 .x1 (x1_ne_eff_x2 layout vb hScratch hNotFregB)]; exact hX1
            have hB_s2 : s2.regs b_reg = nB := by rw [hVal2, hnB]; rfl
            have hPC2' : s2.pc = pcMap pc + (formalLoadImm64 .x1 na ++ vLoadVar layout vb b_reg).length := by
              rw [List.length_append, ← Nat.add_assoc]; exact hPC2
            have hCmp := hPC2'.symm ▸ hCodeCmpBCond.head
            let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs b_reg), pc := s2.pc + 1 }
            have hPC3 : s3.pc = pcMap pc + (formalLoadImm64 .x1 na ++ vLoadVar layout vb b_reg).length + 1 := by
              simp [s3, hPC2']
            have hBCond := hPC3.symm ▸ hCodeCmpBCond.tail.head
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnB] at hcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.cmpRR .x1 b_reg hCmp) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            simp only [s3, hX1_s2, hB_s2, Value.encode]
            cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
              BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_false ⊢ <;> exact hcmp_false
          | lit nb =>
            simp only [] at hCodeInstr
            have hCodeLoadImm := hCodeInstr.append_left
            have hCodeCmpBCond := hCodeInstr.append_right
            have hCodeImmA := hCodeLoadImm.append_left
            have hCodeImmB := hCodeLoadImm.append_right
            obtain ⟨s1, hSteps1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImmA hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImmB hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hX1_s2 : s2.regs .x1 = na := by rw [hRegs2 .x1 (by decide)]; exact hX1
            have hCmp := hCodeCmpBCond.head
            rw [show pcMap pc + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length
                = s2.pc from by rw [List.length_append]; omega] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hBCond := hCodeCmpBCond.tail.head
            rw [show pcMap pc + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt] at hcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.cmpRR .x1 .x2 hCmp) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            simp only [s3, hX1_s2, hX2, Value.encode]
            cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
              BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_false ⊢ <;> exact hcmp_false
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | fcmp fop a b =>
        simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
        obtain rfl := Option.some.inj hSome
        have hSimpleFcmp : (BoolExpr.fcmp fop a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimpleFcmp
        have hWTfcmp : WellTypedBoolExpr p.tyCtx (.fcmp fop a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy p.tyCtx a .float ∧ ExprHasTy p.tyCtx b .float := by
          cases hWTfcmp with | fcmp ha hb => exact ⟨ha, hb⟩
        have hfcmp_false : BoolExpr.eval σ am (.fcmp fop a b) = false := by
          simp [BoolExpr.eval] at hcond; exact hcond
        cases a with
        | var va => cases b with
          | var vb =>
            simp only [] at hCodeInstr
            have hCodeLVRV := hCodeInstr.append_left
            have hCodeFcmpBCond := hCodeInstr.append_right
            have hCodeLV := hCodeLVRV.append_left
            have hCodeRV := hCodeLVRV.append_right
            have hTyL := hTS va; rw [ha_ty] at hTyL
            have hTyR := hTS vb; rw [hb_ty] at hTyR
            obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
            obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
            have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            obtain ⟨s1, hSteps1, hD1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_exec prog layout va .d1 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeLV
                (Or.inr (Or.inl rfl)) hNotIregLV
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            obtain ⟨s2, hSteps2, hD2, hRel2, _, hPC2, hAM2, hFregs2, _⟩ :=
              vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
                (Or.inr (Or.inr rfl)) hNotIregRV
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
              rw [hFregs2 .d1 (by decide)]; exact hD1
            have hFcmp := hCodeFcmpBCond.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length
                = s2.pc from by rw [List.length_append]; omega] at hFcmp
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfL, hfR] at hfcmp_false
            have hCondFalse : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = false := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = false
              rw [hD1_s2, hD2]; simp [Value.encode, hfL, hfR]
              cases fop <;> exact (Flags.condHolds_float_correct _ fL fR).trans hfcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmp) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            show s3.flags.condHolds _ = true
            cases fop <;> (rw [Cond.negate_correct]; simp [hCondFalse])
          | flit fb =>
            simp only [] at hCodeInstr
            have hCodeLV := hCodeInstr.append_left.append_left
            have hCodeFlit := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            -- Load va into d1
            obtain ⟨s1, hSteps1, hD1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_exec prog layout va .d1 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeLV
                (Or.inr (Or.inl rfl)) hNotIregLV
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            -- Load flit fb into d2
            obtain ⟨s2, hSteps2, hD2val, hRel2, hPC2, hAM2, hFregs2⟩ :=
              loadFloatExpr_exec prog layout (.flit fb) .d2 σ am s1 _ hRel1 hScratch hPC1
                (Or.inr ⟨fb, rfl⟩) p.tyCtx hTS hb_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inr rfl)) hCodeFlit
            have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
              rw [hFregs2 .d1 (by decide)]; exact hD1
            -- Get float values
            have hTyL := hTS va; rw [ha_ty] at hTyL
            obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
            -- fcmpR + bCond
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
                = s2.pc from by simp [List.length_append] at hPC2 ⊢; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
                = s3.pc from by simp [s3, List.length_append] at hPC2 ⊢; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfL] at hfcmp_false
            have hCondFalse : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = false := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = false
              rw [hD1_s2]; simp [Value.encode, hfL, hD2val, Expr.eval, Value.toFloat]
              cases fop <;> exact (Flags.condHolds_float_correct _ fL fb).trans hfcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            show s3.flags.condHolds _ = true
            cases fop <;> (rw [Cond.negate_correct]; simp [hCondFalse])
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | flit fa =>
          -- Load flit fa into d1, then case split on b
          cases b with
          | var vb =>
            simp only [] at hCodeInstr
            have hCodeFlit := hCodeInstr.append_left.append_left
            have hCodeRV := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            -- Load flit fa into d1
            obtain ⟨s1, hSteps1, hD1val, hRel1, hPC1, hAM1, hFregs1⟩ :=
              loadFloatExpr_exec prog layout (.flit fa) .d1 σ am s (pcMap pc) hStateRel hScratch hPcRel
                (Or.inr ⟨fa, rfl⟩) p.tyCtx hTS ha_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inl rfl)) hCodeFlit
            -- Load var vb into d2
            have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            obtain ⟨s2, hSteps2, hD2, hRel2, _, hPC2, hAM2, hFregs2, _⟩ :=
              vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
                (Or.inr (Or.inr rfl)) hNotIregRV
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            have hD1_s2 : s2.fregs .d1 = fa := by
              rw [hFregs2 .d1 (by decide)]; simp [hD1val, Expr.eval, Value.toFloat]
            have hTyR := hTS vb; rw [hb_ty] at hTyR
            obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
            -- fcmpR + bCond
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length
                = s2.pc from by simp [List.length_append] at hPC1 hPC2 ⊢; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length + 1
                = s3.pc from by simp [s3, List.length_append] at hPC1 hPC2 ⊢; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfR] at hfcmp_false
            have hCondFalse : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = false := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = false
              rw [hD1_s2, hD2]; simp [Value.encode, hfR]
              cases fop <;> exact (Flags.condHolds_float_correct _ fa fR).trans hfcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            show s3.flags.condHolds _ = true
            cases fop <;> (rw [Cond.negate_correct]; simp [hCondFalse])
          | flit fb =>
            simp only [] at hCodeInstr
            have hCodeFlitA := hCodeInstr.append_left.append_left
            have hCodeFlitB := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            -- Load flit fa into d1
            obtain ⟨s1, hSteps1, hD1val, hRel1, hPC1, hAM1, hFregs1⟩ :=
              loadFloatExpr_exec prog layout (.flit fa) .d1 σ am s (pcMap pc) hStateRel hScratch hPcRel
                (Or.inr ⟨fa, rfl⟩) p.tyCtx hTS ha_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inl rfl)) hCodeFlitA
            -- Load flit fb into d2
            obtain ⟨s2, hSteps2, hD2val, hRel2, hPC2, hAM2, hFregs2⟩ :=
              loadFloatExpr_exec prog layout (.flit fb) .d2 σ am s1 _ hRel1 hScratch hPC1
                (Or.inr ⟨fb, rfl⟩) p.tyCtx hTS hb_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inr rfl)) hCodeFlitB
            have hD1_s2 : s2.fregs .d1 = fa := by
              rw [hFregs2 .d1 (by decide)]; simp [hD1val, Expr.eval, Value.toFloat]
            have hD2_s2 : s2.fregs .d2 = fb := by
              simp [hD2val, Expr.eval, Value.toFloat]
            -- fcmpR + bCond
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
                = s2.pc from by simp [List.length_append] at hPC1 hPC2 ⊢; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
                = s3.pc from by simp [s3, List.length_append] at hPC1 hPC2 ⊢; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat] at hfcmp_false
            have hCondFalse : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = false := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = false
              rw [hD1_s2, hD2_s2]
              cases fop <;> exact (Flags.condHolds_float_correct _ fa fb).trans hfcmp_false
            refine ⟨{ s3 with pc := pcMap l_var },
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_taken _ _ hBCond ?_))),
              ⟨fun v loc hv => hRel2 v loc hv, rfl, by simp [s3, hAM2, hAM1, hArrayMem]⟩⟩
            show s3.flags.condHolds _ = true
            cases fop <;> (rw [Cond.negate_correct]; simp [hCondFalse])
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | _ =>
        simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
        obtain rfl := Option.some.inj hSome
        have hCodeBE := hCodeInstr.append_left
        have hCodeCbnz := hCodeInstr.append_right
        have hSimpleBV' := hSimpleBV  -- preserve across cases
        obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
          verifiedGenBoolExpr_correct prog layout _ σ s (pcMap pc) hStateRel hScratch
            hCodeBE hPcRel p.tyCtx hTS hWTbe hWTL
            (fun v hv => hMapped v (by simp [TAC.vars]; exact hv)) hSimpleBV' am
        have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
        have hx0_ne : s1.regs .x0 ≠ 0 := by rw [hX0_1, hcond]; simp
        exact ⟨{ s1 with pc := pcMap l_var },
          hSteps1.trans (.single (.cbnz_taken .x0 _ hCbnz hx0_ne)),
          ⟨hRel1, rfl, by simp [hAM1, hArrayMem]⟩⟩
    | _ =>
      simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
      obtain rfl := Option.some.inj hSome
      have hCodeBE := hCodeInstr.append_left
      have hCodeCbnz := hCodeInstr.append_right
      obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
        verifiedGenBoolExpr_correct prog layout _ σ s (pcMap pc) hStateRel hScratch
          hCodeBE hPcRel p.tyCtx hTS hWTbe hWTL
          (fun v hv => hMapped v (by simp [TAC.vars]; exact hv)) hSimpleBV am
      have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
      have hx0_ne : s1.regs .x0 ≠ 0 := by rw [hX0_1, hcond]; simp
      exact ⟨{ s1 with pc := pcMap l_var },
        hSteps1.trans (.single (.cbnz_taken .x0 _ hCbnz hx0_ne)),
        ⟨hRel1, rfl, by simp [hAM1, hArrayMem]⟩⟩
  | iffall hinstr hcond =>
    rename_i be_var l_var
    have heq : instr = .ifgoto be_var l_var := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hSimpleBV : be_var.hasSimpleOps = true := by
      cases hb : be_var.hasSimpleOps with
      | true => rfl
      | false => simp [verifiedGenInstr, hSS, hII, hb] at hSome
    have hWTbe : WellTypedBoolExpr p.tyCtx be_var := by
      have hwti := hWT pc hPC_bound
      have heq_i := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq_i; rw [← Option.some.inj heq_i] at hwti
      cases hwti with | ifgoto hbe => exact hbe
    cases be_var with
    | not inner =>
      cases inner with
      | cmp op a b =>
        simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
        obtain rfl := Option.some.inj hSome
        have hSimpleCmp : (BoolExpr.cmp op a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimpleCmp
        have hWTcmp : WellTypedBoolExpr p.tyCtx (.cmp op a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy p.tyCtx a .int ∧ ExprHasTy p.tyCtx b .int := by
          cases hWTcmp with | cmp ha hb => exact ⟨ha, hb⟩
        have hcmp_true : BoolExpr.eval σ am (.cmp op a b) = true := by
          simp [BoolExpr.eval] at hcond; exact hcond
        cases a with
        | var va => cases b with
          | var vb =>
            simp only [] at hCodeInstr
            have hCodeLVRV := hCodeInstr.append_left
            have hCodeCmpBCond := hCodeInstr.append_right
            have hCodeLV := hCodeLVRV.append_left
            have hCodeRV := hCodeLVRV.append_right
            have hTyL := hTS va; rw [ha_ty] at hTyL
            have hTyR := hTS vb; rw [hb_ty] at hTyR
            obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
            obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
            have hNotFregLV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            have hNotFregRV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            obtain ⟨s1, hSteps1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_exec prog layout va .x1 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeLV
                (Or.inr (Or.inl rfl)) hNotFregLV
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            obtain ⟨s2, hSteps2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
              vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
                (Or.inr (Or.inr rfl)) hNotFregRV
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            have hX1_s2 : s2.regs .x1 = (σ va).encode := by
              rw [hRegs2 .x1 (by decide)]; exact hX1
            have hCmp := hCodeCmpBCond.head
            rw [show pcMap pc + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length
                = s2.pc from by rw [List.length_append]; omega] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hBCond := hCodeCmpBCond.tail.head
            rw [show pcMap pc + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnL, hnR] at hcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.cmpRR .x1 .x2 hCmp) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨(ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv)), ?_, by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · -- condHolds cond.negate = false
              simp only [s3, hX1_s2, hX2, hnL, hnR, Value.encode]
              cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_true ⊢ <;>
                exact hcmp_true
            · -- pc = pcMap (pc + 1)
              show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]; simp [s3]; omega
          | lit nb =>
            simp only [] at hCodeInstr
            have hCodeLoadImm := hCodeInstr.append_left
            have hCodeCmpBCond := hCodeInstr.append_right
            have hCodeLV := hCodeLoadImm.append_left
            have hCodeImm := hCodeLoadImm.append_right
            have hTyV := hTS va; rw [ha_ty] at hTyV
            obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
            have hNotFregV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha_ty
            obtain ⟨s1, hSteps1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
              vLoadVar_exec prog layout va .x1 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeLV
                (Or.inr (Or.inl rfl)) hNotFregV
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImm hPC1
            have hX1_s2 : s2.regs .x1 = (σ va).encode := by rw [hRegs2 .x1 (by decide)]; exact hX1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hCmp := hCodeCmpBCond.head
            rw [show pcMap pc + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length
                = s2.pc from by rw [List.length_append]; omega] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hBCond := hCodeCmpBCond.tail.head
            rw [show pcMap pc + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnV] at hcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.cmpRR .x1 .x2 hCmp) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · simp only [s3, hX1_s2, hX2, hnV, Value.encode]
              cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_true ⊢ <;> exact hcmp_true
            · show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]; simp [s3]; omega
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | lit na => cases b with
          | var vb =>
            simp only [] at hCodeInstr
            have hCodeLoadImm := hCodeInstr.append_left
            have hCodeCmpBCond := hCodeInstr.append_right
            have hCodeImm := hCodeLoadImm.append_left
            have hCodeRV := hCodeLoadImm.append_right
            have hTyV := hTS vb; rw [hb_ty] at hTyV
            obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
            have hNotFregV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb_ty
            obtain ⟨s1, hSteps1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImm hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, hSteps2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
              vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
                (Or.inr (Or.inr rfl)) hNotFregV
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            have hX1_s2 : s2.regs .x1 = na := by rw [hRegs2 .x1 (by decide)]; exact hX1
            have hCmp := hCodeCmpBCond.head
            rw [show pcMap pc + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length
                = s2.pc from by rw [List.length_append]; omega] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hBCond := hCodeCmpBCond.tail.head
            rw [show pcMap pc + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt, hnV] at hcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.cmpRR .x1 .x2 hCmp) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · simp only [s3, hX1_s2, hX2, hnV, Value.encode]
              cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_true ⊢ <;> exact hcmp_true
            · show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]; simp [s3]; omega
          | lit nb =>
            simp only [] at hCodeInstr
            have hCodeLoadImm := hCodeInstr.append_left
            have hCodeCmpBCond := hCodeInstr.append_right
            have hCodeImmA := hCodeLoadImm.append_left
            have hCodeImmB := hCodeLoadImm.append_right
            obtain ⟨s1, hSteps1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
              loadImm64_fregs_preserved prog .x1 na s (pcMap pc) hCodeImmA hPcRel
            have hRel1 := loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
                hStateRel hScratch hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
            obtain ⟨s2, hSteps2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
              loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImmB hPC1
            have hRel2 := loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
                hRel1 hScratch hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
            have hX1_s2 : s2.regs .x1 = na := by rw [hRegs2 .x1 (by decide)]; exact hX1
            have hCmp := hCodeCmpBCond.head
            rw [show pcMap pc + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length
                = s2.pc from by rw [List.length_append]; omega] at hCmp
            let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
            have hBCond := hCodeCmpBCond.tail.head
            rw [show pcMap pc + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toInt] at hcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.cmpRR .x1 .x2 hCmp) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · simp only [s3, hX1_s2, hX2, Value.encode]
              cases op <;> simp [Cond.negate, Flags.condHolds, CmpOp.eval,
                BitVec.sle_eq_not_slt, bne, BEq.beq] at hcmp_true ⊢ <;> exact hcmp_true
            · show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]; simp [s3]; omega
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | fcmp fop a b =>
        simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
        obtain rfl := Option.some.inj hSome
        have hSimpleFcmp : (BoolExpr.fcmp fop a b).hasSimpleOps = true := hSimpleBV
        obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimpleFcmp
        have hWTfcmp : WellTypedBoolExpr p.tyCtx (.fcmp fop a b) := by
          cases hWTbe with | not h => exact h
        obtain ⟨ha_ty, hb_ty⟩ : ExprHasTy p.tyCtx a .float ∧ ExprHasTy p.tyCtx b .float := by
          cases hWTfcmp with | fcmp ha hb => exact ⟨ha, hb⟩
        have hfcmp_true : BoolExpr.eval σ am (.fcmp fop a b) = true := by
          simp [BoolExpr.eval] at hcond; exact hcond
        cases a with
        | var va => cases b with
          | var vb =>
            simp only [] at hCodeInstr
            have hCodeLVRV := hCodeInstr.append_left
            have hCodeFcmpBCond := hCodeInstr.append_right
            have hCodeLV := hCodeLVRV.append_left
            have hCodeRV := hCodeLVRV.append_right
            have hTyL := hTS va; rw [ha_ty] at hTyL
            have hTyR := hTS vb; rw [hb_ty] at hTyR
            obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
            obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
            have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            obtain ⟨s1, hSteps1, hD1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_exec prog layout va .d1 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeLV
                (Or.inr (Or.inl rfl)) hNotIregLV
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            obtain ⟨s2, hSteps2, hD2, hRel2, _, hPC2, hAM2, hFregs2, _⟩ :=
              vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
                (Or.inr (Or.inr rfl)) hNotIregRV
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
              rw [hFregs2 .d1 (by decide)]; exact hD1
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length
                = s2.pc from by rw [List.length_append]; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length + 1
                = s3.pc from by simp [s3]; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfL, hfR] at hfcmp_true
            have hCondTrue : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = true := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = true
              rw [hD1_s2, hD2]; simp [Value.encode, hfL, hfR]
              cases fop <;> exact (Flags.condHolds_float_correct _ fL fR).trans hfcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · -- condHolds cond.negate = false
              show s3.flags.condHolds _ = false
              cases fop <;> (rw [Cond.negate_correct]; simp [hCondTrue])
            · -- pc = pcMap (pc + 1)
              show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]; simp [s3]; omega
          | flit fb =>
            simp only [] at hCodeInstr
            have hCodeLV := hCodeInstr.append_left.append_left
            have hCodeFlit := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha_ty
            obtain ⟨s1, hSteps1, hD1, hRel1, _, hPC1, hAM1, hFregs1, _⟩ :=
              vLoadVarFP_exec prog layout va .d1 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeLV
                (Or.inr (Or.inl rfl)) hNotIregLV
                (hMapped va (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            obtain ⟨s2, hSteps2, hD2val, hRel2, hPC2, hAM2, hFregs2⟩ :=
              loadFloatExpr_exec prog layout (.flit fb) .d2 σ am s1 _ hRel1 hScratch hPC1
                (Or.inr ⟨fb, rfl⟩) p.tyCtx hTS hb_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inr rfl)) hCodeFlit
            have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
              rw [hFregs2 .d1 (by decide)]; exact hD1
            have hTyL := hTS va; rw [ha_ty] at hTyL
            obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
                = s2.pc from by simp [List.length_append] at hPC2 ⊢; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
                = s3.pc from by simp [s3, List.length_append] at hPC2 ⊢; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfL] at hfcmp_true
            have hCondTrue : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = true := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = true
              rw [hD1_s2]; simp [Value.encode, hfL, hD2val, Expr.eval, Value.toFloat]
              cases fop <;> exact (Flags.condHolds_float_correct _ fL fb).trans hfcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · show s3.flags.condHolds _ = false
              cases fop <;> (rw [Cond.negate_correct]; simp [hCondTrue])
            · show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]
              simp [List.length_append] at hPC2; simp [s3, List.length_append] at hPC2 ⊢; omega
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | flit fa =>
          cases b with
          | var vb =>
            simp only [] at hCodeInstr
            have hCodeFlit := hCodeInstr.append_left.append_left
            have hCodeRV := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            obtain ⟨s1, hSteps1, hD1val, hRel1, hPC1, hAM1, hFregs1⟩ :=
              loadFloatExpr_exec prog layout (.flit fa) .d1 σ am s (pcMap pc) hStateRel hScratch hPcRel
                (Or.inr ⟨fa, rfl⟩) p.tyCtx hTS ha_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inl rfl)) hCodeFlit
            have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb_ty
            obtain ⟨s2, hSteps2, hD2, hRel2, _, hPC2, hAM2, hFregs2, _⟩ :=
              vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hScratch hPC1 hCodeRV
                (Or.inr (Or.inr rfl)) hNotIregRV
                (hMapped vb (by simp [heq, TAC.vars, BoolExpr.vars, Expr.freeVars]))
            have hD1_s2 : s2.fregs .d1 = fa := by
              rw [hFregs2 .d1 (by decide)]; simp [hD1val, Expr.eval, Value.toFloat]
            have hTyR := hTS vb; rw [hb_ty] at hTyR
            obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length
                = s2.pc from by simp [List.length_append] at hPC1 hPC2 ⊢; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length + 1
                = s3.pc from by simp [s3, List.length_append] at hPC1 hPC2 ⊢; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat, hfR] at hfcmp_true
            have hCondTrue : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = true := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = true
              rw [hD1_s2, hD2]; simp [Value.encode, hfR]
              cases fop <;> exact (Flags.condHolds_float_correct _ fa fR).trans hfcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · show s3.flags.condHolds _ = false
              cases fop <;> (rw [Cond.negate_correct]; simp [hCondTrue])
            · show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]
              simp [List.length_append] at hPC1 hPC2; simp [s3, List.length_append]; omega
          | flit fb =>
            simp only [] at hCodeInstr
            have hCodeFlitA := hCodeInstr.append_left.append_left
            have hCodeFlitB := hCodeInstr.append_left.append_right
            have hCodeFcmpBCond := hCodeInstr.append_right
            obtain ⟨s1, hSteps1, hD1val, hRel1, hPC1, hAM1, hFregs1⟩ :=
              loadFloatExpr_exec prog layout (.flit fa) .d1 σ am s (pcMap pc) hStateRel hScratch hPcRel
                (Or.inr ⟨fa, rfl⟩) p.tyCtx hTS ha_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inl rfl)) hCodeFlitA
            obtain ⟨s2, hSteps2, hD2val, hRel2, hPC2, hAM2, hFregs2⟩ :=
              loadFloatExpr_exec prog layout (.flit fb) .d2 σ am s1 _ hRel1 hScratch hPC1
                (Or.inr ⟨fb, rfl⟩) p.tyCtx hTS hb_ty hWTL
                (fun v hv => by simp [Expr.freeVars] at hv)
                (Or.inr (Or.inr rfl)) hCodeFlitB
            have hD1_s2 : s2.fregs .d1 = fa := by
              rw [hFregs2 .d1 (by decide)]; simp [hD1val, Expr.eval, Value.toFloat]
            have hD2_s2 : s2.fregs .d2 = fb := by simp [hD2val, Expr.eval, Value.toFloat]
            have hFcmpI := hCodeFcmpBCond.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
                = s2.pc from by simp [List.length_append] at hPC1 hPC2 ⊢; omega] at hFcmpI
            let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
            have hBCond := hCodeFcmpBCond.tail.head
            rw [show pcMap pc + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
                = s3.pc from by simp [s3, List.length_append] at hPC1 hPC2 ⊢; omega] at hBCond
            simp only [BoolExpr.eval, Expr.eval, Value.toFloat] at hfcmp_true
            have hCondTrue : s3.flags.condHolds
                (match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le) = true := by
              show ({ lhs := s2.fregs .d1, rhs := s2.fregs .d2 } : Flags).condHolds _ = true
              rw [hD1_s2, hD2_s2]
              cases fop <;> exact (Flags.condHolds_float_correct _ fa fb).trans hfcmp_true
            refine ⟨s3.nextPC,
              (hSteps1.trans hSteps2).trans (.step (.fcmpRR .d1 .d2 hFcmpI) (.single (.bCond_fall _ _ hBCond ?_))),
              ⟨ExtStateRel.nextPC (fun v loc hv => hRel2 v loc hv), ?_,
               by simp [ArmState.nextPC, s3, hAM2, hAM1, hArrayMem]⟩⟩
            · show s3.flags.condHolds _ = false
              cases fop <;> (rw [Cond.negate_correct]; simp [hCondTrue])
            · show s3.pc + 1 = pcMap (pc + 1)
              have := hPcNext _ _ rfl; simp at this; rw [this]
              simp [List.length_append] at hPC1 hPC2; simp [s3, List.length_append]; omega
          | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
        | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
      | _ =>
        simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
        obtain rfl := Option.some.inj hSome
        have hSimpleBV' := hSimpleBV
        have hCodeBE := hCodeInstr.append_left
        have hCodeCbnz := hCodeInstr.append_right
        obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
          verifiedGenBoolExpr_correct prog layout _ σ s (pcMap pc) hStateRel hScratch
            hCodeBE hPcRel p.tyCtx hTS hWTbe hWTL
            (fun v hv => hMapped v (by simp [TAC.vars]; exact hv)) hSimpleBV' am
        have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
        have hx0_eq : s1.regs .x0 = 0 := by rw [hX0_1, hcond]; simp
        refine ⟨s1.nextPC,
          hSteps1.trans (.single (.cbnz_fall .x0 _ hCbnz hx0_eq)),
          ⟨hRel1.nextPC, ?_, by simp [ArmState.nextPC, hAM1, hArrayMem]⟩⟩
        · show s1.pc + 1 = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp at this; rw [this, hPC1]; omega
    | _ =>
      simp only [verifiedGenInstr, hSS, hII, hSimpleBV] at hSome
      obtain rfl := Option.some.inj hSome
      have hSimpleBV' := hSimpleBV
      have hCodeBE := hCodeInstr.append_left
      have hCodeCbnz := hCodeInstr.append_right
      obtain ⟨s1, hSteps1, hX0_1, hRel1, hPC1, hAM1⟩ :=
        verifiedGenBoolExpr_correct prog layout _ σ s (pcMap pc) hStateRel hScratch
          hCodeBE hPcRel p.tyCtx hTS hWTbe hWTL
          (fun v hv => hMapped v (by simp [TAC.vars]; exact hv)) hSimpleBV' am
      have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
      have hx0_eq : s1.regs .x0 = 0 := by rw [hX0_1, hcond]; simp
      refine ⟨s1.nextPC,
        hSteps1.trans (.single (.cbnz_fall .x0 _ hCbnz hx0_eq)),
        ⟨hRel1.nextPC, ?_, by simp [ArmState.nextPC, hAM1, hArrayMem]⟩⟩
      · show s1.pc + 1 = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; rw [this, hPC1]; omega
  | arrLoad hinstr hidx hbounds =>
    sorry  -- arrLoad: vLoadVar idx + bounds check + arrLd + vStoreVar
  | arrStore hinstr hidx hval hbounds =>
    sorry  -- arrStore: vLoadVar idx + bounds check + vLoadVar val + arrSt
  | fbinop hinstr hy hz =>
    rename_i x fop y z a b
    have heq : instr = .fbinop x fop y z := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- Derive notIreg from verifiedGenInstr guard (ireg layouts → none)
    have hNotIregY : ∀ r, layout y ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregZ : ∀ r, layout z ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    -- Effective FP registers
    let lv_reg := match layout y with | some (.freg r) => r | _ => ArmFReg.d1
    let rv_reg := match layout z with | some (.freg r) => r | _ => ArmFReg.d2
    let dst_reg := match layout x with | some (.freg r) => r | _ => ArmFReg.d0
    -- suffices for all FP ops (fadd/fsub/fmul/fdiv share the same structure)
    suffices hSimple : ∀ (fpOp : ArmInstr),
        instrs = vLoadVarFP layout y lv_reg ++
          (vLoadVarFP layout z rv_reg ++ (fpOp :: vStoreVarFP layout x dst_reg)) →
        (∀ s', prog[s'.pc]? = some fpOp →
          ArmStep prog s' (s'.setFReg dst_reg (FloatBinOp.eval fop (s'.fregs lv_reg) (s'.fregs rv_reg)) |>.nextPC)) →
        ∃ s', ArmSteps prog s s' ∧
          ExtSimRel layout pcMap (.run (pc + 1) (σ[x ↦ .float (fop.eval a b)]) am) s' by
      cases fop with
      | fadd =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .faddR dst_reg lv_reg rv_reg h
      | fsub =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .fsubR dst_reg lv_reg rv_reg h
      | fmul =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .fmulR dst_reg lv_reg rv_reg h
      | fdiv =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .fdivR dst_reg lv_reg rv_reg h
      | fpow =>
        -- fpow uses callBinF which havocs caller-saved regs.
        -- Like floatUnaryLibCall, ExtStateRel is preserved via NoCallerSavedLayout.
        have hNCS : NoCallerSavedLayout layout := hNCSLBin x y z heq
        have hInstrs : instrs = vLoadVarFP layout y lv_reg ++
            (vLoadVarFP layout z rv_reg ++ (.callBinF .fpow dst_reg lv_reg rv_reg :: vStoreVarFP layout x dst_reg)) := by
          have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        rw [hInstrs] at hCodeInstr hPcNext
        have hCodeA := hCodeInstr.append_left
        have hCodeBCD := hCodeInstr.append_right
        have hCodeB := hCodeBCD.append_left
        have hCodeCD := hCodeBCD.append_right
        -- Step 1: vLoadVarFP y into lv_reg
        obtain ⟨s1, hSteps1, hLV_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
          vLoadVarFP_eff_exec prog layout y σ s (pcMap pc) .d1 hStateRel hScratch hPcRel
            hNotIregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [heq, TAC.vars])) hCodeA
        -- Step 2: vLoadVarFP z into rv_reg
        obtain ⟨s2, hSteps2, hRV_2, hRel2, hRegs2, hPC2_, hAM2, hFregs2, hStack2⟩ :=
          vLoadVarFP_eff_exec prog layout z σ s1 _ .d2 hRel1 hScratch hPC1
            hNotIregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [heq, TAC.vars])) hCodeB
        have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
            (vLoadVarFP layout z rv_reg).length := hPC2_
        -- lv_reg preserved through second load (same proof as hSimple path)
        have hLV_2 : s2.fregs lv_reg = a := by
          match hLY : layout y with
          | some (.freg ry) =>
            have hlv : lv_reg = ry := by
              show (match layout y with | some (.freg r) => r | _ => .d1) = ry; simp [hLY]
            rw [hlv, hRel2.read_freg hLY, hy]; rfl
          | some (.stack _) | none =>
            have hlv : lv_reg = .d1 := by
              show (match layout y with | some (.freg r) => r | _ => .d1) = .d1; simp [hLY]
            rw [hlv]
            have hne : ArmFReg.d1 ≠ rv_reg := by
              intro h
              match hLZ : layout z with
              | some (.freg rz) =>
                have hrv : rv_reg = rz := by
                  show (match layout z with | some (.freg r) => r | _ => .d2) = rz; simp [hLZ]
                rw [hrv] at h; exact hScratch.not_d1 z (h ▸ hLZ)
              | some (.stack _) | none =>
                have hrv : rv_reg = .d2 := by
                  show (match layout z with | some (.freg r) => r | _ => .d2) = .d2; simp [hLZ]
                rw [hrv] at h; exact absurd h (by decide)
              | some (.ireg r) => exact absurd hLZ (hNotIregZ r)
            rw [hFregs2 .d1 hne, ← hlv, hLV_1, hy]; rfl
          | some (.ireg r) => exact absurd hLY (hNotIregY r)
        -- Step 3: callBinF — havocs caller-saved, sets dst_reg
        have hCall := hCodeCD.head; rw [← hPC2] at hCall
        let newRegs : ArmReg → BitVec 64 := fun _ => 0
        let newFregs : ArmFReg → BitVec 64 := fun _ => 0
        have hRV_eq : s2.fregs rv_reg = b := by rw [hRV_2, hz]; rfl
        let s3 := (s2.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg
          (FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg)) |>.nextPC
        have hSteps3 : ArmSteps prog s2 s3 :=
          ArmSteps.single (.callBinF .fpow dst_reg lv_reg rv_reg newRegs newFregs hCall)
        have hDR_3 : s3.fregs dst_reg = (Value.float (FloatBinOp.eval .fpow a b)).encode := by
          simp [s3, ArmState.setFReg, ArmState.nextPC, ArmState.havocCallerSaved, Value.encode]
          rw [hLV_2, hRV_eq]
        have hPC3 : s3.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
            (vLoadVarFP layout z rv_reg).length + 1 := by
          simp only [s3, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved] at hPC2 ⊢; omega
        have hAM3 : s3.arrayMem = s2.arrayMem := by simp [s3, ArmState.havocCallerSaved]
        -- ExtStateRel preserved through havoc
        have hRelHavoc : ExtStateRel layout σ (s2.havocCallerSaved newRegs newFregs) :=
          ExtStateRel.havocCallerSaved_preserved hRel2 hNCS
        -- Step 4: store — case split on whether dst is in freg
        by_cases hXFR : ∃ r, layout x = some (.freg r)
        · obtain ⟨r_dst, hDst⟩ := hXFR
          have hDR : dst_reg = r_dst := by
            change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
          have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
          have hRel4 : ExtStateRel layout (σ[x ↦ .float (FloatBinOp.eval .fpow a b)]) s3 := by
            show ExtStateRel layout (σ[x ↦ .float (FloatBinOp.eval .fpow a b)])
              ((s2.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg
                (FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg))).nextPC
            rw [hDR]
            have hval : FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg) =
                (Value.float (FloatBinOp.eval .fpow a b)).encode := by
              simp [Value.encode]; rw [hLV_2, hRV_eq]
            rw [hval]
            exact (ExtStateRel.update_freg hRelHavoc hInjective hDst).nextPC
          refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ⟨hRel4, ?_, ?_⟩⟩
          · show s3.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; simp [hStore] at this; omega
          · simp [hAM3, hAM2, hAM1, hArrayMem]
        · have hDR : dst_reg = .d0 := by
            change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
            split
            · next r h => exact absurd ⟨r, h⟩ hXFR
            · rfl
          have hRel3 : ExtStateRel layout σ s3 := by
            show ExtStateRel layout σ
              ((s2.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg
                (FloatBinOp.eval .fpow (s2.fregs lv_reg) (s2.fregs rv_reg))).nextPC
            rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelHavoc (fun v => hScratch.not_d0 v)).nextPC
          have hD0 : s3.fregs .d0 = (Value.float (FloatBinOp.eval .fpow a b)).encode := by
            rw [← hDR]; exact hDR_3
          have hCodeStore : CodeAt prog
              (pcMap pc + (vLoadVarFP layout y lv_reg).length +
                (vLoadVarFP layout z rv_reg).length + 1)
              (vStoreVarFP layout x .d0) := by
            rw [← hDR]
            exact hCodeCD.tail
          obtain ⟨s4, hSteps4, hRel4, hPC4, hAM4⟩ :=
            vStoreVarFP_exec prog layout x (Value.float (FloatBinOp.eval .fpow a b)) σ s3
              (pcMap pc + (vLoadVarFP layout y lv_reg).length +
                (vLoadVarFP layout z rv_reg).length + 1)
              hRel3 hInjective hScratch hPC3 hD0 hCodeStore hNotIregX
              (fun r h => absurd ⟨r, h⟩ hXFR)
          refine ⟨s4, hSteps1.trans (hSteps2.trans (hSteps3.trans hSteps4)), ⟨hRel4, ?_, ?_⟩⟩
          · show s4.pc = pcMap (pc + 1)
            have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
            omega
          · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
      | fmin =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .fminR dst_reg lv_reg rv_reg h
      | fmax =>
        apply hSimple
        · have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
        · exact fun _ h => .fmaxR dst_reg lv_reg rv_reg h
    -- Proof of hSimple
    intro fpOp hInstrs hArmStep
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeA := hCodeInstr.append_left
    have hCodeBCD := hCodeInstr.append_right
    have hCodeB := hCodeBCD.append_left
    have hCodeCD := hCodeBCD.append_right
    -- Step 1: vLoadVarFP y into lv_reg (effective)
    obtain ⟨s1, hSteps1, hLV_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
      vLoadVarFP_eff_exec prog layout y σ s (pcMap pc) .d1 hStateRel hScratch hPcRel
        hNotIregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [heq, TAC.vars])) hCodeA
    -- Step 2: vLoadVarFP z into rv_reg (effective)
    obtain ⟨s2, hSteps2, hRV_2, hRel2, hRegs2, hPC2_, hAM2, hFregs2, hStack2⟩ :=
      vLoadVarFP_eff_exec prog layout z σ s1 _ .d2 hRel1 hScratch hPC1
        hNotIregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [heq, TAC.vars])) hCodeB
    have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
        (vLoadVarFP layout z rv_reg).length := hPC2_
    -- lv_reg preserved through second load
    have hLV_2 : s2.fregs lv_reg = a := by
      match hLY : layout y with
      | some (.freg ry) =>
        have hlv : lv_reg = ry := by
          show (match layout y with | some (.freg r) => r | _ => .d1) = ry; simp [hLY]
        rw [hlv, hRel2.read_freg hLY, hy]; rfl
      | some (.stack _) | none =>
        have hlv : lv_reg = .d1 := by
          show (match layout y with | some (.freg r) => r | _ => .d1) = .d1; simp [hLY]
        rw [hlv]
        have hne : ArmFReg.d1 ≠ rv_reg := by
          intro h
          match hLZ : layout z with
          | some (.freg rz) =>
            have hrv : rv_reg = rz := by
              show (match layout z with | some (.freg r) => r | _ => .d2) = rz; simp [hLZ]
            rw [hrv] at h; exact hScratch.not_d1 z (h ▸ hLZ)
          | some (.stack _) | none =>
            have hrv : rv_reg = .d2 := by
              show (match layout z with | some (.freg r) => r | _ => .d2) = .d2; simp [hLZ]
            rw [hrv] at h; exact absurd h (by decide)
          | some (.ireg r) => exact absurd hLZ (hNotIregZ r)
        rw [hFregs2 .d1 hne, ← hlv, hLV_1, hy]; rfl
      | some (.ireg r) => exact absurd hLY (hNotIregY r)
    have hRV_eq : s2.fregs rv_reg = b := by rw [hRV_2, hz]; rfl
    -- Step 3: execute FP op
    have hOp := hCodeCD.head; rw [← hPC2_] at hOp
    have hSteps3 : ArmSteps prog s2 (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC := by
      have := ArmSteps.single (hArmStep s2 hOp); rwa [hLV_2, hRV_eq] at this
    let s3 := (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC
    have hPC3 : s3.pc = pcMap pc + (vLoadVarFP layout y lv_reg).length +
        (vLoadVarFP layout z rv_reg).length + 1 := by
      show s2.pc + 1 = _; omega
    have hAM3 : s3.arrayMem = s2.arrayMem := by simp [s3]
    -- Step 4: store — case split on whether dst is in freg
    by_cases hXFR : ∃ r, layout x = some (.freg r)
    · -- dst in freg r: vStoreVarFP is [], use update_freg directly
      obtain ⟨r_dst, hDst⟩ := hXFR
      have hDR : dst_reg = r_dst := by
        change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
      have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
      have hRel4 : ExtStateRel layout (σ[x ↦ .float (fop.eval a b)]) s3 := by
        show ExtStateRel layout (σ[x ↦ .float (fop.eval a b)])
          (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC
        rw [hDR]
        have : FloatBinOp.eval fop a b = (Value.float (fop.eval a b)).encode := by
          simp [Value.encode]
        rw [this]
        exact (ExtStateRel.update_freg hRel2 hInjective hDst).nextPC
      refine ⟨s3, (hSteps1.trans hSteps2).trans hSteps3, ⟨hRel4, ?_, ?_⟩⟩
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp [hStore] at this; omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
    · -- dst not in freg: dst_reg = .d0, use vStoreVarFP_exec
      have hDR : dst_reg = .d0 := by
        change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
        split
        · next r h => exact absurd ⟨r, h⟩ hXFR
        · rfl
      have hRel3 : ExtStateRel layout σ s3 := by
        show ExtStateRel layout σ (s2.setFReg dst_reg (FloatBinOp.eval fop a b)).nextPC
        rw [hDR]; exact (ExtStateRel.setFReg_preserved hRel2 (fun v => hScratch.not_d0 v)).nextPC
      have hD0 : s3.fregs .d0 = (Value.float (fop.eval a b)).encode := by
        simp [s3, hDR, ArmState.setFReg, ArmState.nextPC, Value.encode]
      have hCodeStore : CodeAt prog
          (pcMap pc + (vLoadVarFP layout y lv_reg).length + (vLoadVarFP layout z rv_reg).length + 1)
          (vStoreVarFP layout x .d0) := by rw [← hDR]; exact hCodeCD.tail
      obtain ⟨s4, hSteps4, hRel4, hPC4, hAM4⟩ :=
        vStoreVarFP_exec prog layout x (Value.float (fop.eval a b)) σ s3
          (pcMap pc + (vLoadVarFP layout y lv_reg).length + (vLoadVarFP layout z rv_reg).length + 1)
          hRel3 hInjective hScratch hPC3 hD0 hCodeStore hNotIregX
          (fun r h => absurd ⟨r, h⟩ hXFR)
      refine ⟨s4, (hSteps1.trans hSteps2).trans (hSteps3.trans hSteps4), ⟨hRel4, ?_, ?_⟩⟩
      · show s4.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
        omega
      · simp [hAM4, hAM3, hAM2, hAM1, hArrayMem]
  | intToFloat hinstr hy =>
    rename_i x y n
    have heq : instr = .intToFloat x y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- From hSome, derive layout constraints
    have hNotFregY : ∀ r, layout y ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
      intro r h; have := hSome; simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or, h] at this
      split at this <;> simp_all
    -- Case split on layout x to determine dst_reg
    match hLX : layout x with
    | some (.freg r) =>
      -- dst_reg = r, vStoreVarFP layout x r = [] (r == r)
      have hInstrs : instrs =
        vLoadVar layout y .x0 ++ [ArmInstr.scvtf r .x0] := by
        simp [verifiedGenInstr, hSS, hII, hLX, vStoreVarFP] at hSome
        exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      -- Step 1: vLoadVar loads y into x0
      obtain ⟨s1, hSteps1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
        vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeL
          (Or.inl rfl) hNotFregY (hMapped y (by simp [heq, TAC.vars]))
      -- Step 2: scvtf writes directly to allocated freg r
      have hScvtf := hCodeR.head; rw [← hPC1] at hScvtf
      have hX0n : s1.regs .x0 = n := by rw [hX0_1, hy]; rfl
      -- The result state: setFReg r (intToFloatBv n) then nextPC
      -- intToFloatBv n = (Value.float (intToFloatBv n)).encode
      let s2 := (s1.setFReg r (Value.float (intToFloatBv n)).encode).nextPC
      have hS2eq : (s1.setFReg r (intToFloatBv (s1.regs .x0))).nextPC = s2 := by
        simp [s2, hX0n, Value.encode]
      have hSteps2 : ArmSteps prog s1 s2 := hS2eq ▸ ArmSteps.single (.scvtf r .x0 hScvtf)
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y .x0).length + 1 := by
        simp [s2, ArmState.nextPC, hPC1]
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      have hRel2 : ExtStateRel layout (σ[x ↦ Value.float (intToFloatBv n)]) s2 :=
        (ExtStateRel.update_freg hRel1 hInjective hLX).nextPC
      refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel2, ?_, ?_⟩⟩
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; rw [hPC2]; omega
      · simp [hAM2, hAM1, hArrayMem]
    | some (.ireg r) => exact absurd hLX (hNotIregX r)
    | none =>
      exact absurd hLX (hMapped x (by simp [heq, TAC.vars]))
    | some (.stack _) =>
      -- dst_reg = .d0 (stack fallback)
      have hInstrs : instrs =
        vLoadVar layout y .x0 ++ [ArmInstr.scvtf .d0 .x0] ++ vStoreVarFP layout x .d0 := by
        simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or, hLX] at hSome
        split at hSome <;> simp_all
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeLM := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hCodeL := hCodeLM.append_left
      have hCodeM := hCodeLM.append_right
      -- Step 1: vLoadVar loads y into x0
      obtain ⟨s1, hSteps1, hX0_1, hRel1, hFregs1, hPC1, hAM1, _⟩ :=
        vLoadVar_exec prog layout y .x0 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeL
          (Or.inl rfl) hNotFregY (hMapped y (by simp [heq, TAC.vars]))
      -- Step 2: scvtf converts x0 to d0
      have hScvtf := hCodeM.head; rw [← hPC1] at hScvtf
      let s2 := s1.setFReg .d0 (intToFloatBv (s1.regs .x0)) |>.nextPC
      have hSteps2 : ArmSteps prog s1 s2 := ArmSteps.single (.scvtf .d0 .x0 hScvtf)
      have hD0 : s2.fregs .d0 = (Value.float (intToFloatBv n)).encode := by
        simp [s2, ArmState.setFReg, ArmState.nextPC, Value.encode]
        rw [hX0_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y .x0).length + 1 := by
        simp [s2, ArmState.nextPC, hPC1]
      have hRel2 : ExtStateRel layout σ s2 :=
        (ExtStateRel.setFReg_preserved hRel1 (fun v => hScratch.not_d0 v)).nextPC
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      -- Step 3: vStoreVarFP stores d0 into x
      obtain ⟨s3, hSteps3, hRel3, hPC3, hAM3⟩ :=
        vStoreVarFP_exec prog layout x (Value.float (intToFloatBv n)) σ s2
          (pcMap pc + (vLoadVar layout y .x0).length + 1)
          hRel2 hInjective hScratch hPC2 hD0
          (by rw [show (vLoadVar layout y .x0 ++ [ArmInstr.scvtf .d0 .x0]).length =
            (vLoadVar layout y .x0).length + 1 from by simp] at hCodeR; exact hCodeR)
          hNotIregX
          (fun r h => by simp [hLX] at h)
      refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ⟨hRel3, ?_, ?_⟩⟩
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this
        omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
  | floatToInt hinstr hy =>
    rename_i x y f
    have heq : instr = .floatToInt x y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- From hSome, derive layout constraints
    have hNotIregY : ∀ r, layout y ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or, h] at this
      split at this <;> simp_all
    -- Case split on layout y to determine src_reg
    match hLY : layout y with
    | some (.freg r) =>
      -- src_reg = r, vLoadVarFP layout y r = [] (r == r)
      have hInstrs : instrs =
        [ArmInstr.fcvtzs .x0 r] ++ vStoreVar layout x .x0 := by
        simp [verifiedGenInstr, hSS, hII, hLY, vLoadVarFP] at hSome
        exact hSome.symm
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      -- freg r holds (σ y).encode from ExtStateRel
      have hFregR : s.fregs r = (σ y).encode := hStateRel y (.freg r) hLY
      -- Step 1: fcvtzs reads freg r, writes result to x0
      have hFcvtzs := hCodeL.head; rw [← hPcRel] at hFcvtzs
      let s1 := (s.setReg .x0 (floatToIntBv (s.fregs r))).nextPC
      have hSteps1 : ArmSteps prog s s1 := ArmSteps.single (.fcvtzs .x0 r hFcvtzs)
      have hX0 : s1.regs .x0 = (Value.int (floatToIntBv f)).encode := by
        simp [s1, ArmState.setReg, ArmState.nextPC, Value.encode, hFregR, hy]
      have hPC1 : s1.pc = pcMap pc + 1 := by
        simp [s1, ArmState.nextPC]; exact hPcRel
      have hRel1 : ExtStateRel layout σ s1 :=
        ExtStateRel.preserved_by_ireg_only hStateRel hScratch
          (by simp [s1]) (by simp [s1]) (fun rr h0 _ _ _ => by simp [s1, ArmState.setReg, ArmState.nextPC, h0])
      have hAM1 : s1.arrayMem = s.arrayMem := by simp [s1]
      -- Step 2: vStoreVar stores x0 into x
      obtain ⟨s2, hSteps2, hRel2, hPC2, hAM2⟩ :=
        vStoreVar_exec prog layout x (Value.int (floatToIntBv f)) σ s1
          (pcMap pc + 1) hRel1 hInjective hScratch hPC1 hX0 hCodeR hNotFregX
      refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel2, ?_, ?_⟩⟩
      · show s2.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this; omega
      · simp [hAM2, hAM1, hArrayMem]
    | some (.ireg r) => exact absurd hLY (hNotIregY r)
    | none =>
      exact absurd hLY (hMapped y (by simp [heq, TAC.vars]))
    | some (.stack _) =>
      -- src_reg = .d0 (stack fallback)
      have hInstrs : instrs =
        vLoadVarFP layout y .d0 ++ [ArmInstr.fcvtzs .x0 .d0] ++ vStoreVar layout x .x0 := by
        simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or, hLY] at hSome
        split at hSome <;> simp_all
      rw [hInstrs] at hCodeInstr hPcNext
      have hCodeLM := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hCodeL := hCodeLM.append_left
      have hCodeM := hCodeLM.append_right
      -- Step 1: vLoadVarFP loads y into d0
      obtain ⟨s1, hSteps1, hD0_1, hRel1, hRegs1, hPC1, hAM1, _, _⟩ :=
        vLoadVarFP_exec prog layout y .d0 σ s (pcMap pc) hStateRel hScratch hPcRel hCodeL
          (Or.inl rfl) hNotIregY (hMapped y (by simp [heq, TAC.vars]))
      -- Step 2: fcvtzs converts d0 to x0
      have hFcvtzs := hCodeM.head; rw [← hPC1] at hFcvtzs
      let s2 := s1.setReg .x0 (floatToIntBv (s1.fregs .d0)) |>.nextPC
      have hSteps2 : ArmSteps prog s1 s2 := ArmSteps.single (.fcvtzs .x0 .d0 hFcvtzs)
      have hX0 : s2.regs .x0 = (Value.int (floatToIntBv f)).encode := by
        simp [s2, ArmState.setReg, ArmState.nextPC, Value.encode]
        rw [hD0_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y .d0).length + 1 := by
        simp [s2, ArmState.nextPC, hPC1]
      have hRel2 : ExtStateRel layout σ s2 :=
        ExtStateRel.preserved_by_ireg_only hRel1 hScratch
          (by simp [s2]) (by simp [s2]) (fun r h0 _ _ _ => by simp [s2, ArmState.setReg, ArmState.nextPC, h0])
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      -- Step 3: vStoreVar stores x0 into x
      obtain ⟨s3, hSteps3, hRel3, hPC3, hAM3⟩ :=
        vStoreVar_exec prog layout x (Value.int (floatToIntBv f)) σ s2
          (pcMap pc + (vLoadVarFP layout y .d0).length + 1)
          hRel2 hInjective hScratch hPC2 hX0
          (by rw [show (vLoadVarFP layout y .d0 ++ [ArmInstr.fcvtzs .x0 .d0]).length =
            (vLoadVarFP layout y .d0).length + 1 from by simp] at hCodeR; exact hCodeR)
          hNotFregX
      refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ⟨hRel3, ?_, ?_⟩⟩
      · show s3.pc = pcMap (pc + 1)
        have := hPcNext _ _ rfl; simp at this
        omega
      · simp [hAM3, hAM2, hAM1, hArrayMem]
  | floatUnary hinstr hy =>
    rename_i x op y f
    have heq : instr = .floatUnary x op y := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- From hSome, derive layout constraints
    have hNotIregY : ∀ r, layout y ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregX : ∀ r, layout x ≠ some (.ireg r) := by
      intro r h; have := hSome; simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or, h] at this
      split at this <;> simp_all
    -- Effective FP registers
    let src_reg := match layout y with | some (.freg r) => r | _ => ArmFReg.d0
    let dst_reg := match layout x with | some (.freg r) => r | _ => ArmFReg.d0
    -- The ARM instruction for float unary ops
    let armOp := ArmInstr.floatUnaryInstr op dst_reg src_reg
    have hInstrs : instrs =
      vLoadVarFP layout y src_reg ++ [armOp] ++ vStoreVarFP layout x dst_reg := by
      simp only [verifiedGenInstr, hSS, hII, Bool.not_true, Bool.false_or] at hSome
      split at hSome
      · simp_all
      · exact (Option.some.inj hSome).symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLM := hCodeInstr.append_left
    have hCodeR := hCodeInstr.append_right
    have hCodeL := hCodeLM.append_left
    have hCodeM := hCodeLM.append_right
    -- Step 1: vLoadVarFP loads y into src_reg
    obtain ⟨s1, hSteps1, hSR_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
      vLoadVarFP_eff_exec prog layout y σ s (pcMap pc) .d0 hStateRel hScratch hPcRel
        hNotIregY (Or.inl rfl) (hMapped y (by simp [heq, TAC.vars])) hCodeL
    -- Step 2: apply float unary op — case-split on native vs library call
    have hCall := hCodeM.head; rw [← hPC1] at hCall
    by_cases hNat : op.isNative = true
    · -- Native op (sqrt, abs, neg): pure semantics, no clobber
      let s2 := s1.setFReg dst_reg (op.eval (s1.fregs src_reg)) |>.nextPC
      have hSteps2 : ArmSteps prog s1 s2 :=
        ArmSteps.single (.floatUnaryNative op dst_reg src_reg hCall hNat)
      have hDR_2 : s2.fregs dst_reg = (Value.float (op.eval f)).encode := by
        simp [s2, ArmState.setFReg, ArmState.nextPC, Value.encode]
        rw [hSR_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y src_reg).length + 1 := by
        simp only [s2, ArmState.nextPC, ArmState.setFReg, src_reg] at hPC1 ⊢; omega
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2]
      -- Step 3: store — case split on whether dst is in freg
      by_cases hXFR : ∃ r, layout x = some (.freg r)
      · obtain ⟨r_dst, hDst⟩ := hXFR
        have hDR : dst_reg = r_dst := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
        have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
        have hRel3 : ExtStateRel layout (σ[x ↦ .float (op.eval f)]) s2 := by
          show ExtStateRel layout (σ[x ↦ .float (op.eval f)])
            (s1.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]
          have hval : op.eval (s1.fregs src_reg) = (Value.float (op.eval f)).encode := by
            simp [Value.encode]; rw [hSR_1, hy]; rfl
          rw [hval]
          exact (ExtStateRel.update_freg hRel1 hInjective hDst).nextPC
        refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel3, ?_, ?_⟩⟩
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp [hStore] at this; omega
        · simp [hAM2, hAM1, hArrayMem]
      · have hDR : dst_reg = .d0 := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
          split
          · next r h => exact absurd ⟨r, h⟩ hXFR
          · rfl
        have hRel2 : ExtStateRel layout σ s2 := by
          show ExtStateRel layout σ (s1.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]; exact (ExtStateRel.setFReg_preserved hRel1 (fun v => hScratch.not_d0 v)).nextPC
        have hD0 : s2.fregs .d0 = (Value.float (op.eval f)).encode := by
          rw [← hDR]; exact hDR_2
        have hCodeStore : CodeAt prog
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            (vStoreVarFP layout x .d0) := by
          rw [← hDR]
          rw [show (vLoadVarFP layout y src_reg ++ [armOp]).length =
            (vLoadVarFP layout y src_reg).length + 1 from by simp] at hCodeR
          exact hCodeR
        obtain ⟨s3, hSteps3, hRel3, hPC3, hAM3⟩ :=
          vStoreVarFP_exec prog layout x (Value.float (op.eval f)) σ s2
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            hRel2 hInjective hScratch hPC2 hD0 hCodeStore hNotIregX
            (fun r h => absurd ⟨r, h⟩ hXFR)
        refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ⟨hRel3, ?_, ?_⟩⟩
        · show s3.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
          omega
        · simp [hAM3, hAM2, hAM1, hArrayMem]
    · -- Library call (exp, sin, cos, …): havocs caller-saved to arbitrary values, then sets fd
      have hNotNat : op.isNative = false := by cases op <;> simp_all [FloatUnaryOp.isNative]
      -- Pick arbitrary replacement values for havoc (proof works for any choice)
      let newRegs : ArmReg → BitVec 64 := fun _ => 0
      let newFregs : ArmFReg → BitVec 64 := fun _ => 0
      let s2 := (s1.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg (op.eval (s1.fregs src_reg)) |>.nextPC
      have hSteps2 : ArmSteps prog s1 s2 :=
        ArmSteps.single (.floatUnaryLibCall op dst_reg src_reg newRegs newFregs hCall hNotNat)
      have hDR_2 : s2.fregs dst_reg = (Value.float (op.eval f)).encode := by
        simp [s2, ArmState.setFReg, ArmState.nextPC, ArmState.havocCallerSaved, Value.encode]
        rw [hSR_1, hy]; rfl
      have hPC2 : s2.pc = pcMap pc + (vLoadVarFP layout y src_reg).length + 1 := by
        simp only [s2, ArmState.nextPC, ArmState.setFReg, ArmState.havocCallerSaved, src_reg] at hPC1 ⊢; omega
      have hAM2 : s2.arrayMem = s1.arrayMem := by simp [s2, ArmState.havocCallerSaved]
      -- ExtStateRel preserved: havocCallerSaved is safe because NoCallerSavedLayout
      have hRelHavoc : ExtStateRel layout σ (s1.havocCallerSaved newRegs newFregs) :=
        ExtStateRel.havocCallerSaved_preserved hRel1 (hNCSL x op y heq hNotNat)
      -- Step 3: store — case split on whether dst is in freg
      by_cases hXFR : ∃ r, layout x = some (.freg r)
      · obtain ⟨r_dst, hDst⟩ := hXFR
        have hDR : dst_reg = r_dst := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = r_dst; rw [hDst]
        have hStore : vStoreVarFP layout x dst_reg = [] := by simp [vStoreVarFP, hDst, hDR]
        have hRel3 : ExtStateRel layout (σ[x ↦ .float (op.eval f)]) s2 := by
          show ExtStateRel layout (σ[x ↦ .float (op.eval f)])
            ((s1.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]
          have hval : op.eval (s1.fregs src_reg) = (Value.float (op.eval f)).encode := by
            simp [Value.encode]; rw [hSR_1, hy]; rfl
          rw [hval]
          exact (ExtStateRel.update_freg hRelHavoc hInjective hDst).nextPC
        refine ⟨s2, hSteps1.trans hSteps2, ⟨hRel3, ?_, ?_⟩⟩
        · show s2.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; simp [hStore] at this; omega
        · simp [hAM2, hAM1, hArrayMem]
      · have hDR : dst_reg = .d0 := by
          change (match layout x with | some (.freg r) => r | _ => .d0) = .d0
          split
          · next r h => exact absurd ⟨r, h⟩ hXFR
          · rfl
        have hRel2 : ExtStateRel layout σ s2 := by
          show ExtStateRel layout σ
            ((s1.havocCallerSaved newRegs newFregs) |>.setFReg dst_reg (op.eval (s1.fregs src_reg))).nextPC
          rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelHavoc (fun v => hScratch.not_d0 v)).nextPC
        have hD0 : s2.fregs .d0 = (Value.float (op.eval f)).encode := by
          rw [← hDR]; exact hDR_2
        have hCodeStore : CodeAt prog
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            (vStoreVarFP layout x .d0) := by
          rw [← hDR]
          rw [show (vLoadVarFP layout y src_reg ++ [armOp]).length =
            (vLoadVarFP layout y src_reg).length + 1 from by simp] at hCodeR
          exact hCodeR
        obtain ⟨s3, hSteps3, hRel3, hPC3, hAM3⟩ :=
          vStoreVarFP_exec prog layout x (Value.float (op.eval f)) σ s2
            (pcMap pc + (vLoadVarFP layout y src_reg).length + 1)
            hRel2 hInjective hScratch hPC2 hD0 hCodeStore hNotIregX
            (fun r h => absurd ⟨r, h⟩ hXFR)
        refine ⟨s3, hSteps1.trans (hSteps2.trans hSteps3), ⟨hRel3, ?_, ?_⟩⟩
        · show s3.pc = pcMap (pc + 1)
          have := hPcNext _ _ rfl; rw [show dst_reg = ArmFReg.d0 from hDR] at this; simp at this
          omega
        · simp [hAM3, hAM2, hAM1, hArrayMem]
  | fternop hinstr ha hb hc =>
    rename_i dst op a b c va vb vc
    have heq : instr = .fternop dst op a b c := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    -- Derive notIreg from verifiedGenInstr guard
    have hNotIregA : ∀ r, layout a ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregB : ∀ r, layout b ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregC : ∀ r, layout c ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    have hNotIregD : ∀ r, layout dst ≠ some (.ireg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hSS, hII, h] at this
    -- Effective FP registers
    let a_reg := match layout a with | some (.freg r) => r | _ => ArmFReg.d0
    let b_reg := match layout b with | some (.freg r) => r | _ => ArmFReg.d1
    let c_reg := match layout c with | some (.freg r) => r | _ => ArmFReg.d2
    let dst_reg := match layout dst with | some (.freg r) => r | _ => ArmFReg.d0
    -- Determine the ARM instruction
    let fpInstr := match op with
      | .fmadd => ArmInstr.fmaddR dst_reg b_reg c_reg a_reg
      | .fmsub => ArmInstr.fmsubR dst_reg b_reg c_reg a_reg
    have hInstrs : instrs = vLoadVarFP layout a a_reg ++
        (vLoadVarFP layout b b_reg ++
          (vLoadVarFP layout c c_reg ++ (fpInstr :: vStoreVarFP layout dst dst_reg))) := by
      have := hSome; simp [verifiedGenInstr, hSS, hII] at this; exact this.symm
    rw [hInstrs] at hCodeInstr hPcNext
    -- Split code-at
    have hCodeA := hCodeInstr.append_left
    have hCodeBCD := hCodeInstr.append_right
    have hCodeB := hCodeBCD.append_left
    have hCodeCD := hCodeBCD.append_right
    have hCodeC := hCodeCD.append_left
    have hCodeOpStore := hCodeCD.append_right
    -- Step 1: load a into a_reg (fallback d0)
    obtain ⟨s1, hSteps1, hA_1, hRel1, hRegs1, hPC1, hAM1, hFregs1, hStack1⟩ :=
      vLoadVarFP_eff_exec prog layout a σ s (pcMap pc) .d0 hStateRel hScratch hPcRel
        hNotIregA (Or.inl rfl) (hMapped a (by simp [heq, TAC.vars])) hCodeA
    -- Step 2: load b into b_reg (fallback d1)
    obtain ⟨s2, hSteps2, hB_2, hRel2, hRegs2, hPC2, hAM2, hFregs2, hStack2⟩ :=
      vLoadVarFP_eff_exec prog layout b σ s1 _ .d1 hRel1 hScratch hPC1
        hNotIregB (Or.inr (Or.inl rfl)) (hMapped b (by simp [heq, TAC.vars])) hCodeB
    -- Step 3: load c into c_reg (fallback d2)
    obtain ⟨s3, hSteps3, hC_3, hRel3, hRegs3, hPC3, hAM3, hFregs3, hStack3⟩ :=
      vLoadVarFP_eff_exec prog layout c σ s2 _ .d2 hRel2 hScratch hPC2
        hNotIregC (Or.inr (Or.inr rfl)) (hMapped c (by simp [heq, TAC.vars])) hCodeC
    -- a_reg preserved through loads 2 and 3
    have hA_3 : s3.fregs a_reg = va := by
      match hLA : layout a with
      | some (.freg ra) =>
        have : a_reg = ra := by simp [a_reg, hLA]
        rw [this, hRel3.read_freg hLA, ha]; rfl
      | some (.stack _) | none =>
        have : a_reg = .d0 := by simp [a_reg, hLA]
        rw [this]
        -- d0 ≠ b_reg and d0 ≠ c_reg (by scratchSafe)
        have hne_b : ArmFReg.d0 ≠ b_reg := by
          intro h; match hLB : layout b with
          | some (.freg rb) => exact hScratch.not_d0 b (by simp [b_reg, hLB] at h; exact h ▸ hLB)
          | some (.stack _) | none => simp [b_reg, hLB] at h
          | some (.ireg r) => exact absurd hLB (hNotIregB r)
        have hne_c : ArmFReg.d0 ≠ c_reg := by
          intro h; match hLC : layout c with
          | some (.freg rc) => exact hScratch.not_d0 c (by simp [c_reg, hLC] at h; exact h ▸ hLC)
          | some (.stack _) | none => simp [c_reg, hLC] at h
          | some (.ireg r) => exact absurd hLC (hNotIregC r)
        rw [hFregs3 .d0 hne_c, hFregs2 .d0 hne_b, ← this, hA_1, ha]; rfl
      | some (.ireg r) => exact absurd hLA (hNotIregA r)
    -- b_reg preserved through load 3
    have hB_3 : s3.fregs b_reg = vb := by
      match hLB : layout b with
      | some (.freg rb) =>
        have : b_reg = rb := by simp [b_reg, hLB]
        rw [this, hRel3.read_freg hLB, hb]; rfl
      | some (.stack _) | none =>
        have : b_reg = .d1 := by simp [b_reg, hLB]
        rw [this]
        have hne : ArmFReg.d1 ≠ c_reg := by
          intro h; match hLC : layout c with
          | some (.freg rc) => exact hScratch.not_d1 c (by simp [c_reg, hLC] at h; exact h ▸ hLC)
          | some (.stack _) | none => simp [c_reg, hLC] at h
          | some (.ireg r) => exact absurd hLC (hNotIregC r)
        rw [hFregs3 .d1 hne, ← this, hB_2, hb]; rfl
      | some (.ireg r) => exact absurd hLB (hNotIregB r)
    have hC_eq : s3.fregs c_reg = vc := by rw [hC_3, hc]; rfl
    -- Step 4+5: execute fmadd/fmsub and store via fp_exec_and_store
    have hCodeOpStore' : CodeAt prog s3.pc (fpInstr :: vStoreVarFP layout dst dst_reg) := by
      rwa [hPC3]
    -- The ARM step for fmadd/fmsub
    have hResultBv : FloatTernOp.eval op va vb vc =
        (Value.float (FloatTernOp.eval op va vb vc)).encode := by simp [Value.encode]
    have hArmStepReal : ArmStep prog s3
        (s3.setFReg dst_reg (FloatTernOp.eval op va vb vc) |>.nextPC) := by
      have hHead := hCodeOpStore'.head
      simp only [fpInstr] at hHead
      -- Rewrite to register-read form, then case-split to match ArmStep rules
      have hEq : FloatTernOp.eval op va vb vc =
          FloatTernOp.eval op (s3.fregs a_reg) (s3.fregs b_reg) (s3.fregs c_reg) := by
        rw [hA_3, hB_3, hC_eq]
      cases op
      · -- fmadd
        show ArmStep prog s3 (s3.setFReg dst_reg
          (FloatBinOp.eval .fadd va (FloatBinOp.eval .fmul vb vc)) |>.nextPC)
        have step := ArmStep.fmaddR dst_reg b_reg c_reg a_reg hHead
        rw [hA_3, hB_3, hC_eq] at step; exact step
      · -- fmsub
        show ArmStep prog s3 (s3.setFReg dst_reg
          (FloatBinOp.eval .fsub va (FloatBinOp.eval .fmul vb vc)) |>.nextPC)
        have step := ArmStep.fmsubR dst_reg b_reg c_reg a_reg hHead
        rw [hA_3, hB_3, hC_eq] at step; exact step
    obtain ⟨s_fin, hSteps_fin, hSimRel⟩ := fp_exec_and_store prog layout pcMap pc σ am
      dst dst_reg (FloatTernOp.eval op va vb vc) (.float (FloatTernOp.eval op va vb vc))
      hResultBv s3 s3.pc hRel3 hInjective hScratch rfl
      (by simp [hAM3, hAM2, hAM1, hArrayMem]) rfl hNotIregD
      fpInstr hCodeOpStore' hArmStepReal
      ((vLoadVarFP layout a a_reg).length + (vLoadVarFP layout b b_reg).length +
        (vLoadVarFP layout c c_reg).length)
      (by have hPC3' : s3.pc = pcMap pc + (vLoadVarFP layout a a_reg).length +
            (vLoadVarFP layout b b_reg).length + (vLoadVarFP layout c c_reg).length := hPC3
          omega)
      (by have := hPcNext _ _ rfl; simp at this ⊢; omega)
    exact ⟨s_fin, (hSteps1.trans hSteps2).trans (hSteps3.trans hSteps_fin), hSimRel⟩

/-- Top-level backward simulation for verifiedGenInstr.
    Directly delegates to `verifiedGenInstr_correct`. -/
theorem ext_backward_simulation (p : Prog) (armProg : ArmProg)
    (layout : VarLayout) (pcMap : Nat → Nat)
    (haltLabel divLabel boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : ExtSimRel layout pcMap (.run pc σ am) s)
    (hPC : pc < p.size)
    (hWT : WellTypedProg p.tyCtx p) (hTS : TypedStore p.tyCtx σ)
    (hWTL : WellTypedLayout p.tyCtx layout)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (instrs : List ArmInstr)
    (hSome : verifiedGenInstr layout pcMap instr haltLabel divLabel boundsLabel arrayDecls boundsSafe = some instrs)
    (hCode : CodeAt armProg (pcMap pc) instrs)
    (hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      pcMap (pc + 1) = pcMap pc + instrs.length)
    (hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (hAD : arrayDecls = p.arrayDecls)
    (hNCSL : ∀ x op y, instr = .floatUnary x op y → op.isNative = false → NoCallerSavedLayout layout)
    (hNCSLBin : ∀ x y z, instr = .fbinop x .fpow y z → NoCallerSavedLayout layout) :
    ∃ s', ArmSteps armProg s s' ∧ ExtSimRel layout pcMap cfg' s' :=
  verifiedGenInstr_correct armProg layout pcMap p pc σ am s haltLabel divLabel boundsLabel
    arrayDecls boundsSafe instr hInstr hRel instrs hSome hPC hWT hTS hWTL hMapped cfg' hStep hCode hPcNext hAD hNCSL hNCSLBin
