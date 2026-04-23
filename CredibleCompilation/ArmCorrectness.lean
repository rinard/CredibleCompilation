import CredibleCompilation.ArmSemantics
import CredibleCompilation.BvLemmas
import CredibleCompilation.ExecChecker
import Std.Tactic.BVDecide

/-!
# ARM64 Correctness Proofs

Correctness theorems for the ARM64 code generation: loadImm64_correct,
Flags.condHolds_correct, verifiedGenBoolExpr_correct,
verifiedGenInstr_correct, and ext_backward_simulation.
-/

-- === Helpers for loadImm64_correct large case ===

private theorem uint64_nat_roundtrip (u : UInt64) : u.toNat.toUInt64 = u := by
  apply UInt64.eq_of_toBitVec_eq
  simp [Nat.toUInt64]
private theorem BitVec_ofNat_UInt64_toNat (u : UInt64) :
    BitVec.ofNat 64 u.toNat = u.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  exact Nat.mod_eq_of_lt u.toBitVec.isLt
private theorem insertBits_unfold (bv : BitVec 64) (imm16 : UInt64) (shift : Nat) :
    insertBits bv imm16 shift =
    (bv &&& ~~~(0xFFFF#64 <<< shift)) ||| (BitVec.ofNat 64 imm16.toNat <<< shift) := by
  unfold insertBits; rfl
/-- Execute an optional movk instruction (present when w ≠ 0, skipped when w = 0).
    Returns an ArmStepsN-length-tracked witness: `k` equals the list length
    (1 if emitted, 0 if skipped). -/
private theorem optional_movk_step (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      s'.regs rd = (if (w != 0) = true then insertBits (s.regs rd) w shift else s.regs rd) ∧
      s'.stack = s.stack ∧
      s'.pc = pc0 + (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  by_cases hw : (w != 0) = true
  · -- w ≠ 0: one movk instruction (length 1)
    simp only [hw, ite_true] at hCode ⊢
    have hInstr := hCode.head
    rw [← hPC] at hInstr
    refine ⟨s.setReg rd (insertBits (s.regs rd) w shift) |>.nextPC, 1,
      ArmStepsN.single (.movk rd w shift hInstr), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC, hPC]
    · intro r hr; exact ArmState.setReg_regs_other _ _ _ _ hr
    · rfl
  · -- w = 0: no instruction (length 0), identity
    simp only [hw] at hCode ⊢
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨s, 0, rfl, rfl, rfl, rfl, by simp [hPC], fun _ _ => rfl, rfl⟩
private theorem uint64_shl_zero (u : UInt64) : u <<< (0 : UInt64) = u := by
  apply UInt64.eq_of_toBitVec_eq; simp
private theorem uint64_eq_zero_toBitVec (u : UInt64) (h : u = 0) :
    u.toBitVec = 0 := by rw [h]; rfl
private theorem uint64_ne_zero_bne (u : UInt64) (h : ¬(u = 0)) :
    (u != 0) = true := by simp [bne, h]

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
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (formalLoadImm64 rd n).length ∧
      s'.regs rd = n ∧
      s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  unfold formalLoadImm64 at hCode
  split at hCode
  case isTrue hSmall =>
    -- Small case: single mov instruction (length 1)
    have hMov := hCode.head
    rw [← hPC] at hMov
    refine ⟨s.setReg rd n |>.nextPC, 1, ArmStepsN.single (.mov rd n hMov),
      ?_,
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC, hPC, formalLoadImm64, hSmall],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, rfl⟩
    -- k = 1 = (formalLoadImm64 rd n).length in small case
    unfold formalLoadImm64; simp [hSmall]
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
    obtain ⟨s1, k1, hStepsN1, hk1, hRd1, hStack1, hPC1, hRegs1, hAM1⟩ :=
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
    obtain ⟨s2, k2, hStepsN2, hk2, hRd2, hStack2, hPC2, hRegs2, hAM2⟩ :=
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
    obtain ⟨s3, k3, hStepsN3, hk3, hRd3, hStack3, hPC3, hRegs3, hAM3⟩ :=
      optional_movk_step prog rd w3 48 s2
        (startPC + 1 +
         (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
         (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length)
        hPC2 hCodeK3rest
    -- Chain: movz (1 step) + 3 optional movks (k1+k2+k3 steps)
    have hMovzN : ArmStepsN prog s s0 1 := ArmStepsN.single (.movz rd w0 0 hMovz)
    have hChain : ArmStepsN prog s s3 (1 + k1 + k2 + k3) := by
      have h01 : ArmStepsN prog s s1 (1 + k1) := ArmStepsN_trans hMovzN hStepsN1
      have h02 : ArmStepsN prog s s2 (1 + k1 + k2) :=
        (show 1 + k1 + k2 = (1 + k1) + k2 from by omega) ▸
          ArmStepsN_trans h01 hStepsN2
      exact (show 1 + k1 + k2 + k3 = (1 + k1 + k2) + k3 from by omega) ▸
        ArmStepsN_trans h02 hStepsN3
    refine ⟨s3, 1 + k1 + k2 + k3, hChain, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- k = (formalLoadImm64 rd n).length
      rw [hk1, hk2, hk3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
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
      all_goals simp only [show (w1 != 0) = true ↔ w1 ≠ 0 from by simp [bne]] at hRd1
      all_goals simp only [show (w2 != 0) = true ↔ w2 ≠ 0 from by simp [bne]] at hRd2
      all_goals simp only [show (w3 != 0) = true ↔ w3 ≠ 0 from by simp [bne]] at hRd3
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

/-- optional_movk_step extended with fregs preservation. Length-tracked variant
    (Flavor A Phase A.3): returns `ArmStepsN prog s s' k` with `k` equal to the
    emitted list length (0 if skipped, 1 if emitted). -/
private theorem optional_movk_step' (prog : ArmProg) (rd : ArmReg) (w : UInt64) (shift : Nat)
    (s : ArmState) (pc0 : Nat) (hPC : s.pc = pc0)
    (hCode : CodeAt prog pc0 (if (w != 0) = true then [ArmInstr.movk rd w shift] else [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      s'.regs rd = (if (w != 0) = true then insertBits (s.regs rd) w shift else s.regs rd) ∧
      s'.stack = s.stack ∧ s'.fregs = s.fregs ∧
      s'.pc = pc0 + (if (w != 0) = true then [ArmInstr.movk rd w shift] else []).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  by_cases hw : (w != 0) = true
  · simp only [hw, ite_true] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    exact ⟨s.setReg rd (insertBits (s.regs rd) w shift) |>.nextPC, 1,
      ArmStepsN.single (.movk rd w shift hInstr), rfl,
      by simp, by simp, by simp, by simp [hPC],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, by simp⟩
  · simp only [hw] at hCode ⊢; simp only [Bool.false_eq_true, ite_false]
    exact ⟨s, 0, rfl, rfl, rfl, rfl, rfl, by simp [hPC], fun _ _ => rfl, rfl⟩

set_option maxHeartbeats 40000000 in
/-- Re-execute formalLoadImm64 tracking fregs. Since mov/movz/movk only use
    setReg+nextPC (which preserve fregs), the resulting state has s'.fregs = s.fregs.
    This is a standalone re-derivation — it doesn't depend on loadImm64_correct's witness.
    Length-tracked variant (Flavor A Phase A.4): returns `ArmStepsN prog s s' k` with
    `k = (formalLoadImm64 rd n).length`. -/
theorem loadImm64_fregs_preserved (prog : ArmProg) (rd : ArmReg) (n : BitVec 64)
    (s : ArmState) (startPC : Nat)
    (hCode : CodeAt prog startPC (formalLoadImm64 rd n))
    (hPC : s.pc = startPC) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (formalLoadImm64 rd n).length ∧
      s'.fregs = s.fregs ∧
      s'.regs rd = n ∧ s'.stack = s.stack ∧
      s'.pc = startPC + (formalLoadImm64 rd n).length ∧
      (∀ r, r ≠ rd → s'.regs r = s.regs r) ∧
      s'.arrayMem = s.arrayMem := by
  unfold formalLoadImm64 at hCode
  split at hCode
  case isTrue hSmall =>
    have hMov := hCode.head
    rw [← hPC] at hMov
    refine ⟨s.setReg rd n |>.nextPC, 1, ArmStepsN.single (.mov rd n hMov),
      ?_,
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC],
      by simp [ArmState.setReg, ArmState.nextPC, hPC, formalLoadImm64, hSmall],
      fun r hr => ArmState.setReg_regs_other _ _ _ _ hr, rfl⟩
    unfold formalLoadImm64; simp [hSmall]
  case isFalse hLarge =>
    dsimp only at hCode
    let bits : UInt64 := n.toNat.toUInt64
    let w0 : UInt64 := bits &&& 65535
    let w1 : UInt64 := bits >>> 16 &&& 65535
    let w2 : UInt64 := bits >>> 32 &&& 65535
    let w3 : UInt64 := bits >>> 48 &&& 65535
    have hCodeBase := hCode.append_left.append_left.append_left
    have hCodeK1rest := hCode.append_left.append_left.append_right
    have hCodeK1K2 := hCode.append_left
    have hCodeK2rest := hCodeK1K2.append_right
    have hCodeK3rest := hCode.append_right
    have hMovz := hCodeBase.head
    rw [← hPC] at hMovz
    let s0 := s.setReg rd (BitVec.ofNat 64 (w0 <<< (0 : UInt64)).toNat) |>.nextPC
    have hPC0 : s0.pc = startPC + 1 := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hPC]
    have hs0f : s0.fregs = s.fregs := by simp [s0]
    have hw0_shift : (w0 <<< (0 : UInt64)) = w0 := uint64_shl_zero w0
    have hRd0 : s0.regs rd = BitVec.ofNat 64 w0.toNat := by
      simp [s0, ArmState.setReg, ArmState.nextPC, hw0_shift]
    obtain ⟨s1, k1, hStepsN1, hk1, hRd1, hStack1, hFregs1, hPC1, hRegs1, hAM1⟩ :=
      optional_movk_step' prog rd w1 16 s0 (startPC + 1) hPC0 hCodeK1rest
    have hPC_k2 : startPC + ([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])).length =
        startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length := by
      simp; omega
    rw [hPC_k2] at hCodeK2rest
    obtain ⟨s2, k2, hStepsN2, hk2, hRd2, hStack2, hFregs2, hPC2, hRegs2, hAM2⟩ :=
      optional_movk_step' prog rd w2 32 s1
        (startPC + 1 + (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length)
        hPC1 hCodeK2rest
    have hPC_k3 : startPC + (([ArmInstr.movz rd w0 0] ++
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else [])) ++
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else [])).length =
        startPC + 1 +
        (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
        (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length := by
      simp; omega
    rw [hPC_k3] at hCodeK3rest
    obtain ⟨s3, k3, hStepsN3, hk3, hRd3, hStack3, hFregs3, hPC3, hRegs3, hAM3⟩ :=
      optional_movk_step' prog rd w3 48 s2
        (startPC + 1 +
         (if (w1 != 0) = true then [ArmInstr.movk rd w1 16] else []).length +
         (if (w2 != 0) = true then [ArmInstr.movk rd w2 32] else []).length)
        hPC2 hCodeK3rest
    have hMovzN : ArmStepsN prog s s0 1 := ArmStepsN.single (.movz rd w0 0 hMovz)
    have hChain : ArmStepsN prog s s3 (1 + k1 + k2 + k3) := by
      have h01 : ArmStepsN prog s s1 (1 + k1) := ArmStepsN_trans hMovzN hStepsN1
      have h02 : ArmStepsN prog s s2 (1 + k1 + k2) :=
        (show 1 + k1 + k2 = (1 + k1) + k2 from by omega) ▸
          ArmStepsN_trans h01 hStepsN2
      exact (show 1 + k1 + k2 + k3 = (1 + k1 + k2) + k3 from by omega) ▸
        ArmStepsN_trans h02 hStepsN3
    refine ⟨s3, 1 + k1 + k2 + k3, hChain, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk1, hk2, hk3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · rw [hFregs3, hFregs2, hFregs1, hs0f]
    · have hbits_bv : bits.toBitVec = n := by
        show n.toNat.toUInt64.toBitVec = n
        rw [UInt64.toBitVec]
        apply BitVec.eq_of_toNat_eq
        simp [Nat.toUInt64]
      have hc0 : w0.toBitVec = bits.toBitVec &&& 0xFFFF#64 := uint64_toBitVec_chunk0 bits
      have hc1 : w1.toBitVec = (bits.toBitVec >>> 16) &&& 0xFFFF#64 := uint64_toBitVec_chunk16 bits
      have hc2 : w2.toBitVec = (bits.toBitVec >>> 32) &&& 0xFFFF#64 := uint64_toBitVec_chunk32 bits
      have hc3 : w3.toBitVec = (bits.toBitVec >>> 48) &&& 0xFFFF#64 := uint64_toBitVec_chunk48 bits
      by_cases hw1z : w1 = 0 <;> by_cases hw2z : w2 = 0 <;> by_cases hw3z : w3 = 0
      all_goals simp only [show (w1 != 0) = true ↔ w1 ≠ 0 from by simp [bne]] at hRd1
      all_goals simp only [show (w2 != 0) = true ↔ w2 ≠ 0 from by simp [bne]] at hRd2
      all_goals simp only [show (w3 != 0) = true ↔ w3 ≠ 0 from by simp [bne]] at hRd3
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
    · rw [hStack3, hStack2, hStack1]
      simp [s0, ArmState.setReg, ArmState.nextPC]
    · rw [hPC3]
      unfold formalLoadImm64
      simp only [hLarge, ite_false]
      simp only [List.length_append, List.length_cons, List.length_nil]
      split <;> split <;> split <;> simp <;> omega
    · intro r hr
      rw [hRegs3 r hr, hRegs2 r hr, hRegs1 r hr]
      simp [s0, ArmState.setReg, ArmState.nextPC]
      intro heq; exact absurd heq hr
    · rw [hAM3, hAM2, hAM1]; simp [s0, ArmState.setReg, ArmState.nextPC]


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
    satisfies RegConventionSafe. -/
theorem ExtStateRel.preserved_by_ireg_only
    {layout : VarLayout} {σ : Store} {s s' : ArmState}
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hStack : s'.stack = s.stack) (hFregs : s'.fregs = s.fregs)
    (hRegsOther : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → s'.regs r = s.regs r) :
    ExtStateRel layout σ s' := by
  intro v loc hv
  match loc with
  | .stack off => rw [hStack]; exact hRel v (.stack off) hv
  | .ireg r =>
    have h0 := hRegConv.not_x0 v; have h1 := hRegConv.not_x1 v
    have h2 := hRegConv.not_x2 v
    have hr0 : r ≠ .x0 := fun h => h0 (h ▸ hv)
    have hr1 : r ≠ .x1 := fun h => h1 (h ▸ hv)
    have hr2 : r ≠ .x2 := fun h => h2 (h ▸ hv)
    show s'.regs r = (σ v).encode
    rw [hRegsOther r hr0 hr1 hr2]; exact hRel v (.ireg r) hv
  | .freg r =>
    show s'.fregs r = (σ v).encode
    rw [hFregs]; exact hRel v (.freg r) hv

/-- loadImm64 preserves ExtStateRel (it only clobbers one integer scratch register). -/
theorem loadImm64_preserves_ExtStateRel (_prog : ArmProg) (layout : VarLayout)
    (rd : ArmReg) (_n : BitVec 64) (σ : Store) (s s' : ArmState)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hStack : s'.stack = s.stack) (hFregs : s'.fregs = s.fregs)
    (hRegs : ∀ r, r ≠ rd → s'.regs r = s.regs r)
    (_hAM : s'.arrayMem = s.arrayMem)
    (hRdScratch : rd = .x0 ∨ rd = .x1 ∨ rd = .x2) :
    ExtStateRel layout σ s' := by
  apply ExtStateRel.preserved_by_ireg_only hRel hRegConv hStack hFregs
  intro r h0 h1 h2
  apply hRegs
  rcases hRdScratch with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- After executing `vStoreVar layout v .x0` when `s.regs .x0 = val.encode`,
    `ExtStateRel layout (σ[v ↦ val]) s'` holds.
    Requires: v is at a stack or ireg (not freg) location.
    Length-tracked variant (Flavor A Phase A.5): `k = 1`. -/
theorem vStoreVar_x0_correct (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (_hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (off : Nat) (hLoc : layout v = some (.stack off))
    (hCode : CodeAt prog startPC (ArmInstr.str .x0 off :: [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = 1 ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + 1 ∧
        s'.arrayMem = s.arrayMem := by
  have hStr := hCode.head; rw [← hPC] at hStr
  refine ⟨s.setStack off (s.regs .x0) |>.nextPC, 1,
    ArmStepsN.single (.str .x0 off hStr), rfl, ?_, ?_, ?_⟩
  · rw [hX0]; exact ExtStateRel.update_stack hRel hInj hLoc
  · simp [hPC]
  · simp

/-- After executing `vStoreVar layout v .x0` when v is in ireg r (r ≠ x0),
    `ExtStateRel layout (σ[v ↦ val]) s'` holds.
    Length-tracked variant (Flavor A Phase A.6): `k = 1`. -/
theorem vStoreVar_x0_ireg_correct (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (_hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (r : ArmReg) (hLoc : layout v = some (.ireg r)) (_hne : (r == ArmReg.x0) = false)
    (hCode : CodeAt prog startPC (ArmInstr.movR r .x0 :: [])) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = 1 ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + 1 ∧
        s'.arrayMem = s.arrayMem := by
  have hMovR := hCode.head; rw [← hPC] at hMovR
  refine ⟨s.setReg r (s.regs .x0) |>.nextPC, 1,
    ArmStepsN.single (.movR r .x0 hMovR), rfl, ?_, ?_, ?_⟩
  · rw [hX0]; exact ExtStateRel.update_ireg hRel hInj hLoc
  · simp [hPC]
  · simp

/-- Execute vLoadVar: loads v into scratch register tmp, preserving ExtStateRel.
    Case-splits on layout to determine instruction sequence.
    Length-tracked variant (Flavor A Phase A.7): `k = (vLoadVar layout v tmp).length`. -/
theorem vLoadVar_exec (prog : ArmProg) (layout : VarLayout) (v : Var) (tmp : ArmReg)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hCode : CodeAt prog startPC (vLoadVar layout v tmp))
    (hTmpScratch : tmp = .x0 ∨ tmp = .x1 ∨ tmp = .x2)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    (hMapped : layout v ≠ none) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVar layout v tmp).length ∧
        s'.regs tmp = (σ v).encode ∧
        ExtStateRel layout σ s' ∧
        s'.fregs = s.fregs ∧
        s'.pc = startPC + (vLoadVar layout v tmp).length ∧
        s'.arrayMem = s.arrayMem ∧
        (∀ r, r ≠ tmp → s'.regs r = s.regs r) := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vLoadVar_stack layout v tmp off hv
    rw [hEq] at hCode ⊢
    have hInstr := hCode.head; rw [← hPC] at hInstr
    refine ⟨s.setReg tmp (s.stack off) |>.nextPC, 1,
      ArmStepsN.single (.ldr tmp off hInstr), rfl,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp; exact hRel.read_stack hv
    · exact (ExtStateRel.setReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hRegConv.not_x0 w
        · exact hRegConv.not_x1 w
        · exact hRegConv.not_x2 w)).nextPC
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
      exact ⟨s, 0, rfl, rfl, hRel.read_ireg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl⟩
    · have hbeq : (r == tmp) = false := by
        cases h : r == tmp
        · rfl
        · simp [beq_iff_eq] at h; exact absurd h heq
      have hEq := vLoadVar_ireg_diff layout v tmp r hv hbeq
      rw [hEq] at hCode ⊢
      have hInstr := hCode.head; rw [← hPC] at hInstr
      refine ⟨s.setReg tmp (s.regs r) |>.nextPC, 1,
        ArmStepsN.single (.movR tmp r hInstr), rfl,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp; exact hRel.read_ireg hv
      · exact (ExtStateRel.setReg_preserved hRel (fun w => by
          rcases hTmpScratch with rfl | rfl | rfl
          · exact hRegConv.not_x0 w
          · exact hRegConv.not_x1 w
          · exact hRegConv.not_x2 w)).nextPC
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
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hNotFreg : ∀ r, layout v ≠ some (.freg r))
    (hFB : fallback = .x0 ∨ fallback = .x1 ∨ fallback = .x2)
    (hMapped : layout v ≠ none) :
    let eff := match layout v with | some (.ireg r) => r | _ => fallback
    ∀ (_hCode : CodeAt prog startPC (vLoadVar layout v eff)),
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVar layout v eff).length ∧
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
    exact ⟨s, 0, rfl, rfl, hRel.read_ireg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl⟩
  | some (.stack off) =>
    simp only [show (match some (VarLoc.stack off) with | some (.ireg r) => r | _ => fallback) = fallback from rfl]
    exact fun hCode => vLoadVar_exec prog layout v fallback σ s startPC hRel hRegConv hPC hCode hFB hNotFreg hMapped
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none => exact absurd hv hMapped

/-- Execute vStoreVar from x0: stores result into v's location, updating ExtStateRel.
    Length-tracked variant (Flavor A Phase A.9): `k = (vStoreVar layout v .x0).length`. -/
theorem vStoreVar_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC) (hX0 : s.regs .x0 = val.encode)
    (hCode : CodeAt prog startPC (vStoreVar layout v .x0))
    (hNotFreg : ∀ r, layout v ≠ some (.freg r)) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vStoreVar layout v .x0).length ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + (vStoreVar layout v .x0).length ∧
        s'.arrayMem = s.arrayMem := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vStoreVar_stack layout v .x0 off hv
    rw [hEq] at hCode ⊢
    have hStr := hCode.head; rw [← hPC] at hStr
    refine ⟨s.setStack off (s.regs .x0) |>.nextPC, 1,
      ArmStepsN.single (.str .x0 off hStr), rfl, ?_, ?_, ?_⟩
    · rw [hX0]; exact (ExtStateRel.update_stack hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.ireg r) =>
    have hne : (r == ArmReg.x0) = false := by
      cases hr : r == ArmReg.x0
      · rfl
      · simp [beq_iff_eq] at hr; exact absurd (hr ▸ hv) (hRegConv.not_x0 v)
    have hEq := vStoreVar_ireg_diff layout v .x0 r hv hne
    rw [hEq] at hCode ⊢
    have hMovR := hCode.head; rw [← hPC] at hMovR
    refine ⟨s.setReg r (s.regs .x0) |>.nextPC, 1,
      ArmStepsN.single (.movR r .x0 hMovR), rfl, ?_, ?_, ?_⟩
    · rw [hX0]; exact (ExtStateRel.update_ireg hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.freg r) => exact absurd hv (hNotFreg r)
  | none =>
    simp [vStoreVar, hv]
    refine ⟨s, 0, rfl, rfl, ?_, by omega, rfl⟩
    intro w loc hw
    have hwv : w ≠ v := fun h => by subst h; simp [hv] at hw
    rw [Store.update_other σ v w val hwv]; exact hRel w loc hw

/-- Execute vStoreVarFP from d0: stores FP result into v's location.
    Length-tracked variant (Flavor A Phase A.10): `k = (vStoreVarFP layout v .d0).length`. -/
theorem vStoreVarFP_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (val : Value) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hInj : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC) (hD0 : s.fregs .d0 = val.encode)
    (hCode : CodeAt prog startPC (vStoreVarFP layout v .d0))
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hFregPrecond : ∀ r, layout v = some (.freg r) → s.fregs r = val.encode) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vStoreVarFP layout v .d0).length ∧
        ExtStateRel layout (σ[v ↦ val]) s' ∧
        s'.pc = startPC + (vStoreVarFP layout v .d0).length ∧
        s'.arrayMem = s.arrayMem := by
  match hv : layout v with
  | some (.stack off) =>
    have hEq := vStoreVarFP_stack layout v .d0 off hv
    rw [hEq] at hCode ⊢
    have hFstr := hCode.head; rw [← hPC] at hFstr
    refine ⟨s.setStack off (s.fregs .d0) |>.nextPC, 1,
      ArmStepsN.single (.fstr .d0 off hFstr), rfl, ?_, ?_, ?_⟩
    · rw [hD0]; exact (ExtStateRel.update_stack hRel hInj hv).nextPC
    · simp [hPC]
    · simp
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | some (.freg r) =>
    have hne : (r == ArmFReg.d0) = false := by
      simp; exact fun h => absurd hv (h ▸ hRegConv.not_d0 v)
    simp only [vStoreVarFP, hv, hne] at hCode ⊢
    have hFmov := hCode.head; rw [← hPC] at hFmov
    refine ⟨(s.setFReg r (s.fregs .d0)).nextPC, 1,
      ArmStepsN.single (.fmovRR r .d0 hFmov), rfl, ?_, ?_, ?_⟩
    · rw [hD0]; exact (ExtStateRel.update_freg hRel hInj hv).nextPC
    · simp [ArmState.nextPC, ArmState.setFReg, hPC]
    · simp [ArmState.nextPC, ArmState.setFReg]
  | none =>
    simp [vStoreVarFP, hv]
    refine ⟨s, 0, rfl, rfl, ?_, by omega, rfl⟩
    intro w loc hw
    have hwv : w ≠ v := fun h => by subst h; simp [hv] at hw
    rw [Store.update_other σ v w val hwv]; exact hRel w loc hw

/-- Execute one FP instruction and store the result into a variable's location.
    Abstracts the common "op + store" pattern shared by fbinop, fternop, and
    floatUnary proofs. Length-tracked variant (Flavor A Phase A.11):
    `k = 1 + (vStoreVarFP layout x dst_reg).length`. -/
theorem fp_exec_and_store (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (divS boundsS : Nat)
    (pc : Nat) (σ : Store) (am : ArrayMem) (x : Var)
    (dst_reg : ArmFReg)
    (resultBv : BitVec 64) (resultVal : Value)
    (hResultEnc : resultBv = resultVal.encode)
    (s_pre : ArmState) (prePC : Nat)
    (hRelPre : ExtStateRel layout σ s_pre)
    (hInjective : VarLayoutInjective layout)
    (hRegConv : RegConventionSafe layout)
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
    ∃ s' k, ArmStepsN prog s_pre s' k ∧
      k = 1 + (vStoreVarFP layout x dst_reg).length ∧
      ExtSimRel layout pcMap divS boundsS (.run (pc + 1) (σ[x ↦ resultVal]) am) s' := by
  let s_op := (s_pre.setFReg dst_reg resultBv).nextPC
  have hStepsOpN : ArmStepsN prog s_pre s_op 1 := ArmStepsN.single hArmStep
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
    refine ⟨s_op, 1, hStepsOpN, ?_, ⟨hRelPost, ?_, hAM_op⟩⟩
    · rw [hStore]; simp
    · show s_op.pc = pcMap (pc + 1)
      simp [hStore] at hPcNext
      simp [s_op, ArmState.nextPC, ArmState.setFReg, hPC_pre, hPrePC_eq]; omega
  · have hDR : dst_reg = .d0 := by
      rw [hDstReg]; split
      · next r h => exact absurd ⟨r, h⟩ hXFR
      · rfl
    have hRelOp : ExtStateRel layout σ s_op := by
      show ExtStateRel layout σ (s_pre.setFReg dst_reg resultBv).nextPC
      rw [hDR]; exact (ExtStateRel.setFReg_preserved hRelPre (fun v => hRegConv.not_d0 v)).nextPC
    have hD0 : s_op.fregs .d0 = resultVal.encode := by
      simp [s_op, hDR, ArmState.setFReg, ArmState.nextPC, hResultEnc]
    have hCodeStore : CodeAt prog (prePC + 1) (vStoreVarFP layout x .d0) := by
      rw [← hDR]; exact hCodeOpStore.tail
    obtain ⟨s_fin, k_fin, hStepsFinN, hk_fin, hRelFin, hPC_fin, hAM_fin⟩ :=
      vStoreVarFP_exec prog layout x resultVal σ s_op (prePC + 1)
        hRelOp hInjective hRegConv hPC_op hD0 hCodeStore hNotIregX
        (fun r h => absurd ⟨r, h⟩ hXFR)
    have hChain : ArmStepsN prog s_pre s_fin (1 + k_fin) :=
      ArmStepsN_trans hStepsOpN hStepsFinN
    have : dst_reg = .d0 := hDR
    refine ⟨s_fin, 1 + k_fin, hChain, ?_, ⟨hRelFin, ?_, by simp [hAM_fin, hAM_op]⟩⟩
    · rw [hk_fin]; rw [this]
    · show s_fin.pc = pcMap (pc + 1)
      simp [this] at hPcNext; omega

/-- Execute vLoadVarFP: loads float variable v into scratch FP register tmp,
    preserving ExtStateRel. Case-splits on layout.
    Length-tracked variant (Flavor A Phase A.12): `k = (vLoadVarFP layout v tmp).length`. -/
theorem vLoadVarFP_exec (prog : ArmProg) (layout : VarLayout) (v : Var) (tmp : ArmFReg)
    (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hCode : CodeAt prog startPC (vLoadVarFP layout v tmp))
    (hTmpScratch : tmp = .d0 ∨ tmp = .d1 ∨ tmp = .d2)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hMapped : layout v ≠ none) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVarFP layout v tmp).length ∧
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
    refine ⟨s.setFReg tmp (s.stack off) |>.nextPC, 1,
      ArmStepsN.single (.fldr tmp off hInstr), rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setFReg, ArmState.nextPC]; exact hRel.read_stack hv
    · exact (ExtStateRel.setFReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hRegConv.not_d0 w
        · exact hRegConv.not_d1 w
        · exact hRegConv.not_d2 w)).nextPC
    · simp
    · simp [hPC]
    · simp
    · intro r hr; simp [ArmState.setFReg, ArmState.nextPC, hr]
    · simp
  | some (.freg r) =>
    have hne : (r == tmp) = false := by
      simp
      rcases hTmpScratch with rfl | rfl | rfl
      · exact fun h => absurd hv (h ▸ hRegConv.not_d0 v)
      · exact fun h => absurd hv (h ▸ hRegConv.not_d1 v)
      · exact fun h => absurd hv (h ▸ hRegConv.not_d2 v)
    simp only [vLoadVarFP, hv, hne] at hCode ⊢
    have hFmov := hCode.head; rw [← hPC] at hFmov
    refine ⟨(s.setFReg tmp (s.fregs r)).nextPC, 1,
      ArmStepsN.single (.fmovRR tmp r hFmov), rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setFReg, ArmState.nextPC]; exact hRel.read_freg hv
    · exact (ExtStateRel.setFReg_preserved hRel (fun w => by
        rcases hTmpScratch with rfl | rfl | rfl
        · exact hRegConv.not_d0 w
        · exact hRegConv.not_d1 w
        · exact hRegConv.not_d2 w)).nextPC
    · simp
    · simp [ArmState.setFReg, ArmState.nextPC, hPC]
    · simp
    · intro r' hr'; simp [ArmState.setFReg, ArmState.nextPC, hr']
    · simp
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | none => exact absurd hv hMapped

/-- Execute vLoadVarFP with effective register: if v is in a freg, uses that freg directly;
    otherwise falls back to a scratch register. Analogous to vLoadVar_eff_exec.
    Length-tracked variant (Flavor A Phase A.13): `k = (vLoadVarFP layout v eff).length`. -/
theorem vLoadVarFP_eff_exec (prog : ArmProg) (layout : VarLayout) (v : Var)
    (σ : Store) (s : ArmState) (startPC : Nat) (fallback : ArmFReg)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hPC : s.pc = startPC)
    (hNotIreg : ∀ r, layout v ≠ some (.ireg r))
    (hFB : fallback = .d0 ∨ fallback = .d1 ∨ fallback = .d2)
    (hMapped : layout v ≠ none) :
    let eff := match layout v with | some (.freg r) => r | _ => fallback
    ∀ (_hCode : CodeAt prog startPC (vLoadVarFP layout v eff)),
    ∃ s' k, ArmStepsN prog s s' k ∧
        k = (vLoadVarFP layout v eff).length ∧
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
    exact ⟨s, 0, rfl, rfl, hRel.read_freg hv, hRel, rfl, by omega, rfl, fun _ _ => rfl, rfl⟩
  | some (.stack off) =>
    simp only [show (match some (VarLoc.stack off) with | some (.freg r) => r | _ => fallback) = fallback from rfl]
    exact fun hCode => vLoadVarFP_exec prog layout v fallback σ s startPC hRel hRegConv hPC hCode
      hFB hNotIreg hMapped
  | some (.ireg r) => exact absurd hv (hNotIreg r)
  | none => exact absurd hv hMapped

-- ============================================================
-- § loadFloatExpr_exec: unified float operand loading
-- ============================================================

/-- Load a float expression operand (.var or .flit) into a float register.
    Unifies vLoadVarFP and loadImm64+fmovToFP into a single helper.
    Length-tracked variant (Flavor A Phase A.14): `k = <code-list>.length`. -/
theorem loadFloatExpr_exec (prog : ArmProg) (layout : VarLayout) (e : Expr) (dst : ArmFReg)
    (σ : Store) (am : ArrayMem) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
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
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (match e with | .var v => vLoadVarFP layout v dst
                        | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP dst .x0]
                        | _ => []).length ∧
      s'.fregs dst = (e.eval σ am).toFloat ∧
      ExtStateRel layout σ s' ∧
      s'.pc = startPC +
        (match e with | .var v => vLoadVarFP layout v dst
                      | .flit n => formalLoadImm64 .x0 n ++ [ArmInstr.fmovToFP dst .x0]
                      | _ => []).length ∧
      s'.arrayMem = s.arrayMem ∧
      (∀ r, r ≠ dst → s'.fregs r = s.fregs r) := by
  rcases hSimple with ⟨v, rfl⟩ | ⟨n, rfl⟩
  · simp only [] at hCode
    have hNotIreg : ∀ r, layout v ≠ some (.ireg r) := hWTL.float_not_ireg hTy
    have hMappedV : layout v ≠ none := hMapped v (by simp [Expr.freeVars])
    obtain ⟨s', k', hStepsN', hk', hFreg, hRel', _, hPC', hAM', hFregs', _⟩ :=
      vLoadVarFP_exec prog layout v dst σ s startPC hRel hRegConv hPC hCode hDst hNotIreg hMappedV
    have hTyV := hTS v; rw [hTy] at hTyV
    obtain ⟨fv, hfv⟩ := Value.float_of_typeOf_float hTyV
    refine ⟨s', k', hStepsN', hk', ?_, hRel', hPC', hAM', hFregs'⟩
    simp [Expr.eval, Value.toFloat, hFreg, hfv, Value.encode]
  · simp only [] at hCode
    have hCodeImm := hCode.append_left
    have hCodeFmov := hCode.append_right
    obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX0, hStack1, hPC1, hRegs1, hAM1⟩ :=
      loadImm64_fregs_preserved prog .x0 n s startPC hCodeImm hPC
    have hRel1 : ExtStateRel layout σ s1 :=
      loadImm64_preserves_ExtStateRel prog layout .x0 n σ s s1
        hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
    have hFmov := hCodeFmov.head; rw [← hPC1] at hFmov
    let s2 := s1.setFReg dst (s1.regs .x0) |>.nextPC
    have hRel2 : ExtStateRel layout σ s2 := by
      have hNotDst : ∀ w, layout w ≠ some (.freg dst) := by
        cases hDst with
        | inl h => subst h; exact fun w => hRegConv.not_d0 w
        | inr h => cases h with
          | inl h => subst h; exact fun w => hRegConv.not_d1 w
          | inr h => subst h; exact fun w => hRegConv.not_d2 w
      exact (ExtStateRel.setFReg_preserved hRel1 hNotDst).nextPC
    have hStepsFmovN : ArmStepsN prog s1 s2 1 :=
      ArmStepsN.single (ArmStep.fmovToFP dst .x0 hFmov)
    have hChain : ArmStepsN prog s s2 (k1 + 1) :=
      ArmStepsN_trans hStepsN1 hStepsFmovN
    refine ⟨s2, k1 + 1, hChain, ?_, ?_, hRel2, ?_, ?_, ?_⟩
    · rw [hk1]; simp [List.length_append]
    · simp [s2, ArmState.setFReg, ArmState.nextPC, hX0, Expr.eval, Value.toFloat]
    · simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append, hPC1]; omega
    · simp [s2, ArmState.setFReg, ArmState.nextPC, hAM1]
    · intro r hr; simp [s2, ArmState.setFReg, ArmState.nextPC, hr, hFregs1]

-- ============================================================
-- § verifiedGenBoolExpr_correct
-- ============================================================

/-- Correctness of verifiedGenBoolExpr: after execution, x0 holds the boolean result
    encoded as 1 (true) or 0 (false), and ExtStateRel is preserved. -/
theorem verifiedGenBoolExpr_correct (prog : ArmProg) (layout : VarLayout)
    (be : BoolExpr) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : ExtStateRel layout σ s) (hRegConv : RegConventionSafe layout)
    (hCode : CodeAt prog startPC (verifiedGenBoolExpr layout be))
    (hPC : s.pc = startPC)
    (Γ : TyCtx) (hTS : TypedStore Γ σ)
    (hWTBE : WellTypedBoolExpr Γ be)
    (hWTL : WellTypedLayout Γ layout)
    (hMapped : ∀ v, v ∈ be.vars → layout v ≠ none)
    (hSimple : be.hasSimpleOps = true)
    (am : ArrayMem) :
    ∃ s' k, ArmStepsN prog s s' k ∧
      k = (verifiedGenBoolExpr layout be).length ∧
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
    refine ⟨_, 1, ArmStepsN.single (.mov .x0 _ hMov), ?_, ?_, ?_, ?_, ?_⟩
    · simp [verifiedGenBoolExpr]
    · simp [ArmState.setReg, ArmState.nextPC, BoolExpr.eval]
    · exact (ExtStateRel.setReg_preserved hRel (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr, hPC]
    · simp [ArmState.setReg, ArmState.nextPC]
  | bvar hty =>
    rename_i x
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeLoad := hCode.append_left
    have hCodeAnd := hCode.append_right
    have hTy := hTS x; rw [hty] at hTy
    obtain ⟨bv, hbv⟩ := Value.bool_of_typeOf_bool hTy
    have hNotFreg : ∀ r, layout x ≠ some (.freg r) := hWTL.bool_not_freg hty
    obtain ⟨s1, k1, hStepsN1, hk1, hX0_1, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout x .x0 σ s startPC hRel hRegConv hPC hCodeLoad
        (Or.inl rfl) hNotFreg (hMapped x (by simp [BoolExpr.vars]))
    have hAnd := hCodeAnd.head; rw [← hPC1] at hAnd
    have hStepAndN : ArmStepsN prog s1 _ 1 := ArmStepsN.single (.andImm .x0 .x0 1 hAnd)
    have hChain : ArmStepsN prog s _ (k1 + 1) := ArmStepsN_trans hStepsN1 hStepAndN
    refine ⟨_, k1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk1]; simp [verifiedGenBoolExpr]
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, hbv, BoolExpr.eval, Value.toBool,
            Value.encode]
      cases bv <;> simp
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | not hbe =>
    rename_i e
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    have hSimpleE : e.hasSimpleOps = true := by
      simp [BoolExpr.hasSimpleOps] at hSimple; exact hSimple
    obtain ⟨s1, k1, hStepsN1, hk1, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout e σ s startPC hRel hRegConv hCodeE hPC Γ hTS hbe
        hWTL (fun v hv => hMapped v (by simp [BoolExpr.vars]; exact hv)) hSimpleE am
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    have hStepEorN : ArmStepsN prog s1 _ 1 := ArmStepsN.single (.eorImm .x0 .x0 1 hEor)
    have hChain : ArmStepsN prog s _ (k1 + 1) := ArmStepsN_trans hStepsN1 hStepEorN
    refine ⟨_, k1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk1]; simp [verifiedGenBoolExpr]
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, BoolExpr.eval]
      cases h : BoolExpr.eval σ am e <;> simp <;> decide
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | cmp ha hb =>
    rename_i a b op'
    obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_cmp hSimple
    cases a with
    | var va => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLVRV := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeLV := hCodeLVRV.append_left
        have hCodeRV := hCodeLVRV.append_right
        have hTyL := hTS va; rw [ha] at hTyL
        have hTyR := hTS vb; rw [hb] at hTyR
        obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
        obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
        have hNotFregLV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha
        have hNotFregRV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb
        obtain ⟨s1, k1, hStepsN1, hk1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_exec prog layout va .x1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotFregLV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        obtain ⟨s2, k2, hStepsN2, hk2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotFregRV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hX1_s2 : s2.regs .x1 = (σ va).encode := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (vLoadVar layout va .x1 ++ vLoadVar layout vb .x2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnL, hnR,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' nL nR)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | lit nb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeLV := hCodeLoadImm.append_left
        have hCodeImm := hCodeLoadImm.append_right
        have hTyV := hTS va; rw [ha] at hTyV
        obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
        have hNotFregV : ∀ r, layout va ≠ some (.freg r) := hWTL.int_not_freg ha
        obtain ⟨s1, k1, hStepsN1, hk1, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
          vLoadVar_exec prog layout va .x1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotFregV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        obtain ⟨s2, k2, hStepsN2, hk2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImm hPC1
        have hX1_s2 : s2.regs .x1 = (σ va).encode := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
            hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (vLoadVar layout va .x1 ++ formalLoadImm64 .x2 nb).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnV,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' nV nb)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | lit na => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeImm := hCodeLoadImm.append_left
        have hCodeRV := hCodeLoadImm.append_right
        have hTyV := hTS vb; rw [hb] at hTyV
        obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
        have hNotFregV : ∀ r, layout vb ≠ some (.freg r) := hWTL.int_not_freg hb
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x1 na s _ hCodeImm hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
        obtain ⟨s2, k2, hStepsN2, hk2, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
          vLoadVar_exec prog layout vb .x2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotFregV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hX1_s2 : s2.regs .x1 = na := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ vLoadVar layout vb .x2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2, hnV,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' na nV)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | lit nb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeCmpCset := hCode.append_right
        have hCodeImmA := hCodeLoadImm.append_left
        have hCodeImmB := hCodeLoadImm.append_right
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x1 na s _ hCodeImmA hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x1 na σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inr (Or.inl rfl))
        obtain ⟨s2, k2, hStepsN2, hk2, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x2 nb s1 _ hCodeImmB hPC1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x2 nb σ s1 s2
            hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
        have hX1_s2 : s2.regs .x1 = na := by
          rw [hRegs2 .x1 (by decide)]; exact hX1
        have hCmp := hCodeCmpCset.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length
            = s2.pc from by rw [List.length_append]; omega] at hCmp
        let s3 := { s2 with flags := Flags.mk (s2.regs .x1) (s2.regs .x2), pc := s2.pc + 1 }
        have hRelCmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeCmpCset.tail.head
        rw [show startPC + (formalLoadImm64 .x1 na ++ formalLoadImm64 .x2 nb).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepCmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.cmpRR .x1 .x2 hCmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hX1_s2, hX2,
                BoolExpr.eval, Expr.eval, Value.toInt]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_correct op' na nb)
        · exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | _ => rcases hSimpleA with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
  | fcmp ha hb =>
    rename_i a b fop
    obtain ⟨hSimpleA, hSimpleB⟩ := BoolExpr.hasSimpleOps_fcmp hSimple
    cases a with
    | var va => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLVRV := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeLV := hCodeLVRV.append_left
        have hCodeRV := hCodeLVRV.append_right
        have hTyL := hTS va; rw [ha] at hTyL
        have hTyR := hTS vb; rw [hb] at hTyR
        obtain ⟨fL, hfL⟩ := Value.float_of_typeOf_float hTyL
        obtain ⟨fR, hfR⟩ := Value.float_of_typeOf_float hTyR
        have hNotIregLV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha
        have hNotIregRV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb
        obtain ⟨s1, k1, hStepsN1, hk1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
          vLoadVarFP_exec prog layout va .d1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotIregLV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        obtain ⟨s2, k2, hStepsN2, hk2, hD2, hRel2, hRegsI2, hPC2, hAM2, hFregs2, _⟩ :=
          vLoadVarFP_exec prog layout vb .d2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
            (Or.inr (Or.inr rfl)) hNotIregRV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hD1_s2 : s2.fregs .d1 = (σ va).encode := by
          rw [hFregs2 .d1 (by decide)]; exact hD1
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length
            = s2.pc from by rw [List.length_append]; omega] at hFcmp
        let s3 := { s2 with flags := Flags.mk (s2.fregs .d1) (s2.fregs .d2), pc := s2.pc + 1 }
        have hRelFcmp : ExtStateRel layout σ s3 := fun v loc hv => hRel2 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ vLoadVarFP layout vb .d2).length + 1
            = s3.pc from by simp [s3]; omega] at hCset
        have hStepFcmpN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s3 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFcmpN
        have hChain : ArmStepsN prog s _ ((k1 + k2 + 1) + 1) :=
          ArmStepsN_trans h23 hStepCsetN
        refine ⟨_, (k1 + k2 + 1) + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hD1_s2, hD2, hfL, hfR,
                BoolExpr.eval, Expr.eval, Value.toFloat, Value.encode]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fL fR)
        · exact (ExtStateRel.setReg_preserved hRelFcmp (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s3, ArmState.setReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s3, ArmState.setReg, ArmState.nextPC, hAM2, hAM1]
      | flit fb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeLV := hCodeLoadImm.append_left
        have hCodeImmFmov := hCodeLoadImm.append_right
        have hTyV := hTS va; rw [ha] at hTyV
        obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
        have hNotIregV : ∀ r, layout va ≠ some (.ireg r) := hWTL.float_not_ireg ha
        obtain ⟨s1, k1, hStepsN1, hk1, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
          vLoadVarFP_exec prog layout va .d1 σ s startPC hRel hRegConv hPC hCodeLV
            (Or.inr (Or.inl rfl)) hNotIregV (hMapped va (by simp [BoolExpr.vars, Expr.freeVars]))
        have hCodeImm := hCodeImmFmov.append_left
        obtain ⟨s2, k2, hStepsN2, hk2, hFregs2, hX0, hStack2, hPC2, hRegs2, hAM2⟩ :=
          loadImm64_fregs_preserved prog .x0 fb s1 _ hCodeImm hPC1
        have hD1_s2 : s2.fregs .d1 = (σ va).encode := by rw [hFregs2]; exact hD1
        have hRel2 : ExtStateRel layout σ s2 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fb σ s1 s2
            hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inl rfl)
        have hFmov := hCodeImmFmov.append_right |>.head
        rw [← hPC2] at hFmov
        let s3 := s2.setFReg .d2 (s2.regs .x0) |>.nextPC
        have hRel3 : ExtStateRel layout σ s3 :=
          (ExtStateRel.setFReg_preserved hRel2 (fun w => hRegConv.not_d2 w)).nextPC
        have hD1_s3 : s3.fregs .d1 = (σ va).encode := by
          simp [s3, ArmState.setFReg, ArmState.nextPC]; exact hD1_s2
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
            = s3.pc from by simp [s3, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega] at hFcmp
        let s4 := { s3 with flags := Flags.mk (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
        have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + (vLoadVarFP layout va .d1 ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
            = s4.pc from by simp [s4, s3, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega] at hCset
        have hStepFmovN : ArmStepsN prog s2 s3 1 := ArmStepsN.single (.fmovToFP .d2 .x0 hFmov)
        have hStepFcmpN : ArmStepsN prog s3 s4 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s4 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hStepsN1 hStepsN2
        have h23 : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepFmovN
        have h34 : ArmStepsN prog s s4 (k1 + k2 + 1 + 1) := ArmStepsN_trans h23 hStepFcmpN
        have hChain : ArmStepsN prog s _ (k1 + k2 + 1 + 1 + 1) :=
          ArmStepsN_trans h34 hStepCsetN
        refine ⟨_, k1 + k2 + 1 + 1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk2]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s2, hX0, hfV, Value.encode, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fV fb)
        · exact (ExtStateRel.setReg_preserved hRel4 (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
        · simp [s4, s3, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM2, hAM1]
      | _ => rcases hSimpleB with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
    | flit fa => cases b with
      | var vb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeImmFmov := hCodeLoadImm.append_left
        have hCodeRV := hCodeLoadImm.append_right
        have hTyV := hTS vb; rw [hb] at hTyV
        obtain ⟨fV, hfV⟩ := Value.float_of_typeOf_float hTyV
        have hNotIregV : ∀ r, layout vb ≠ some (.ireg r) := hWTL.float_not_ireg hb
        have hCodeImm := hCodeImmFmov.append_left
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 fa s _ hCodeImm hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fa σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
        have hFmov := hCodeImmFmov.append_right |>.head
        rw [← hPC1] at hFmov
        let s2 := s1.setFReg .d1 (s1.regs .x0) |>.nextPC
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun w => hRegConv.not_d1 w)).nextPC
        have hD1_s2 : s2.fregs .d1 = fa := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
        have hStepFmovN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fmovToFP .d1 .x0 hFmov)
        obtain ⟨s3, k3, hStepsN3, hk3, hD2, hRel3, hRegsI3, hPC3, hAM3, hFregs3, _⟩ :=
          vLoadVarFP_exec prog layout vb .d2 σ s2 _ hRel2 hRegConv
            (by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega)
            hCodeRV
            (Or.inr (Or.inr rfl)) hNotIregV (hMapped vb (by simp [BoolExpr.vars, Expr.freeVars]))
        have hD1_s3 : s3.fregs .d1 = fa := by
          rw [hFregs3 .d1 (by decide)]; exact hD1_s2
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length
            = s3.pc from by simp [List.length_append] at hPC3 ⊢; omega] at hFcmp
        let s4 := { s3 with flags := Flags.mk (s3.fregs .d1) (s3.fregs .d2), pc := s3.pc + 1 }
        have hRel4 : ExtStateRel layout σ s4 := fun v loc hv => hRel3 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ vLoadVarFP layout vb .d2).length + 1
            = s4.pc from by simp [s4, List.length_append] at hPC3 ⊢; omega] at hCset
        have hStepFcmpN : ArmStepsN prog s3 s4 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s4 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hStepsN1 hStepFmovN
        have h23 : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hStepsN3
        have h34 : ArmStepsN prog s s4 (k1 + 1 + k3 + 1) := ArmStepsN_trans h23 hStepFcmpN
        have hChain : ArmStepsN prog s _ (k1 + 1 + k3 + 1 + 1) :=
          ArmStepsN_trans h34 hStepCsetN
        refine ⟨_, k1 + 1 + k3 + 1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk3]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp [s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC,
                hD1_s3, hD2, hfV, Value.encode, BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fa fV)
        · exact (ExtStateRel.setReg_preserved hRel4 (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s4, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr,
                List.length_append] at hPC3 ⊢; omega
        · simp [s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM3, hAM1]
      | flit fb =>
        simp only [verifiedGenBoolExpr] at hCode
        have hCodeLoadImm := hCode.append_left
        have hCodeFcmpCset := hCode.append_right
        have hCodeImmFmovA := hCodeLoadImm.append_left
        have hCodeImmFmovB := hCodeLoadImm.append_right
        have hCodeImmA := hCodeImmFmovA.append_left
        obtain ⟨s1, k1, hStepsN1, hk1, hFregs1, hX0_1, hStack1, hPC1, hRegs1, hAM1⟩ :=
          loadImm64_fregs_preserved prog .x0 fa s _ hCodeImmA hPC
        have hRel1 : ExtStateRel layout σ s1 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fa σ s s1
            hRel hRegConv hStack1 hFregs1 hRegs1 hAM1 (Or.inl rfl)
        have hFmovA := hCodeImmFmovA.append_right |>.head
        rw [← hPC1] at hFmovA
        let s2 := s1.setFReg .d1 (s1.regs .x0) |>.nextPC
        have hRel2 : ExtStateRel layout σ s2 :=
          (ExtStateRel.setFReg_preserved hRel1 (fun w => hRegConv.not_d1 w)).nextPC
        have hD1_s2 : s2.fregs .d1 = fa := by
          simp [s2, ArmState.setFReg, ArmState.nextPC, hX0_1]
        have hStepFmovAN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.fmovToFP .d1 .x0 hFmovA)
        have hCodeImmB := hCodeImmFmovB.append_left
        obtain ⟨s3, k3, hStepsN3, hk3, hFregs3, hX0_3, hStack3, hPC3, hRegs3, hAM3⟩ :=
          loadImm64_fregs_preserved prog .x0 fb s2 _ hCodeImmB
            (by simp [s2, ArmState.setFReg, ArmState.nextPC, List.length_append]; omega)
        have hRel3 : ExtStateRel layout σ s3 :=
          loadImm64_preserves_ExtStateRel prog layout .x0 fb σ s2 s3
            hRel2 hRegConv hStack3 hFregs3 hRegs3 hAM3 (Or.inl rfl)
        have hD1_s3 : s3.fregs .d1 = fa := by rw [hFregs3]; exact hD1_s2
        have hFmovB := hCodeImmFmovB.append_right |>.head
        rw [← hPC3] at hFmovB
        let s4 := s3.setFReg .d2 (s3.regs .x0) |>.nextPC
        have hRel4 : ExtStateRel layout σ s4 :=
          (ExtStateRel.setFReg_preserved hRel3 (fun w => hRegConv.not_d2 w)).nextPC
        have hD1_s4 : s4.fregs .d1 = fa := by
          simp [s4, ArmState.setFReg, ArmState.nextPC]; exact hD1_s3
        have hD2_s4 : s4.fregs .d2 = fb := by
          simp [s4, ArmState.setFReg, ArmState.nextPC, hX0_3]
        have hStepFmovBN : ArmStepsN prog s3 s4 1 := ArmStepsN.single (.fmovToFP .d2 .x0 hFmovB)
        have hFcmp := hCodeFcmpCset.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length
            = s4.pc from by simp [s4, ArmState.setFReg, ArmState.nextPC, List.length_append] at hPC3 ⊢; omega] at hFcmp
        let s5 := { s4 with flags := Flags.mk (s4.fregs .d1) (s4.fregs .d2), pc := s4.pc + 1 }
        have hRel5 : ExtStateRel layout σ s5 := fun v loc hv => hRel4 v loc hv
        have hCset := hCodeFcmpCset.tail.head
        rw [show startPC + ((formalLoadImm64 .x0 fa ++ [ArmInstr.fmovToFP .d1 .x0]) ++ (formalLoadImm64 .x0 fb ++ [ArmInstr.fmovToFP .d2 .x0])).length + 1
            = s5.pc from by simp [s5, s4, ArmState.setFReg, ArmState.nextPC, List.length_append] at hPC3 ⊢; omega] at hCset
        have hStepFcmpN : ArmStepsN prog s4 s5 1 := ArmStepsN.single (.fcmpRR .d1 .d2 hFcmp)
        have hStepCsetN : ArmStepsN prog s5 _ 1 := ArmStepsN.single (.cset .x0 _ hCset)
        have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hStepsN1 hStepFmovAN
        have h23 : ArmStepsN prog s s3 (k1 + 1 + k3) := ArmStepsN_trans h12 hStepsN3
        have h34 : ArmStepsN prog s s4 (k1 + 1 + k3 + 1) := ArmStepsN_trans h23 hStepFmovBN
        have h45 : ArmStepsN prog s s5 (k1 + 1 + k3 + 1 + 1) := ArmStepsN_trans h34 hStepFcmpN
        have hChain : ArmStepsN prog s _ (k1 + 1 + k3 + 1 + 1 + 1) :=
          ArmStepsN_trans h45 hStepCsetN
        refine ⟨_, k1 + 1 + k3 + 1 + 1 + 1, hChain, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hk1, hk3]; simp [verifiedGenBoolExpr, List.length_append]; omega
        · simp only [s5, ArmState.setReg, ArmState.nextPC, hD1_s4, hD2_s4]
          simp [BoolExpr.eval, Expr.eval, Value.toFloat]
          exact congrArg (fun b => if b = true then (1 : BitVec 64) else 0)
            (Flags.condHolds_float_correct fop fa fb)
        · exact (ExtStateRel.setReg_preserved hRel5 (fun w => hRegConv.not_x0 w)).nextPC
        · simp [s5, s4, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr,
                List.length_append] at hPC3 ⊢; omega
        · simp [s5, s4, s2, ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM3, hAM1]
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
    obtain ⟨s1, _, hSteps1N, _, hX0_1, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout x .x0 σ s startPC hRel hRegConv hPC hCodeLoad
        (Or.inl rfl) hNotFreg (hMapped x (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- andImm x0 x0 1
    have hAnd := hCodeAnd.head; rw [← hPC1] at hAnd
    refine ⟨_, hSteps1.trans (.single (.andImm .x0 .x0 1 hAnd)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, hbv, BoolExpr.eval, Value.toBool,
            Value.encode]
      cases bv <;> simp
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
    · simp [ArmState.setReg, ArmState.nextPC, hPC1, verifiedGenBoolExpr]; omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
  | not hbe =>
    rename_i e
    simp only [verifiedGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    -- Recursive call
    obtain ⟨s1, _, hSteps1N, _, hX0_1, hRel1, hPC1, hAM1⟩ :=
      verifiedGenBoolExpr_correct prog layout e σ s startPC hRel hRegConv hCodeE hPC Γ hTS hbe
        hWTL hMapped
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- eorImm x0 x0 1
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    refine ⟨_, hSteps1.trans (.single (.eorImm .x0 .x0 1 hEor)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hX0_1, BoolExpr.eval]
      cases h : BoolExpr.eval σ e <;> simp [h] <;> decide
    · exact (ExtStateRel.setReg_preserved hRel1 (fun w => hRegConv.not_x0 w)).nextPC
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
    obtain ⟨s1, _, hSteps1N, _, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_exec prog layout lv .x1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotFregLV (hMapped lv (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: vLoadVar rv into x2
    obtain ⟨s2, _, hSteps2N, _, hX2, hRel2, _, hPC2, hAM2, hRegs2⟩ :=
      vLoadVar_exec prog layout rv .x2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
        (Or.inr (Or.inr rfl)) hNotFregRV (hMapped rv (by simp [BoolExpr.vars]))
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
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
      exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
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
    obtain ⟨s1, _, hSteps1N, _, hX1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_exec prog layout v .x1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotFregV (hMapped v (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: loadImm64 n into x2 (preserves x1 and fregs)
    obtain ⟨s2, _, hSteps2N, _, hFregs2, hX2, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_fregs_preserved prog .x2 n s1 _ hCodeImm hPC1
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
    -- x1 preserved through loadImm64 (x2 ≠ x1)
    have hX1_s2 : s2.regs .x1 = (σ v).encode := by
      rw [hRegs2 .x1 (by decide)]; exact hX1
    -- ExtStateRel preserved through loadImm64
    have hRel2 : ExtStateRel layout σ s2 :=
      loadImm64_preserves_ExtStateRel prog layout .x2 n σ s1 s2
        hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inr (Or.inr rfl))
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
      exact (ExtStateRel.setReg_preserved hRelCmp (fun w => hRegConv.not_x0 w)).nextPC
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
    obtain ⟨s1, _, hSteps1N, _, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
      vLoadVarFP_exec prog layout lv .d1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotIregLV (hMapped lv (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: vLoadVarFP rv into d2
    obtain ⟨s2, _, hSteps2N, _, hD2, hRel2, hRegsI2, hPC2, hAM2, hFregs2, _⟩ :=
      vLoadVarFP_exec prog layout rv .d2 σ s1 _ hRel1 hRegConv hPC1 hCodeRV
        (Or.inr (Or.inr rfl)) hNotIregRV (hMapped rv (by simp [BoolExpr.vars]))
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
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
      exact (ExtStateRel.setReg_preserved hRelFcmp (fun w => hRegConv.not_x0 w)).nextPC
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
    obtain ⟨s1, _, hSteps1N, _, hD1, hRel1, hRegsI1, hPC1, hAM1, hFregs1, _⟩ :=
      vLoadVarFP_exec prog layout v .d1 σ s startPC hRel hRegConv hPC hCodeLV
        (Or.inr (Or.inl rfl)) hNotIregV (hMapped v (by simp [BoolExpr.vars]))
    have hSteps1 := ArmStepsN_to_ArmSteps hSteps1N
    -- Step 2: loadImm64 n into x0 (preserves fregs)
    obtain ⟨s2, _, hSteps2N, _, hFregs2, hX0, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_fregs_preserved prog .x0 n s1 _ hCodeImm hPC1
    have hSteps2 := ArmStepsN_to_ArmSteps hSteps2N
    -- d1 preserved through loadImm64 (loadImm64 preserves fregs)
    have hD1_s2 : s2.fregs .d1 = (σ v).encode := by
      rw [hFregs2]; exact hD1
    -- ExtStateRel preserved through loadImm64
    have hRel2 : ExtStateRel layout σ s2 :=
      loadImm64_preserves_ExtStateRel prog layout .x0 n σ s1 s2
        hRel1 hRegConv hStack2 hFregs2 hRegs2 hAM2 (Or.inl rfl)
    -- Step 3: fmovToFP d2 x0
    have hFmov := hCodeFmovFcmpCset.head
    rw [show startPC + (vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n).length
        = s2.pc from by rw [List.length_append]; omega] at hFmov
    let s3 := s2.setFReg .d2 (s2.regs .x0) |>.nextPC
    have hRel3 : ExtStateRel layout σ s3 :=
      (ExtStateRel.setFReg_preserved hRel2 (fun w => hRegConv.not_d2 w)).nextPC
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
      exact (ExtStateRel.setReg_preserved hRel4 (fun w => hRegConv.not_x0 w)).nextPC
    · -- pc advanced
      simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, verifiedGenBoolExpr]; omega
    · -- arrayMem preserved
      simp [ArmState.setReg, ArmState.setFReg, ArmState.nextPC, hAM2, hAM1]
-/

/-- x1 ≠ effective ireg with x2 fallback. -/
theorem x1_ne_eff_x2 (layout : VarLayout) (v : Var)
    (hRegConv : RegConventionSafe layout) (hNotFreg : ∀ r, layout v ≠ some (.freg r)) :
    ArmReg.x1 ≠ (match layout v with | some (.ireg r) => r | _ => ArmReg.x2) := by
  match hv : layout v with
  | some (.ireg r) => intro h; exact (hRegConv.not_x1 v (h ▸ hv)).elim
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
    (hRegConv : RegConventionSafe layout) (hNotIreg : ∀ r, layout v ≠ some (.ireg r)) :
    ArmFReg.d1 ≠ (match layout v with | some (.freg r) => r | _ => ArmFReg.d2) := by
  match hv : layout v with
  | some (.freg r) => intro h; exact (hRegConv.not_d1 v (h ▸ hv)).elim
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

set_option maxHeartbeats 400000 in
/-- Single TAC instruction backward simulation for the verified codegen.
    Analogous to `genInstr_correct` but uses `ExtStateRel`/`VarLayout`
    and supports register-allocated variables. -/
theorem verifiedGenInstr_correct (prog : ArmProg) (layout : VarLayout) (pcMap : Nat → Nat)
    (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) (s : ArmState)
    (haltLabel divLabel boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool)
    (hBoundsSafeOracle : boundsSafe = true →
      (∀ dst arr idx ty, p[pc]? = some (.arrLoad dst arr idx ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr) ∧
      (∀ arr idx val ty, p[pc]? = some (.arrStore arr idx val ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr))
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hRel : ExtSimRel layout pcMap divLabel boundsLabel (.run pc σ am) s)
    (instrs : List ArmInstr)
    (hSome : verifiedGenInstr layout pcMap instr haltLabel divLabel boundsLabel arrayDecls boundsSafe = some instrs)
    (hPC_bound : pc < p.size)
    (tyCtx : TyCtx)
    (hWT : WellTypedProg tyCtx p) (hTS : TypedStore tyCtx σ)
    (hWTL : WellTypedLayout tyCtx layout)
    (hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (cfg' : Cfg) (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hCodeInstr : CodeAt prog (pcMap pc) instrs)
    (hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      pcMap (pc + 1) = pcMap pc + instrs.length)
    (hAD : arrayDecls = p.arrayDecls)
    (hNCSL : ∀ x op y, instr = .floatUnary x op y → op.isNative = false → NoCallerSavedLayout layout)
    (hNCSLBin : ∀ x y z, instr = .fbinop x .fpow y z → NoCallerSavedLayout layout)
    (hNCSLPrintInt : ∀ v, instr = .printInt v → NoCallerSavedLayout layout)
    (hNCSLPrintBool : ∀ v, instr = .printBool v → NoCallerSavedLayout layout)
    (hNCSLPrintFloat : ∀ v, instr = .printFloat v → NoCallerSavedLayout layout)
    (hNCSLPrintStr : ∀ lit, instr = .printString lit → NoCallerSavedLayout layout) :
    ∃ s' k, ArmStepsN prog s s' k ∧
        (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
        ExtSimRel layout pcMap divLabel boundsLabel cfg' s' := by
  -- Phase B.0 (session 7): per-case sorries; bodies filled in B.1+.
  -- Sig is length-tracked: k tracks ArmStepsN; on .run targets, k = instrs.length.
  have hRC : layout.regConventionSafe = true := by
    cases h : layout.regConventionSafe
    · simp [verifiedGenInstr, h] at hSome
    · rfl
  have hII : layout.isInjective = true := by
    cases h : layout.isInjective
    · simp [verifiedGenInstr, hRC, h] at hSome
    · rfl
  have hRegConv : RegConventionSafe layout := VarLayout.regConventionSafe_spec layout hRC
  have hInjective : VarLayoutInjective layout := VarLayout.isInjective_spec layout hII
  obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
  cases hStep with
  | goto hinstr =>
    -- Block: [.b (pcMap l)]; k = 1 = instrs.length.
    have heq : instr = .goto _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr, hRC, hII] at hSome
    rw [← hSome] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    refine ⟨{ s with pc := pcMap _ }, 1, ArmStepsN.single (.branch _ hb), ?_,
      ⟨hStateRel, rfl, hArrayMem⟩⟩
    intro pc' σ' am' _hCfg
    rw [← hSome]; rfl
  | halt hinstr =>
    -- Block: [.b haltLabel]; k = 1, but cfg' = .halt so length-claim vacuous.
    have heq : instr = .halt := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr, hRC, hII] at hSome
    rw [← hSome] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    refine ⟨{ s with pc := haltLabel }, 1, ArmStepsN.single (.branch haltLabel hb), ?_,
      ⟨hStateRel, hArrayMem⟩⟩
    intro pc' σ' am' hCfg
    exact absurd hCfg (by simp)
  | binop_divByZero hinstr hy hz hs =>
    -- cfg' = .errorDiv σ am — length-claim vacuous; chain reaches divLabel sentinel.
    rename_i x op y z a b
    have heq : instr = .binop x op y z := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFregY : ∀ r, layout y ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregZ : ∀ r, layout z ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    have hNotFregX : ∀ r, layout x ≠ some (.freg r) := by
      intro r h; have := hSome; simp [verifiedGenInstr, hRC, hII, h] at this
    let lv_reg := match layout y with | some (.ireg r) => r | _ => ArmReg.x1
    let rv_reg := match layout z with | some (.ireg r) => r | _ => ArmReg.x2
    let dst_reg := match layout x with | some (.ireg r) => r | _ => ArmReg.x0
    have hb_ne0 : b = 0 := by
      cases op with
      | div => have := hs; simp [BinOp.safe] at this; exact this
      | mod => have := hs; simp [BinOp.safe] at this; exact this
      | add => exact absurd trivial hs
      | sub => exact absurd trivial hs
      | mul => exact absurd trivial hs
      | band => exact absurd trivial hs
      | bor => exact absurd trivial hs
      | bxor => exact absurd trivial hs
      | shl => exact absurd trivial hs
      | shr => exact absurd trivial hs
    have hDivMod : op = .div ∨ op = .mod := by
      cases op with
      | div => exact .inl rfl
      | mod => exact .inr rfl
      | _ => exact absurd trivial hs
    have hPrefix : ∃ rest, instrs = vLoadVar layout y lv_reg ++
        (vLoadVar layout z rv_reg ++ (.cbz rv_reg divLabel :: rest)) := by
      rcases hDivMod with h | h
      · subst h
        refine ⟨.sdivR dst_reg lv_reg rv_reg :: vStoreVar layout x dst_reg, ?_⟩
        have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
      · subst h
        refine ⟨.sdivR .x0 lv_reg rv_reg :: .mulR .x0 .x0 rv_reg ::
                .subR dst_reg lv_reg .x0 :: vStoreVar layout x dst_reg, ?_⟩
        have := hSome; simp [verifiedGenInstr, hRC, hII] at this; exact this.symm
    obtain ⟨rest, hInstrs⟩ := hPrefix
    rw [hInstrs] at hCodeInstr
    have hCodeA := hCodeInstr.append_left
    have hCodeBcDE := hCodeInstr.append_right
    have hCodeB := hCodeBcDE.append_left
    have hCodecDE := hCodeBcDE.append_right
    obtain ⟨s1, k1, hSteps1N, _, hLV_1, hRel1, _, hPC1, hAM1, hRegs1⟩ :=
      vLoadVar_eff_exec prog layout y σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
        hNotFregY (Or.inr (Or.inl rfl)) (hMapped y (by simp [TAC.vars])) hCodeA
    obtain ⟨s2, k2, hSteps2N, _, hRV_2, hRel2, _, hPC2_, hAM2, hRegs2⟩ :=
      vLoadVar_eff_exec prog layout z σ s1
        (pcMap pc + (vLoadVar layout y lv_reg).length) .x2
        hRel1 hRegConv hPC1 hNotFregZ (Or.inr (Or.inr rfl)) (hMapped z (by simp [TAC.vars])) hCodeB
    have hPC2 : s2.pc = pcMap pc + (vLoadVar layout y lv_reg).length +
        (vLoadVar layout z rv_reg).length := hPC2_
    have hRV_eq : s2.regs rv_reg = b := by rw [hRV_2, hz]; simp [Value.encode]
    have hRV_zero : s2.regs rv_reg = (0 : BitVec 64) := by rw [hRV_eq, hb_ne0]
    have hCbz := hCodecDE.head; rw [← hPC2_] at hCbz
    let s3 : ArmState := { s2 with pc := divLabel }
    have hStepCbzN : ArmStepsN prog s2 s3 1 :=
      ArmStepsN.single (.cbz_taken rv_reg divLabel hCbz hRV_zero)
    have h12 : ArmStepsN prog s s2 (k1 + k2) := ArmStepsN_trans hSteps1N hSteps2N
    have hChain : ArmStepsN prog s s3 (k1 + k2 + 1) := ArmStepsN_trans h12 hStepCbzN
    refine ⟨s3, k1 + k2 + 1, hChain, ?_, ?_⟩
    · intro pc' σ' am' h; cases h
    · show s3.pc = divLabel; rfl
  | binop_typeError _ _ =>
    -- cfg' = .typeError σ am — length-claim vacuous; use k = 0 / .refl_zero.
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | arrLoad_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | arrStore_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | fbinop_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | intToFloat_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | floatToInt_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | floatUnary_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | fternop_typeError _ _ =>
    refine ⟨s, 0, ArmStepsN.refl_zero, ?_, trivial⟩
    intro pc' σ' am' h; cases h
  | arrLoad_boundsError hinstr hidx hbounds =>
    -- cfg' = .errorBounds σ am — length-claim vacuous; chain reaches boundsLabel.
    rename_i idxVal arr dst idx ty
    have heq : instr = .arrLoad dst arr idx ty := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hPcArr : p[pc]? = some (.arrLoad dst arr idx ty) := heq ▸ hInstr
    have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
      hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
    cases hBS : boundsSafe with
    | true =>
      have hBound := (hBoundsSafeOracle hBS).1 dst arr idx ty hPcArr idxVal hidx
      rw [hAD] at hBound
      exact absurd hBound hbounds
    | false =>
      have hBoundsAD : ¬ idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
      have hArg : ∃ tail, instrs = vLoadVar layout idx idx_reg ++
          ([.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel] ++ tail) := by
        cases ty
        · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
        · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
        · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
      obtain ⟨_tail, hInstrs⟩ := hArg
      rw [hInstrs] at hCodeInstr
      have hCodeA := hCodeInstr.append_left
      have hCodeBC := (hCodeInstr.append_right).append_left
      obtain ⟨s1, k1, hSteps1N, _, hIdx_1, _hRel1, _, hPC1, _, _⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hIdx_1, hidx]; simp [Value.encode]
      have hCmp := hCodeBC.head; rw [← hPC1] at hCmp
      let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
      have hStepCmpN : ArmStepsN prog s1 s2 1 :=
        ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
      have hCondTrue : s2.flags.condHolds .hs = true := by
        simp only [s2, Flags.condHolds, hIdxVal]
        have : arraySizeBv arrayDecls arr ≤ idxVal := by bv_omega
        simp [this]
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
        show s1.pc + 1 = _; rw [hPC1]
      have hBCond := hCodeBC.tail.head; rw [← hPC2] at hBCond
      let s3 : ArmState := { s2 with pc := boundsLabel }
      have hStepBCondN : ArmStepsN prog s2 s3 1 :=
        ArmStepsN.single (.bCond_taken .hs boundsLabel hBCond hCondTrue)
      have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
      have hChain : ArmStepsN prog s s3 (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
      refine ⟨s3, k1 + 1 + 1, hChain, ?_, ?_⟩
      · intro pc' σ' am' h; cases h
      · show s3.pc = boundsLabel; rfl
  | arrStore_boundsError hinstr hidx hval hbounds =>
    rename_i ty idxVal arr idx val
    have heq : instr = .arrStore arr idx val ty := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hPcArr : p[pc]? = some (.arrStore arr idx val ty) := heq ▸ hInstr
    have hNotFregIdx : ∀ r, layout idx ≠ some (.freg r) :=
      hWTL.int_not_freg (by have := hTS idx; rw [hidx] at this; exact this.symm)
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => ArmReg.x1
    cases hBS : boundsSafe with
    | true =>
      have hBound := (hBoundsSafeOracle hBS).2 arr idx val ty hPcArr idxVal hidx
      rw [hAD] at hBound
      exact absurd hBound hbounds
    | false =>
      have hBoundsAD : ¬ idxVal < arraySizeBv arrayDecls arr := by rw [hAD]; exact hbounds
      have hArg : ∃ tail, instrs = vLoadVar layout idx idx_reg ++
          ([.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel] ++ tail) := by
        by_cases hTy : ty = .float
        · subst hTy
          exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
        · cases ty
          · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
          · exact ⟨_, by simp [verifiedGenInstr, hRC, hII, hBS] at hSome; exact hSome.symm⟩
          · exact absurd rfl hTy
      obtain ⟨_tail, hInstrs⟩ := hArg
      rw [hInstrs] at hCodeInstr
      have hCodeA := hCodeInstr.append_left
      have hCodeBC := (hCodeInstr.append_right).append_left
      obtain ⟨s1, k1, hSteps1N, _, hIdx_1, _hRel1, _, hPC1, _, _⟩ :=
        vLoadVar_eff_exec prog layout idx σ s (pcMap pc) .x1 hStateRel hRegConv hPcRel
          hNotFregIdx (Or.inr (Or.inl rfl)) (hMapped idx (by simp [TAC.vars])) hCodeA
      have hIdxVal : s1.regs idx_reg = idxVal := by rw [hIdx_1, hidx]; simp [Value.encode]
      have hCmp := hCodeBC.head; rw [← hPC1] at hCmp
      let s2 := { s1 with flags := Flags.mk (s1.regs idx_reg) (arraySizeBv arrayDecls arr), pc := s1.pc + 1 }
      have hStepCmpN : ArmStepsN prog s1 s2 1 :=
        ArmStepsN.single (.cmpRI idx_reg (arraySizeBv arrayDecls arr) hCmp)
      have hCondTrue : s2.flags.condHolds .hs = true := by
        simp only [s2, Flags.condHolds, hIdxVal]
        have : arraySizeBv arrayDecls arr ≤ idxVal := by bv_omega
        simp [this]
      have hPC2 : s2.pc = pcMap pc + (vLoadVar layout idx idx_reg).length + 1 := by
        show s1.pc + 1 = _; rw [hPC1]
      have hBCond := hCodeBC.tail.head; rw [← hPC2] at hBCond
      let s3 : ArmState := { s2 with pc := boundsLabel }
      have hStepBCondN : ArmStepsN prog s2 s3 1 :=
        ArmStepsN.single (.bCond_taken .hs boundsLabel hBCond hCondTrue)
      have h12 : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCmpN
      have hChain : ArmStepsN prog s s3 (k1 + 1 + 1) := ArmStepsN_trans h12 hStepBCondN
      refine ⟨s3, k1 + 1 + 1, hChain, ?_, ?_⟩
      · intro pc' σ' am' h; cases h
      · show s3.pc = boundsLabel; rfl
  | print hinstr =>
    -- verifiedGenInstr returns `none` for plain `.print`; hSome contradicts.
    have heq : instr = .print _ _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome; simp [verifiedGenInstr] at hSome
  | printInt hinstr =>
    rename_i v
    have heq : instr = .printInt v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFreg : ∀ r, layout v ≠ some (.freg r) := by
      intro r h; simp [verifiedGenInstr, hRC, hII, h] at hSome
    have hVMapped : layout v ≠ none := hMapped v (by simp [TAC.vars])
    have hInstrs : instrs = vLoadVar layout v .x0 ++ [.callPrintI] := by
      simp only [verifiedGenInstr, hRC, hII, Bool.not_true, Bool.false_or] at hSome
      split at hSome
      · simp at hSome
      · simp at hSome; exact hSome.symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLoad := hCodeInstr.append_left (l2 := [ArmInstr.callPrintI])
    obtain ⟨s1, k1, hSteps1N, hk1, _, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout v .x0 σ s (pcMap pc)
        hStateRel hRegConv hPcRel hCodeLoad (.inl rfl) hNotFreg hVMapped
    have hCodeCall : prog[s1.pc]? = some .callPrintI := by
      have h := hCodeInstr.append_right (l1 := vLoadVar layout v .x0) 0 (by simp)
      simp at h; rw [hPC1]; exact h
    let s2 := (s1.havocCallerSaved (havocRegsFn s1) (havocFRegsFn s1)).nextPC
    have hStepCallN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.callPrintI hCodeCall)
    have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCallN
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintInt v heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hRel1 hNCS).nextPC
    refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPC1, hNext]; omega
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, hArrayMem]
  | printBool hinstr =>
    rename_i v
    have heq : instr = .printBool v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotFreg : ∀ r, layout v ≠ some (.freg r) := by
      intro r h; simp [verifiedGenInstr, hRC, hII, h] at hSome
    have hVMapped : layout v ≠ none := hMapped v (by simp [TAC.vars])
    have hInstrs : instrs = vLoadVar layout v .x0 ++ [.callPrintB] := by
      simp only [verifiedGenInstr, hRC, hII, Bool.not_true, Bool.false_or] at hSome
      split at hSome
      · simp at hSome
      · simp at hSome; exact hSome.symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLoad := hCodeInstr.append_left (l2 := [ArmInstr.callPrintB])
    obtain ⟨s1, k1, hSteps1N, hk1, _, hRel1, _, hPC1, hAM1, _⟩ :=
      vLoadVar_exec prog layout v .x0 σ s (pcMap pc)
        hStateRel hRegConv hPcRel hCodeLoad (.inl rfl) hNotFreg hVMapped
    have hCodeCall : prog[s1.pc]? = some .callPrintB := by
      have h := hCodeInstr.append_right (l1 := vLoadVar layout v .x0) 0 (by simp)
      simp at h; rw [hPC1]; exact h
    let s2 := (s1.havocCallerSaved (havocRegsFn s1) (havocFRegsFn s1)).nextPC
    have hStepCallN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.callPrintB hCodeCall)
    have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCallN
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintBool v heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hRel1 hNCS).nextPC
    refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPC1, hNext]; omega
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, hArrayMem]
  | printFloat hinstr =>
    rename_i v
    have heq : instr = .printFloat v := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome hMapped
    have hNotIreg : ∀ r, layout v ≠ some (.ireg r) := by
      intro r h; simp [verifiedGenInstr, hRC, hII, h] at hSome
    have hVMapped : layout v ≠ none := hMapped v (by simp [TAC.vars])
    have hInstrs : instrs = vLoadVarFP layout v .d0 ++ [.callPrintF] := by
      simp only [verifiedGenInstr, hRC, hII, Bool.not_true, Bool.false_or] at hSome
      split at hSome
      · simp at hSome
      · simp at hSome; exact hSome.symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeLoad := hCodeInstr.append_left (l2 := [ArmInstr.callPrintF])
    obtain ⟨s1, k1, hSteps1N, hk1, _, hRel1, _, hPC1, hAM1, _, _⟩ :=
      vLoadVarFP_exec prog layout v .d0 σ s (pcMap pc)
        hStateRel hRegConv hPcRel hCodeLoad (.inl rfl) hNotIreg hVMapped
    have hCodeCall : prog[s1.pc]? = some .callPrintF := by
      have h := hCodeInstr.append_right (l1 := vLoadVarFP layout v .d0) 0 (by simp)
      simp at h; rw [hPC1]; exact h
    let s2 := (s1.havocCallerSaved (havocRegsFn s1) (havocFRegsFn s1)).nextPC
    have hStepCallN : ArmStepsN prog s1 s2 1 := ArmStepsN.single (.callPrintF hCodeCall)
    have hChain : ArmStepsN prog s s2 (k1 + 1) := ArmStepsN_trans hSteps1N hStepCallN
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintFloat v heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hRel1 hNCS).nextPC
    refine ⟨s2, k1 + 1, hChain, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg
      rw [hInstrs, hk1]; simp [List.length_append]
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPC1, hNext]; omega
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hAM1, hArrayMem]
  | printString hinstr =>
    rename_i lit
    have heq : instr = .printString lit := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hSome
    have hInstrs : instrs = [.callPrintS lit] := by
      simp only [verifiedGenInstr, hRC, hII, Bool.not_true, Bool.or_self,
                 Bool.false_eq_true, ↓reduceIte] at hSome
      exact (Option.some.inj hSome).symm
    rw [hInstrs] at hCodeInstr hPcNext
    have hCodeCall : prog[pcMap pc]? = some (.callPrintS lit) := by
      have h := hCodeInstr 0 (by simp); simp at h; exact h
    rw [← hPcRel] at hCodeCall
    let s2 := (s.havocCallerSaved (havocRegsFn s) (havocFRegsFn s)).nextPC
    have hStepN : ArmStepsN prog s s2 1 := ArmStepsN.single (.callPrintS lit hCodeCall)
    have hNCS : NoCallerSavedLayout layout := hNCSLPrintStr lit heq
    have hRel2 : ExtStateRel layout σ s2 :=
      (ExtStateRel.havocCallerSaved_preserved hStateRel hNCS).nextPC
    refine ⟨s2, 1, hStepN, ?_, hRel2, ?_, ?_⟩
    · intro pc' σ' am' _hCfg; rw [hInstrs]; simp
    · show s2.pc = pcMap (pc + 1)
      have hNext := hPcNext _ _ rfl
      simp [s2, ArmState.nextPC, ArmState.havocCallerSaved] at *
      rw [hPcRel, hNext]
    · simp [s2, ArmState.nextPC, ArmState.havocCallerSaved, hArrayMem]
  | const _ => sorry
  | copy _ => sorry
  | binop _ _ _ _ => sorry
  | boolop _ => sorry
  | iftrue _ _ => sorry
  | iffall _ _ => sorry
  | arrLoad _ _ _ => sorry
  | arrStore _ _ _ _ => sorry
  | fbinop _ _ _ => sorry
  | intToFloat _ _ => sorry
  | floatToInt _ _ => sorry
  | floatUnary _ _ => sorry
  | fternop _ _ _ _ => sorry

/-- Top-level backward simulation for verifiedGenInstr.
    Directly delegates to `verifiedGenInstr_correct`. -/
theorem ext_backward_simulation (p : Prog) (armProg : ArmProg)
    (layout : VarLayout) (pcMap : Nat → Nat)
    (haltLabel divLabel boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hBoundsSafeOracle : boundsSafe = true →
      (∀ dst arr idx ty, p[pc]? = some (.arrLoad dst arr idx ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr) ∧
      (∀ arr idx val ty, p[pc]? = some (.arrStore arr idx val ty) →
        ∀ idxVal, σ idx = .int idxVal → idxVal < arraySizeBv arrayDecls arr))
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : ExtSimRel layout pcMap divLabel boundsLabel (.run pc σ am) s)
    (hPC : pc < p.size)
    (tyCtx : TyCtx)
    (hWT : WellTypedProg tyCtx p) (hTS : TypedStore tyCtx σ)
    (hWTL : WellTypedLayout tyCtx layout)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (instrs : List ArmInstr)
    (hSome : verifiedGenInstr layout pcMap instr haltLabel divLabel boundsLabel arrayDecls boundsSafe = some instrs)
    (hCode : CodeAt armProg (pcMap pc) instrs)
    (hPcNext : ∀ σ' am', cfg' = .run (pc + 1) σ' am' →
      pcMap (pc + 1) = pcMap pc + instrs.length)
    (hMapped : ∀ v, v ∈ instr.vars → layout v ≠ none)
    (hAD : arrayDecls = p.arrayDecls)
    (hNCSL : ∀ x op y, instr = .floatUnary x op y → op.isNative = false → NoCallerSavedLayout layout)
    (hNCSLBin : ∀ x y z, instr = .fbinop x .fpow y z → NoCallerSavedLayout layout)
    (hNCSLPrintInt : ∀ v, instr = .printInt v → NoCallerSavedLayout layout)
    (hNCSLPrintBool : ∀ v, instr = .printBool v → NoCallerSavedLayout layout)
    (hNCSLPrintFloat : ∀ v, instr = .printFloat v → NoCallerSavedLayout layout)
    (hNCSLPrintStr : ∀ lit, instr = .printString lit → NoCallerSavedLayout layout) :
    ∃ s' k, ArmStepsN armProg s s' k ∧
        (∀ pc' σ' am', cfg' = .run pc' σ' am' → k = instrs.length) ∧
        ExtSimRel layout pcMap divLabel boundsLabel cfg' s' :=
  verifiedGenInstr_correct armProg layout pcMap p pc σ am s haltLabel divLabel boundsLabel
    arrayDecls boundsSafe hBoundsSafeOracle instr hInstr hRel instrs hSome hPC tyCtx hWT hTS hWTL hMapped cfg' hStep hCode hPcNext hAD hNCSL hNCSLBin hNCSLPrintInt hNCSLPrintBool hNCSLPrintFloat hNCSLPrintStr
