import CredibleCompilation.ArmSemantics
import CredibleCompilation.BvLemmas
import CredibleCompilation.ExecChecker
import Std.Tactic.BVDecide

/-!
# ARM64 Correctness Proofs

Correctness theorems for the ARM64 code generation: loadImm64_correct,
Flags.condHolds_correct, genBoolExpr_correct, StateRel.update,
genInstr_correct, and backward_simulation.

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
/-- Helper: Flags.condHolds matches CmpOp.eval for signed integer comparison.
    Uses BitVec 64 subtraction; correctness depends on the msb faithfully
    representing the sign of the mathematical difference for values that
    fit in 64 bits. -/
private theorem msb_eq_decide_ge (x : BitVec 64) :
    x.msb = decide (2^63 ≤ x.toNat) := by
  simp only [BitVec.msb, BitVec.getMsbD]
  simp only [show 64 - 1 - 0 = 63 from by omega]
  simp only [show (decide (0 < 64) && x.getLsbD 63) = x.getLsbD 63 from by simp]
  simp only [BitVec.getLsbD, Nat.testBit]
  have hsr : x.toNat >>> 63 = x.toNat / 2^63 := Nat.shiftRight_eq_div_pow x.toNat 63
  rw [hsr]; rcases (by omega : x.toNat / 2^63 = 0 ∨ x.toNat / 2^63 = 1) with h | h <;> simp [h] <;> omega

private theorem beq_sub_zero (a b : BitVec 64) : ((a - b) == (0 : BitVec 64)) = (a == b) := by
  simp only [BEq.beq, decide_eq_decide]; constructor
  · intro h; bv_omega
  · intro h; subst h; simp

private theorem bne_sub_zero (a b : BitVec 64) : ((a - b) != (0 : BitVec 64)) = (a != b) := by
  have := beq_sub_zero a b; simp only [bne] at *; rw [this]

private theorem BitVec_beq_eq_decide (a b : BitVec 64) : (a == b) = decide (a = b) := rfl

theorem Flags.condHolds_correct (op : CmpOp) (a b : BitVec 64)
    (ha : 0 ≤ a.toInt) (ha' : a.toInt < 2 ^ 63) (hb : 0 ≤ b.toInt) (hb' : b.toInt < 2 ^ 63) :
    (Flags.mk (a - b)).condHolds
      (match op with | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le)
    = op.eval a b := by
  have ha_nat : a.toNat < 2^63 := by
    simp only [BitVec.toInt_eq_toNat_cond] at ha ha'; split at ha <;> split at ha' <;> omega
  have hb_nat : b.toNat < 2^63 := by
    simp only [BitVec.toInt_eq_toNat_cond] at hb hb'; split at hb <;> split at hb' <;> omega
  have ha_eq : a.toInt = a.toNat := by
    simp only [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hb_eq : b.toInt = b.toNat := by
    simp only [BitVec.toInt_eq_toNat_cond]; split <;> omega
  cases op <;> simp only [Flags.condHolds, CmpOp.eval]
  case eq => exact beq_sub_zero a b
  case ne => exact bne_sub_zero a b
  case lt =>
    rw [msb_eq_decide_ge, BitVec.slt, ha_eq, hb_eq, decide_eq_decide]
    constructor
    · intro h; simp [BitVec.toNat_sub] at h; omega
    · intro h; simp [BitVec.toNat_sub]; omega
  case le =>
    rw [msb_eq_decide_ge, beq_sub_zero, BitVec_beq_eq_decide,
        BitVec.sle, ha_eq, hb_eq]
    cases hab : decide (a = b) with
    | false =>
      simp only [Bool.or_false]; rw [decide_eq_decide]
      have hne : a ≠ b := of_decide_eq_false hab
      constructor
      · intro h; simp [BitVec.toNat_sub] at h; omega
      · intro h
        have : a.toNat ≠ b.toNat := fun heq => hne (BitVec.eq_of_toNat_eq heq)
        simp [BitVec.toNat_sub]; omega
    | true =>
      have heq := of_decide_eq_true hab; subst heq; simp
/-- Helper: executing ldr/ldr/cmp/cset for a `.cmp` boolean expression. -/
private theorem genBoolExpr_cmp_correct (prog : ArmProg) (vm : VarMap)
    (op : CmpOp) (lv rv : Var) (σ : Store) (s : ArmState) (startPC : Nat)
    (offL offR : Nat)
    (hL : vm.lookup lv = some offL) (hR : vm.lookup rv = some offR)
    (hRel : StateRel vm σ s)
    (hIntL : ∃ n, σ lv = .int n) (hIntR : ∃ n, σ rv = .int n)
    (hWrapped : WrappedStore σ)
    (hCode : CodeAt prog startPC
      (.ldr .x1 offL :: .ldr .x2 offR :: .cmp .x1 .x2 ::
       .cset .x0 (match op with | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le) :: List.nil))
    (hPC : s.pc = startPC) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs .x0 = (if op.eval (σ lv).toInt (σ rv).toInt then (1 : BitVec 64) else 0) ∧
      (∀ v off, vm.lookup v = some off → s'.stack off = s.stack off) ∧
      s'.pc = startPC + 4 ∧
      s'.arrayMem = s.arrayMem := by
  obtain ⟨nL, hIntL⟩ := hIntL
  obtain ⟨nR, hIntR⟩ := hIntR
  have h0 := hCode.head; have h1 := hCode.tail.head
  have h2 := hCode.tail.tail.head; have h3 := hCode.tail.tail.tail.head
  rw [← hPC] at h0 h1 h2 h3
  -- After ldr x1, ldr x2, cmp, cset
  -- x1 = stack[offL] = (σ lv).encode = nL (since σ lv = .int nL)
  -- x2 = stack[offR] = (σ rv).encode = nR
  -- flags = Flags.mk (x1 - x2) = Flags.mk (nL - nR)
  -- x0 = if flags.condHolds cond then 1 else 0
  have hStackL := hRel lv offL hL
  have hStackR := hRel rv offR hR
  rw [hIntL] at hStackL; rw [hIntR] at hStackR
  simp [Value.encode] at hStackL hStackR
  -- Build the final state
  refine ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
    (.step (.cmpRR .x1 .x2 h2) (.single (.cset .x0 _ h3)))), ?_, ?_, ?_, ?_⟩
  · -- x0 = correct value
    simp [ArmState.setReg, ArmState.nextPC, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
          ArmReg.x1_ne_x2, ArmReg.x2_ne_x1]
    rw [hStackL, hStackR, hIntL, hIntR]
    simp [Value.toInt]
    -- Now need: condHolds (Flags.mk (nL - nR)) cond = op.eval nL nR
    have ⟨hnnL, hltL⟩ := hWrapped lv nL hIntL
    have ⟨hnnR, hltR⟩ := hWrapped rv nR hIntR
    rw [Flags.condHolds_correct op nL nR hnnL hltL hnnR hltR]
  · -- stack preserved
    intro v off hv
    simp [ArmState.setReg, ArmState.nextPC, ArmState.setStack]
  · -- pc advanced by 4
    simp [ArmState.setReg, ArmState.nextPC, hPC]
  · -- arrayMem preserved
    simp [ArmState.setReg, ArmState.nextPC]
/-- `genBoolExpr` correctly evaluates a boolean expression into x0.
    Requires that compared variables are integers (guaranteed by well-typedness). -/
theorem genBoolExpr_correct (prog : ArmProg) (vm : VarMap)
    (be : BoolExpr) (σ : Store) (s : ArmState) (startPC : Nat)
    (hRel : StateRel vm σ s)
    (hScratch : ScratchSafe vm)
    (hCode : CodeAt prog startPC (formalGenBoolExpr vm be))
    (hPC : s.pc = startPC)
    (hVarMap : ∀ v, ∃ off, vm.lookup v = some off)
    (Γ : TyCtx) (hTS : TypedStore Γ σ)
    (hWTBE : WellTypedBoolExpr Γ be)
    (hWrapped : WrappedStore σ) :
    ∃ s', ArmSteps prog s s' ∧
      s'.regs .x0 = (if be.eval σ then (1 : BitVec 64) else 0) ∧
      (∀ v off, vm.lookup v = some off → s'.stack off = s.stack off) ∧
      s'.pc = startPC + (formalGenBoolExpr vm be).length ∧
      s'.arrayMem = s.arrayMem := by
  cases hWTBE with
  | lit =>
    -- be = .lit b → formalGenBoolExpr = [mov x0 (if b then 1 else 0)]
    rename_i b
    simp only [formalGenBoolExpr] at hCode
    have hMov := hCode.head; rw [← hPC] at hMov
    refine ⟨_, .single (.mov .x0 _ hMov), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, BoolExpr.eval]
    · intro v off hv; simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC, hPC, formalGenBoolExpr]
    · rfl
  | bvar hty =>
    -- be = .bvar x → formalGenBoolExpr = [ldr x0 off, andImm x0 x0 1]
    rename_i x
    obtain ⟨offX, hX⟩ := hVarMap x
    simp only [formalGenBoolExpr, hX] at hCode
    have h0 := hCode.head; have h1 := hCode.tail.head
    rw [← hPC] at h0 h1
    -- σ x is a bool since Γ x = .bool and store is typed
    have hTy := hTS x; rw [hty] at hTy
    obtain ⟨bv, hbv⟩ := Value.bool_of_typeOf_bool hTy
    have hStack := hRel x offX hX; rw [hbv] at hStack
    refine ⟨_, .step (.ldr .x0 offX h0) (.single (.andImm .x0 .x0 1 h1)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, hStack, BoolExpr.eval, hbv, Value.toBool, Value.encode]
      cases bv <;> simp
    · intro v off hv; simp [ArmState.setReg, ArmState.nextPC]
    · simp [ArmState.setReg, ArmState.nextPC, hPC, formalGenBoolExpr, hX]
    · rfl
  | cmp htyL htyR =>
    -- be = .cmp op lv rv; implicit order: x, y, op
    rename_i lv rv op'
    obtain ⟨offL, hL⟩ := hVarMap lv; obtain ⟨offR, hR⟩ := hVarMap rv
    simp only [formalGenBoolExpr, hL, hR] at hCode
    have hTyL := hTS lv; rw [htyL] at hTyL
    have hTyR := hTS rv; rw [htyR] at hTyR
    obtain ⟨nL, hnL⟩ := Value.int_of_typeOf_int hTyL
    obtain ⟨nR, hnR⟩ := Value.int_of_typeOf_int hTyR
    have := genBoolExpr_cmp_correct prog vm op' lv rv σ s startPC offL offR hL hR hRel
      ⟨nL, hnL⟩ ⟨nR, hnR⟩ hWrapped hCode hPC
    simp only [BoolExpr.eval, formalGenBoolExpr, hL, hR] at this ⊢
    exact this
  | fcmp htyL htyR =>
    -- Float comparison not yet supported in ARM backend
    sorry
  | cmpLit hty hnn hlt =>
    -- be = .cmpLit op v n
    -- formalGenBoolExpr = [ldr x1 off] ++ formalLoadImm64 x2 n ++ [cmp x1 x2, cset x0 cond]
    rename_i v op' n
    obtain ⟨offV, hV⟩ := hVarMap v
    simp only [formalGenBoolExpr, hV] at hCode
    -- CodeAt for: [ldr x1 offV] ++ formalLoadImm64 x2 n ++ [cmp x1 x2, cset x0 cond]
    -- Split as ([ldr x1 offV] ++ formalLoadImm64 x2 n) ++ [cmp x1 x2, cset x0 cond]
    have hCodeLeft := hCode.append_left  -- [ldr x1 offV] ++ formalLoadImm64 x2 n
    have hCodeCmpCset := hCode.append_right -- [cmp x1 x2, cset x0 cond]
    have hCodeLdr := hCodeLeft.append_left  -- [ldr x1 offV]
    have hCodeLoad := hCodeLeft.append_right -- formalLoadImm64 x2 n
    -- Step 1: ldr x1 offV
    have hLdr := hCodeLdr.head; rw [← hPC] at hLdr
    -- σ v is an integer
    have hTyV := hTS v; rw [hty] at hTyV
    obtain ⟨nV, hnV⟩ := Value.int_of_typeOf_int hTyV
    have hStackV := hRel v offV hV; rw [hnV] at hStackV
    simp [Value.encode] at hStackV
    let s1 := s.setReg .x1 (s.stack offV) |>.nextPC
    -- Step 2: loadImm64 x2 n
    have hLenEq : startPC + [ArmInstr.ldr .x1 offV].length = startPC + 1 := by simp
    rw [hLenEq] at hCodeLoad
    have hPC1 : s1.pc = startPC + 1 := by simp [s1, ArmState.setReg, ArmState.nextPC, hPC]
    obtain ⟨s2, hSteps2, hx2, hStack2, hPC2, hRegs2, hAM2⟩ :=
      loadImm64_correct prog .x2 n s1 (startPC + 1) hCodeLoad hPC1
    -- Step 3: cmp x1 x2, cset x0 cond
    have hLenEq2 : startPC + ([ArmInstr.ldr .x1 offV] ++ formalLoadImm64 .x2 n).length
        = startPC + 1 + (formalLoadImm64 .x2 n).length := by simp; omega
    rw [hLenEq2] at hCodeCmpCset
    have hCmp := hCodeCmpCset.head; rw [← hPC2] at hCmp
    have hCset := hCodeCmpCset.tail.head
    rw [show startPC + 1 + (formalLoadImm64 .x2 n).length + 1 = s2.pc + 1 from by rw [← hPC2]] at hCset
    -- x1 in s2 = x1 in s1 (loadImm64 only writes x2)
    have hx1_s2 : s2.regs .x1 = s1.regs .x1 := hRegs2 .x1 (by decide)
    have hx1_val : s1.regs .x1 = s.stack offV := by simp [s1, ArmState.setReg, ArmState.nextPC]
    -- After cmp: flags = Flags.mk (x1 - x2) = Flags.mk (nV - n)
    -- After cset: x0 = if flags.condHolds cond then 1 else 0
    let cond := match op' with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    let s3 := { s2 with flags := ⟨s2.regs .x1 - s2.regs .x2⟩, pc := s2.pc + 1 }
    let s4 := s3.setReg .x0 (if s3.flags.condHolds cond then (1 : BitVec 64) else 0) |>.nextPC
    refine ⟨s4,
      (.step (.ldr .x1 offV hLdr) (hSteps2.trans
        (.step (.cmpRR .x1 .x2 hCmp) (.single (.cset .x0 cond hCset))))),
      ?_, ?_, ?_, ?_⟩
    · -- x0 = correct value
      -- First establish the key value equalities
      have hx1_eq : s2.regs .x1 = nV := by rw [hx1_s2, hx1_val, hStackV]
      have hx2_eq : s2.regs .x2 = n := hx2
      -- The goal involves s3.flags.condHolds cond which depends on s2.regs
      -- Unfold s4, s3 and simplify the register read
      simp only [s4, s3, ArmState.setReg, ArmState.nextPC, ArmReg.beq_self, ite_true]
      -- Now the goal has condHolds applied to (s2.regs x1 - s2.regs x2)
      -- Use simp with the value equalities to rewrite inside the match
      simp only [hx1_eq, hx2_eq, BoolExpr.eval, hnV, Value.toInt]
      have ⟨hnnV, hltV⟩ := hWrapped v nV hnV
      rw [Flags.condHolds_correct op' nV n hnnV hltV hnn hlt]
    · -- stack preserved
      intro w off hv
      simp only [s4, s3, ArmState.setReg, ArmState.nextPC, ArmState.setStack]
      rw [hStack2]; simp [s1, ArmState.setReg, ArmState.nextPC]
    · -- pc advanced
      simp only [s4, s3, ArmState.setReg, ArmState.nextPC, formalGenBoolExpr, hV,
                  List.length_append, List.length_cons, List.length_nil]
      rw [hPC2]; omega
    · -- arrayMem preserved
      simp only [s4, s3, ArmState.setReg, ArmState.nextPC]
      rw [hAM2]; simp [s1, ArmState.setReg, ArmState.nextPC]
  | not hbe =>
    -- be = .not e → formalGenBoolExpr = formalGenBoolExpr e ++ [eorImm x0 x0 1]
    rename_i e
    simp only [formalGenBoolExpr] at hCode
    have hCodeE := hCode.append_left
    have hCodeEor := hCode.append_right
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1, hAM1⟩ :=
      genBoolExpr_correct prog vm e σ s startPC hRel hScratch hCodeE hPC hVarMap Γ hTS hbe hWrapped
    have hEor := hCodeEor.head; rw [← hPC1] at hEor
    refine ⟨s1.setReg .x0 (s1.regs .x0 ^^^ 1) |>.nextPC,
      hSteps1.trans (.single (.eorImm .x0 .x0 1 hEor)), ?_, ?_, ?_, ?_⟩
    · simp [ArmState.setReg, ArmState.nextPC, BoolExpr.eval, hx0]
      cases e.eval σ <;> simp
    · intro v off hv; simp [ArmState.setReg, ArmState.nextPC]
      exact hStack1 v off hv
    · simp [ArmState.setReg, ArmState.nextPC, formalGenBoolExpr, List.length_append]
      omega
    · simp [ArmState.setReg, ArmState.nextPC, hAM1]
/-- StateRel is preserved when store is updated at `x ↦ w` and stack at `off ↦ w.encode`,
    provided `vm.lookup x = some off` and the VarMap is injective. -/
theorem StateRel.update {vm : VarMap} {σ : Store} {arm : ArmState}
    (hRel : StateRel vm σ arm)
    (hInj : VarMapInjective vm)
    (x : Var) (w : Value) (off : Nat) (hOff : vm.lookup x = some off) :
    StateRel vm (Store.update σ x w) (arm.setStack off w.encode) := by
  intro v off' hv
  simp only [ArmState.setStack]
  by_cases hoff : off' = off
  · subst hoff
    simp
    have := hInj v x off' hv hOff; subst this
    rw [Store.update_self]
  · simp [hoff]
    have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hOff))
    rw [Store.update_other _ _ _ _ hne]
    exact hRel v off' hv
/-- Single TAC instruction backward simulation. -/
theorem genInstr_correct (prog : ArmProg) (vm : VarMap) (pcMap : Nat → Nat)
    (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) (s : ArmState)
    (haltLabel divLabel : Nat)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hRel : SimRel vm pcMap (.run pc σ am) s)
    (hScratch : ScratchSafe vm)
    (hInjective : VarMapInjective vm)
    (hWT : WellTypedProg p.tyCtx p)
    (hTS : TypedStore p.tyCtx σ)
    (hAllInt : AllArrayOpsInt p)
    (hPC_bound : pc < p.size)
    (cfg' : Cfg) (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hVarMap : ∀ v, ∃ off, vm.lookup v = some off)
    (hCodeInstr : CodeAt prog (pcMap pc) (formalGenInstr vm pcMap instr haltLabel divLabel))
    (hWrapped : WrappedStore σ)
    (hPcNext : ∀ pc' σ' am', cfg' = .run pc' σ' am' →
      pcMap pc' = pcMap pc + (formalGenInstr vm pcMap instr haltLabel divLabel).length) :
    ∃ s', ArmSteps prog s s' ∧ SimRel vm pcMap cfg' s' := by
  obtain ⟨hStateRel, hPcRel, hArrayMem⟩ := hRel
  cases hStep with
  | goto hinstr =>
    -- TAC: goto l → ARM: b (pcMap l)
    have heq : instr = .goto _ := Option.some.inj (hInstr.symm.trans hinstr)
    rw [heq] at hCodeInstr; simp only [formalGenInstr] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    exact ⟨{ s with pc := pcMap _ }, .single (.branch _ hb),
      ⟨hStateRel, rfl, hArrayMem⟩⟩
  | halt hinstr =>
    -- TAC: halt → ARM: b haltLabel
    -- formalGenInstr for .halt = [.b haltLabel]
    have hformal : formalGenInstr vm pcMap .halt haltLabel divLabel = [.b haltLabel] := rfl
    rw [show instr = .halt from by
      have := Option.some.inj (hInstr.symm.trans hinstr); exact this] at hCodeInstr
    rw [hformal] at hCodeInstr
    have hb := hCodeInstr.head
    rw [← hPcRel] at hb
    exact ⟨{ s with pc := haltLabel },
      .single (.branch haltLabel hb),
      ⟨hStateRel, hArrayMem⟩⟩
  | const hinstr =>
    -- TAC: x := v → ARM: loadImm64 + str (int) or mov + str (bool)
    rename_i x v
    obtain ⟨offD, hD⟩ := hVarMap x
    have heq : instr = .const x v := Option.some.inj (hInstr.symm.trans hinstr)
    cases v with
    | int n =>
      -- formalGenInstr = formalLoadImm64 x0 n ++ [str x0 offD]
      have hformal : formalGenInstr vm pcMap (.const x (.int n)) haltLabel divLabel =
          formalLoadImm64 .x0 n ++ (.str .x0 offD :: List.nil) := by
        show (match vm.lookup x with | some off => _ | none => _) = _
        rw [hD]
      rw [heq, hformal] at hCodeInstr
      -- Split CodeAt into loadImm64 part and str part
      have hCodeL := hCodeInstr.append_left
      have hCodeR := hCodeInstr.append_right
      have hStr := hCodeR.head
      -- Use loadImm64_correct to load n into x0
      -- 64-bit bound: extract from WellTypedInstr.const via well-typedness
      have hwti := hWT pc hPC_bound
      have heq2 : p[pc] = TAC.const x (.int n) := by
        have := Prog.getElem?_eq_getElem hPC_bound
        rw [this] at hinstr; exact Option.some.inj hinstr
      rw [heq2] at hwti
      have hn64 : n.toNat < 2 ^ 64 := n.isLt
      obtain ⟨s1, hSteps1, hx0, hStack1, hPC1, _, hAM1⟩ :=
        loadImm64_correct prog .x0 n s (pcMap pc) hCodeL hPcRel
      -- Then str x0, [sp, #offD]
      rw [← hPC1] at hStr
      let s2 := s1.setStack offD (s1.regs .x0) |>.nextPC
      refine ⟨s2, hSteps1.trans (.single (.str .x0 offD hStr)), ⟨?_, ?_, ?_⟩⟩
      · -- StateRel
        intro w off hv
        simp only [s2, ArmState.setStack, ArmState.nextPC]
        by_cases hoff : off = offD
        · subst hoff; simp
          have := hInjective w x off hv hD; subst this
          rw [Store.update_self, hx0]; simp [Value.encode]
        · simp [hoff]
          have hne : w ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD))
          rw [Store.update_other _ _ _ _ hne]
          rw [show s1.stack off = s.stack off from by rw [hStack1]]
          exact hStateRel w off hv
      · -- PcRel
        show s1.pc + 1 = pcMap (pc + 1)
        rw [heq, hformal] at hPcNext
        have := hPcNext _ _ _ rfl; simp at this
        rw [this, hPC1]; omega
      · -- arrayMem preserved
        simp only [s2, ArmState.setStack, ArmState.nextPC]
        exact hAM1.trans hArrayMem
    | bool b =>
      have hformal : formalGenInstr vm pcMap (.const x (.bool b)) haltLabel divLabel =
          (.mov .x0 (if b then 1 else 0) :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup x with | some off => _ | none => _) = _
        rw [hD]
      rw [heq, hformal] at hCodeInstr
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      rw [← hPcRel] at h0 h1
      refine ⟨(s.setReg .x0 (if b then 1 else 0) |>.nextPC |>.setStack offD
                (s.setReg .x0 (if b then 1 else 0) |>.nextPC |>.regs .x0) |>.nextPC),
        .step (.mov .x0 _ h0) (.single (.str .x0 offD h1)), ⟨?_, ?_, ?_⟩⟩
      · -- StateRel
        intro w off hv
        simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                    ArmReg.beq_self, ite_true]
        by_cases hoff : off = offD
        · subst hoff; simp
          have := hInjective w x off hv hD; subst this
          rw [Store.update_self]; simp [Value.encode]
        · simp [hoff]
          have hne : w ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD))
          rw [Store.update_other _ _ _ _ hne]; exact hStateRel w off hv
      · -- PcRel
        show s.pc + 1 + 1 = pcMap (pc + 1)
        rw [heq, hformal] at hPcNext
        have := hPcNext _ _ _ rfl; simp at this
        rw [this, hPcRel]
      · -- arrayMem preserved
        simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]
    | float f =>
      -- Float constants not yet supported in ARM backend
      sorry
  | copy hinstr =>
    -- TAC: copy x y → ARM: ldr x0 offS; str x0 offD
    rename_i x y
    have heq : instr = .copy x y := Option.some.inj (hInstr.symm.trans hinstr)
    obtain ⟨offS, hS⟩ := hVarMap y
    obtain ⟨offD, hD⟩ := hVarMap x
    have hformal : formalGenInstr vm pcMap (.copy x y) haltLabel divLabel =
        (.ldr .x0 offS :: .str .x0 offD :: List.nil) := by
      show (match vm.lookup y, vm.lookup x with
        | some offS, some offD => _ | _, _ => _) = _
      rw [hS, hD]
    rw [heq, hformal] at hCodeInstr
    have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
    rw [← hPcRel] at h0 h1
    -- Execute: ldr x0, [sp, #offS]; str x0, [sp, #offD]
    refine ⟨(s.setReg .x0 (s.stack offS) |>.nextPC |>.setStack offD
              (s.setReg .x0 (s.stack offS) |>.nextPC |>.regs .x0) |>.nextPC),
      .step (.ldr .x0 offS h0) (.single (.str .x0 offD h1)),
      ⟨?_, ?_, ?_⟩⟩
    · -- StateRel for σ[x ↦ σ y]
      intro v off hv
      simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                  ArmReg.beq_self, ite_true]
      by_cases hoff : off = offD
      · subst hoff
        simp
        have := hInjective v _ off hv hD; subst this
        rw [Store.update_self]; exact hStateRel y offS hS
      · simp [hoff]
        have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD))
        show s.stack off = (σ[x ↦ σ y] v).encode
        rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv
    · -- PcRel
      show s.pc + 1 + 1 = pcMap (pc + 1)
      rw [heq, hformal] at hPcNext
      have := hPcNext _ _ _ rfl; simp at this
      rw [this, hPcRel]
    · -- arrayMem preserved
      simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]
  | binop hinstr hy hz hs =>
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    rename_i x bop y z a b
    obtain ⟨offL, hL⟩ := hVarMap y
    obtain ⟨offR, hR⟩ := hVarMap z
    obtain ⟨offD, hD'⟩ := hVarMap x
    -- Case split on BinOp first, then compute formalGenInstr for each
    cases bop with
    | div =>
      -- formalGenInstr for div = [ldr x2 offR, cbz x2 divLabel, ldr x1 offL, ldr x2 offR, sdiv x0 x1 x2, str x0 offD]
      have hformal : formalGenInstr vm pcMap (.binop x .div y z) haltLabel divLabel =
          (.ldr .x2 offR :: .cbz .x2 divLabel :: .ldr .x1 offL :: .ldr .x2 offR ::
           .sdivR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head
      have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head
      have h3 := hCodeInstr.tail.tail.tail.head
      have h4 := hCodeInstr.tail.tail.tail.tail.head
      have h5 := hCodeInstr.tail.tail.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3 h4 h5
      -- hs : BinOp.div.safe a b means b ≠ 0
      -- After ldr x2 offR: x2 = stack[offR] = (σ z).encode = b
      -- cbz x2 divLabel: since b ≠ 0, falls through
      -- Then ldr x1, ldr x2, sdiv, str — same as add/sub/mul
      have ⟨hb_nn, hb_lt⟩ := hWrapped z b hz
      have hb_ne0 : b ≠ 0 := by unfold BinOp.safe at hs; exact hs
      have hb_enc_ne : (Value.int b).encode ≠ (0 : BitVec 64) := by
        simp [Value.encode]; exact hb_ne0
      have hb_ne : s.stack offR ≠ (0 : BitVec 64) := by
        rw [hStateRel z offR hR, hz]; exact hb_enc_ne
      exact ⟨_, .step (.ldr .x2 offR h0)
              (.step (.cbz_fall .x2 divLabel h1 (by simp [ArmState.setReg, ArmState.nextPC]; exact hb_ne))
              (.step (.ldr .x1 offL h2)
              (.step (.ldr .x2 offR h3)
              (.step (.sdivR .x0 .x1 .x2 h4 (by
                simp [ArmState.setReg, ArmState.nextPC]
                rw [hStateRel z offR hR, hz]; exact hb_enc_ne))
              (.single (.str .x0 offD h5)))))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1,
                       ite_true, ite_false, Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp
             have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 6 = pcMap (pc + 1)
           have := hPcNext _ _ _ rfl; simp at this; rw [this, hPcRel],
        by simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]⟩
    | mod =>
      -- formalGenInstr for mod = [ldr x2 offR, cbz x2 divLabel, ldr x1 offL, ldr x2 offR,
      --   sdiv x0 x1 x2, mul x0 x0 x2, sub x0 x1 x0, str x0 offD]
      have hformal : formalGenInstr vm pcMap (.binop x .mod y z) haltLabel divLabel =
          (.ldr .x2 offR :: .cbz .x2 divLabel :: .ldr .x1 offL :: .ldr .x2 offR ::
           .sdivR .x0 .x1 .x2 :: .mulR .x0 .x0 .x2 :: .subR .x0 .x1 .x0 ::
           .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head
      have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head
      have h3 := hCodeInstr.tail.tail.tail.head
      have h4 := hCodeInstr.tail.tail.tail.tail.head
      have h5 := hCodeInstr.tail.tail.tail.tail.tail.head
      have h6 := hCodeInstr.tail.tail.tail.tail.tail.tail.head
      have h7 := hCodeInstr.tail.tail.tail.tail.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3 h4 h5 h6 h7
      -- hs : BinOp.mod.safe a b means b ≠ 0
      have ⟨hb_nn, hb_lt⟩ := hWrapped z b hz
      have hb_ne0 : b ≠ 0 := by unfold BinOp.safe at hs; exact hs
      have hb_enc_ne : (Value.int b).encode ≠ (0 : BitVec 64) := by
        simp [Value.encode]; exact hb_ne0
      have hb_ne : s.stack offR ≠ (0 : BitVec 64) := by
        rw [hStateRel z offR hR, hz]; exact hb_enc_ne
      exact ⟨_, .step (.ldr .x2 offR h0)
              (.step (.cbz_fall .x2 divLabel h1 (by simp [ArmState.setReg, ArmState.nextPC]; exact hb_ne))
              (.step (.ldr .x1 offL h2)
              (.step (.ldr .x2 offR h3)
              (.step (.sdivR .x0 .x1 .x2 h4 (by
                simp [ArmState.setReg, ArmState.nextPC]
                rw [hStateRel z offR hR, hz]; exact hb_enc_ne))
              (.step (.mulR .x0 .x0 .x2 h5)
              (.step (.subR .x0 .x1 .x0 h6)
              (.single (.str .x0 offD h7)))))))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1,
                       ite_true, ite_false, Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp
             have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
             exact BitVec.srem_eq_sub_sdiv_mul a b
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 8 = pcMap (pc + 1)
           have := hPcNext _ _ _ rfl; simp at this; rw [this, hPcRel],
        by simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]⟩
    | add =>
      -- formalGenInstr for add = [ldr x1 offL, ldr x2 offR, addR x0 x1 x2, str x0 offD]
      have hformal : formalGenInstr vm pcMap (.binop x .add y z) haltLabel divLabel =
          (.ldr .x1 offL :: .ldr .x2 offR :: .addR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head; have h3 := hCodeInstr.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3
      exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
          (.step (.addR .x0 .x1 .x2 h2) (.single (.str .x0 offD h3)))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, ite_false,
                       Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp; have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 4 = pcMap (pc + 1)
           have := hPcNext _ _ _ rfl; simp at this; rw [this, hPcRel],
        by simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]⟩
    | sub =>
      have hformal : formalGenInstr vm pcMap (.binop x .sub y z) haltLabel divLabel =
          (.ldr .x1 offL :: .ldr .x2 offR :: .subR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head; have h3 := hCodeInstr.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3
      exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
          (.step (.subR .x0 .x1 .x2 h2) (.single (.str .x0 offD h3)))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, ite_false,
                       Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp; have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 4 = pcMap (pc + 1)
           have := hPcNext _ _ _ rfl; simp at this; rw [this, hPcRel],
        by simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]⟩
    | mul =>
      have hformal : formalGenInstr vm pcMap (.binop x .mul y z) haltLabel divLabel =
          (.ldr .x1 offL :: .ldr .x2 offR :: .mulR .x0 .x1 .x2 :: .str .x0 offD :: List.nil) := by
        show (match vm.lookup y, vm.lookup z, vm.lookup x with
          | some offL, some offR, some offD => _ | _, _, _ => _) = _
        rw [hL, hR, hD']; simp
      rw [hformal] at hCodeInstr hPcNext
      have h0 := hCodeInstr.head; have h1 := hCodeInstr.tail.head
      have h2 := hCodeInstr.tail.tail.head; have h3 := hCodeInstr.tail.tail.tail.head
      rw [← hPcRel] at h0 h1 h2 h3
      exact ⟨_, .step (.ldr .x1 offL h0) (.step (.ldr .x2 offR h1)
          (.step (.mulR .x0 .x1 .x2 h2) (.single (.str .x0 offD h3)))),
        by intro v off hv
           simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                       ArmReg.beq_self, ArmReg.x0_ne_x1, ArmReg.x0_ne_x2,
                       ArmReg.x1_ne_x2, ArmReg.x2_ne_x1, ite_true, ite_false,
                       Bool.false_eq_true]
           by_cases hoff : off = offD
           · subst hoff; simp; have := hInjective v x off hv hD'; subst this
             rw [Store.update_self, hStateRel y offL hL, hStateRel z offR hR, hy, hz]
             simp [Value.encode, BinOp.eval]
           · simp [hoff]
             have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
             rw [Store.update_other _ _ _ _ hne]; exact hStateRel v off hv,
        by simp only [ArmState.setStack, ArmState.setReg, ArmState.nextPC]
           show s.pc + 4 = pcMap (pc + 1)
           have := hPcNext _ _ _ rfl; simp at this; rw [this, hPcRel],
        by simp [ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]⟩
  | boolop hinstr =>
    -- TAC: x := bexpr → ARM: genBoolExpr ++ [str x0 offD]
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    rename_i x be
    obtain ⟨offD, hD'⟩ := hVarMap x
    -- formalGenInstr = formalGenBoolExpr ++ [str x0 offD]
    have hformal : formalGenInstr vm pcMap (.boolop x be) haltLabel divLabel =
        formalGenBoolExpr vm be ++ (.str .x0 offD :: List.nil) := by
      show (match vm.lookup x with | some offD => _ | none => _) = _
      rw [hD']
    rw [hformal] at hCodeInstr hPcNext
    have hCodeBE := hCodeInstr.append_left
    have hCodeStr := hCodeInstr.append_right
    -- Extract WellTypedBoolExpr from instruction well-typedness
    have hWTbe : WellTypedBoolExpr p.tyCtx be := by
      have hwti := hWT pc hPC_bound
      have heq := Prog.getElem?_eq_getElem hPC_bound
      rw [hinstr] at heq; rw [← Option.some.inj heq] at hwti
      cases hwti with | boolop _ hbe => exact hbe
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1, hAM1⟩ :=
      genBoolExpr_correct prog vm be σ s (pcMap pc) hStateRel hScratch hCodeBE hPcRel hVarMap
        p.tyCtx hTS hWTbe hWrapped
    -- Then str x0, [sp, #offD]
    have hStr := hCodeStr.head; rw [← hPC1] at hStr
    refine ⟨s1.setStack offD (s1.regs .x0) |>.nextPC,
      hSteps1.trans (.single (.str .x0 offD hStr)), ⟨?_, ?_, ?_⟩⟩
    · -- StateRel for σ[x ↦ .bool (be.eval σ)]
      intro v off hv
      simp only [ArmState.setStack, ArmState.nextPC]
      by_cases hoff : off = offD
      · subst hoff; simp
        have := hInjective v x off hv hD'; subst this
        rw [Store.update_self, hx0]
        simp [Value.encode]
      · simp [hoff]
        have hne : v ≠ x := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hD'))
        rw [Store.update_other _ _ _ _ hne]
        exact (hStack1 v off hv).trans (hStateRel v off hv)
    · -- PcRel
      simp only [ArmState.setStack, ArmState.nextPC]
      show s1.pc + 1 = pcMap (pc + 1)
      have := hPcNext _ _ _ rfl
      simp [List.length_append] at this
      rw [this, hPC1]; omega
    · -- arrayMem preserved
      simp only [ArmState.setStack, ArmState.nextPC]
      exact hAM1.trans hArrayMem
  | iftrue hinstr hcond =>
    -- Extract WellTypedBoolExpr before subst (while instr is still accessible)
    have hWTi := hWT pc hPC_bound
    have heq_instr := Prog.getElem?_eq_getElem hPC_bound
    rw [hinstr] at heq_instr
    have hinstr_eq := Option.some.inj heq_instr
    rw [← hinstr_eq] at hWTi
    have hWTbe := match hWTi with | .ifgoto hbe => hbe
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    simp only [formalGenInstr] at hCodeInstr
    have hCodeBE := hCodeInstr.append_left
    have hCodeCbnz := hCodeInstr.append_right
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1, hAM1⟩ :=
      genBoolExpr_correct prog vm _ σ s (pcMap pc) hStateRel hScratch hCodeBE hPcRel hVarMap
        p.tyCtx hTS hWTbe hWrapped
    have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
    have hx0_ne : s1.regs .x0 ≠ 0 := by rw [hx0, hcond]; simp
    exact ⟨{ s1 with pc := pcMap _ },
      hSteps1.trans (.single (.cbnz_taken .x0 _ hCbnz hx0_ne)),
      ⟨fun v off hv => (hStack1 v off hv).trans (hStateRel v off hv), rfl, hAM1.trans hArrayMem⟩⟩
  | iffall hinstr hcond =>
    -- Extract WellTypedBoolExpr before subst
    have hWTi := hWT pc hPC_bound
    have heq_instr := Prog.getElem?_eq_getElem hPC_bound
    rw [hinstr] at heq_instr
    rw [← Option.some.inj heq_instr] at hWTi
    have hWTbe := match hWTi with | .ifgoto hbe => hbe
    have heq : instr = _ := Option.some.inj (hInstr.symm.trans hinstr)
    subst heq
    simp only [formalGenInstr] at hCodeInstr hPcNext
    have hCodeBE := hCodeInstr.append_left
    have hCodeCbnz := hCodeInstr.append_right
    obtain ⟨s1, hSteps1, hx0, hStack1, hPC1, hAM1⟩ :=
      genBoolExpr_correct prog vm _ σ s (pcMap pc) hStateRel hScratch hCodeBE hPcRel hVarMap
        p.tyCtx hTS hWTbe hWrapped
    have hCbnz := hCodeCbnz.head; rw [← hPC1] at hCbnz
    have hx0_eq : s1.regs .x0 = 0 := by rw [hx0]; simp [hcond]
    refine ⟨s1.nextPC,
      hSteps1.trans (.single (.cbnz_fall .x0 _ hCbnz hx0_eq)),
      ⟨fun v off hv => (hStack1 v off hv).trans (hStateRel v off hv), ?_, ?_⟩⟩
    · show s1.pc + 1 = pcMap (pc + 1)
      have := hPcNext _ _ _ rfl
      simp [List.length_append] at this
      rw [this, hPC1]; omega
    · simp only [ArmState.nextPC]; exact hAM1.trans hArrayMem
  | error hinstr hy hz hs =>
    exact ⟨s, .refl, trivial⟩
  | binop_typeError hinstr hne =>
    exact absurd (Step.binop_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)
  | arrLoad hinstr hidx hbounds =>
    rename_i idxVal arrNm destV idxV _
    have htyint := hAllInt.arrLoad_int hinstr; subst htyint
    obtain ⟨offIdx, hIdx⟩ := hVarMap idxV
    obtain ⟨offX, hX⟩ := hVarMap destV
    have heq : instr = .arrLoad destV arrNm idxV .int := Option.some.inj (hInstr.symm.trans hinstr)
    have hformal : formalGenInstr vm pcMap (.arrLoad destV arrNm idxV .int) haltLabel divLabel =
        [.ldr .x1 offIdx, .arrLd .x0 arrNm .x1, .str .x0 offX] := by
      show (match vm.lookup idxV, vm.lookup destV with
        | some offIdx, some offX => _ | _, _ => _) = _
      rw [hIdx, hX]
    rw [heq, hformal] at hCodeInstr hPcNext
    have h0 := hCodeInstr.head
    have h1 := hCodeInstr.tail.head
    have h2 := hCodeInstr.tail.tail.head
    rw [← hPcRel] at h0 h1 h2
    let s1 := s.setReg .x1 (s.stack offIdx) |>.nextPC
    let s2 := s1.setReg .x0 (s1.arrayMem arrNm (s1.regs .x1)) |>.nextPC
    let s3 := s2.setStack offX (s2.regs .x0) |>.nextPC
    refine ⟨s3, .step (.ldr .x1 offIdx h0) (.step (.arrLd .x0 arrNm .x1 h1) (.single (.str .x0 offX h2))),
      ⟨?_, ?_, ?_⟩⟩
    · -- StateRel for σ[destV ↦ .int (am.read arrNm idxVal)]
      intro w off hv
      simp only [s3, s2, s1, ArmState.setStack, ArmState.setReg, ArmState.nextPC,
                  ArmReg.beq_self, ArmReg.x0_ne_x1, ite_true, ite_false, Bool.false_eq_true]
      by_cases hoff : off = offX
      · subst hoff; simp
        have := hInjective w destV off hv hX; subst this
        rw [Store.update_self]
        simp [Value.encode, ArrayMem.read]
        rw [hArrayMem, hStateRel idxV offIdx hIdx, hidx]; simp [Value.encode]
      · simp [hoff]
        have hne : w ≠ destV := fun h => hoff (Option.some.inj ((h ▸ hv).symm.trans hX))
        rw [Store.update_other _ _ _ _ hne]
        exact hStateRel w off hv
    · -- PcRel
      show s.pc + 1 + 1 + 1 = pcMap (pc + 1)
      have := hPcNext _ _ _ rfl; simp at this
      rw [this, hPcRel]
    · -- arrayMem preserved
      simp [s3, s2, s1, ArmState.setStack, ArmState.setReg, ArmState.nextPC, hArrayMem]
  | arrStore hinstr hidx hval hbounds =>
    rename_i _ idxVal arrNm idxV valV
    have htyint := hAllInt.arrStore_int hinstr; subst htyint
    obtain ⟨offIdx, hIdx⟩ := hVarMap idxV
    obtain ⟨offVal, hVal⟩ := hVarMap valV
    have heq : instr = .arrStore arrNm idxV valV .int := Option.some.inj (hInstr.symm.trans hinstr)
    have hformal : formalGenInstr vm pcMap (.arrStore arrNm idxV valV .int) haltLabel divLabel =
        [.ldr .x1 offIdx, .ldr .x2 offVal, .arrSt arrNm .x1 .x2] := by
      show (match vm.lookup idxV, vm.lookup valV with
        | some offIdx, some offVal => _ | _, _ => _) = _
      rw [hIdx, hVal]
    rw [heq, hformal] at hCodeInstr hPcNext
    have h0 := hCodeInstr.head
    have h1 := hCodeInstr.tail.head
    have h2 := hCodeInstr.tail.tail.head
    rw [← hPcRel] at h0 h1 h2
    let s1 := s.setReg .x1 (s.stack offIdx) |>.nextPC
    let s2 := s1.setReg .x2 (s1.stack offVal) |>.nextPC
    let s3 := s2.setArrayMem arrNm (s2.regs .x1) (s2.regs .x2) |>.nextPC
    refine ⟨s3, .step (.ldr .x1 offIdx h0) (.step (.ldr .x2 offVal h1) (.single (.arrSt arrNm .x1 .x2 h2))),
      ⟨?_, ?_, ?_⟩⟩
    · -- StateRel: σ unchanged
      intro w off hv
      simp only [s3, s2, s1, ArmState.setArrayMem, ArmState.setReg, ArmState.nextPC,
                  ArmState.setStack]
      exact hStateRel w off hv
    · -- PcRel
      show s.pc + 1 + 1 + 1 = pcMap (pc + 1)
      have := hPcNext _ _ _ rfl; simp at this
      rw [this, hPcRel]
    · -- arrayMem: need s3.arrayMem = am.write arrNm idxVal (σ valV).toBits
      simp only [s3, s2, s1, ArmState.setArrayMem, ArmState.setReg, ArmState.nextPC]
      funext x i
      simp only [ArrayMem.write, ArmState.setArrayMem]
      simp only [ArmReg.beq_self, ite_true, ArmReg.x1_ne_x2, Bool.false_eq_true, ite_false]
      have hx1eq : (s.stack offIdx) = idxVal := by
        rw [hStateRel idxV offIdx hIdx, hidx]; simp [Value.encode]
      have hx2eq : s.stack offVal = (σ valV).toBits := by
        rw [hStateRel valV offVal hVal]
        cases hv' : σ valV with
        | int n => simp [Value.encode, Value.toBits]
        | bool bb => rw [hv'] at hval; simp [Value.typeOf] at hval
        | float f => simp [Value.encode, Value.toBits]
      rw [hx1eq, hx2eq, hArrayMem]
  | arrLoad_boundsError hinstr hidx hbounds =>
    exact ⟨s, .refl, trivial⟩
  | arrStore_boundsError hinstr hidx hval hbounds =>
    exact ⟨s, .refl, trivial⟩
  | arrLoad_typeError hinstr hne =>
    exact absurd (Step.arrLoad_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)
  | arrStore_typeError hinstr hne =>
    exact absurd (Step.arrStore_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)
  | fbinop hinstr hy hz =>
    -- Float binary ops not yet supported in ARM backend
    sorry
  | fbinop_typeError hinstr hne =>
    exact absurd (Step.fbinop_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)
  | intToFloat hinstr hy =>
    -- intToFloat not yet supported in ARM backend
    sorry
  | intToFloat_typeError hinstr hne =>
    exact absurd (Step.intToFloat_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)
  | floatToInt hinstr hy =>
    -- floatToInt not yet supported in ARM backend
    sorry
  | floatToInt_typeError hinstr hne =>
    exact absurd (Step.floatToInt_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)
  | floatExp hinstr hy =>
    -- floatExp not yet supported in ARM backend
    sorry
  | floatExp_typeError hinstr hne =>
    exact absurd (Step.floatExp_typeError (am := am) hinstr hne) (Step.no_typeError_of_wellTyped hPC_bound hWT hTS)

/-- Main backward simulation: every TAC step is matched by ARM64 steps.
    Directly delegates to `genInstr_correct`. -/
theorem backward_simulation (p : Prog) (armProg : ArmProg)
    (vm : VarMap) (pcMap : Nat → Nat)
    (hWT : WellTypedProg p.tyCtx p)
    (hInjective : VarMapInjective vm)
    (hVarMap : ∀ v, ∃ off, vm.lookup v = some off)
    (hScratch : ScratchSafe vm)
    (hAllInt : AllArrayOpsInt p)
    {pc : Nat} {σ : Store} {am : ArrayMem} {cfg' : Cfg} {s : ArmState}
    (hStep : p ⊩ Cfg.run pc σ am ⟶ cfg')
    (hRel : SimRel vm pcMap (.run pc σ am) s)
    (hTS : TypedStore p.tyCtx σ)
    (hPC : pc < p.size)
    (haltLabel divLabel : Nat)
    (instr : TAC) (hInstr : p[pc]? = some instr)
    (hCode : CodeAt armProg (pcMap pc) (formalGenInstr vm pcMap instr haltLabel divLabel))
    (hWrapped : WrappedStore σ)
    (hPcNext : ∀ pc' σ' am', cfg' = .run pc' σ' am' →
      pcMap pc' = pcMap pc + (formalGenInstr vm pcMap instr haltLabel divLabel).length) :
    ∃ s', ArmSteps armProg s s' ∧ SimRel vm pcMap cfg' s' := by
  exact genInstr_correct armProg vm pcMap p pc σ am s haltLabel divLabel
    instr hInstr hRel hScratch hInjective hWT hTS hAllInt hPC cfg' hStep hVarMap hCode hWrapped hPcNext
