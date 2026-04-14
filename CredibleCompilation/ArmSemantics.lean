import CredibleCompilation.Semantics
import CredibleCompilation.ArmDefs

/-!
# ARM64 Subset Semantics

Small-step semantics, value encoding/decoding, state relation,
formal instruction generation, CodeAt and simp lemmas.

Split from `AsmSemantics.lean`.
-/

-- ============================================================
-- § 5. Small-step semantics
-- ============================================================

/-- Insert a 16-bit value at a given shift position, keeping other bits. -/
def insertBits (val : BitVec 64) (imm16 : UInt64) (shift : Nat) : BitVec 64 :=
  let imm16bv : BitVec 64 := BitVec.ofNat 64 imm16.toNat
  let mask : BitVec 64 := 0xFFFF#64 <<< shift
  let imm : BitVec 64 := imm16bv <<< shift
  (val &&& ~~~mask) ||| imm

/-- Small-step semantics for the ARM64 subset. -/
inductive ArmStep (prog : ArmProg) : ArmState → ArmState → Prop where

  | mov (rd : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.mov rd imm) →
    ArmStep prog s (s.setReg rd imm |>.nextPC)

  | movR (rd rn : ArmReg) :
    prog[s.pc]? = some (.movR rd rn) →
    ArmStep prog s (s.setReg rd (s.regs rn) |>.nextPC)

  | movz (rd : ArmReg) (imm16 : UInt64) (shift : Nat) :
    prog[s.pc]? = some (.movz rd imm16 shift) →
    ArmStep prog s (s.setReg rd (BitVec.ofNat 64 (imm16 <<< shift.toUInt64).toNat) |>.nextPC)

  | movk (rd : ArmReg) (imm16 : UInt64) (shift : Nat) :
    prog[s.pc]? = some (.movk rd imm16 shift) →
    ArmStep prog s (s.setReg rd (insertBits (s.regs rd) imm16 shift) |>.nextPC)

  | ldr (rd : ArmReg) (off : Nat) :
    prog[s.pc]? = some (.ldr rd off) →
    ArmStep prog s (s.setReg rd (s.stack off) |>.nextPC)

  | str (rs : ArmReg) (off : Nat) :
    prog[s.pc]? = some (.str rs off) →
    ArmStep prog s (s.setStack off (s.regs rs) |>.nextPC)

  | addR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.addR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn + s.regs rm) |>.nextPC)

  | subR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.subR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn - s.regs rm) |>.nextPC)

  | mulR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.mulR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn * s.regs rm) |>.nextPC)

  | sdivR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.sdivR rd rn rm) →
    s.regs rm ≠ 0 →
    ArmStep prog s (s.setReg rd (BitVec.sdiv (s.regs rn) (s.regs rm)) |>.nextPC)

  | cmpRR (rn rm : ArmReg) :
    prog[s.pc]? = some (.cmp rn rm) →
    ArmStep prog s ({ s with flags := Flags.mk (s.regs rn) (s.regs rm), pc := s.pc + 1 })

  | cmpRI (rn : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.cmpImm rn imm) →
    ArmStep prog s ({ s with flags := Flags.mk (s.regs rn) imm, pc := s.pc + 1 })

  | cset (rd : ArmReg) (c : Cond) :
    prog[s.pc]? = some (.cset rd c) →
    ArmStep prog s (s.setReg rd (if s.flags.condHolds c then (1 : BitVec 64) else 0) |>.nextPC)

  | cbz_taken (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbz rn lbl) →
    s.regs rn = (0 : BitVec 64) →
    ArmStep prog s { s with pc := lbl }

  | cbz_fall (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbz rn lbl) →
    s.regs rn ≠ (0 : BitVec 64) →
    ArmStep prog s s.nextPC

  | cbnz_taken (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbnz rn lbl) →
    s.regs rn ≠ (0 : BitVec 64) →
    ArmStep prog s { s with pc := lbl }

  | cbnz_fall (rn : ArmReg) (lbl : Nat) :
    prog[s.pc]? = some (.cbnz rn lbl) →
    s.regs rn = (0 : BitVec 64) →
    ArmStep prog s s.nextPC

  | andImm (rd rn : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.andImm rd rn imm) →
    ArmStep prog s (s.setReg rd (s.regs rn &&& imm) |>.nextPC)

  | andR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.andR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn &&& s.regs rm) |>.nextPC)

  | eorImm (rd rn : ArmReg) (imm : BitVec 64) :
    prog[s.pc]? = some (.eorImm rd rn imm) →
    ArmStep prog s (s.setReg rd (s.regs rn ^^^ imm) |>.nextPC)

  | orrR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.orrR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn ||| s.regs rm) |>.nextPC)

  | eorR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.eorR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn ^^^ s.regs rm) |>.nextPC)

  | lslR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.lslR rd rn rm) →
    ArmStep prog s (s.setReg rd (s.regs rn <<< s.regs rm) |>.nextPC)

  | asrR (rd rn rm : ArmReg) :
    prog[s.pc]? = some (.asrR rd rn rm) →
    ArmStep prog s (s.setReg rd (BitVec.sshiftRight (s.regs rn) (s.regs rm).toNat) |>.nextPC)

  | branch (lbl : Nat) :
    prog[s.pc]? = some (.b lbl) →
    ArmStep prog s { s with pc := lbl }

  | arrLd (dst : ArmReg) (arr : ArrayName) (idxReg : ArmReg) :
    prog[s.pc]? = some (.arrLd dst arr idxReg) →
    ArmStep prog s (s.setReg dst (s.arrayMem arr (s.regs idxReg)) |>.nextPC)

  | arrSt (arr : ArrayName) (idxReg valReg : ArmReg) :
    prog[s.pc]? = some (.arrSt arr idxReg valReg) →
    ArmStep prog s (s.setArrayMem arr (s.regs idxReg) (s.regs valReg) |>.nextPC)

  -- Floating-point instructions

  | fmovToFP (fd : ArmFReg) (rn : ArmReg) :
    prog[s.pc]? = some (.fmovToFP fd rn) →
    ArmStep prog s (s.setFReg fd (s.regs rn) |>.nextPC)

  | fmovRR (fd fn : ArmFReg) :
    prog[s.pc]? = some (.fmovRR fd fn) →
    ArmStep prog s (s.setFReg fd (s.fregs fn) |>.nextPC)

  | fldr (fd : ArmFReg) (off : Nat) :
    prog[s.pc]? = some (.fldr fd off) →
    ArmStep prog s (s.setFReg fd (s.stack off) |>.nextPC)

  | fstr (fs : ArmFReg) (off : Nat) :
    prog[s.pc]? = some (.fstr fs off) →
    ArmStep prog s (s.setStack off (s.fregs fs) |>.nextPC)

  | faddR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.faddR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fsubR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fsubR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fmulR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fmulR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fdivR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fdivR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fdiv (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fcmpRR (fn fm : ArmFReg) :
    prog[s.pc]? = some (.fcmpR fn fm) →
    ArmStep prog s ({ s with flags := Flags.mk (s.fregs fn) (s.fregs fm), pc := s.pc + 1 })

  | scvtf (fd : ArmFReg) (rn : ArmReg) :
    prog[s.pc]? = some (.scvtf fd rn) →
    ArmStep prog s (s.setFReg fd (intToFloatBv (s.regs rn)) |>.nextPC)

  | fcvtzs (rd : ArmReg) (fn : ArmFReg) :
    prog[s.pc]? = some (.fcvtzs rd fn) →
    ArmStep prog s (s.setReg rd (floatToIntBv (s.fregs fn)) |>.nextPC)

  | farrLd (fd : ArmFReg) (arr : ArrayName) (idxReg : ArmReg) :
    prog[s.pc]? = some (.farrLd fd arr idxReg) →
    ArmStep prog s (s.setFReg fd (s.arrayMem arr (s.regs idxReg)) |>.nextPC)

  | farrSt (arr : ArrayName) (idxReg : ArmReg) (valFReg : ArmFReg) :
    prog[s.pc]? = some (.farrSt arr idxReg valFReg) →
    ArmStep prog s (s.setArrayMem arr (s.regs idxReg) (s.fregs valFReg) |>.nextPC)

  | fminR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fminR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fmin (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | fmaxR (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.fmaxR fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fmax (s.fregs fn) (s.fregs fm)) |>.nextPC)

  | callBinF (fop : FloatBinOp) (fd fn fm : ArmFReg) :
    prog[s.pc]? = some (.callBinF fop fd fn fm) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC)

  /-- Native float unary (fsqrt, fabs, fneg): pure, only modifies fd. -/
  | floatUnaryNative (op : FloatUnaryOp) (fd fn : ArmFReg) :
    prog[s.pc]? = some (.floatUnaryInstr op fd fn) →
    op.isNative = true →
    ArmStep prog s (s.setFReg fd (op.eval (s.fregs fn)) |>.nextPC)

  /-- Library float unary (exp, sin, cos, …): havocs all caller-saved
      registers, then sets fd to result (models `bl _exp; fmov fd, d0`). -/
  | floatUnaryLibCall (op : FloatUnaryOp) (fd fn : ArmFReg) :
    prog[s.pc]? = some (.floatUnaryInstr op fd fn) →
    op.isNative = false →
    ArmStep prog s (s.havocCallerSaved |>.setFReg fd (op.eval (s.fregs fn)) |>.nextPC)

/-- Multi-step closure. -/
inductive ArmSteps (prog : ArmProg) : ArmState → ArmState → Prop where
  | refl : ArmSteps prog s s
  | step : ArmStep prog s s' → ArmSteps prog s' s'' → ArmSteps prog s s''

theorem ArmSteps.single {prog : ArmProg} {s s' : ArmState}
    (h : ArmStep prog s s') : ArmSteps prog s s' :=
  .step h .refl

theorem ArmSteps.trans {prog : ArmProg} {s s' s'' : ArmState}
    (h1 : ArmSteps prog s s') (h2 : ArmSteps prog s' s'') :
    ArmSteps prog s s'' := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

-- ============================================================
-- § 6. Value encoding
-- ============================================================

/-- Encode a TAC `Value` as a 64-bit bitvector for the ARM64 representation.
    Since `Value.int` now carries `BitVec 64`, encoding is the identity for ints. -/
def Value.encode : Value → BitVec 64
  | .int n  => n
  | .bool b => if b then 1 else 0
  | .float f => f

/-- Decode a 64-bit bitvector back to a `Value` given its type. -/
def Value.decode (ty : VarTy) (bv : BitVec 64) : Value :=
  match ty with
  | .int  => .int bv
  | .bool => .bool (bv != 0)
  | .float => .float bv

/-- For integer values, encode produces toInt. -/
theorem Value.encode_eq_toInt_of_int {v : Value} (h : ∃ n, v = .int n) :
    v.encode = v.toInt := by
  obtain ⟨n, rfl⟩ := h; rfl

/-- For any value, encode of an integer. -/
@[simp] theorem Value.encode_int (n : BitVec 64) : (Value.int n).encode = n := rfl

theorem Value.encode_decode_int (n : BitVec 64) :
    Value.decode .int (Value.encode (.int n)) = .int n := rfl

theorem Value.encode_decode_bool (b : Bool) :
    Value.decode .bool (Value.encode (.bool b)) = .bool b := by
  simp [encode, decode]; cases b <;> simp

-- ============================================================
-- § 7. State relation
-- ============================================================

/-- A variable-to-stack-offset map. -/
abbrev VarMap := List (Var × Nat)

/-- Look up a variable's stack offset. -/
def VarMap.lookup (vm : VarMap) (v : Var) : Option Nat :=
  vm.find? (fun (x, _) => x == v) |>.map Prod.snd

/-- The ARM64 stack correctly represents the TAC store:
    for every mapped variable, the stack slot holds the encoded value. -/
def StateRel (vm : VarMap) (σ : Store) (arm : ArmState) : Prop :=
  ∀ v off, vm.lookup v = some off → arm.stack off = (σ v).encode

/-- The scratch slot at offset 0 does not alias any variable slot. -/
def ScratchSafe (vm : VarMap) : Prop :=
  ∀ v off, vm.lookup v = some off → off ≠ 0


/-- If a BitVec 64 is nonzero as a BitVec, it is nonzero. (Trivial but useful for readability.) -/
theorem BitVec_ne_zero {b : BitVec 64} (hb : b ≠ 0) : b ≠ 0 := hb

/-- The VarMap is injective: distinct variables have distinct offsets. -/
def VarMapInjective (vm : VarMap) : Prop :=
  ∀ v1 v2 off, vm.lookup v1 = some off → vm.lookup v2 = some off → v1 = v2

/-- PC correspondence: TAC PC maps to ARM PC. -/
def PcRel (pcMap : Nat → Nat) (tac_pc : Nat) (arm_pc : Nat) : Prop :=
  arm_pc = pcMap tac_pc

/-- Full simulation invariant. -/
def SimRel (vm : VarMap) (pcMap : Nat → Nat) (tac_cfg : Cfg) (arm : ArmState) : Prop :=
  match tac_cfg with
  | .run pc σ am    => StateRel vm σ arm ∧ PcRel pcMap pc arm.pc ∧ arm.arrayMem = am
  | .halt σ am      => StateRel vm σ arm ∧ arm.arrayMem = am
  | .error _ _      => True
  | .typeError _ _  => False

-- ============================================================
-- § 7b. Extended state relation (register allocation)
-- ============================================================

/-- Where a variable lives in the ARM64 state. -/
inductive VarLoc where
  /-- On the stack at the given offset. -/
  | stack : Nat → VarLoc
  /-- In an integer register (x0-x28). -/
  | ireg  : ArmReg → VarLoc
  /-- In a floating-point register (d0-d31). -/
  | freg  : ArmFReg → VarLoc
  deriving Repr, DecidableEq

/-- Maps each variable to its location (stack slot or register). -/
structure VarLayout where
  entries : List (Var × VarLoc)

instance : CoeFun VarLayout (fun _ => Var → Option VarLoc) where
  coe layout v := layout.entries.lookup v

/-- Extended state relation: for every mapped variable, the ARM64 location
    holds the encoded TAC value. Generalizes `StateRel` to registers. -/
def ExtStateRel (layout : VarLayout) (σ : Store) (arm : ArmState) : Prop :=
  ∀ v loc, layout v = some loc →
    match loc with
    | .stack off => arm.stack off = (σ v).encode
    | .ireg r    => arm.regs r = (σ v).encode
    | .freg r    => arm.fregs r = (σ v).encode

/-- The layout is injective: distinct variables map to distinct locations. -/
def VarLayoutInjective (layout : VarLayout) : Prop :=
  ∀ v1 v2 loc, layout v1 = some loc → layout v2 = some loc → v1 = v2

/-- No variable is mapped to a scratch register.
    Scratch: x0, x1, x2 (integer), d0, d1 (float).
    x8 is also reserved for array address computation. -/
def ExtScratchSafe (layout : VarLayout) : Prop :=
  ∀ v, layout v ≠ some (.ireg .x0) ∧ layout v ≠ some (.ireg .x1) ∧
       layout v ≠ some (.ireg .x2) ∧ layout v ≠ some (.ireg .x8) ∧
       layout v ≠ some (.freg .d0) ∧ layout v ≠ some (.freg .d1) ∧
       layout v ≠ some (.freg .d2)

/-- Convenience: ExtScratchSafe implies no variable in a specific scratch ireg. -/
theorem ExtScratchSafe.not_x0 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.ireg .x0) := (h v).1
theorem ExtScratchSafe.not_x1 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.ireg .x1) := (h v).2.1
theorem ExtScratchSafe.not_x2 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.ireg .x2) := (h v).2.2.1
theorem ExtScratchSafe.not_x8 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.ireg .x8) := (h v).2.2.2.1
theorem ExtScratchSafe.not_d0 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.freg .d0) := (h v).2.2.2.2.1
theorem ExtScratchSafe.not_d1 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.freg .d1) := (h v).2.2.2.2.2.1
theorem ExtScratchSafe.not_d2 (h : ExtScratchSafe layout) (v : Var) : layout v ≠ some (.freg .d2) := (h v).2.2.2.2.2.2

/-- A layout respects types: non-float variables are not in float registers,
    and float variables are not in integer registers. -/
def WellTypedLayout (Γ : TyCtx) (layout : VarLayout) : Prop :=
  (∀ v r, Γ v ≠ .float → layout v ≠ some (.freg r)) ∧
  (∀ v r, Γ v = .float → layout v ≠ some (.ireg r))

theorem WellTypedLayout.int_not_freg (h : WellTypedLayout Γ layout) (hty : Γ v = .int) :
    ∀ r, layout v ≠ some (.freg r) := fun r => h.1 v r (by rw [hty]; decide)

theorem WellTypedLayout.bool_not_freg (h : WellTypedLayout Γ layout) (hty : Γ v = .bool) :
    ∀ r, layout v ≠ some (.freg r) := fun r => h.1 v r (by rw [hty]; decide)

theorem WellTypedLayout.float_not_ireg (h : WellTypedLayout Γ layout) (hty : Γ v = .float) :
    ∀ r, layout v ≠ some (.ireg r) := fun r => h.2 v r hty

/-- Check no variable maps to a scratch register. -/
def VarLayout.scratchSafe (layout : VarLayout) : Bool :=
  layout.entries.all fun (_, loc) =>
    loc != .ireg .x0 && loc != .ireg .x1 && loc != .ireg .x2 &&
    loc != .ireg .x8 && loc != .freg .d0 && loc != .freg .d1 && loc != .freg .d2

/-- Check no two variables share a location. -/
def VarLayout.isInjective (layout : VarLayout) : Bool :=
  go layout.entries
where
  go : List (Var × VarLoc) → Bool
  | [] => true
  | (_, loc) :: rest => !(rest.any fun (_, l) => l == loc) && go rest

private theorem List.lookup_mem_of_some {entries : List (String × VarLoc)} {v : String} {loc : VarLoc}
    (h : entries.lookup v = some loc) : ∃ k, (k, loc) ∈ entries ∧ (v == k) = true := by
  induction entries with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    next heq =>
      cases hd with | mk a b =>
      simp at h; subst h
      exact ⟨a, .head _, heq⟩
    next hne =>
      obtain ⟨k, hk_mem, hk_eq⟩ := ih h
      exact ⟨k, .tail _ hk_mem, hk_eq⟩

theorem VarLayout.scratchSafe_spec (layout : VarLayout) (h : layout.scratchSafe = true) :
    ExtScratchSafe layout := by
  intro v
  unfold VarLayout.scratchSafe at h
  rw [List.all_eq_true] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro heq <;> simp at heq
  all_goals (
    obtain ⟨k, hk_mem, _⟩ := List.lookup_mem_of_some heq
    have := h ⟨k, _⟩ hk_mem
    simp at this)

private theorem lookup_snd_mem_entries {entries : List (String × VarLoc)} {v : String} {loc : VarLoc}
    (h : entries.lookup v = some loc) : ∃ k, (k, loc) ∈ entries := by
  induction entries with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    next => cases hd with | mk a b => simp at h; subst h; exact ⟨a, .head _⟩
    next => obtain ⟨k, hk⟩ := ih h; exact ⟨k, .tail _ hk⟩

private theorem injective_of_entriesNoDupLoc :
    ∀ (entries : List (String × VarLoc)),
    VarLayout.isInjective.go entries = true →
    ∀ v1 v2 loc, entries.lookup v1 = some loc → entries.lookup v2 = some loc → v1 = v2 := by
  intro entries
  induction entries with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    intro hnd v1 v2 loc h1 h2
    simp [VarLayout.isInjective.go, Bool.and_eq_true] at hnd
    obtain ⟨hnodup_hd, hnd_tl⟩ := hnd
    simp only [List.lookup] at h1 h2
    split at h1
    next hv1eq =>
      split at h2
      next hv2eq =>
        exact (beq_iff_eq.mp hv1eq).symm ▸ (beq_iff_eq.mp hv2eq).symm ▸ rfl
      next hv2ne =>
        simp at h1; subst h1
        obtain ⟨k, hk⟩ := lookup_snd_mem_entries h2
        exact absurd rfl (hnodup_hd k _ hk)
    next hv1ne =>
      split at h2
      next hv2eq =>
        simp at h2; subst h2
        obtain ⟨k, hk⟩ := lookup_snd_mem_entries h1
        exact absurd rfl (hnodup_hd k _ hk)
      next hv2ne =>
        exact ih hnd_tl v1 v2 loc h1 h2

theorem VarLayout.isInjective_spec (layout : VarLayout) (h : layout.isInjective = true) :
    VarLayoutInjective layout := by
  intro v1 v2 loc h1 h2
  simp at h1 h2
  exact injective_of_entriesNoDupLoc layout.entries h v1 v2 loc h1 h2

/-- Full extended simulation invariant (generalizes SimRel). -/
def ExtSimRel (layout : VarLayout) (pcMap : Nat → Nat) (tac_cfg : Cfg) (arm : ArmState) : Prop :=
  match tac_cfg with
  | .run pc σ am    => ExtStateRel layout σ arm ∧ PcRel pcMap pc arm.pc ∧ arm.arrayMem = am
  | .halt σ am      => ExtStateRel layout σ arm ∧ arm.arrayMem = am
  | .error _ _      => True
  | .typeError _ _  => True

-- Read lemmas: extract the value from ExtStateRel

theorem ExtStateRel.read_stack {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {v : Var} {off : Nat}
    (hLoc : layout v = some (.stack off)) :
    arm.stack off = (σ v).encode :=
  h v (.stack off) hLoc

theorem ExtStateRel.read_ireg {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {v : Var} {r : ArmReg}
    (hLoc : layout v = some (.ireg r)) :
    arm.regs r = (σ v).encode :=
  h v (.ireg r) hLoc

theorem ExtStateRel.read_freg {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {v : Var} {r : ArmFReg}
    (hLoc : layout v = some (.freg r)) :
    arm.fregs r = (σ v).encode :=
  h v (.freg r) hLoc

-- Update lemma: after storing a new value for variable v, ExtStateRel is preserved

theorem ExtStateRel.update_stack {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) (hInj : VarLayoutInjective layout)
    {v : Var} {off : Nat} {val : Value}
    (hLoc : layout v = some (.stack off)) :
    ExtStateRel layout (σ[v ↦ val]) (arm.setStack off val.encode) := by
  intro w loc hW
  by_cases hwv : w = v
  · -- w = v: both store and stack updated
    subst hwv; rw [hLoc] at hW; cases hW
    simp [Store.update, ArmState.setStack]
  · -- w ≠ v: store unchanged, stack unchanged at other offsets
    have hStoreEq : (σ[v ↦ val]) w = σ w := Store.update_other σ v w val hwv
    rw [hStoreEq]
    match loc, hW with
    | .stack off', hW =>
      have hne : off' ≠ off := fun heq =>
        hwv (hInj w v (.stack off) (heq ▸ hW) hLoc)
      simp [ArmState.setStack, beq_iff_eq, hne]; exact h w (.stack off') hW
    | .ireg r, hW => exact h w (.ireg r) hW
    | .freg r, hW => exact h w (.freg r) hW

theorem ExtStateRel.update_ireg {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) (hInj : VarLayoutInjective layout)
    {v : Var} {r : ArmReg} {val : Value}
    (hLoc : layout v = some (.ireg r)) :
    ExtStateRel layout (σ[v ↦ val]) (arm.setReg r val.encode) := by
  intro w loc hW
  by_cases hwv : w = v
  · subst hwv; rw [hLoc] at hW; cases hW
    simp [Store.update, ArmState.setReg]
  · have hStoreEq : (σ[v ↦ val]) w = σ w := Store.update_other σ v w val hwv
    rw [hStoreEq]
    match loc, hW with
    | .stack off, hW => exact h w (.stack off) hW
    | .ireg r', hW =>
      have hne : r' ≠ r := fun heq =>
        hwv (hInj w v (.ireg r) (heq ▸ hW) hLoc)
      simp [ArmState.setReg, beq_iff_eq, hne]; exact h w (.ireg r') hW
    | .freg r', hW => exact h w (.freg r') hW

theorem ExtStateRel.update_freg {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) (hInj : VarLayoutInjective layout)
    {v : Var} {r : ArmFReg} {val : Value}
    (hLoc : layout v = some (.freg r)) :
    ExtStateRel layout (σ[v ↦ val]) (arm.setFReg r val.encode) := by
  intro w loc hW
  by_cases hwv : w = v
  · subst hwv; rw [hLoc] at hW; cases hW
    simp [Store.update, ArmState.setFReg]
  · have hStoreEq : (σ[v ↦ val]) w = σ w := Store.update_other σ v w val hwv
    rw [hStoreEq]
    match loc, hW with
    | .stack off, hW => exact h w (.stack off) hW
    | .ireg r', hW => exact h w (.ireg r') hW
    | .freg r', hW =>
      have hne : r' ≠ r := fun heq =>
        hwv (hInj w v (.freg r) (heq ▸ hW) hLoc)
      simp [ArmState.setFReg, beq_iff_eq, hne]; exact h w (.freg r') hW

-- Preservation under operations that don't touch mapped locations

theorem ExtStateRel.setReg_preserved {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {r : ArmReg} {val : BitVec 64}
    (hNoAlias : ∀ v, layout v ≠ some (.ireg r)) :
    ExtStateRel layout σ (arm.setReg r val) := by
  intro w loc hW
  match loc with
  | .stack off => exact h w (.stack off) hW
  | .ireg r' =>
    have hne : r' ≠ r := fun heq => hNoAlias w (heq ▸ hW)
    simp [ArmState.setReg, beq_iff_eq, hne]; exact h w (.ireg r') hW
  | .freg r' => exact h w (.freg r') hW

theorem ExtStateRel.setFReg_preserved {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {r : ArmFReg} {val : BitVec 64}
    (hNoAlias : ∀ v, layout v ≠ some (.freg r)) :
    ExtStateRel layout σ (arm.setFReg r val) := by
  intro w loc hW
  match loc with
  | .stack off => exact h w (.stack off) hW
  | .ireg r' => exact h w (.ireg r') hW
  | .freg r' =>
    have hne : r' ≠ r := fun heq => hNoAlias w (heq ▸ hW)
    simp [ArmState.setFReg, beq_iff_eq, hne]; exact h w (.freg r') hW

-- ExtStateRel is insensitive to PC and flags changes

theorem ExtStateRel.nextPC {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) : ExtStateRel layout σ arm.nextPC := by
  intro v loc hv; exact h v loc hv

theorem ExtStateRel.withPC {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) (pc : Nat) :
    ExtStateRel layout σ { arm with pc := pc } := by
  intro v loc hv; exact h v loc hv

-- ExtStateRel preserved under array memory updates (no scalar locations affected)

theorem ExtStateRel.setArrayMem_preserved {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {arr : ArrayName} {idx val : BitVec 64} :
    ExtStateRel layout σ (arm.setArrayMem arr idx val) := by
  intro w loc hW
  match loc with
  | .stack off => exact h w (.stack off) hW
  | .ireg r => exact h w (.ireg r) hW
  | .freg r => exact h w (.freg r) hW

-- ============================================================
-- § 7b. Caller-saved register safety for library calls
-- ============================================================

/-- No variable in the layout is mapped to a caller-saved register.
    This is a compile-time invariant: the register allocator uses only
    callee-saved registers (and stack) when library calls are present. -/
def NoCallerSavedLayout (layout : VarLayout) : Prop :=
  (∀ v r, layout v = some (.ireg r) → r.isCallerSaved = false) ∧
  (∀ v r, layout v = some (.freg r) → r.isCallerSaved = false)

/-- Decidable checker for `NoCallerSavedLayout`. -/
def checkNoCallerSavedLayout (layout : VarLayout) : Bool :=
  layout.entries.all fun (_, loc) =>
    match loc with
    | .ireg r => !r.isCallerSaved
    | .freg r => !r.isCallerSaved
    | .stack _ => true

private theorem checkNoCallerSavedLayout_ireg {entries : List (String × VarLoc)}
    (h : entries.all (fun (_, loc) => match loc with
      | .ireg r => !r.isCallerSaved | .freg r => !r.isCallerSaved | .stack _ => true) = true)
    {v : String} {r : ArmReg} (hlookup : entries.lookup v = some (.ireg r)) :
    r.isCallerSaved = false := by
  rw [List.all_eq_true] at h
  obtain ⟨k, hk_mem, hk_eq⟩ := List.lookup_mem_of_some hlookup
  have := h ⟨k, .ireg r⟩ hk_mem
  simp [Bool.not_eq_false'] at this; exact this

private theorem checkNoCallerSavedLayout_freg {entries : List (String × VarLoc)}
    (h : entries.all (fun (_, loc) => match loc with
      | .ireg r => !r.isCallerSaved | .freg r => !r.isCallerSaved | .stack _ => true) = true)
    {v : String} {r : ArmFReg} (hlookup : entries.lookup v = some (.freg r)) :
    r.isCallerSaved = false := by
  rw [List.all_eq_true] at h
  obtain ⟨k, hk_mem, hk_eq⟩ := List.lookup_mem_of_some hlookup
  have := h ⟨k, .freg r⟩ hk_mem
  simp [Bool.not_eq_false'] at this; exact this

theorem checkNoCallerSavedLayout_spec (layout : VarLayout)
    (h : checkNoCallerSavedLayout layout = true) :
    NoCallerSavedLayout layout := by
  unfold checkNoCallerSavedLayout at h
  exact ⟨fun v r hloc => checkNoCallerSavedLayout_ireg h hloc,
         fun v r hloc => checkNoCallerSavedLayout_freg h hloc⟩

/-- `havocCallerSaved` preserves `ExtStateRel` when no mapped variable is
    in a caller-saved register. -/
theorem ExtStateRel.havocCallerSaved_preserved
    {layout : VarLayout} {σ : Store} {s : ArmState}
    (hRel : ExtStateRel layout σ s)
    (hNCS : NoCallerSavedLayout layout) :
    ExtStateRel layout σ s.havocCallerSaved := by
  intro v loc hloc
  match loc with
  | .stack off => simp [ArmState.havocCallerSaved]; exact hRel v (.stack off) hloc
  | .ireg r =>
    have hcs := hNCS.1 v r hloc
    simp [ArmState.havocCallerSaved, hcs]; exact hRel v (.ireg r) hloc
  | .freg r =>
    have hcs := hNCS.2 v r hloc
    simp [ArmState.havocCallerSaved, hcs]; exact hRel v (.freg r) hloc

-- ============================================================
-- § 8. Formal instruction generation
-- ============================================================

/-- Generate formal ARM64 instructions for loading an immediate.
    Mirrors `loadImm64` in CodeGen.lean. -/
def formalLoadImm64 (rd : ArmReg) (n : BitVec 64) : List ArmInstr :=
  if n.toNat < 65536 then
    -- Small: single mov
    [.mov rd n]
  else
    -- Large: movz/movk sequence
    let bits : UInt64 := n.toNat.toUInt64
    let w0 := bits &&& 0xFFFF
    let w1 := (bits >>> 16) &&& 0xFFFF
    let w2 := (bits >>> 32) &&& 0xFFFF
    let w3 := (bits >>> 48) &&& 0xFFFF
    let base := [.movz rd w0 0]
    let k1 := if w1 != 0 then [.movk rd w1 16] else []
    let k2 := if w2 != 0 then [.movk rd w2 32] else []
    let k3 := if w3 != 0 then [.movk rd w3 48] else []
    base ++ k1 ++ k2 ++ k3

/-- Generate formal ARM64 instructions for a boolean expression.
    Result is left in x0 (0 or 1). Mirrors `genBoolExpr` in CodeGen.lean. -/
def formalGenBoolExpr (vm : VarMap) (be : BoolExpr) : List ArmInstr :=
  match be with
  | .lit b =>
    [.mov .x0 (if b then (1 : BitVec 64) else 0)]
  | .bvar v =>
    match vm.lookup v with
    | some off => [.ldr .x0 off, .andImm .x0 .x0 (1 : BitVec 64)]
    | none => []
  | .cmp op lv rv =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    match vm.lookup lv, vm.lookup rv with
    | some offL, some offR =>
      [.ldr .x1 offL, .ldr .x2 offR, .cmp .x1 .x2, .cset .x0 cond]
    | _, _ => []
  | .cmpLit op v n =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    match vm.lookup v with
    | some off =>
      [.ldr .x1 off] ++ formalLoadImm64 .x2 n ++ [.cmp .x1 .x2, .cset .x0 cond]
    | none => []
  | .not e =>
    formalGenBoolExpr vm e ++ [.eorImm .x0 .x0 (1 : BitVec 64)]
  | .fcmp fop lv rv =>
    let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
    match vm.lookup lv, vm.lookup rv with
    | some offL, some offR =>
      [.fldr .d1 offL, .fldr .d2 offR, .fcmpR .d1 .d2, .cset .x0 cond]
    | _, _ => []
  | .fcmpLit fop v n =>
    let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
    match vm.lookup v with
    | some off =>
      [.fldr .d1 off] ++ formalLoadImm64 .x0 n ++ [.fmovToFP .d2 .x0, .fcmpR .d1 .d2, .cset .x0 cond]
    | none => []

/-- Generate formal ARM64 instructions for a TAC instruction.
    Mirrors `genInstr` in CodeGen.lean (without the label string).
    `pcMap` maps TAC labels to ARM PCs for branch targets. -/
def formalGenInstr (vm : VarMap) (pcMap : Nat → Nat) (instr : TAC)
    (haltLabel : Nat) (divLabel : Nat) : List ArmInstr :=
  match instr with
  | .const v (.int n) =>
    match vm.lookup v with
    | some off => formalLoadImm64 .x0 n ++ [.str .x0 off]
    | none => []
  | .const v (.bool b) =>
    match vm.lookup v with
    | some off => [.mov .x0 (if b then (1 : BitVec 64) else 0), .str .x0 off]
    | none => []
  | .const v (.float f) =>
    match vm.lookup v with
    | some off => formalLoadImm64 .x0 f ++ [.str .x0 off]
    | none => []
  | .copy dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD => [.ldr .x0 offS, .str .x0 offD]
    | _, _ => []
  | .binop dst op lv rv =>
    match vm.lookup lv, vm.lookup rv, vm.lookup dst with
    | some offL, some offR, some offD =>
      let opInstr := match op with
        | .add  => [ArmInstr.addR .x0 .x1 .x2]
        | .sub  => [.subR .x0 .x1 .x2]
        | .mul  => [.mulR .x0 .x1 .x2]
        | .div  => [.sdivR .x0 .x1 .x2]
        | .mod  => [.sdivR .x0 .x1 .x2, .mulR .x0 .x0 .x2, .subR .x0 .x1 .x0]
        | .band => [.andR .x0 .x1 .x2]
        | .bor  => [.orrR .x0 .x1 .x2]
        | .bxor => [.eorR .x0 .x1 .x2]
        | .shl  => [.lslR .x0 .x1 .x2]
        | .shr  => [.asrR .x0 .x1 .x2]
      if op == .div || op == .mod then
        [.ldr .x2 offR, .cbz .x2 divLabel,
         .ldr .x1 offL, .ldr .x2 offR] ++ opInstr ++ [.str .x0 offD]
      else
        [.ldr .x1 offL, .ldr .x2 offR] ++ opInstr ++ [.str .x0 offD]
    | _, _, _ => []
  | .boolop dst be =>
    match vm.lookup dst with
    | some offD => formalGenBoolExpr vm be ++ [.str .x0 offD]
    | none => []
  | .goto l => [.b (pcMap l)]
  | .ifgoto be l =>
    formalGenBoolExpr vm be ++ [.cbnz .x0 (pcMap l)]
  | .halt => [.b haltLabel]
  | .arrLoad x arr idx ty =>
    match vm.lookup idx, vm.lookup x with
    | some offIdx, some offX =>
      match ty with
      | .float => [.ldr .x1 offIdx, .farrLd .d0 arr .x1, .fstr .d0 offX]
      | .bool  => [.ldr .x1 offIdx, .arrLd .x0 arr .x1, .cmpImm .x0 0, .cset .x0 .ne, .str .x0 offX]
      | .int   => [.ldr .x1 offIdx, .arrLd .x0 arr .x1, .str .x0 offX]
    | _, _ => []
  | .arrStore arr idx val ty =>
    match vm.lookup idx, vm.lookup val with
    | some offIdx, some offVal =>
      if ty == .float then
        [.ldr .x1 offIdx, .fldr .d0 offVal, .farrSt arr .x1 .d0]
      else
        [.ldr .x1 offIdx, .ldr .x2 offVal, .arrSt arr .x1 .x2]
    | _, _ => []
  | .fbinop dst fop lv rv =>
    let fpInstr := match fop with
      | .fadd => ArmInstr.faddR .d0 .d1 .d2
      | .fsub => .fsubR .d0 .d1 .d2
      | .fmul => .fmulR .d0 .d1 .d2
      | .fdiv => .fdivR .d0 .d1 .d2
      | .fmin => .fminR .d0 .d1 .d2
      | .fmax => .fmaxR .d0 .d1 .d2
      | .fpow => .callBinF .fpow .d0 .d1 .d2
    match vm.lookup lv, vm.lookup rv, vm.lookup dst with
    | some offL, some offR, some offD =>
      [.fldr .d1 offL, .fldr .d2 offR, fpInstr, .fstr .d0 offD]
    | _, _, _ => []
  | .intToFloat dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD =>
      [.ldr .x0 offS, .scvtf .d0 .x0, .fstr .d0 offD]
    | _, _ => []
  | .floatToInt dst src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD =>
      [.fldr .d0 offS, .fcvtzs .x0 .d0, .str .x0 offD]
    | _, _ => []
  | .floatUnary dst op src =>
    match vm.lookup src, vm.lookup dst with
    | some offS, some offD =>
      [.fldr .d0 offS, .floatUnaryInstr op .d0 .d0, .fstr .d0 offD]
    | _, _ => []

-- ============================================================
-- § 8b. Verified codegen helpers (register-allocation-aware)
-- ============================================================

/-- Load an integer variable into a scratch register.
    Returns the instruction(s) needed based on where the variable lives. -/
def vLoadVar (layout : VarLayout) (v : Var) (tmp : ArmReg) : List ArmInstr :=
  match layout v with
  | some (.stack off) => [.ldr tmp off]
  | some (.ireg r)    => if r == tmp then [] else [.movR tmp r]
  | some (.freg _)    => []  -- type mismatch: caller should use vLoadVarFP
  | none              => []

/-- Load a float variable into a scratch FP register.
    Returns the instruction(s) needed based on where the variable lives. -/
def vLoadVarFP (layout : VarLayout) (v : Var) (tmp : ArmFReg) : List ArmInstr :=
  match layout v with
  | some (.stack off) => [.fldr tmp off]
  | some (.freg r)    => if r == tmp then [] else [.fmovRR tmp r]
  | some (.ireg _)    => []  -- type mismatch
  | none              => []

/-- Store from a scratch integer register into a variable's location. -/
def vStoreVar (layout : VarLayout) (v : Var) (tmp : ArmReg) : List ArmInstr :=
  match layout v with
  | some (.stack off) => [.str tmp off]
  | some (.ireg r)    => if r == tmp then [] else [.movR r tmp]
  | some (.freg _)    => []  -- type mismatch
  | none              => []

/-- Store from a scratch FP register into a variable's location. -/
def vStoreVarFP (layout : VarLayout) (v : Var) (tmp : ArmFReg) : List ArmInstr :=
  match layout v with
  | some (.stack off) => [.fstr tmp off]
  | some (.freg r)    => if r == tmp then [] else [.fmovRR r tmp]
  | some (.ireg _)    => []  -- type mismatch
  | none              => []

-- ============================================================
-- § 8c. Verified boolean expression codegen
-- ============================================================

/-- Generate verified ARM64 instructions for a boolean expression.
    Result is left in x0 (0 or 1). Mirrors `formalGenBoolExpr` but with VarLayout. -/
def verifiedGenBoolExpr (layout : VarLayout) (be : BoolExpr) : List ArmInstr :=
  match be with
  | .lit b =>
    [.mov .x0 (if b then (1 : BitVec 64) else 0)]
  | .bvar v =>
    vLoadVar layout v .x0 ++ [.andImm .x0 .x0 (1 : BitVec 64)]
  | .cmp op lv rv =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    vLoadVar layout lv .x1 ++ vLoadVar layout rv .x2 ++
    [.cmp .x1 .x2, .cset .x0 cond]
  | .cmpLit op v n =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    vLoadVar layout v .x1 ++ formalLoadImm64 .x2 n ++ [.cmp .x1 .x2, .cset .x0 cond]
  | .not e =>
    verifiedGenBoolExpr layout e ++ [.eorImm .x0 .x0 (1 : BitVec 64)]
  | .fcmp fop lv rv =>
    let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
    vLoadVarFP layout lv .d1 ++ vLoadVarFP layout rv .d2 ++
    [.fcmpR .d1 .d2, .cset .x0 cond]
  | .fcmpLit fop v n =>
    let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
    vLoadVarFP layout v .d1 ++ formalLoadImm64 .x0 n ++ [.fmovToFP .d2 .x0, .fcmpR .d1 .d2, .cset .x0 cond]

-- ============================================================
-- § 8d. Verified instruction codegen
-- ============================================================

/-- Generate verified ARM64 instructions for a TAC instruction.
    Takes `VarLayout` (register allocation) and per-array-access `boundsSafe` flag.
    Mirrors `formalGenInstr` but supports register-allocated variables and bounds-check elimination.
    `boundsSafe` is computed by the caller from interval analysis. -/
def verifiedGenInstr (layout : VarLayout) (pcMap : Nat → Nat) (instr : TAC)
    (haltLabel : Nat) (divLabel : Nat) (boundsLabel : Nat)
    (arrayDecls : List (ArrayName × Nat × VarTy))
    (boundsSafe : Bool := false) : Option (List ArmInstr) :=
  if !layout.scratchSafe || !layout.isInjective then none
  else match instr with
  | .const v (.int n) =>
    match layout v with
    | some (.stack _) | some (.ireg _) =>
      some (formalLoadImm64 .x0 n ++ vStoreVar layout v .x0)
    | _ => none
  | .const v (.bool b) =>
    match layout v with
    | some (.stack _) | some (.ireg _) =>
      some ([.mov .x0 (if b then (1 : BitVec 64) else 0)] ++ vStoreVar layout v .x0)
    | _ => none
  | .const v (.float f) =>
    match layout v with
    | some (.freg _) | some (.stack _) =>
      let dst_reg := match layout v with | some (.freg r) => r | _ => .d0
      some (formalLoadImm64 .x0 f ++ [.fmovToFP dst_reg .x0] ++ vStoreVarFP layout v dst_reg)
    | _ => none
  | .copy dst src =>
    -- Check if source is in a float register; if so, use FP path
    match layout src with
    | some (.freg r) => some (vStoreVarFP layout dst r)
    | _ =>
      match layout dst with
      | some (.freg _) => none
      | _ => some (vLoadVar layout src .x0 ++ vStoreVar layout dst .x0)
  | .binop dst op lv rv =>
    let notFreg := fun v => match layout v with | some (.freg _) => true | _ => false
    if notFreg lv || notFreg rv || notFreg dst then none else
    let lv_reg := match layout lv with | some (.ireg r) => r | _ => .x1
    let rv_reg := match layout rv with | some (.ireg r) => r | _ => .x2
    let dst_reg := match layout dst with | some (.ireg r) => r | _ => .x0
    let opInstr := match op with
      | .add  => [ArmInstr.addR dst_reg lv_reg rv_reg]
      | .sub  => [.subR dst_reg lv_reg rv_reg]
      | .mul  => [.mulR dst_reg lv_reg rv_reg]
      | .div  => [.sdivR dst_reg lv_reg rv_reg]
      | .mod  => [.sdivR .x0 lv_reg rv_reg, .mulR .x0 .x0 rv_reg, .subR dst_reg lv_reg .x0]
      | .band => [.andR dst_reg lv_reg rv_reg]
      | .bor  => [.orrR dst_reg lv_reg rv_reg]
      | .bxor => [.eorR dst_reg lv_reg rv_reg]
      | .shl  => [.lslR dst_reg lv_reg rv_reg]
      | .shr  => [.asrR dst_reg lv_reg rv_reg]
    if op == .div || op == .mod then
      some (vLoadVar layout lv lv_reg ++ vLoadVar layout rv rv_reg ++
      [.cbz rv_reg divLabel] ++ opInstr ++ vStoreVar layout dst dst_reg)
    else
      some (vLoadVar layout lv lv_reg ++ vLoadVar layout rv rv_reg ++
      opInstr ++ vStoreVar layout dst dst_reg)
  | .boolop dst be =>
    let notFreg := match layout dst with | some (.freg _) => true | _ => false
    if notFreg then none else
    some (verifiedGenBoolExpr layout be ++ vStoreVar layout dst .x0)
  | .goto l => some [.b (pcMap l)]
  | .ifgoto be l =>
    some (verifiedGenBoolExpr layout be ++ [.cbnz .x0 (pcMap l)])
  | .halt => some [.b haltLabel]
  | .arrLoad x arr idx ty =>
    let loadIdx := vLoadVar layout idx .x1
    let boundsCheck := if boundsSafe then [] else
      [.cmpImm .x1 (arraySizeBv arrayDecls arr), .cset .x0 .lt, .cbz .x0 boundsLabel]
    match ty with
    | .float =>
      let dst_reg := match layout x with | some (.freg r) => r | _ => .d0
      some (loadIdx ++ boundsCheck ++ [.farrLd dst_reg arr .x1] ++ vStoreVarFP layout x dst_reg)
    | .bool  => some (loadIdx ++ boundsCheck ++ [.arrLd .x0 arr .x1, .cmpImm .x0 0, .cset .x0 .ne] ++ vStoreVar layout x .x0)
    | .int   => some (loadIdx ++ boundsCheck ++ [.arrLd .x0 arr .x1] ++ vStoreVar layout x .x0)
  | .arrStore arr idx val ty =>
    let loadIdx := vLoadVar layout idx .x1
    let boundsCheck := if boundsSafe then [] else
      [.cmpImm .x1 (arraySizeBv arrayDecls arr), .cset .x0 .lt, .cbz .x0 boundsLabel]
    if ty == .float then
      let val_reg := match layout val with | some (.freg r) => r | _ => .d0
      some (loadIdx ++ boundsCheck ++ vLoadVarFP layout val val_reg ++ [.farrSt arr .x1 val_reg])
    else
      some (loadIdx ++ boundsCheck ++ vLoadVar layout val .x2 ++ [.arrSt arr .x1 .x2])
  | .fbinop dst fop lv rv =>
    match layout lv, layout rv, layout dst with
    | some (.ireg _), _, _ => none
    | _, some (.ireg _), _ => none
    | _, _, some (.ireg _) => none
    | _, _, _ =>
      let lv_reg := match layout lv with | some (.freg r) => r | _ => .d1
      let rv_reg := match layout rv with | some (.freg r) => r | _ => .d2
      let dst_reg := match layout dst with | some (.freg r) => r | _ => .d0
      let fpInstr := match fop with
        | .fadd => ArmInstr.faddR dst_reg lv_reg rv_reg
        | .fsub => .fsubR dst_reg lv_reg rv_reg
        | .fmul => .fmulR dst_reg lv_reg rv_reg
        | .fdiv => .fdivR dst_reg lv_reg rv_reg
        | .fmin => .fminR dst_reg lv_reg rv_reg
        | .fmax => .fmaxR dst_reg lv_reg rv_reg
        | .fpow => .callBinF .fpow dst_reg lv_reg rv_reg
      some (vLoadVarFP layout lv lv_reg ++ vLoadVarFP layout rv rv_reg ++ [fpInstr] ++ vStoreVarFP layout dst dst_reg)
  | .intToFloat dst src =>
    match layout src, layout dst with
    | some (.freg _), _ => none
    | _, some (.ireg _) => none
    | _, _ =>
      let dst_reg := match layout dst with | some (.freg r) => r | _ => .d0
      some (vLoadVar layout src .x0 ++ [.scvtf dst_reg .x0] ++ vStoreVarFP layout dst dst_reg)
  | .floatToInt dst src =>
    match layout src, layout dst with
    | some (.ireg _), _ => none
    | _, some (.freg _) => none
    | _, _ =>
      let src_reg := match layout src with | some (.freg r) => r | _ => .d0
      some (vLoadVarFP layout src src_reg ++ [.fcvtzs .x0 src_reg] ++ vStoreVar layout dst .x0)
  | .floatUnary dst op src =>
    match layout src, layout dst with
    | some (.ireg _), _ => none
    | _, some (.ireg _) => none
    | _, _ =>
      let src_reg := match layout src with | some (.freg r) => r | _ => .d0
      let dst_reg := match layout dst with | some (.freg r) => r | _ => .d0
      some (vLoadVarFP layout src src_reg ++ [.floatUnaryInstr op dst_reg src_reg] ++ vStoreVarFP layout dst dst_reg)

-- ============================================================
-- § 9. CodeAt and helper lemmas
-- ============================================================

/-- A code segment is embedded in the program starting at a given PC. -/
def CodeAt (prog : ArmProg) (startPC : Nat) (instrs : List ArmInstr) : Prop :=
  ∀ i, (h : i < instrs.length) →
    prog[startPC + i]? = some instrs[i]

-- Helper: CodeAt for a single instruction
theorem CodeAt.head {prog : ArmProg} {startPC : Nat} {instr : ArmInstr} {rest : List ArmInstr}
    (h : CodeAt prog startPC (instr :: rest)) :
    prog[startPC]? = some instr := by
  have := h 0 (by simp)
  simp at this; exact this

-- Helper: CodeAt for the tail
theorem CodeAt.tail {prog : ArmProg} {startPC : Nat} {instr : ArmInstr} {rest : List ArmInstr}
    (h : CodeAt prog startPC (instr :: rest)) :
    CodeAt prog (startPC + 1) rest := by
  intro i hi
  have := h (i + 1) (by simp; omega)
  rw [show startPC + (i + 1) = startPC + 1 + i from by omega] at this
  exact this

-- Helper: execute one instruction and advance
theorem ArmSteps.one_then {prog : ArmProg} {s s' s'' : ArmState}
    (h1 : ArmStep prog s s') (h2 : ArmSteps prog s' s'') :
    ArmSteps prog s s'' :=
  .step h1 h2

-- setReg preserves stack
@[simp] theorem ArmState.setReg_stack (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).stack = s.stack := rfl

-- nextPC preserves stack and regs
@[simp] theorem ArmState.nextPC_stack (s : ArmState) :
    s.nextPC.stack = s.stack := rfl

@[simp] theorem ArmState.nextPC_regs (s : ArmState) :
    s.nextPC.regs = s.regs := rfl

@[simp] theorem ArmState.nextPC_pc (s : ArmState) :
    s.nextPC.pc = s.pc + 1 := rfl

-- setReg reads
@[simp] theorem ArmState.setReg_regs_same (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).regs r = v := by
  simp [setReg]

@[simp] theorem ArmState.setReg_regs_other (s : ArmState) (r r' : ArmReg) (v : BitVec 64) (h : r' ≠ r) :
    (s.setReg r v).regs r' = s.regs r' := by
  simp [setReg, h]

@[simp] theorem ArmState.setReg_pc (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).pc = s.pc := rfl

@[simp] theorem ArmState.setReg_flags (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).flags = s.flags := rfl

@[simp] theorem ArmState.nextPC_flags (s : ArmState) :
    s.nextPC.flags = s.flags := rfl

-- arrayMem preservation
@[simp] theorem ArmState.setReg_arrayMem (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).arrayMem = s.arrayMem := rfl

@[simp] theorem ArmState.nextPC_arrayMem (s : ArmState) :
    s.nextPC.arrayMem = s.arrayMem := rfl

-- setStack preserves regs, fregs, pc, flags, arrayMem
@[simp] theorem ArmState.setStack_regs (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).regs = s.regs := rfl

@[simp] theorem ArmState.setStack_fregs (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).fregs = s.fregs := rfl

@[simp] theorem ArmState.setStack_pc (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).pc = s.pc := rfl

@[simp] theorem ArmState.setStack_flags (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).flags = s.flags := rfl

@[simp] theorem ArmState.setStack_arrayMem (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).arrayMem = s.arrayMem := rfl

-- setReg preserves fregs
@[simp] theorem ArmState.setReg_fregs (s : ArmState) (r : ArmReg) (v : BitVec 64) :
    (s.setReg r v).fregs = s.fregs := rfl

-- setFReg preserves regs, stack, pc, flags, arrayMem
@[simp] theorem ArmState.setFReg_regs (s : ArmState) (r : ArmFReg) (v : BitVec 64) :
    (s.setFReg r v).regs = s.regs := rfl

@[simp] theorem ArmState.setFReg_stack (s : ArmState) (r : ArmFReg) (v : BitVec 64) :
    (s.setFReg r v).stack = s.stack := rfl

@[simp] theorem ArmState.setFReg_pc (s : ArmState) (r : ArmFReg) (v : BitVec 64) :
    (s.setFReg r v).pc = s.pc := rfl

@[simp] theorem ArmState.setFReg_flags (s : ArmState) (r : ArmFReg) (v : BitVec 64) :
    (s.setFReg r v).flags = s.flags := rfl

@[simp] theorem ArmState.setFReg_arrayMem (s : ArmState) (r : ArmFReg) (v : BitVec 64) :
    (s.setFReg r v).arrayMem = s.arrayMem := rfl

@[simp] theorem ArmState.setFReg_fregs_same (s : ArmState) (r : ArmFReg) (v : BitVec 64) :
    (s.setFReg r v).fregs r = v := by
  simp [setFReg]

@[simp] theorem ArmState.setFReg_fregs_other (s : ArmState) (r r' : ArmFReg) (v : BitVec 64) (h : r' ≠ r) :
    (s.setFReg r v).fregs r' = s.fregs r' := by
  simp [setFReg, h]

-- nextPC preserves fregs
@[simp] theorem ArmState.nextPC_fregs (s : ArmState) :
    s.nextPC.fregs = s.fregs := rfl

-- setArrayMem preserves fregs
@[simp] theorem ArmState.setArrayMem_fregs (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).fregs = s.fregs := rfl

-- setArrayMem preserves stack, regs, pc, flags
@[simp] theorem ArmState.setArrayMem_stack (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).stack = s.stack := rfl

@[simp] theorem ArmState.setArrayMem_regs (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).regs = s.regs := rfl

@[simp] theorem ArmState.setArrayMem_pc (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).pc = s.pc := rfl

@[simp] theorem ArmState.setArrayMem_flags (s : ArmState) (arr : ArrayName) (idx : BitVec 64) (v : BitVec 64) :
    (s.setArrayMem arr idx v).flags = s.flags := rfl

-- Register inequality facts for simp
@[simp] theorem ArmReg.x0_ne_x1 : (ArmReg.x0 == ArmReg.x1) = false := by native_decide
@[simp] theorem ArmReg.x0_ne_x2 : (ArmReg.x0 == ArmReg.x2) = false := by native_decide
@[simp] theorem ArmReg.x1_ne_x0 : (ArmReg.x1 == ArmReg.x0) = false := by native_decide
@[simp] theorem ArmReg.x1_ne_x2 : (ArmReg.x1 == ArmReg.x2) = false := by native_decide
@[simp] theorem ArmReg.x2_ne_x0 : (ArmReg.x2 == ArmReg.x0) = false := by native_decide
@[simp] theorem ArmReg.x2_ne_x1 : (ArmReg.x2 == ArmReg.x1) = false := by native_decide
@[simp] theorem ArmReg.beq_self (r : ArmReg) : (r == r) = true := by cases r <;> native_decide

-- FP register inequality facts for simp
@[simp] theorem ArmFReg.d0_ne_d1 : (ArmFReg.d0 == ArmFReg.d1) = false := by native_decide
@[simp] theorem ArmFReg.d0_ne_d2 : (ArmFReg.d0 == ArmFReg.d2) = false := by native_decide
@[simp] theorem ArmFReg.d1_ne_d0 : (ArmFReg.d1 == ArmFReg.d0) = false := by native_decide
@[simp] theorem ArmFReg.d1_ne_d2 : (ArmFReg.d1 == ArmFReg.d2) = false := by native_decide
@[simp] theorem ArmFReg.d2_ne_d0 : (ArmFReg.d2 == ArmFReg.d0) = false := by native_decide
@[simp] theorem ArmFReg.d2_ne_d1 : (ArmFReg.d2 == ArmFReg.d1) = false := by native_decide
@[simp] theorem ArmFReg.beq_self (r : ArmFReg) : (r == r) = true := by cases r <;> native_decide

-- Helper: split CodeAt for appended lists
theorem CodeAt.append_left {prog : ArmProg} {startPC : Nat} {l1 l2 : List ArmInstr}
    (h : CodeAt prog startPC (l1 ++ l2)) :
    CodeAt prog startPC l1 := by
  intro i hi
  have := h i (by simp; omega)
  simp [List.getElem_append_left hi] at this
  exact this

theorem CodeAt.append_right {prog : ArmProg} {startPC : Nat} {l1 l2 : List ArmInstr}
    (h : CodeAt prog startPC (l1 ++ l2)) :
    CodeAt prog (startPC + l1.length) l2 := by
  intro i hi
  have hlt : l1.length + i < (l1 ++ l2).length := by simp; omega
  have := h (l1.length + i) hlt
  have hge : l1.length ≤ l1.length + i := Nat.le_add_right _ _
  rw [List.getElem_append_right hge] at this
  simp at this
  rw [show startPC + l1.length + i = startPC + (l1.length + i) from by omega]
  exact this
