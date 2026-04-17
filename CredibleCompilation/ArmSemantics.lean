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

  | bCond_taken (c : Cond) (lbl : Nat) :
    prog[s.pc]? = some (.bCond c lbl) →
    s.flags.condHolds c = true →
    ArmStep prog s { s with pc := lbl }

  | bCond_fall (c : Cond) (lbl : Nat) :
    prog[s.pc]? = some (.bCond c lbl) →
    s.flags.condHolds c = false →
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

  /-- Print library call: havocs all caller-saved registers to arbitrary
      values (models `bl _printf`). -/
  | printCall (lines : List String)
    (newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64) :
    prog[s.pc]? = some (.printCall lines) →
    ArmStep prog s (s.havocCallerSaved newRegs newFregs |>.nextPC)

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

  /-- `fmadd Dd, Dn, Dm, Da` — Dd ← Da + Dn × Dm (option 3: two-rounding model). -/
  | fmaddR (fd fn fm fa : ArmFReg) :
    prog[s.pc]? = some (.fmaddR fd fn fm fa) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fadd (s.fregs fa) (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm))) |>.nextPC)

  /-- `fmsub Dd, Dn, Dm, Da` — Dd ← Da - Dn × Dm (option 3: two-rounding model). -/
  | fmsubR (fd fn fm fa : ArmFReg) :
    prog[s.pc]? = some (.fmsubR fd fn fm fa) →
    ArmStep prog s (s.setFReg fd (FloatBinOp.eval .fsub (s.fregs fa) (FloatBinOp.eval .fmul (s.fregs fn) (s.fregs fm))) |>.nextPC)

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

  /-- Binary float library call (pow): havocs all caller-saved registers
      to arbitrary values, then sets fd to result (models `bl _pow`). -/
  | callBinF (fop : FloatBinOp) (fd fn fm : ArmFReg)
    (newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64) :
    prog[s.pc]? = some (.callBinF fop fd fn fm) →
    ArmStep prog s (s.havocCallerSaved newRegs newFregs |>.setFReg fd (FloatBinOp.eval fop (s.fregs fn) (s.fregs fm)) |>.nextPC)

  /-- Native float unary (fsqrt, fabs, fneg): pure, only modifies fd. -/
  | floatUnaryNative (op : FloatUnaryOp) (fd fn : ArmFReg) :
    prog[s.pc]? = some (.floatUnaryInstr op fd fn) →
    op.isNative = true →
    ArmStep prog s (s.setFReg fd (op.eval (s.fregs fn)) |>.nextPC)

  /-- Library float unary (exp, sin, cos, …): havocs all caller-saved
      registers to arbitrary values, then sets fd to result (models `bl _exp`). -/
  | floatUnaryLibCall (op : FloatUnaryOp) (fd fn : ArmFReg)
    (newRegs : ArmReg → BitVec 64) (newFregs : ArmFReg → BitVec 64) :
    prog[s.pc]? = some (.floatUnaryInstr op fd fn) →
    op.isNative = false →
    ArmStep prog s (s.havocCallerSaved newRegs newFregs |>.setFReg fd (op.eval (s.fregs fn)) |>.nextPC)

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

/-- For float values, encode produces toFloat. -/
theorem Value.encode_eq_toFloat_of_float {v : Value} (h : ∃ f, v = .float f) :
    v.encode = v.toFloat := by
  obtain ⟨f, rfl⟩ := h; rfl

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

/-- PC correspondence: TAC PC maps to ARM PC. -/
def PcRel (pcMap : Nat → Nat) (tac_pc : Nat) (arm_pc : Nat) : Prop :=
  arm_pc = pcMap tac_pc

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
    in a caller-saved register (for any choice of replacement values). -/
theorem ExtStateRel.havocCallerSaved_preserved
    {layout : VarLayout} {σ : Store} {s : ArmState}
    {newRegs : ArmReg → BitVec 64} {newFregs : ArmFReg → BitVec 64}
    (hRel : ExtStateRel layout σ s)
    (hNCS : NoCallerSavedLayout layout) :
    ExtStateRel layout σ (s.havocCallerSaved newRegs newFregs) := by
  intro v loc hloc
  match loc with
  | .stack off => simp [ArmState.havocCallerSaved]; exact hRel v (.stack off) hloc
  | .ireg r =>
    have hcs := hNCS.1 v r hloc
    simp [ArmState.havocCallerSaved, hcs]; exact hRel v (.ireg r) hloc
  | .freg r =>
    have hcs := hNCS.2 v r hloc
    simp [ArmState.havocCallerSaved, hcs]; exact hRel v (.freg r) hloc

/-- Caller-save round-trip for integer registers:
    str r off → havocCallerSaved → ldr r off restores the original value.
    The final state's register `r` equals `(σ v).encode`. -/
theorem callerSave_str_havoc_ldr_ireg
    {layout : VarLayout} {σ : Store} {s : ArmState}
    {v : Var} {r : ArmReg} {off : Nat}
    {newRegs : ArmReg → BitVec 64} {newFregs : ArmFReg → BitVec 64}
    (hRel : ExtStateRel layout σ s)
    (hLoc : layout v = some (.ireg r))
    (hCS : r.isCallerSaved = true) :
    let s₁ := s.setStack off (s.regs r)
    let s₂ := s₁.havocCallerSaved newRegs newFregs
    let s₃ := s₂.setReg r (s₂.stack off)
    s₃.regs r = (σ v).encode := by
  simp [ArmState.setReg, ArmState.setStack, ArmState.havocCallerSaved]
  exact hRel v (.ireg r) hLoc

/-- Caller-save round-trip for float registers:
    fstr fr off → havocCallerSaved → fldr fr off restores the original value.
    The final state's float register `fr` equals `(σ v).encode`. -/
theorem callerSave_fstr_havoc_fldr_freg
    {layout : VarLayout} {σ : Store} {s : ArmState}
    {v : Var} {fr : ArmFReg} {off : Nat}
    {newRegs : ArmReg → BitVec 64} {newFregs : ArmFReg → BitVec 64}
    (hRel : ExtStateRel layout σ s)
    (hLoc : layout v = some (.freg fr))
    (hCS : fr.isCallerSaved = true) :
    let s₁ := s.setStack off (s.fregs fr)
    let s₂ := s₁.havocCallerSaved newRegs newFregs
    let s₃ := s₂.setFReg fr (s₂.stack off)
    s₃.fregs fr = (σ v).encode := by
  simp [ArmState.setFReg, ArmState.setStack, ArmState.havocCallerSaved]
  exact hRel v (.freg fr) hLoc

/-- Writing to a stack offset not used by any variable preserves ExtStateRel. -/
theorem ExtStateRel.setStack_fresh {layout : VarLayout} {σ : Store} {arm : ArmState}
    (h : ExtStateRel layout σ arm) {off : Nat} {val : BitVec 64}
    (hFresh : ∀ v, layout v ≠ some (.stack off)) :
    ExtStateRel layout σ (arm.setStack off val) := by
  intro w loc hW
  match loc with
  | .stack off' =>
    have hne : off' ≠ off := fun heq =>
      hFresh w (heq ▸ hW)
    simp [ArmState.setStack, beq_iff_eq, hne]; exact h w (.stack off') hW
  | .ireg r => exact h w (.ireg r) hW
  | .freg r => exact h w (.freg r) hW

/-- Full ExtStateRel preservation through ireg caller-save round-trip:
    str r off → havocCallerSaved → ldr r off preserves ExtStateRel
    when the save slot is fresh and no layout variable uses a caller-saved register. -/
theorem ExtStateRel.callerSave_roundtrip_ireg
    {layout : VarLayout} {σ : Store} {s : ArmState}
    {r : ArmReg} {off : Nat}
    {newRegs : ArmReg → BitVec 64} {newFregs : ArmFReg → BitVec 64}
    (hRel : ExtStateRel layout σ s)
    (hNCS : NoCallerSavedLayout layout)
    (hFresh : ∀ v, layout v ≠ some (.stack off)) :
    ExtStateRel layout σ
      (let sh := (s.setStack off (s.regs r)).havocCallerSaved newRegs newFregs
       sh.setReg r (sh.stack off)) := by
  intro w loc hW
  match loc with
  | .stack off' =>
    have hne : off' ≠ off := fun heq => hFresh w (heq ▸ hW)
    simp [ArmState.setReg, ArmState.havocCallerSaved, ArmState.setStack, beq_iff_eq, hne]
    exact hRel w (.stack off') hW
  | .ireg r' =>
    have hcs := hNCS.1 w r' hW
    by_cases hrr : r' = r
    · subst hrr
      simp [ArmState.setReg, ArmState.havocCallerSaved, ArmState.setStack]
      exact hRel w (.ireg r') hW
    · simp [ArmState.setReg, beq_iff_eq, hrr, ArmState.havocCallerSaved, hcs]
      exact hRel w (.ireg r') hW
  | .freg r' =>
    have hcs := hNCS.2 w r' hW
    simp [ArmState.setReg, ArmState.havocCallerSaved, hcs]
    exact hRel w (.freg r') hW

/-- Full ExtStateRel preservation through freg caller-save round-trip:
    fstr fr off → havocCallerSaved → fldr fr off preserves ExtStateRel
    when the save slot is fresh and no layout variable uses a caller-saved register. -/
theorem ExtStateRel.callerSave_roundtrip_freg
    {layout : VarLayout} {σ : Store} {s : ArmState}
    {fr : ArmFReg} {off : Nat}
    {newRegs : ArmReg → BitVec 64} {newFregs : ArmFReg → BitVec 64}
    (hRel : ExtStateRel layout σ s)
    (hNCS : NoCallerSavedLayout layout)
    (hFresh : ∀ v, layout v ≠ some (.stack off)) :
    ExtStateRel layout σ
      (let sh := (s.setStack off (s.fregs fr)).havocCallerSaved newRegs newFregs
       sh.setFReg fr (sh.stack off)) := by
  intro w loc hW
  match loc with
  | .stack off' =>
    have hne : off' ≠ off := fun heq => hFresh w (heq ▸ hW)
    simp [ArmState.setFReg, ArmState.havocCallerSaved, ArmState.setStack, beq_iff_eq, hne]
    exact hRel w (.stack off') hW
  | .ireg r' =>
    have hcs := hNCS.1 w r' hW
    simp [ArmState.setFReg, ArmState.havocCallerSaved, hcs]
    exact hRel w (.ireg r') hW
  | .freg r' =>
    have hcs := hNCS.2 w r' hW
    by_cases hrr : r' = fr
    · subst hrr
      simp [ArmState.setFReg, ArmState.havocCallerSaved, ArmState.setStack]
      exact hRel w (.freg r') hW
    · simp [ArmState.setFReg, beq_iff_eq, hrr, ArmState.havocCallerSaved, hcs]
      exact hRel w (.freg r') hW

-- § 7b. Caller-save composition (N-variable round-trip)
-- ============================================================

/-- An entry describing a single caller-saved register to save/restore,
    paired with the stack offset used as a scratch save slot. -/
inductive CallerSaveEntry where
  | ireg : ArmReg → Nat → CallerSaveEntry
  | freg : ArmFReg → Nat → CallerSaveEntry
  deriving DecidableEq

/-- The stack offset of a save entry. -/
def CallerSaveEntry.off : CallerSaveEntry → Nat
  | .ireg _ o => o
  | .freg _ o => o

/-- Apply all saves: store each caller-saved register to its save slot. -/
def applyCallerSaves : List CallerSaveEntry → ArmState → ArmState
  | [], s => s
  | .ireg r off :: rest, s => applyCallerSaves rest (s.setStack off (s.regs r))
  | .freg r off :: rest, s => applyCallerSaves rest (s.setStack off (s.fregs r))

/-- Apply all restores: load each save slot back into its register. -/
def applyCallerRestores : List CallerSaveEntry → ArmState → ArmState
  | [], s => s
  | .ireg r off :: rest, s => applyCallerRestores rest (s.setReg r (s.stack off))
  | .freg r off :: rest, s => applyCallerRestores rest (s.setFReg r (s.stack off))

/-- Build the save list from a layout: every variable in a caller-saved register
    gets an entry, with save offset looked up from varMap.
    Variables not found in varMap are silently skipped. -/
def genCallerSaveAll (layout : VarLayout) (varMap : List (Var × Nat)) : List CallerSaveEntry :=
  layout.entries.filterMap fun (v, loc) =>
    match loc with
    | .ireg r =>
      if r.isCallerSaved then
        (varMap.find? (fun (x, _) => x == v)).map fun (_, off) => .ireg r off
      else none
    | .freg r =>
      if r.isCallerSaved then
        (varMap.find? (fun (x, _) => x == v)).map fun (_, off) => .freg r off
      else none
    | .stack _ => none

/-- Helper: characterize membership in genCallerSaveAll. -/
private theorem mem_genCallerSaveAll {layout : VarLayout} {varMap : List (Var × Nat)}
    {e : CallerSaveEntry} (h : e ∈ genCallerSaveAll layout varMap) :
    ∃ v loc, (v, loc) ∈ layout.entries ∧
      (match loc with
       | .ireg r =>
         if r.isCallerSaved then
           (varMap.find? (fun (x, _) => x == v)).map (fun (_, off) => CallerSaveEntry.ireg r off) = some e
         else False
       | .freg r =>
         if r.isCallerSaved then
           (varMap.find? (fun (x, _) => x == v)).map (fun (_, off) => CallerSaveEntry.freg r off) = some e
         else False
       | .stack _ => False) := by
  simp only [genCallerSaveAll, List.mem_filterMap] at h
  obtain ⟨⟨v, loc⟩, hMem, hMap⟩ := h
  refine ⟨v, loc, hMem, ?_⟩
  cases loc with
  | ireg r => simp only; split <;> simp_all
  | freg r => simp only; split <;> simp_all
  | stack _ => simp at hMap

/-- Every integer register in a genCallerSaveAll entry is caller-saved. -/
theorem genCallerSaveAll_allCS_ireg {layout : VarLayout} {varMap : List (Var × Nat)}
    {ir : ArmReg} {off : Nat}
    (h : CallerSaveEntry.ireg ir off ∈ genCallerSaveAll layout varMap) :
    ir.isCallerSaved = true := by
  obtain ⟨v, loc, _, hSpec⟩ := mem_genCallerSaveAll h
  cases loc with
  | ireg r =>
    simp only at hSpec; split at hSpec
    · rename_i hcs
      match hFind : varMap.find? (fun (x, _) => x == v) with
      | some (_, off') => simp [hFind, Option.map] at hSpec; exact hSpec.1 ▸ hcs
      | none => simp [hFind] at hSpec
    · exact hSpec.elim
  | freg r =>
    simp only at hSpec; split at hSpec
    · match hFind : varMap.find? (fun (x, _) => x == v) with
      | some (_, off') => simp [hFind, Option.map] at hSpec
      | none => simp [hFind] at hSpec
    · exact hSpec.elim
  | stack _ => simp only at hSpec

/-- Every float register in a genCallerSaveAll entry is caller-saved. -/
theorem genCallerSaveAll_allCS_freg {layout : VarLayout} {varMap : List (Var × Nat)}
    {fr : ArmFReg} {off : Nat}
    (h : CallerSaveEntry.freg fr off ∈ genCallerSaveAll layout varMap) :
    fr.isCallerSaved = true := by
  obtain ⟨v, loc, _, hSpec⟩ := mem_genCallerSaveAll h
  cases loc with
  | ireg r =>
    simp only at hSpec; split at hSpec
    · match hFind : varMap.find? (fun (x, _) => x == v) with
      | some (_, off') => simp [hFind, Option.map] at hSpec
      | none => simp [hFind] at hSpec
    · exact hSpec.elim
  | freg r =>
    simp only at hSpec; split at hSpec
    · rename_i hcs
      match hFind : varMap.find? (fun (x, _) => x == v) with
      | some (_, off') => simp [hFind, Option.map] at hSpec; exact hSpec.1 ▸ hcs
      | none => simp [hFind] at hSpec
    · exact hSpec.elim
  | stack _ => simp only at hSpec

/-- Saves don't change integer registers. -/
theorem applyCallerSaves_regs (entries : List CallerSaveEntry) (s : ArmState) (r : ArmReg) :
    (applyCallerSaves entries s).regs r = s.regs r := by
  match entries with
  | [] => rfl
  | .ireg _ _ :: tl => simp [applyCallerSaves, applyCallerSaves_regs tl, ArmState.setStack]
  | .freg _ _ :: tl => simp [applyCallerSaves, applyCallerSaves_regs tl, ArmState.setStack]

/-- Saves don't change floating-point registers. -/
theorem applyCallerSaves_fregs (entries : List CallerSaveEntry) (s : ArmState) (r : ArmFReg) :
    (applyCallerSaves entries s).fregs r = s.fregs r := by
  match entries with
  | [] => rfl
  | .ireg _ _ :: tl => simp [applyCallerSaves, applyCallerSaves_fregs tl, ArmState.setStack]
  | .freg _ _ :: tl => simp [applyCallerSaves, applyCallerSaves_fregs tl, ArmState.setStack]

/-- Saves don't change arrayMem. -/
theorem applyCallerSaves_arrayMem (entries : List CallerSaveEntry) (s : ArmState) :
    (applyCallerSaves entries s).arrayMem = s.arrayMem := by
  match entries with
  | [] => rfl
  | .ireg _ _ :: tl => simp [applyCallerSaves, applyCallerSaves_arrayMem tl, ArmState.setStack]
  | .freg _ _ :: tl => simp [applyCallerSaves, applyCallerSaves_arrayMem tl, ArmState.setStack]

/-- Restores don't change arrayMem. -/
theorem applyCallerRestores_arrayMem (entries : List CallerSaveEntry) (s : ArmState) :
    (applyCallerRestores entries s).arrayMem = s.arrayMem := by
  match entries with
  | [] => rfl
  | .ireg _ _ :: tl =>
    simp [applyCallerRestores, applyCallerRestores_arrayMem tl, ArmState.setReg]
  | .freg _ _ :: tl =>
    simp [applyCallerRestores, applyCallerRestores_arrayMem tl, ArmState.setFReg]

/-- Restores don't change the stack. -/
theorem applyCallerRestores_stack (entries : List CallerSaveEntry) (s : ArmState) (off : Nat) :
    (applyCallerRestores entries s).stack off = s.stack off := by
  match entries with
  | [] => rfl
  | .ireg _ _ :: tl => simp [applyCallerRestores, applyCallerRestores_stack tl, ArmState.setReg]
  | .freg _ _ :: tl => simp [applyCallerRestores, applyCallerRestores_stack tl, ArmState.setFReg]

/-- Restores don't change integer registers not in the restore list. -/
theorem applyCallerRestores_regs_other (entries : List CallerSaveEntry) (s : ArmState)
    (r : ArmReg) (hNot : ∀ off, .ireg r off ∉ entries) :
    (applyCallerRestores entries s).regs r = s.regs r := by
  match entries with
  | [] => rfl
  | .ireg r' off :: tl =>
    have hne : r' ≠ r := fun h => by subst h; exact hNot off (.head _)
    show (applyCallerRestores tl (s.setReg r' (s.stack off))).regs r = s.regs r
    rw [applyCallerRestores_regs_other tl _ r (fun o hm => hNot o (.tail _ hm))]
    simp only [ArmState.setReg]
    split <;> simp_all
  | .freg _ off :: tl =>
    show (applyCallerRestores tl (s.setFReg _ (s.stack off))).regs r = s.regs r
    rw [applyCallerRestores_regs_other tl _ r (fun o hm => hNot o (.tail _ hm))]
    simp [ArmState.setFReg]

/-- Restores don't change floating-point registers not in the restore list. -/
theorem applyCallerRestores_fregs_other (entries : List CallerSaveEntry) (s : ArmState)
    (r : ArmFReg) (hNot : ∀ off, .freg r off ∉ entries) :
    (applyCallerRestores entries s).fregs r = s.fregs r := by
  match entries with
  | [] => rfl
  | .ireg _ off :: tl =>
    show (applyCallerRestores tl (s.setReg _ (s.stack off))).fregs r = s.fregs r
    rw [applyCallerRestores_fregs_other tl _ r (fun o hm => hNot o (.tail _ hm))]
    simp [ArmState.setReg]
  | .freg r' off :: tl =>
    have hne : r' ≠ r := fun h => by subst h; exact hNot off (.head _)
    show (applyCallerRestores tl (s.setFReg r' (s.stack off))).fregs r = s.fregs r
    rw [applyCallerRestores_fregs_other tl _ r (fun o hm => hNot o (.tail _ hm))]
    simp only [ArmState.setFReg]
    split <;> simp_all

/-- Saving all caller-saved registers to fresh stack slots preserves ExtStateRel.
    "Fresh" means no save offset coincides with any layout stack slot. -/
theorem ExtStateRel.applyCallerSaves_preserved
    {layout : VarLayout} {σ : Store} {s : ArmState}
    (hRel : ExtStateRel layout σ s)
    (entries : List CallerSaveEntry)
    (hFresh : ∀ e ∈ entries, ∀ v, layout v ≠ some (.stack e.off)) :
    ExtStateRel layout σ (applyCallerSaves entries s) := by
  match entries with
  | [] => exact hRel
  | .ireg r off :: tl =>
    simp only [applyCallerSaves]
    exact applyCallerSaves_preserved
      (setStack_fresh hRel (hFresh _ (.head _)))
      tl (fun e he => hFresh e (.tail _ he))
  | .freg r off :: tl =>
    simp only [applyCallerSaves]
    exact applyCallerSaves_preserved
      (setStack_fresh hRel (hFresh _ (.head _)))
      tl (fun e he => hFresh e (.tail _ he))

/-- Saves don't change stack slots whose offset doesn't appear in any entry. -/
theorem applyCallerSaves_stack_other (entries : List CallerSaveEntry) (s : ArmState)
    (off : Nat) (hNot : ∀ e ∈ entries, e.off ≠ off) :
    (applyCallerSaves entries s).stack off = s.stack off := by
  induction entries generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    have hTl := fun e he => hNot e (.tail _ he)
    have hHd := hNot hd (.head _)
    cases hd with
    | ireg r off' =>
      unfold applyCallerSaves
      rw [ih _ hTl]; simp only [ArmState.setStack]; split <;> simp_all [CallerSaveEntry.off]
    | freg r off' =>
      unfold applyCallerSaves
      rw [ih _ hTl]; simp only [ArmState.setStack]; split <;> simp_all [CallerSaveEntry.off]

/-- After saves with distinct offsets, the slot of an ireg entry holds the original register value. -/
theorem applyCallerSaves_stack_ireg (entries : List CallerSaveEntry) (s : ArmState)
    {r : ArmReg} {off : Nat} (hmem : CallerSaveEntry.ireg r off ∈ entries)
    (hNodup : (entries.map CallerSaveEntry.off).Nodup) :
    (applyCallerSaves entries s).stack off = s.regs r := by
  match entries with
  | [] => nomatch hmem
  | .ireg r' off' :: tl =>
    simp only [List.map, List.nodup_cons] at hNodup
    obtain ⟨hNotIn, hNodupTl⟩ := hNodup
    cases hmem with
    | head =>
      show (applyCallerSaves tl (s.setStack off (s.regs r))).stack off = s.regs r
      have hOther : ∀ e ∈ tl, e.off ≠ off := by
        intro e he hEq; exact hNotIn (List.mem_map.mpr ⟨e, he, hEq⟩)
      rw [applyCallerSaves_stack_other tl _ off hOther]
      simp [ArmState.setStack]
    | tail _ htl =>
      show (applyCallerSaves tl (s.setStack off' (s.regs r'))).stack off = s.regs r
      rw [applyCallerSaves_stack_ireg tl _ htl hNodupTl]
      simp [ArmState.setStack]
  | .freg _ off' :: tl =>
    simp only [List.map, List.nodup_cons] at hNodup
    obtain ⟨_, hNodupTl⟩ := hNodup
    cases hmem with
    | tail _ htl =>
      show (applyCallerSaves tl (s.setStack off' (s.fregs _))).stack off = s.regs r
      rw [applyCallerSaves_stack_ireg tl _ htl hNodupTl]
      simp [ArmState.setStack]

/-- After saves with distinct offsets, the slot of a freg entry holds the original register value. -/
theorem applyCallerSaves_stack_freg (entries : List CallerSaveEntry) (s : ArmState)
    {r : ArmFReg} {off : Nat} (hmem : CallerSaveEntry.freg r off ∈ entries)
    (hNodup : (entries.map CallerSaveEntry.off).Nodup) :
    (applyCallerSaves entries s).stack off = s.fregs r := by
  match entries with
  | [] => nomatch hmem
  | .freg r' off' :: tl =>
    simp only [List.map, List.nodup_cons] at hNodup
    obtain ⟨hNotIn, hNodupTl⟩ := hNodup
    cases hmem with
    | head =>
      show (applyCallerSaves tl (s.setStack off (s.fregs r))).stack off = s.fregs r
      have hOther : ∀ e ∈ tl, e.off ≠ off := by
        intro e he hEq; exact hNotIn (List.mem_map.mpr ⟨e, he, hEq⟩)
      rw [applyCallerSaves_stack_other tl _ off hOther]
      simp [ArmState.setStack]
    | tail _ htl =>
      show (applyCallerSaves tl (s.setStack off' (s.fregs r'))).stack off = s.fregs r
      rw [applyCallerSaves_stack_freg tl _ htl hNodupTl]
      simp [ArmState.setStack]
  | .ireg _ off' :: tl =>
    simp only [List.map, List.nodup_cons] at hNodup
    obtain ⟨_, hNodupTl⟩ := hNodup
    cases hmem with
    | tail _ htl =>
      show (applyCallerSaves tl (s.setStack off' (s.regs _))).stack off = s.fregs r
      rw [applyCallerSaves_stack_freg tl _ htl hNodupTl]
      simp [ArmState.setStack]

/-- After restores, an ireg holds the value from its save slot,
    provided all entries for that register use the same offset. -/
theorem applyCallerRestores_regs_at (entries : List CallerSaveEntry) (s : ArmState)
    {r : ArmReg} {off : Nat} (hmem : CallerSaveEntry.ireg r off ∈ entries)
    (hUniq : ∀ off', CallerSaveEntry.ireg r off' ∈ entries → off' = off) :
    (applyCallerRestores entries s).regs r = s.stack off := by
  match entries with
  | [] => nomatch hmem
  | .ireg r' off' :: tl =>
    by_cases hr : r' = r
    · -- head restores to r; by hUniq, off' = off
      have hoff := hUniq off' (hr ▸ .head _)
      show (applyCallerRestores tl (s.setReg r' (s.stack off'))).regs r = s.stack off
      rw [hr, hoff]
      -- goal: (applyCallerRestores tl (s.setReg r (s.stack off))).regs r = s.stack off
      have hUniqTl : ∀ o, CallerSaveEntry.ireg r o ∈ tl → o = off :=
        fun o hm => hUniq o (.tail _ hm)
      by_cases hmTl : CallerSaveEntry.ireg r off ∈ tl
      · rw [applyCallerRestores_regs_at tl _ hmTl hUniqTl]
        simp [ArmState.setReg]
      · have hNot : ∀ off2, CallerSaveEntry.ireg r off2 ∉ tl :=
          fun off2 hm => hmTl (hUniqTl off2 hm ▸ hm)
        rw [applyCallerRestores_regs_other tl _ r hNot]
        simp [ArmState.setReg]
    · -- head restores to r' ≠ r; hmem must be tail
      have htl : CallerSaveEntry.ireg r off ∈ tl := by
        cases hmem with
        | head => simp_all
        | tail _ h => exact h
      show (applyCallerRestores tl (s.setReg r' (s.stack off'))).regs r = s.stack off
      rw [applyCallerRestores_regs_at tl _ htl (fun o hm => hUniq o (.tail _ hm))]
      simp [ArmState.setReg]
  | .freg _ _ :: tl =>
    have htl : CallerSaveEntry.ireg r off ∈ tl := by
      cases hmem with | tail _ h => exact h
    show (applyCallerRestores tl (s.setFReg _ (s.stack _))).regs r = s.stack off
    rw [applyCallerRestores_regs_at tl _ htl (fun o hm => hUniq o (.tail _ hm))]
    simp [ArmState.setFReg]

/-- After restores, a freg holds the value from its save slot,
    provided all entries for that register use the same offset. -/
theorem applyCallerRestores_fregs_at (entries : List CallerSaveEntry) (s : ArmState)
    {r : ArmFReg} {off : Nat} (hmem : CallerSaveEntry.freg r off ∈ entries)
    (hUniq : ∀ off', CallerSaveEntry.freg r off' ∈ entries → off' = off) :
    (applyCallerRestores entries s).fregs r = s.stack off := by
  match entries with
  | [] => nomatch hmem
  | .freg r' off' :: tl =>
    by_cases hr : r' = r
    · have hoff := hUniq off' (hr ▸ .head _)
      show (applyCallerRestores tl (s.setFReg r' (s.stack off'))).fregs r = s.stack off
      rw [hr, hoff]
      have hUniqTl : ∀ o, CallerSaveEntry.freg r o ∈ tl → o = off :=
        fun o hm => hUniq o (.tail _ hm)
      by_cases hmTl : CallerSaveEntry.freg r off ∈ tl
      · rw [applyCallerRestores_fregs_at tl _ hmTl hUniqTl]
        simp [ArmState.setFReg]
      · have hNot : ∀ off2, CallerSaveEntry.freg r off2 ∉ tl :=
          fun off2 hm => hmTl (hUniqTl off2 hm ▸ hm)
        rw [applyCallerRestores_fregs_other tl _ r hNot]
        simp [ArmState.setFReg]
    · have htl : CallerSaveEntry.freg r off ∈ tl := by
        cases hmem with
        | head => simp_all
        | tail _ h => exact h
      show (applyCallerRestores tl (s.setFReg r' (s.stack off'))).fregs r = s.stack off
      rw [applyCallerRestores_fregs_at tl _ htl (fun o hm => hUniq o (.tail _ hm))]
      simp [ArmState.setFReg]
  | .ireg _ _ :: tl =>
    have htl : CallerSaveEntry.freg r off ∈ tl := by
      cases hmem with | tail _ h => exact h
    show (applyCallerRestores tl (s.setReg _ (s.stack _))).fregs r = s.stack off
    rw [applyCallerRestores_fregs_at tl _ htl (fun o hm => hUniq o (.tail _ hm))]
    simp [ArmState.setReg]

/-- **Caller-save composition theorem.**
    Saving all caller-saved registers, havocing, then restoring preserves
    ExtStateRel — without requiring NoCallerSavedLayout.

    Hypotheses:
    - `hFresh`: save offsets don't collide with layout stack slots
    - `hNodup`: save offsets are pairwise distinct
    - `hAllCS`: every entry is for a caller-saved register
    - `hCoversIreg`/`hCoversFReg`: every layout variable in a caller-saved
      register has a corresponding entry
    - `hUniqIreg`/`hUniqFreg`: each register appears with a unique offset -/
theorem ExtStateRel.callerSave_composition
    {layout : VarLayout} {σ : Store} {s : ArmState}
    (hRel : ExtStateRel layout σ s)
    (entries : List CallerSaveEntry)
    {newRegs : ArmReg → BitVec 64} {newFregs : ArmFReg → BitVec 64}
    (hFresh : ∀ e ∈ entries, ∀ v, layout v ≠ some (.stack e.off))
    (hNodup : (entries.map CallerSaveEntry.off).Nodup)
    (hCoversIreg : ∀ v r, layout v = some (.ireg r) → r.isCallerSaved = true →
      ∃ off, CallerSaveEntry.ireg r off ∈ entries)
    (hCoversFreg : ∀ v r, layout v = some (.freg r) → r.isCallerSaved = true →
      ∃ off, CallerSaveEntry.freg r off ∈ entries)
    (hUniqIreg : ∀ r off1 off2, CallerSaveEntry.ireg r off1 ∈ entries →
      CallerSaveEntry.ireg r off2 ∈ entries → off1 = off2)
    (hUniqFreg : ∀ r off1 off2, CallerSaveEntry.freg r off1 ∈ entries →
      CallerSaveEntry.freg r off2 ∈ entries → off1 = off2)
    (hAllCSIreg : ∀ r off, CallerSaveEntry.ireg r off ∈ entries → r.isCallerSaved = true)
    (hAllCSFreg : ∀ r off, CallerSaveEntry.freg r off ∈ entries → r.isCallerSaved = true) :
    ExtStateRel layout σ
      (applyCallerRestores entries
        ((applyCallerSaves entries s).havocCallerSaved newRegs newFregs)) := by
  -- Add hypothesis: entries only contain caller-saved registers
  -- (needed for callee-saved case; add as explicit hypothesis)
  intro v loc hLoc
  match loc with
  | .stack off =>
    simp only [applyCallerRestores_stack, ArmState.havocCallerSaved_stack]
    rw [applyCallerSaves_stack_other entries s off (fun e he hEq =>
      hFresh e he v (hEq ▸ hLoc))]
    exact hRel v (.stack off) hLoc
  | .ireg r =>
    by_cases hcs : r.isCallerSaved
    · -- Caller-saved: was saved, havoc'd, restored
      obtain ⟨saveOff, hMem⟩ := hCoversIreg v r hLoc hcs
      have hUn := fun off' hm => hUniqIreg r off' saveOff hm hMem
      simp only [applyCallerRestores_regs_at entries _ hMem hUn,
        ArmState.havocCallerSaved_stack,
        applyCallerSaves_stack_ireg entries s hMem hNodup]
      exact hRel v (.ireg r) hLoc
    · -- Callee-saved: untouched by havoc, no entry restores to it
      have hNotIn : ∀ off, CallerSaveEntry.ireg r off ∉ entries := by
        intro off hm; exact absurd (hAllCSIreg r off hm) (by simp [hcs])
      simp only [applyCallerRestores_regs_other entries _ r hNotIn,
        ArmState.havocCallerSaved, hcs, ite_false,
        applyCallerSaves_regs]
      exact hRel v (.ireg r) hLoc
  | .freg r =>
    by_cases hcs : r.isCallerSaved
    · obtain ⟨saveOff, hMem⟩ := hCoversFreg v r hLoc hcs
      have hUn := fun off' hm => hUniqFreg r off' saveOff hm hMem
      simp only [applyCallerRestores_fregs_at entries _ hMem hUn,
        ArmState.havocCallerSaved_stack,
        applyCallerSaves_stack_freg entries s hMem hNodup]
      exact hRel v (.freg r) hLoc
    · have hNotIn : ∀ off, CallerSaveEntry.freg r off ∉ entries := by
        intro off hm; exact absurd (hAllCSFreg r off hm) (by simp [hcs])
      simp only [applyCallerRestores_fregs_other entries _ r hNotIn,
        ArmState.havocCallerSaved, hcs, ite_false,
        applyCallerSaves_fregs]
      exact hRel v (.freg r) hLoc

/-- **Caller-save composition with destination exclusion.**
    Like `callerSave_composition` but for lib-call sites where:
    - entries exclude the destination variable's register
    - the middle operation changes σ to σ' (updating dst)
    - s_mid is the state after saves + base instructions (before restores)

    For non-dst variables with entries: save slots hold pre-save values,
    restores reload them, and σ'(v) = σ(v).
    For dst and callee-saved variables: s_mid already has the right values. -/
theorem ExtStateRel.callerSave_composition_excluding
    {layout : VarLayout} {σ σ' : Store} {s : ArmState}
    (hRel : ExtStateRel layout σ s)
    (entries : List CallerSaveEntry)
    (s_mid : ArmState)
    (hFresh : ∀ e ∈ entries, ∀ v, layout v ≠ some (.stack e.off))
    (hNodup : (entries.map CallerSaveEntry.off).Nodup)
    (hUniqIreg : ∀ r off1 off2, CallerSaveEntry.ireg r off1 ∈ entries →
      CallerSaveEntry.ireg r off2 ∈ entries → off1 = off2)
    (hUniqFreg : ∀ r off1 off2, CallerSaveEntry.freg r off1 ∈ entries →
      CallerSaveEntry.freg r off2 ∈ entries → off1 = off2)
    (hAllCSIreg : ∀ r off, CallerSaveEntry.ireg r off ∈ entries → r.isCallerSaved = true)
    (hAllCSFreg : ∀ r off, CallerSaveEntry.freg r off ∈ entries → r.isCallerSaved = true)
    -- Save slots in s_mid still hold the values written by applyCallerSaves
    (hSaveSlots : ∀ e ∈ entries, s_mid.stack e.off = (applyCallerSaves entries s).stack e.off)
    -- Variables whose registers are NOT in entries already have σ' values in s_mid
    (hNonEntryIreg : ∀ v r, layout v = some (.ireg r) →
      (∀ off, CallerSaveEntry.ireg r off ∉ entries) → s_mid.regs r = (σ' v).encode)
    (hNonEntryFreg : ∀ v r, layout v = some (.freg r) →
      (∀ off, CallerSaveEntry.freg r off ∉ entries) → s_mid.fregs r = (σ' v).encode)
    -- Stack variables have σ' values in s_mid
    (hStackVars : ∀ v off, layout v = some (.stack off) → s_mid.stack off = (σ' v).encode)
    -- Variables WITH entries are unchanged: σ'(v) = σ(v)
    (hEntryIregUnchanged : ∀ v r, layout v = some (.ireg r) →
      (∃ off, CallerSaveEntry.ireg r off ∈ entries) → σ' v = σ v)
    (hEntryFregUnchanged : ∀ v r, layout v = some (.freg r) →
      (∃ off, CallerSaveEntry.freg r off ∈ entries) → σ' v = σ v) :
    ExtStateRel layout σ' (applyCallerRestores entries s_mid) := by
  intro v loc hLoc
  match loc with
  | .stack off =>
    show (applyCallerRestores entries s_mid).stack off = (σ' v).encode
    rw [applyCallerRestores_stack]
    exact hStackVars v off hLoc
  | .ireg r =>
    show (applyCallerRestores entries s_mid).regs r = (σ' v).encode
    by_cases hIn : ∃ off, CallerSaveEntry.ireg r off ∈ entries
    · -- Has entry: restore from save slot → σ(v) = σ'(v)
      obtain ⟨saveOff, hMem⟩ := hIn
      have hUn := fun off' hm => hUniqIreg r off' saveOff hm hMem
      rw [applyCallerRestores_regs_at entries _ hMem hUn]
      have := hSaveSlots (.ireg r saveOff) hMem
      simp only [CallerSaveEntry.off] at this
      rw [this, applyCallerSaves_stack_ireg entries s hMem hNodup,
          hEntryIregUnchanged v r hLoc ⟨saveOff, hMem⟩]
      exact hRel v (.ireg r) hLoc
    · -- No entry: s_mid already has σ'(v)
      have hNotIn : ∀ off, CallerSaveEntry.ireg r off ∉ entries :=
        fun off hm => hIn ⟨off, hm⟩
      rw [applyCallerRestores_regs_other entries _ r hNotIn]
      exact hNonEntryIreg v r hLoc hNotIn
  | .freg r =>
    show (applyCallerRestores entries s_mid).fregs r = (σ' v).encode
    by_cases hIn : ∃ off, CallerSaveEntry.freg r off ∈ entries
    · obtain ⟨saveOff, hMem⟩ := hIn
      have hUn := fun off' hm => hUniqFreg r off' saveOff hm hMem
      rw [applyCallerRestores_fregs_at entries _ hMem hUn]
      have := hSaveSlots (.freg r saveOff) hMem
      simp only [CallerSaveEntry.off] at this
      rw [this, applyCallerSaves_stack_freg entries s hMem hNodup,
          hEntryFregUnchanged v r hLoc ⟨saveOff, hMem⟩]
      exact hRel v (.freg r) hLoc
    · have hNotIn : ∀ off, CallerSaveEntry.freg r off ∉ entries :=
        fun off hm => hIn ⟨off, hm⟩
      rw [applyCallerRestores_fregs_other entries _ r hNotIn]
      exact hNonEntryFreg v r hLoc hNotIn

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
  | .cmp op a b =>
    let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
    let loadA := match a with
      | .var v => vLoadVar layout v .x1
      | .lit n => formalLoadImm64 .x1 n
      | _ => []
    let loadB := match b with
      | .var v => vLoadVar layout v .x2
      | .lit n => formalLoadImm64 .x2 n
      | _ => []
    loadA ++ loadB ++ [.cmp .x1 .x2, .cset .x0 cond]
  | .not e =>
    verifiedGenBoolExpr layout e ++ [.eorImm .x0 .x0 (1 : BitVec 64)]
  | .fcmp fop a b =>
    let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
    let loadA := match a with
      | .var v => vLoadVarFP layout v .d1
      | .flit n => formalLoadImm64 .x0 n ++ [.fmovToFP .d1 .x0]
      | _ => []
    let loadB := match b with
      | .var v => vLoadVarFP layout v .d2
      | .flit n => formalLoadImm64 .x0 n ++ [.fmovToFP .d2 .x0]
      | _ => []
    loadA ++ loadB ++ [.fcmpR .d1 .d2, .cset .x0 cond]
  | .bexpr e =>
    match e with
    | .var v => vLoadVar layout v .x0 ++ [.andImm .x0 .x0 (1 : BitVec 64)]
    | _ => []

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
    if !be.hasSimpleOps then none else
    let notFreg := match layout dst with | some (.freg _) => true | _ => false
    if notFreg then none else
    some (verifiedGenBoolExpr layout be ++ vStoreVar layout dst .x0)
  | .goto l => some [.b (pcMap l)]
  | .ifgoto be l =>
    if !be.hasSimpleOps then none else
    -- Fuse compare + branch for negated comparisons (common while-loop pattern)
    match be with
    | .not (.cmp op a b) =>
      let cond := match op with | .eq => Cond.eq | .ne => .ne | .lt => .lt | .le => .le
      let a_reg := match a with
        | .var v => (match layout v with | some (.ireg r) => r | _ => .x1)
        | _ => .x1
      let b_reg := match b with
        | .var v => (match layout v with | some (.ireg r) => r | _ => .x2)
        | _ => .x2
      let loadA := match a with
        | .var v => vLoadVar layout v a_reg
        | .lit n => formalLoadImm64 a_reg n
        | _ => []
      let loadB := match b with
        | .var v => vLoadVar layout v b_reg
        | .lit n => formalLoadImm64 b_reg n
        | _ => []
      some (loadA ++ loadB ++ [.cmp a_reg b_reg, .bCond cond.negate (pcMap l)])
    | .not (.fcmp fop a b) =>
      let cond := match fop with | .feq => Cond.eq | .fne => .ne | .flt => .lt | .fle => .le
      let a_freg := match a with
        | .var v => (match layout v with | some (.freg r) => r | _ => .d1)
        | _ => .d1
      let b_freg := match b with
        | .var v => (match layout v with | some (.freg r) => r | _ => .d2)
        | _ => .d2
      let loadA := match a with
        | .var v => vLoadVarFP layout v a_freg
        | .flit n => formalLoadImm64 .x0 n ++ [.fmovToFP a_freg .x0]
        | _ => []
      let loadB := match b with
        | .var v => vLoadVarFP layout v b_freg
        | .flit n => formalLoadImm64 .x0 n ++ [.fmovToFP b_freg .x0]
        | _ => []
      -- Always load var before flit so proof-side PC plumbing is uniform
      let loads := match a, b with
        | .flit _, .var _ => loadB ++ loadA
        | _, _ => loadA ++ loadB
      some (loads ++ [.fcmpR a_freg b_freg, .bCond cond.negate (pcMap l)])
    | _ => some (verifiedGenBoolExpr layout be ++ [.cbnz .x0 (pcMap l)])
  | .halt => some [.b haltLabel]
  | .arrLoad x arr idx ty =>
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => .x1
    let loadIdx := vLoadVar layout idx idx_reg
    let boundsCheck := if boundsSafe then [] else
      [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]
    match ty with
    | .float =>
      let dst_reg := match layout x with | some (.freg r) => r | _ => .d0
      some (loadIdx ++ boundsCheck ++ [.farrLd dst_reg arr idx_reg] ++ vStoreVarFP layout x dst_reg)
    | .bool  =>
      let dst_reg := match layout x with | some (.ireg r) => r | _ => .x0
      some (loadIdx ++ boundsCheck ++ [.arrLd dst_reg arr idx_reg, .cmpImm dst_reg 0, .cset dst_reg .ne] ++ vStoreVar layout x dst_reg)
    | .int   =>
      let dst_reg := match layout x with | some (.ireg r) => r | _ => .x0
      some (loadIdx ++ boundsCheck ++ [.arrLd dst_reg arr idx_reg] ++ vStoreVar layout x dst_reg)
  | .arrStore arr idx val ty =>
    let idx_reg := match layout idx with | some (.ireg r) => r | _ => .x1
    let loadIdx := vLoadVar layout idx idx_reg
    let boundsCheck := if boundsSafe then [] else
      [.cmpImm idx_reg (arraySizeBv arrayDecls arr), .bCond .hs boundsLabel]
    if ty == .float then
      let val_reg := match layout val with | some (.freg r) => r | _ => .d0
      some (loadIdx ++ boundsCheck ++ vLoadVarFP layout val val_reg ++ [.farrSt arr idx_reg val_reg])
    else
      let val_reg := match layout val with | some (.ireg r) => r | _ => .x2
      some (loadIdx ++ boundsCheck ++ vLoadVar layout val val_reg ++ [.arrSt arr idx_reg val_reg])
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
  | .fternop dst op a b c =>
    match layout a, layout b, layout c, layout dst with
    | some (.ireg _), _, _, _ => none
    | _, some (.ireg _), _, _ => none
    | _, _, some (.ireg _), _ => none
    | _, _, _, some (.ireg _) => none
    | _, _, _, _ =>
      let a_reg := match layout a with | some (.freg r) => r | _ => .d0
      let b_reg := match layout b with | some (.freg r) => r | _ => .d1
      let c_reg := match layout c with | some (.freg r) => r | _ => .d2
      let dst_reg := match layout dst with | some (.freg r) => r | _ => .d0
      let fpInstr := match op with
        | .fmadd => ArmInstr.fmaddR dst_reg b_reg c_reg a_reg
        | .fmsub => ArmInstr.fmsubR dst_reg b_reg c_reg a_reg
      some (vLoadVarFP layout a a_reg ++ vLoadVarFP layout b b_reg ++
        vLoadVarFP layout c c_reg ++ [fpInstr] ++ vStoreVarFP layout dst dst_reg)
  | .print _ _ => none      -- handled by unverified codegen path

-- ────────────────────────────────────────────────────────────
-- § 8e. verifiedGenInstr output length is pcMap-independent
-- ────────────────────────────────────────────────────────────

/-- The length of verifiedGenInstr output does not depend on the pcMap.
    pcMap only affects branch target immediates, not instruction count. -/
theorem verifiedGenInstr_length_pcMap_ind
    (layout : VarLayout) (instr : TAC)
    (haltS divS boundsS : Nat) (arrayDecls : List (ArrayName × Nat × VarTy))
    (safe : Bool) (pcMap1 pcMap2 : Nat → Nat)
    (l1 l2 : List ArmInstr)
    (h1 : verifiedGenInstr layout pcMap1 instr haltS divS boundsS arrayDecls safe = some l1)
    (h2 : verifiedGenInstr layout pcMap2 instr haltS divS boundsS arrayDecls safe = some l2) :
    l1.length = l2.length := by
  cases instr with
  | const v val =>
    simp only [verifiedGenInstr] at h1 h2
    cases val <;> simp_all <;> split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | copy dst src =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | binop x op y z =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | boolop x be =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | goto l =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all; subst h1; subst h2; rfl
  | ifgoto be l =>
    simp only [verifiedGenInstr] at h1 h2
    -- Split the `if !be.hasSimpleOps` guard
    split at h1 <;> simp_all
    -- Now h1, h2 have the `match be` result. Split h1 into 3 arms.
    split at h1 <;> simp_all
    -- In each arm, h1 is subst'd. h2 still has the conjunction; obtain the eq part.
    all_goals (try obtain ⟨_, h2⟩ := h2)
    all_goals (subst_vars; simp [List.length_append, List.length_cons])
  | halt =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> subst_vars <;> simp_all
  | arrLoad x arr idx ty =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | arrStore arr idx val ty =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | fbinop x fop y z =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | intToFloat x y =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | floatToInt x y =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | floatUnary x op y =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | fternop x op a b c =>
    simp only [verifiedGenInstr] at h1 h2
    split at h1 <;> simp_all <;> split at h2 <;> simp_all
  | print fmt vs =>
    simp [verifiedGenInstr] at h1

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

@[simp] theorem ArmState.setStack_stack_same (s : ArmState) (off : Nat) (v : BitVec 64) :
    (s.setStack off v).stack off = v := by
  simp [setStack]

@[simp] theorem ArmState.setStack_stack_other (s : ArmState) (off off' : Nat) (v : BitVec 64) (h : off' ≠ off) :
    (s.setStack off v).stack off' = s.stack off' := by
  simp [setStack, beq_iff_eq, h]

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

-- ============================================================
-- § 10. Instruction-level save/restore bridge
-- ============================================================

/-- `applyCallerSaves` is independent of the `pc` field. -/
theorem applyCallerSaves_pc_irrelevant (entries : List CallerSaveEntry) (s : ArmState) (p : Nat) :
    applyCallerSaves entries {s with pc := p} = {applyCallerSaves entries s with pc := p} := by
  induction entries generalizing s p with
  | nil => simp [applyCallerSaves]
  | cons e rest ih =>
    cases e with
    | ireg r off =>
      simp only [applyCallerSaves]
      -- setStack on {s with pc := p} = {setStack on s with pc := p}
      have : (({s with pc := p}).setStack off (({s with pc := p}).regs r)) =
        {s.setStack off (s.regs r) with pc := p} := by
        simp [ArmState.setStack]
      rw [this]; exact ih _ _
    | freg r off =>
      simp only [applyCallerSaves]
      have : (({s with pc := p}).setStack off (({s with pc := p}).fregs r)) =
        {s.setStack off (s.fregs r) with pc := p} := by
        simp [ArmState.setStack]
      rw [this]; exact ih _ _

/-- `applyCallerRestores` is independent of the `pc` field. -/
theorem applyCallerRestores_pc_irrelevant (entries : List CallerSaveEntry) (s : ArmState) (p : Nat) :
    applyCallerRestores entries {s with pc := p} = {applyCallerRestores entries s with pc := p} := by
  induction entries generalizing s p with
  | nil => simp [applyCallerRestores]
  | cons e rest ih =>
    cases e with
    | ireg r off =>
      simp only [applyCallerRestores]
      have : (({s with pc := p}).setReg r (({s with pc := p}).stack off)) =
        {s.setReg r (s.stack off) with pc := p} := by
        simp [ArmState.setReg]
      rw [this]; exact ih _ _
    | freg r off =>
      simp only [applyCallerRestores]
      have : (({s with pc := p}).setFReg r (({s with pc := p}).stack off)) =
        {s.setFReg r (s.stack off) with pc := p} := by
        simp [ArmState.setFReg]
      rw [this]; exact ih _ _

/-- Convert CallerSaveEntry list to save instructions (str/fstr). -/
def entriesToSaves : List CallerSaveEntry → List ArmInstr
  | [] => []
  | .ireg r off :: rest => .str r off :: entriesToSaves rest
  | .freg r off :: rest => .fstr r off :: entriesToSaves rest

/-- Convert CallerSaveEntry list to restore instructions (ldr/fldr). -/
def entriesToRestores : List CallerSaveEntry → List ArmInstr
  | [] => []
  | .ireg r off :: rest => .ldr r off :: entriesToRestores rest
  | .freg r off :: rest => .fldr r off :: entriesToRestores rest

@[simp] theorem entriesToSaves_length (entries : List CallerSaveEntry) :
    (entriesToSaves entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons e _ ih => cases e <;> simp [entriesToSaves, ih]

@[simp] theorem entriesToRestores_length (entries : List CallerSaveEntry) :
    (entriesToRestores entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons e _ ih => cases e <;> simp [entriesToRestores, ih]

/-- Executing save instructions produces the same state as applyCallerSaves
    (plus PC advancement). -/
theorem armSteps_saves (prog : ArmProg) (entries : List CallerSaveEntry) (s : ArmState)
    (hCode : CodeAt prog s.pc (entriesToSaves entries)) :
    ArmSteps prog s {applyCallerSaves entries s with pc := s.pc + entries.length} := by
  induction entries generalizing s with
  | nil => simp [applyCallerSaves]; exact .refl
  | cons e rest ih =>
    cases e with
    | ireg r off =>
      simp only [applyCallerSaves]
      have step1 := ArmStep.str r off hCode.head
      have hIH := ih (s.setStack off (s.regs r) |>.nextPC) hCode.tail
      have hNP : (s.setStack off (s.regs r)).nextPC =
        {s.setStack off (s.regs r) with pc := s.pc + 1} := by
        simp [ArmState.nextPC, ArmState.setStack]
      rw [hNP] at hIH; rw [applyCallerSaves_pc_irrelevant] at hIH; dsimp only at hIH
      refine (ArmSteps.single step1).trans ?_
      rw [hNP]; dsimp only
      simp only [List.length_cons]
      rw [show s.pc + (rest.length + 1) = s.pc + 1 + rest.length by omega]
      exact hIH
    | freg r off =>
      simp only [applyCallerSaves]
      have step1 := ArmStep.fstr r off hCode.head
      have hIH := ih (s.setStack off (s.fregs r) |>.nextPC) hCode.tail
      have hNP : (s.setStack off (s.fregs r)).nextPC =
        {s.setStack off (s.fregs r) with pc := s.pc + 1} := by
        simp [ArmState.nextPC, ArmState.setStack]
      rw [hNP] at hIH; rw [applyCallerSaves_pc_irrelevant] at hIH; dsimp only at hIH
      refine (ArmSteps.single step1).trans ?_
      rw [hNP]; dsimp only
      simp only [List.length_cons]
      rw [show s.pc + (rest.length + 1) = s.pc + 1 + rest.length by omega]
      exact hIH

/-- Executing restore instructions produces the same state as applyCallerRestores
    (plus PC advancement). -/
theorem armSteps_restores (prog : ArmProg) (entries : List CallerSaveEntry) (s : ArmState)
    (hCode : CodeAt prog s.pc (entriesToRestores entries)) :
    ArmSteps prog s {applyCallerRestores entries s with pc := s.pc + entries.length} := by
  induction entries generalizing s with
  | nil => simp [applyCallerRestores]; exact .refl
  | cons e rest ih =>
    cases e with
    | ireg r off =>
      simp only [applyCallerRestores]
      have step1 := ArmStep.ldr r off hCode.head
      have hIH := ih (s.setReg r (s.stack off) |>.nextPC) hCode.tail
      have hNP : (s.setReg r (s.stack off)).nextPC =
        {s.setReg r (s.stack off) with pc := s.pc + 1} := by
        simp [ArmState.nextPC, ArmState.setReg]
      rw [hNP] at hIH; rw [applyCallerRestores_pc_irrelevant] at hIH; dsimp only at hIH
      refine (ArmSteps.single step1).trans ?_
      rw [hNP]; dsimp only
      simp only [List.length_cons]
      rw [show s.pc + (rest.length + 1) = s.pc + 1 + rest.length by omega]
      exact hIH
    | freg r off =>
      simp only [applyCallerRestores]
      have step1 := ArmStep.fldr r off hCode.head
      have hIH := ih (s.setFReg r (s.stack off) |>.nextPC) hCode.tail
      have hNP : (s.setFReg r (s.stack off)).nextPC =
        {s.setFReg r (s.stack off) with pc := s.pc + 1} := by
        simp [ArmState.nextPC, ArmState.setFReg]
      rw [hNP] at hIH; rw [applyCallerRestores_pc_irrelevant] at hIH; dsimp only at hIH
      refine (ArmSteps.single step1).trans ?_
      rw [hNP]; dsimp only
      simp only [List.length_cons]
      rw [show s.pc + (rest.length + 1) = s.pc + 1 + rest.length by omega]
      exact hIH
