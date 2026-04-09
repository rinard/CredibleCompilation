import CredibleCompilation.TAC

/-!
# Type System for Three-Address Code

Well-typedness definitions, decidable type checking, type preservation,
and type safety.

Split from `Semantics.lean`.
-/

-- ============================================================
-- § 3a. Type system definitions
-- ============================================================

/-- Well-typedness for boolean expressions. -/
inductive WellTypedBoolExpr (Γ : TyCtx) : BoolExpr → Prop where
  | lit    : WellTypedBoolExpr Γ (.lit b)
  | bvar   : Γ x = .bool → WellTypedBoolExpr Γ (.bvar x)
  | cmp    : Γ x = .int → Γ y = .int → WellTypedBoolExpr Γ (.cmp op x y)
  | cmpLit : Γ x = .int → 0 ≤ n.toInt → n.toInt < 2 ^ 63 → WellTypedBoolExpr Γ (.cmpLit op x n)
  | not    : WellTypedBoolExpr Γ b → WellTypedBoolExpr Γ (.not b)
  | fcmp   : Γ x = .float → Γ y = .float → WellTypedBoolExpr Γ (.fcmp op x y)

/-- Well-typedness for a single TAC instruction. -/
inductive WellTypedInstr (Γ : TyCtx) : TAC → Prop where
  | const  : v.typeOf = Γ x → WellTypedInstr Γ (.const x v)
  | copy   : Γ x = Γ y → WellTypedInstr Γ (.copy x y)
  | binop  : Γ x = .int → Γ y = .int → Γ z = .int →
      WellTypedInstr Γ (.binop x op y z)
  | boolop : Γ x = .bool → WellTypedBoolExpr Γ be →
      WellTypedInstr Γ (.boolop x be)
  | goto   : WellTypedInstr Γ (.goto l)
  | ifgoto : WellTypedBoolExpr Γ b → WellTypedInstr Γ (.ifgoto b l)
  | halt   : WellTypedInstr Γ .halt
  | arrLoad  : Γ x = ty → Γ idx = .int → WellTypedInstr Γ (.arrLoad x arr idx ty)
  | arrStore : Γ idx = .int → Γ val = ty → WellTypedInstr Γ (.arrStore arr idx val ty)
  | fbinop : Γ x = .float → Γ y = .float → Γ z = .float →
      WellTypedInstr Γ (.fbinop x fop y z)
  | intToFloat : Γ x = .float → Γ y = .int → WellTypedInstr Γ (.intToFloat x y)
  | floatToInt : Γ x = .int → Γ y = .float → WellTypedInstr Γ (.floatToInt x y)

/-- A program is well-typed if every instruction is well-typed. -/
def WellTypedProg (Γ : TyCtx) (p : Prog) : Prop :=
  ∀ i, (h : i < p.size) → WellTypedInstr Γ p[i]

-- ============================================================
-- § 9. Progress and successor lemmas
-- ============================================================

/-- Helper: extract instruction identity from array lookup. -/
private theorem instr_eq_of_lookup {p : Prog} {pc : Nat} {instr : TAC}
    (hpc : pc < p.size) (h : p[pc]? = some instr) : p[pc] = instr :=
  Option.some.inj ((Prog.getElem?_eq_getElem hpc).symm.trans h)

/-- **Progress**: if the instruction at `pc` exists, the program is
    well-typed, and the store is well-typed, then a step is always possible.
    Unsafe division produces a `Cfg.error` transition rather than getting stuck. -/
theorem Step.progress (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem) (Γ : TyCtx)
    (hinb : pc < p.size)
    (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ) :
    ∃ c', Step p (Cfg.run pc σ am) c' := by
  have hinstr : p[pc]? = some p[pc] := Prog.getElem?_eq_getElem hinb
  have hwti := hwtp pc hinb
  match hp : p[pc] with
  | .const x v     => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y      => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z =>
    rw [hp] at hwti; cases hwti with
    | binop _ hy hz =>
      obtain ⟨a, ha⟩ : ∃ n, σ y = .int n := Value.int_of_typeOf_int (by rw [hts y]; exact hy)
      obtain ⟨b, hb⟩ : ∃ n, σ z = .int n := Value.int_of_typeOf_int (by rw [hts z]; exact hz)
      by_cases hs : op.safe a b
      · exact ⟨_, .binop (hp ▸ hinstr) ha hb hs⟩
      · exact ⟨_, .error (hp ▸ hinstr) ha hb hs⟩
  | .boolop x be   => exact ⟨_, .boolop (hp ▸ hinstr)⟩
  | .goto l        => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l    =>
    by_cases hb : b.eval σ = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt          => exact ⟨_, .halt (hp ▸ hinstr)⟩
  | .arrLoad x arr idx ty =>
    rw [hp] at hwti; cases hwti with
    | arrLoad _ hidx =>
      obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
      by_cases hb : iv < p.arraySizeBv arr
      · exact ⟨_, .arrLoad (hp ▸ hinstr) hiv hb⟩
      · exact ⟨_, .arrLoad_boundsError (hp ▸ hinstr) hiv hb⟩
  | .arrStore arr idx val ty =>
    rw [hp] at hwti; cases hwti with
    | arrStore hidx hval =>
      obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int (by rw [hts idx]; exact hidx)
      have hty : (σ val).typeOf = ty := by rw [hts val]; exact hval
      by_cases hb : iv < p.arraySizeBv arr
      · exact ⟨_, .arrStore (hp ▸ hinstr) hiv hty hb⟩
      · exact ⟨_, .arrStore_boundsError (hp ▸ hinstr) hiv hty hb⟩
  | .fbinop x fop y z =>
    rw [hp] at hwti; cases hwti with
    | fbinop _ hy hz =>
      obtain ⟨a, ha⟩ := Value.float_of_typeOf_float (by rw [hts y]; exact hy)
      obtain ⟨b, hb⟩ := Value.float_of_typeOf_float (by rw [hts z]; exact hz)
      exact ⟨_, .fbinop (hp ▸ hinstr) ha hb⟩
  | .intToFloat x y =>
    rw [hp] at hwti; cases hwti with
    | intToFloat _ hy =>
      obtain ⟨n, hn⟩ := Value.int_of_typeOf_int (by rw [hts y]; exact hy)
      exact ⟨_, .intToFloat (hp ▸ hinstr) hn⟩
  | .floatToInt x y =>
    rw [hp] at hwti; cases hwti with
    | floatToInt _ hy =>
      obtain ⟨f, hf⟩ := Value.float_of_typeOf_float (by rw [hts y]; exact hy)
      exact ⟨_, .floatToInt (hp ▸ hinstr) hf⟩

/-- **Type safety (single step)**: a well-typed program with a well-typed store
    never steps to a type-error configuration. -/
theorem Step.no_typeError_of_wellTyped {p : Prog} {pc : Nat} {σ τ : Store} {am am' : ArrayMem} {Γ : TyCtx}
    (hpc : pc < p.size) (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ) :
    ¬ (p ⊩ Cfg.run pc σ am ⟶ Cfg.typeError τ am') := by
  intro hstep
  cases hstep with
  | binop_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | binop _ hy hz =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hy)
      | inr hr => exact hr (by rw [hts]; exact hz)
  | arrLoad_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | arrLoad _ hidx => exact hne (by rw [hts]; exact hidx)
  | arrStore_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | arrStore hidx hval =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hidx)
      | inr hr => exact hr (by rw [hts]; exact hval)
  | fbinop_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | fbinop _ hy hz =>
      cases hne with
      | inl hl => exact hl (by rw [hts]; exact hy)
      | inr hr => exact hr (by rw [hts]; exact hz)
  | intToFloat_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | intToFloat _ hy => exact hne (by rw [hts]; exact hy)
  | floatToInt_typeError hinstr hne =>
    have hwti := hwtp pc hpc
    have := instr_eq_of_lookup hpc hinstr
    rw [this] at hwti
    cases hwti with
    | floatToInt _ hy => exact hne (by rw [hts]; exact hy)

/-- **Progress (untyped)**: an in-bounds PC always admits a step,
    regardless of type safety. For ill-typed binop operands, the step
    is `binop_typeError`. -/
theorem Step.progress_untyped (p : Prog) (pc : Nat) (σ : Store) (am : ArrayMem)
    (hinb : pc < p.size) :
    ∃ c', Step p (Cfg.run pc σ am) c' := by
  have hinstr : p[pc]? = some p[pc] := Prog.getElem?_eq_getElem hinb
  match hp : p[pc] with
  | .const x v     => exact ⟨_, .const (hp ▸ hinstr)⟩
  | .copy x y      => exact ⟨_, .copy (hp ▸ hinstr)⟩
  | .binop x op y z =>
    by_cases hy : (σ y).typeOf = .int
    · by_cases hz : (σ z).typeOf = .int
      · obtain ⟨a, ha⟩ := Value.int_of_typeOf_int hy
        obtain ⟨b, hb⟩ := Value.int_of_typeOf_int hz
        by_cases hs : op.safe a b
        · exact ⟨_, .binop (hp ▸ hinstr) ha hb hs⟩
        · exact ⟨_, .error (hp ▸ hinstr) ha hb hs⟩
      · exact ⟨_, .binop_typeError (hp ▸ hinstr) (.inr hz)⟩
    · exact ⟨_, .binop_typeError (hp ▸ hinstr) (.inl hy)⟩
  | .boolop x be   => exact ⟨_, .boolop (hp ▸ hinstr)⟩
  | .goto l        => exact ⟨_, .goto (hp ▸ hinstr)⟩
  | .ifgoto b l    =>
    by_cases hb : b.eval σ = true
    · exact ⟨_, .iftrue (hp ▸ hinstr) hb⟩
    · exact ⟨_, .iffall (hp ▸ hinstr) (Bool.eq_false_iff.mpr hb)⟩
  | .halt          => exact ⟨_, .halt (hp ▸ hinstr)⟩
  | .arrLoad x arr idx ty =>
    by_cases hidx : (σ idx).typeOf = .int
    · obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int hidx
      by_cases hb : iv < p.arraySizeBv arr
      · exact ⟨_, .arrLoad (hp ▸ hinstr) hiv hb⟩
      · exact ⟨_, .arrLoad_boundsError (hp ▸ hinstr) hiv hb⟩
    · exact ⟨_, .arrLoad_typeError (hp ▸ hinstr) hidx⟩
  | .arrStore arr idx val ty =>
    by_cases hidx : (σ idx).typeOf = .int
    · by_cases hval : (σ val).typeOf = ty
      · obtain ⟨iv, hiv⟩ := Value.int_of_typeOf_int hidx
        by_cases hb : iv < p.arraySizeBv arr
        · exact ⟨_, .arrStore (hp ▸ hinstr) hiv hval hb⟩
        · exact ⟨_, .arrStore_boundsError (hp ▸ hinstr) hiv hval hb⟩
      · exact ⟨_, .arrStore_typeError (hp ▸ hinstr) (.inr hval)⟩
    · exact ⟨_, .arrStore_typeError (hp ▸ hinstr) (.inl hidx)⟩
  | .fbinop x fop y z =>
    by_cases hy : (σ y).typeOf = .float
    · by_cases hz : (σ z).typeOf = .float
      · obtain ⟨a, ha⟩ := Value.float_of_typeOf_float hy
        obtain ⟨b, hb⟩ := Value.float_of_typeOf_float hz
        exact ⟨_, .fbinop (hp ▸ hinstr) ha hb⟩
      · exact ⟨_, .fbinop_typeError (hp ▸ hinstr) (.inr hz)⟩
    · exact ⟨_, .fbinop_typeError (hp ▸ hinstr) (.inl hy)⟩
  | .intToFloat x y =>
    by_cases hy : (σ y).typeOf = .int
    · obtain ⟨n, hn⟩ := Value.int_of_typeOf_int hy
      exact ⟨_, .intToFloat (hp ▸ hinstr) hn⟩
    · exact ⟨_, .intToFloat_typeError (hp ▸ hinstr) hy⟩
  | .floatToInt x y =>
    by_cases hy : (σ y).typeOf = .float
    · obtain ⟨f, hf⟩ := Value.float_of_typeOf_float hy
      exact ⟨_, .floatToInt (hp ▸ hinstr) hf⟩
    · exact ⟨_, .floatToInt_typeError (hp ▸ hinstr) hy⟩

-- ============================================================
-- § 11. Decidable type checking
-- ============================================================

def checkWellTypedBoolExpr (Γ : TyCtx) : BoolExpr → Bool
  | .lit _        => true
  | .bvar x       => decide (Γ x = .bool)
  | .cmp _ x y    => decide (Γ x = .int) && decide (Γ y = .int)
  | .cmpLit _ x n => decide (Γ x = .int) && decide (0 ≤ n.toInt) && decide (n.toInt < 2 ^ 63)
  | .not e        => checkWellTypedBoolExpr Γ e
  | .fcmp _ x y   => decide (Γ x = .float) && decide (Γ y = .float)

def checkWellTypedInstr (Γ : TyCtx) : TAC → Bool
  | .const x v     => decide (v.typeOf = Γ x)
  | .copy x y      => decide (Γ x = Γ y)
  | .binop x _ y z => decide (Γ x = .int) && decide (Γ y = .int) && decide (Γ z = .int)
  | .boolop x be   => decide (Γ x = .bool) && checkWellTypedBoolExpr Γ be
  | .goto _        => true
  | .ifgoto b _    => checkWellTypedBoolExpr Γ b
  | .halt          => true
  | .arrLoad x _ idx ty  => decide (Γ x = ty) && decide (Γ idx = .int)
  | .arrStore _ idx val ty => decide (Γ idx = .int) && decide (Γ val = ty)
  | .fbinop x _ y z => decide (Γ x = .float) && decide (Γ y = .float) && decide (Γ z = .float)
  | .intToFloat x y => decide (Γ x = .float) && decide (Γ y = .int)
  | .floatToInt x y => decide (Γ x = .int) && decide (Γ y = .float)

theorem checkWellTypedBoolExpr_sound {Γ : TyCtx} {b : BoolExpr}
    (h : checkWellTypedBoolExpr Γ b = true) : WellTypedBoolExpr Γ b := by
  induction b with
  | lit _ => exact .lit
  | bvar x =>
    simp [checkWellTypedBoolExpr, decide_eq_true_eq] at h
    exact .bvar h
  | cmp op x y =>
    simp [checkWellTypedBoolExpr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cmp h.1 h.2
  | cmpLit op x n =>
    simp only [checkWellTypedBoolExpr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cmpLit h.1.1 h.1.2 h.2
  | not e ih =>
    simp [checkWellTypedBoolExpr] at h; exact .not (ih h)
  | fcmp op x y =>
    simp [checkWellTypedBoolExpr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .fcmp h.1 h.2

theorem checkWellTypedInstr_sound {Γ : TyCtx} {instr : TAC}
    (h : checkWellTypedInstr Γ instr = true) : WellTypedInstr Γ instr := by
  cases instr with
  | const x v =>
    simp only [checkWellTypedInstr, decide_eq_true_eq] at h
    exact .const h
  | copy x y =>
    simp [checkWellTypedInstr, decide_eq_true_eq] at h; exact .copy h
  | binop x op y z =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .binop h.1.1 h.1.2 h.2
  | boolop x be =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .boolop h.1 (checkWellTypedBoolExpr_sound h.2)
  | goto l => exact .goto
  | ifgoto b l =>
    simp [checkWellTypedInstr] at h
    exact .ifgoto (checkWellTypedBoolExpr_sound h)
  | halt => exact .halt
  | arrLoad x arr idx ty =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .arrLoad h.1 h.2
  | arrStore arr idx val ty =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .arrStore h.1 h.2
  | fbinop x fop y z =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .fbinop h.1.1 h.1.2 h.2
  | intToFloat x y =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .intToFloat h.1 h.2
  | floatToInt x y =>
    simp [checkWellTypedInstr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .floatToInt h.1 h.2

/-- Check that every instruction in a program is well-typed. -/
def checkWellTypedProg (Γ : TyCtx) (p : Prog) : Bool :=
  (List.range p.size).all fun i =>
    match p[i]? with
    | some instr => checkWellTypedInstr Γ instr
    | none => true

theorem checkWellTypedProg_sound {Γ : TyCtx} {p : Prog}
    (h : checkWellTypedProg Γ p = true) : WellTypedProg Γ p := by
  intro i hi
  have hmem : i ∈ List.range p.size := List.mem_range.mpr hi
  have hcheck := (List.all_eq_true.mp h) i hmem
  have hsome : p[i]? = some p[i] := Prog.getElem?_eq_getElem hi
  rw [hsome] at hcheck
  exact checkWellTypedInstr_sound hcheck

-- ============================================================
-- § 11a. Type preservation
-- ============================================================

/-- **Type preservation**: a well-typed program with a well-typed store
    preserves the typed-store invariant after any step to a run config. -/
theorem type_preservation {Γ : TyCtx} {p : Prog} {pc pc' : Nat} {σ σ' : Store} {am am' : ArrayMem}
    (hwtp : WellTypedProg Γ p) (hts : TypedStore Γ σ)
    (hpc : pc < p.size)
    (hstep : p ⊩ Cfg.run pc σ am ⟶ Cfg.run pc' σ' am') :
    TypedStore Γ σ' := by
  have hwti := hwtp pc hpc
  cases hstep with
  | const h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .const hv => exact TypedStore.update_typed hts hv
  | copy h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .copy hxy => exact TypedStore.update_typed hts (by rw [hts]; exact hxy.symm)
  | binop h _ _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .binop hx _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | boolop h =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .boolop hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | goto _ => exact hts
  | iftrue _ _ => exact hts
  | iffall _ _ => exact hts
  | arrLoad h _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .arrLoad hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf_ofBitVec]; exact hx.symm)
  | arrStore _ _ _ _ => exact hts
  | fbinop h _ _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .fbinop hx _ _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | intToFloat h _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .intToFloat hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)
  | floatToInt h _ =>
    have := instr_eq_of_lookup hpc h
    rw [this] at hwti
    match hwti with
    | .floatToInt hx _ => exact TypedStore.update_typed hts (by simp [Value.typeOf]; exact hx.symm)


/-- **Type safety (multi-step)**: a well-typed, step-closed program never
    reaches a type-error configuration from a well-typed initial store. -/
theorem type_safety {p : Prog} {σ₀ σ' : Store} {am₀ am' : ArrayMem} {Γ : TyCtx}
    (hwtp : WellTypedProg Γ p) (hts₀ : TypedStore Γ σ₀)
    (hclosed : StepClosedInBounds p) :
    ¬ (p ⊩ Cfg.run 0 σ₀ am₀ ⟶* Cfg.typeError σ' am') := by
  intro hsteps
  suffices ∀ c c', Steps p c c' →
      ∀ pc σ am, c = Cfg.run pc σ am → c' = Cfg.typeError σ' am' →
      pc < p.size → TypedStore Γ σ → False from
    this _ _ hsteps 0 σ₀ am₀ rfl rfl hclosed.1 hts₀
  intro c c' hss
  induction hss with
  | refl => intro _ _ _ hc hc' _ _; rw [hc] at hc'; exact Cfg.noConfusion hc'
  | step hstep rest ih =>
    intro pc σ am hc hc' hpc hts; subst hc
    cases hstep with
    | halt h => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_halt s
    | error h _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_error s
    | binop_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.binop_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | const h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.const (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.const (am := am) h))
    | copy h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.copy (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.copy (am := am) h))
    | binop h hy hz hs =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.binop (am := am) h hy hz hs))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.binop (am := am) h hy hz hs))
    | boolop h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.boolop (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.boolop (am := am) h))
    | goto h =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.goto (am := am) h))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.goto (am := am) h))
    | iftrue h hne =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.iftrue (am := am) h hne))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.iftrue (am := am) h hne))
    | iffall h heq =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.iffall (am := am) h heq))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.iffall (am := am) h heq))
    | arrLoad h hidx hb =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.arrLoad (am := am) h hidx hb))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.arrLoad (am := am) h hidx hb))
    | arrStore h hidx hty hb =>
      exact ih _ _ _ rfl hc'
        (hclosed.2 pc _ σ _ am _ hpc (Step.arrStore (am := am) h hidx hty hb))
        (type_preservation (am := am) hwtp hts hpc (Step.arrStore (am := am) h hidx hty hb))
    | arrLoad_boundsError _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_error s
    | arrStore_boundsError _ _ _ _ => cases rest with
      | refl => exact Cfg.noConfusion hc'
      | step s _ => exact Step.no_step_from_error s
    | arrLoad_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.arrLoad_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | arrStore_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.arrStore_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | fbinop h hy hz =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.fbinop (am := am) h hy hz))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.fbinop (am := am) h hy hz))
    | fbinop_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.fbinop_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | intToFloat h hy =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.intToFloat (am := am) h hy))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.intToFloat (am := am) h hy))
    | intToFloat_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.intToFloat_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
    | floatToInt h hy =>
      exact ih _ _ am rfl hc'
        (hclosed.2 pc _ σ _ am am hpc (Step.floatToInt (am := am) h hy))
        (type_preservation (am := am) (am' := am) hwtp hts hpc (Step.floatToInt (am := am) h hy))
    | floatToInt_typeError hinstr hne =>
      cases rest with
      | refl => exact Step.no_typeError_of_wellTyped (am := am) (am' := am) hpc hwtp hts
                  (.floatToInt_typeError (am := am) hinstr hne)
      | step s _ => exact Step.no_step_from_typeError s
