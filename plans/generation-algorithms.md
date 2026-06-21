# Random Generation Algorithms (study techniques T1–T4c)

Companion to `study-protocol.md` §4. Documents the *exact* generation algorithm for the built
technique (T1) and the precise, implementable algorithm for each to-build technique. All
generators are seeded and deterministic (a seed reproduces a finding — protocol §9).

## Common PRNG

A 64-bit LCG (the constants are the Knuth/MMIX multiplier + increment):
`next(s) = s · 6364136223846793005 + 1442695040888963407  (mod 2⁶⁴)`.
Each draw advances the state; the seed is `lcg(taskSeed)`. Determinism comes from the LCG, not
from `Math.random` (which is unavailable in Lean's `#eval`/`--run`).

---

## T1 — assembly co-simulation  (BUILT: `Harness/{T1,T1Branch,T1Stack,T1Array}.lean`)

**Pipeline:** generate a random assembler-safe instruction sequence → run it through the
proven-sound `execStep` (model) **and** through the compiler's printed asm assembled + run on the
local arm64 machine → diff all registers. Divergence ⇒ a bug in `ArmStep` or the printer.

### Operand value pool (edge-biased)
`genVal(s) = s` if `s mod 3 == 0` else `edgePool[s mod |edgePool|]`, where
`edgePool = [0, 1, 0xFFFFFFFFFFFFFFFF (−1), 0x8000000000000000 (INT_MIN), 0x7FFFFFFFFFFFFFFF
(INT_MAX), 2, 64, 65, 100, 0x100000000 (2³²), 7, 63]`.
→ ⅓ uniform-random (covers the interior), ⅔ boundary values (sign edges, shift thresholds 63/64/65,
the 2³² low/high-word boundary). Register inits draw from this pool.

### Instruction selection (straight-line core, `T1.lean`)
`op = seed mod 13`, operands `rd,rn,rm` drawn by `pickReg` over **usableRegs** = x0–x28 minus the
reserved x16/x17/x18 (harness pointers). The 13 arms: `mov rd (imm mod 4096)`, `movR`, `addR`,
`subR`, `mulR`, `sdivR`, `andR`, `orrR`, `eorR`, `lslR`, `asrR`, and a paired `cmp rn,rm ; cset
x0,cond` (flag semantics; cond drawn from `[eq,ne,lt,le,gt,ge,hs,lo]`). cset targets **x0** because
the printer renders `cset w0` (codegen convention — protocol finding 3).

### Panic-safe shift amounts
`lslR/asrR` take their shift amount from a **bounded register set** `{x25,x26,x27,x28}`, whose
inits are forced into `0..127` (`boundShiftRegs`: any reg index ≥ 25 is reduced `mod 128`). This
keeps amounts ≥ 64 (so the shift-masking bug still fires) while avoiding the `Nat.shiftl exponent
too big` panic that an astronomically large unmasked shift would cause in the evaluator.

### Control flow (`T1Branch.lean`)
Per-position generation of length `n`: at index `i`, with some probability emit `cbz rn, tgt` with
a **forward** target `tgt = i + 1 + (seed mod (n − i)) ∈ [i+1, n]`. Forward-only ⇒ the program
counter is monotone ⇒ the model run terminates (driver `runEnd`, fuel `n+1`). The asm emits a
`.Li:` label before every instruction and a `.Ln:` exit label so `.L<tgt>` references resolve.
Inits are 0-biased (`[0,0,0,1,2,7,−1,100,0,64]`) so branches go both ways. Only `cbz` is generated
(`cbnz` renders `cbnz w0`, hardcoding x0 + 32-bit — protocol finding 2; it would false-positive on
wide values, so it is excluded and recorded as an open candidate finding).

### Stack memory (`T1Stack.lean`)
`ldr/str` use offsets from a scratch slice `{96,104,…,152}` of the frame that the register-save
prologue allocates but does not use; the slice is pre-zeroed (`stp xzr,xzr`) so a load before any
store matches the model's zero-initialized stack. Generation mixes data ops with `str rd,off` /
`ldr rd,off` round-trips.

### Array memory (`T1Array.lean`)
Arrays are `.comm _arr_A/_arr_B` globals (BSS-zero, matching zero-init `arrayMem`). Index registers
are held to `0..15` (in bounds). x0 is excluded from operands and the diff because the printer uses
it as `adrp` address scratch (protocol finding 4). Generation mixes data ops with `arrSt nm,ix,rd`
/ `arrLd rd,nm,ix`.

### Coverage levers (to surface more in a longer session)
Widen `edgePool`; raise per-opcode hit counts; lengthen sequences; add any *emitted* instruction
not yet generated (e.g. `movz/movk`, `bCond`, `eorImm/andImm`); add register-aliasing pressure
(reuse one register as multiple operands). **Float ops are intentionally excluded — opaque/
axiomatized, not co-simulable (protocol RQ1a / finding 1).**

---

## T2 — AST round-trip  (TO-BUILD)   round-trip = `parse ∘ print = id`

**Goal:** find parser/printer disagreement on *well-formed* programs.

**Algorithm — grammar-directed, type-correct AST generation** with a depth budget `d`:
1. Maintain a typing context `Γ` (var → {int, float, bool, int[], float[]}). Seed it by generating
   a random `var`-block: N variables with random types + a few array decls with random sizes.
2. Generate a statement list; for each statement pick a constructor by `seed mod |Stmt|`
   (assign, if, while, array-write, print, …), recursing with `d−1`. At `d = 0`, emit only leaves
   (a literal or a variable of the required type).
3. **Type-correctness is the invariant** (the parser only accepts well-typed programs): to fill a
   hole of type τ, draw from {variables of type τ in Γ, a τ-literal, an operator whose result is τ
   applied to recursively-generated τ-typed args}. Never produce `i + 0.5` (no auto-promotion —
   a known language gotcha).
4. **Literal-edge coverage** (the round-trip's sharp corners): negative and special floats
   (`0.0, -0.0, inf, nan, 1e308, denormals`), integers at `INT_MIN/MAX`, strings with escapes/
   quotes, identifiers adjacent to reserved words (`neg`, `exp`, …), and deep nesting.
5. **Constructor coverage:** track which AST constructors have been emitted; bias selection toward
   unused ones until all are hit, then continue uniformly.

**Oracle:** `print(ast)` → text → `parse(text)` → `ast'`; assert `ast == ast'` (structural). A
mismatch is a parser or printer bug (RQ3). A parse *failure* on a well-formed AST is also a bug.

---

## T3 — text → parse  (TO-BUILD)   parser totality + accept/reject

**Goal:** parser robustness — it must **terminate** on any input (never crash/hang) and classify
grammar-valid vs grammar-invalid correctly.

**Three generators:**
1. **Grammar-valid** — reuse T2's printer output: these must parse, and round-trip.
2. **Grammar-invalid (constructed)** — deliberately violate one production (drop a `}`, use a
   reserved word as an identifier, give an array two `var` blocks, write `bool == bool`): these
   must be **rejected** (clean error, no crash).
3. **Mutational fuzz of valid seeds** — token- and char-level edits over a valid program: delete /
   insert / substitute a token; swap or unbalance delimiters; inject huge numerals, Unicode bytes,
   reserved-word collisions, deeply nested parens. Edit count drawn `1 + seed mod k`.

**Oracle (per input):** the parser must **halt with accept-or-reject within a step bound** (totality
— the strongest invariant for arbitrary text); for (1) accept + round-trip; for (2) reject. For (3)
the only firm oracle is totality + "no internal panic"; an accept is then fed to the round-trip
check. Generation strategy: bias the mutational fuzzer toward the lexer/parser boundary tokens
(string delimiters, numeric literals, block keywords) where totality bugs cluster.

---

## T4 — random program → reference C + Axon  (partial: `stress/diff_test.py`; gen TO-BUILD)

**Goal:** end-to-end differential testing (RQ1b) + cert-failure harvesting (RQ4/RQ5).

**Algorithm — Csmith-style well-defined program generation.** The hard requirement is that every
generated program be **well-typed, terminating, deterministic, and free of undefined behavior**, so
that a C-vs-Axon output difference is a real compiler bug, not a generator artifact:
- **Type-correct** as in T2.
- **No division/mod by zero:** generate divisors as `(e mod K) + 1`, or guard with a conditional.
- **No out-of-bounds:** every array index is `(e mod size)`; never read an array inside a condition
  (load to a scalar first — language gotcha).
- **No uninitialized reads:** assign every variable before first use (initialize the whole `var`
  block).
- **Termination:** loops use a fresh counter with a fixed compile-time bound (`for`-shaped
  `while`); no data-dependent loop conditions, or a hard iteration cap injected.
- **Determinism:** no nondeterministic constructs; a fixed input vector per program.
- **Output:** the program prints a checksum/fold over its live variables so a single value witnesses
  agreement.
Emit the **same** program twice: once as Axon `.w` source (compiled by the verified compiler), once
as equivalent reference **C** (compiled by `cc`). Run both on the fixed input; compare output.

**Float is in scope here (unlike T1).** T4a runs both binaries on real IEEE-754 hardware, so float
numeric behavior *is* observable. It catches **gross float miscompiles** — a wrong float
instruction (`fadd` for `fsub`, wrong `fmin/fmax`), a wrong constant, or a control-flow / register-
allocation error that changes which float ops run. **Compare floats TOLERANTLY** (`printFloat` +
numeric tolerance, exact for int tokens): **FMA fusion and reassociation produce *correct* results
that differ only in the bottom bits** — a bit-exact or ULP-*amplified* compare would flag these
legitimate optimizations as false bugs, so it must NOT be used. (Therefore no `-ffp-contract=off`
is needed — the tolerance absorbs contraction.) Subtle, bottom-bit float-axiom questions are *not*
differentially observable and are not a T4a target; they belong to the **RQ1a axiom audit**
(inspection), not here. Float is also *easier* to keep UB-free than int (no div-by-0 or overflow
UB) — but bound magnitudes so the `floatToInt`/cast at output stays in int64 range (ARM `fcvtzs`
*saturates* out-of-range while a C cast is UB → a spurious divergence), guard divisors positive
(no `inf`), and avoid `sqrt`/`log` of bad args (no `NaN`). Built as `stress/t4_gen.py`
(int+float, `printInt`+`printFloat`) + `stress/t4_run.py` (tolerant token compare); validated 0
divergences / 40 seeds on the correct compiler. Generate a mix of int-only, float-only, and mixed
programs (exercise `intToFloat`/`floatToInt`, the `a*b+c` shape, and accumulation loops).

**Layered experiments on the same generator:**
- **T4a — differential:** outputs must agree. Adjudicate a diff as compiler-bug vs C-generator-bug
  vs C↔Axon-semantics-mismatch (the reference-C emitter must itself be validated, else diffs are
  ambiguous — see protocol §issues).
- **EMI / metamorphic (no reference compiler):** profile an Axon program on its input; find code
  not executed; mutate only that dead region — *Orion* deletes it, *Athena* inserts/deletes
  statements there, *Hermes* rewrites *live* code with equivalence-preserving transforms. The
  variant must give identical output on that input; any divergence is a bug.
- **T4b — cert harvest:** record every certificate-check failure the pipeline throws while compiling
  the generated programs; adjudicate each (RQ4a/4b, RQ5a/5b).

---

## T4c — certificate / transform mutation  (partial: `certmutate`)

**Goal:** confirm the checker rejects bad certificates (RQ1c / RQ4b).

**Algorithm:** from a real `(program, optimizer-output, certificate)` triple, apply a
**structure-aware mutation** to the certificate (or the transform):
- flip/alter one **relation** entry or **invariant**;
- change a **pc-mapping** (orig↔trans correspondence) target;
- **drop / add / duplicate / swap** a transition in the cert's transition list;
- **perturb a literal** (constant, register, variable id).
Run the verified checker on the mutant.

**Equivalence-preserving classification (the crux).** A mutation can land on a *don't-care* field
and yield a certificate that is still valid for a still-correct transform — the checker *should*
accept it, and that is **not** a bug. So each mutant is classified:
- **semantics-changing** → the checker **must reject**; an *accept* is an RQ4b soundness bug;
- **equivalence-preserving** → accept is fine; **count** these (the rate of harmless mutations is
  itself a reported number, protocol §4).
Classification needs an independent oracle (re-derive whether the mutated cert still certifies the
actual transform); where that can't be decided automatically, the mutant is flagged for post-hoc
human adjudication rather than auto-labeled. Generation strategy: enumerate mutation *operators ×
cert sites* systematically (not just uniform random) so every operator is exercised on every cert
field type, and bias toward the fields the checker's soundness proof most relies on.
