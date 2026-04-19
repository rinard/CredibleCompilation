# Design Decisions

Record of key design decisions for CredibleCompilation.

---
Useful prompts:
  a) Is there an abstraction that would simplify the proofs?
  b) Are there probes or blockers that would help derisk the plan?
  c) Are there any blockers to the current plan?
  d) Can you take another look at the plan and see if there are issues to be addressed?
  e) Should I execute the plan in this session or a new session?
  f) Give me a prompt for the new session. 
  g) Isolate failing goal and focus on that - try different alternatives quickly. 
  h) when it looks like it is thrashing, ask what is the problem - basically have it explain what is going on. This makes it reflect and apparently helps it get enough context to come up with a solution instead of thrashing. 

Compromises:
  Provability compromises:
    All caller save variables live anywhere saved and restored across call instructions. Obviates a need to thread per instruction liveness information through proofs. 
    Loads from boolean arrays normalize to 0/1. Avoids having to thread invariant that all booleans are 0/1 through entire proof structure. 
    Float literal/variable comparisons - handle only one direction, turns out can't prove one of the combinations. 	

    fmadd semantics subtly different from fmul + fadd - fixed by putting in an axiom that they are the same.

  Provability Design Decisions:
    Programming language level data types (integers, floats) identical to hardware data types. 

    No gotos in source while language - interferes with while to TAC proof. 

    hasSimpleOps and checkBoolExprNoArrRead checks in the certificate checker. These rule out potential expression patterns that the proofs find difficult to handle. They are true of programs that the While to TAC compiler produces and true of programs that optimizer produces (because the optimization is rejected if it does not satisfy). Not a problem in practice - checkBoolExprNoArrRead is avoided by placing read array value in variable before boolexpr. hasSimpleOps removes .bexpr issues (treats ints/floats as booleans). 

  Certificate checks that typing context does not change when going from original to transformed program. So eliminated variables persist in the typing context. The original typing context also assigns a type to every possible variable name, with naming conventions for bool, integer, and float variables. So passes have to conform to this naming convention for any new variables that they add. One approach is to prepopulate the typing context with register and temporary names. I'm telling it to use this approach. Next time around make sure to enable arbitrary typctx extensions. 

  Surprises: .bexpr - treats ints/floats as booleans. left over from development, was a potential blocker to totality theorem that says compiler always generates asm output. 
    Propositional checker vs. executable checker. Introduced by Claude for proof structuring reasons. 

+++ Recall codegen anomaly around r18 - one app silently failed. 
 
> what happens if r18 used in generated code? why is this register reserved?

x18 is the platform register on macOS/iOS — the OS reserves it for thread-local storage (TLS). The kernel sets x18 to point to the thread's TLS block, and any system call or library function (like _printf, _exit) may assume it's intact. Clobbering x18 could cause crashes in libc or the OS runtime.

+++  Another codegen anomaly - without optimization, k18 generates a stack size larger than 4095. The prologue and epilogue use add and sub immediates to update stack pointer. Fails (does not assemble) when stack size no longer fits in immediate for add and sub. Stack offsets up to 32760 fit in the load and store immediates. Code right now supports up to this size. All of this is in the unverified code gen. 

Originally used register 16 as part of the new code gen when frame size does not fit. 

  Question and answer session:

> is r16 ok for this - why was it reserved in the first place? why not use one of the scratch registers 0-2

  Good question. x16/x17 are reserved because the linker may clobber them — when a bl target is too far away, the linker inserts a veneer (trampoline) that uses x16/x17 as scratch. So any bl _printf or bl _exit could silently destroy x16/x17 between the call site and the target.

But in the prologue/epilogue, there are no bl instructions between our mov x16 and the sub/add that consumes it — it's purely local arithmetic. So x16 is safe here. This is actually the intended ABI use: x16/x17 are "intra-procedure-call scratch" registers, meant for exactly this kind of compiler-internal plumbing.

As for x0–x2: they'd work in the prologue (x0 gets overwritten with mov x0, #0 right after), but in the epilogue x0 already holds the return value:

> how about using x1 in epilogue

    You're right — x1 is not the return value and is free at that point. It's a simpler choice since it doesn't carry the "linker might clobber it" baggage that requires reasoning about. Let me switch to x1.

> how would this affect a totality proof (working on this in another session) that the compiler always generates asm
  
It doesn't. The subSpFrame/addSpFrame/addFp are pure if/else expressions that both produce List String — neither branch can fail. They're in the unverified generateAsm wrapper, not in verifiedGenerateAsm.

The totality proof (your plan in zesty-tumbling-sunrise.md) is about showing verifiedGenerateAsm tyCtx p = .ok r. The wrapper generateAsm can only fail at the defense-in-depth checks (callee-save mismatch), not at string assembly. The frame size helpers just change which strings get emitted, with no error path.

> can you add a quick defense in depth check to the unverified code gen

Done. Now instead of a cryptic assembler error, programs with >4095 stack variables get a clear error message up front. Note this adds a new error path to generateAsm, which would need to be discharged in the totality proof — but it's a simple vars.length bound that real programs won't hit.

+++ 

> are you aware of all register usage conventions on this platform and can you audit the code to see if the compiler follows these conventions

Let me do a systematic audit. The AArch64 macOS calling convention (AAPCS64 + Apple platform ABI) has these rules:

Register	Role	Convention
x0–x7	args/results	caller-saved
x8	indirect result	caller-saved
x9–x15	temporaries	caller-saved
x16–x17	linker scratch (ip0/ip1)	clobbered by veneers at bl
x18	platform register	never touch (macOS TLS)
x19–x28	general purpose	callee-saved
x29	frame pointer	callee-saved
x30	link register	callee-saved
sp	stack pointer	16-byte aligned at bl
d0–d7	float args/results	caller-saved
d8–d15	float temporaries	callee-saved
d16–d31	float temporaries	caller-saved
Let me check each concern:
  
...

Here's the full audit:

1. x18 never written — SAFE
x18 is excluded from the allocatable register pool in RegAllocOpt.lean. violatesRegConvention rejects __ir18/__br18 names, RegConventionSafe formally blocks it, and there's a defense-in-depth check in generateAsm. x18 never appears in generated code.

2. x16/x17 not live across bl — SAFE
Both excluded from allocation pools and blocked by RegConventionSafe. No generated instruction puts values in x16/x17 that need to survive a bl. (Our new prologue use of x1 avoids this entirely.)

3. Callee-saved int regs (x19–x28) — SAFE
detectCalleeSavedLayout scans the layout, genVerifiedCalleeSave generates str/ldr pairs in prologue/epilogue, and there's a defense-in-depth check confirming all used callee-saved regs are actually saved.

4. Callee-saved float regs (d8–d15) — SAFE
Same mechanism. ArmFReg.isCallerSaved returns false for d8–d15, so they're detected and saved/restored. d8–d15 are allocatable but properly handled.

5. SP 16-byte alignment — SAFE
Frame size: rounded up to 16 via (... + 15) / 16 * 16
Print calls: sub sp, sp, #16 or #32 (multiples of 16)
Library calls: stp x29, x30, [sp, #-16]! / ldp x29, x30, [sp], #16
6. Caller-saved regs around bl — SAFE
Three call-site categories all handled:

In-body print: genCallerSaveAll saves/restores ALL caller-saved regs in layout (formally verified via callerSaveSpec)
Library calls (sin/exp/pow): same mechanism, excluding destination register
Observable print at halt: haltSaveInstrs saves register values to stack first, then printf loads from stack — no live register values across bl
7. x29/x30 save/restore — SAFE
Prologue stores, epilogue restores. Library calls within the body use stp/ldp pairs. The bl _printf at div-by-zero/bounds-error handlers doesn't save x30, but the next instruction is bl _exit which never returns — harmless.

8. d0–d7 around calls — SAFE
d0–d2 are scratch (blocked from allocation). d3–d7 are caller-saved and handled by the genCallerSaveAll save/restore mechanism. d0 is the float argument/return register for library calls — not allocatable, so no variable value is in d0 across a bl.

No violations found. The compiler has a solid layered defense: register allocator exclusion, naming convention checks, formal RegConventionSafe property, caller/callee-save protocols with formal proofs, and defense-in-depth runtime checks.

+++

Partial def issue for proving compiler termination. This is a Lean issue:

> what is the partial def issue and what is the fix

10 functions in the compiler use partial def — Lean's escape hatch for functions without a termination proof. They compile and run fine, but Lean's logic treats them as opaque axioms. This means:

The totality theorem ∃ asm, generateAsm ... = .ok asm is provable (Lean can't see inside the partial def to find a contradiction)
But operationally meaningless — if analyzeLiveness loops forever, generateAsm never returns, and the "existing" asm is a fiction
The 10 functions are all worklist/fixpoint algorithms that iterate until convergence. They always terminate in practice (bounded by lattice height × program size) but lack a Lean termination proof.

The fix: Add a fuel : Nat parameter to each. The recursive call passes fuel - 1. When fuel hits 0, return a conservative default (e.g., "all variables are live" for liveness, "no constants known" for const prop). Then remove partial.

This makes every function provably total. Fuel exhaustion never produces wrong code — it just produces less-optimized code, which the certificate checker validates anyway. The default fuel is set high enough (e.g., prog.size * latticeHeight) that it never triggers in practice.

The conversion is mechanical — ~5 minutes per function, ~half a day total for all 10.

0) Initial certificate prompt:

Develop a certificate checker that checks a certificate that an original program was correctly transformed into a transformed program. 

The setup is largely similar to Credible Compilation as described in https://people.csail.mit.edu/rinard/techreport/MIT-LCS-TR-776.pdf.

Use the program representation and operational semantics in Semantics.lean.

A program behavior is an execution from start instruction to halt instruction. Certificate checker should check one way correspondence that every behavior of transformed program has a corresponding behavior of original program but not the other way around.

Certificate should specify:
  1) Original program and transformed program. Programs can be different sizes.

  2) For original program and transformed program, a Floyd-Hoare style proof of properties that always hold in the original or transformed program. These properties may be used to establish correspondence between transitions in transformed and original programs.

  3) For each instruction in transformed program,
    a) A corresponding instruction in original program,

    b) A function from variables in transformed program to expressions in original program with the same values,

    c) For each transition from the instruction in the transformed program to a next instruction in the transformed program, 0 to n corresponding transitions in the original program that lead to a corresponding next instruction in the original program. These transitions enable a proof, by induction on sequences of executed instructions in the transformed program, that each behavior of the transformed program has a corresponding behavior in the original program.

  4) For each halt instruction in the transformed program,
     a) Check that corresponding instruction in original program is a halt instruction,
     b) Check that observable variables at halt instruction in transformed program and at corresponding halt instruction in original program have same values.

  5) Prove that is there is a behavior in the transformed program that does not halt, there is also a behavior in the original program that does not terminate.

1) Bounds check elimination - code gen takes a tac program plus interval bounds invariants. checks invariants, if imply bounds checks are always satisfied, generate code without bounds checks. bounds analysis runs just before code gen or optimizations that run after bounds analysis preserve interval bounds invariants. include analysis of multiplication as in idx := i * 32 + k style indexing to bounds analysis.

2) Think about including bitwise operations - and, or, not, nand, etc. In addition to standard integer operations like +, -, *, /, %.

3) download livermore loops from netlib, have original C version, C version generated by LLM, and while lang version generated by LLM. Looks like original versions have out of bounds accesses. Looks like original FORTAN has out of bounds error too. Livermore Fortran Kernels Test - Netlib, UCRL-53745 Technical Report - OSTI

4) while language needs goto statement, both conditinal and unconditional. also need clock intrinsic.

5) lots of issues running optimizations on programs with dead code. run dce after all optimizations that may introduce dead code.

6) Maybe add opaque noops like starttimer, endtimer, printimer that the code generator fills in appropriately to time the code.

7) exp(), sqrt() implemented. More intrinsics TBD.

8) How to handle arrays efficiently. Looks like have a separate load array base and load/store array element instructions, enables array base to be allocated in register and not reconstructed every time. arrBase x arr loads address of array into x, arrLoad x i loads i'th element of x, arrStore x i v stores v into i'th element of x. To keep type safety would need to have a new type - array base (effectively an address). Another fix is to have codegen track array bases and not deal with it at TAC level. 

9) How to handle SIMD. Add SIMD instructions to TAC level code. Axioms that state equivalence of SIMD and scalar computations/loads. 

10) Registers can, in principle, hold values of different types at different locations. So one register might hold bool for some ranges, int for other ranges, and array base for yet other ranges. One approach is to have program point specific typing. Another approach is to have register allocator allocate each register to hold variables of only one type during compilation unit. 

11) Numbers are a problem - any mismatches between semantics and hardware causes enormous difficulties. Make semantics of numbers exactly match hardware, incuding wrapping integer overfow and IEEE floating point. 

12) Make sure codegen works with register allocation information (special variable names for registers) and arrays bounds check elimination information. This means that initial system needs some kind of array bounds elimination information from an analysis like interval analysis. Codegen should check that scratch registers are not used and reject program if they are (or save on stack before use). Or just make scratch registers unnamable - interpret __x? as stack variables.

13) Make sure tac programs are well typed. more generally, codegen is self validating and can refuse to generate code if checks fail. also scratch register safety and layout injectivity. also consider making data structures finite maps not functions. Also while to tac is self validating and does not generate tac code if various well formedness checks fail. 

14) Always be sure using verified code. Claude has a habit of doing both verified and unverified versions. This was the case for translations into and out of TAC intermediate representation. 

15) Top level theorems should work with initial states to eliminate overly general hypotheses. 

16) Think about adding a nondeterministic choice, something like choose bexpr1 : l1 bexpr2: l2; where bexpr1 and bexpr2 can both be true and implementation can choose one nondeterministically. 

17) Be sure register allocator respects register usage conventions - for example, can't use x16-x18, x19-x28 are callee save, x3-x15 caller save. Code was allocating x17. Note - usage convention is architecture specific so must change if change machines. 

18) Looks like difficult to support goto at source level but not TAC level. For now rewrite benchmarks to use only structured flow of control. 

19) LICM does not support irreducible CFGs. Initially showed up as certificate failure for program with irreducible CFG. Added an explicit check for irreducible CFG to LICM. Initial fix - identity transform if irreducible, added explicit pass not applicable to interface with driver checking. 

20) Standard C operations like bitwise and arithmetic operations can be handled in a uniform way by abstracting specific operation cases. Similarly for floating point intrinsics like exp, sqrt, sin, cos, ...

21) Generated code sometimes calls procedures like exp() and sqrt(). Codegen needs to save caller save registers around call. 

22) fmadd different rounding than fadd fmul. ignore in semantics - just say has same semantics. Also adding axioms about IEEE floating point numbers, specifically comparisons, etc. This is to avoid having to prove theorems about IEEE floating point because compiler treats them as opaque. 

23) Certificate checkers do exhibit success for some programs and failures for others. Often cascading failures as ramp up the optimizations and more general expressions make it into the optimizations. These are typically handled via Claude Code, which automatically prints the certificate, traces the failure to a specific node, and immediately spots and corrects the certificate/reasoning error. Most of the time the reasoning is not general enough. 

23) implementation of fmadd detail:
  Starting situation: fmadd in ARM semantics and TAC operation (added in less than two hours to existing infrastructure)

  a) Initial prompt issued at 12:58. 
     right now the compiler generates fmul followed by fadd instead of fmadd. plan the implementation of a tac optimization pass that converts fmul+fadd to fmadd.
  b) Plan generated at 1:02, saved into fma-fusion-opt.md
  c) Accept this plan? Yes, and auto-accept issued at 1:06
  d) Plan completed at 1:14. 
  e) Summary is:
    All done. Here's a summary of what was implemented:

FMA Fusion Optimization Pass
New file: FMAFusionOpt.lean — fuses adjacent fmul + fadd/fsub pairs into single fmadd/fmsub ternary instructions.

Patterns fused
t := fmul(b, c); x := fadd(a, t) → x := fmadd(a, b, c)
t := fmul(b, c); x := fadd(t, a) → x := fmadd(a, b, c) (commutative)
t := fmul(b, c); x := fsub(a, t) → x := fmsub(a, b, c)
Safety constraints
Instructions must be adjacent with no incoming jumps to the second
Temp t must be dead after the fadd/fsub (verified via liveness analysis)
t != a to prevent clobbering
Architecture
Reuses DAEOpt.analyzeLiveness and DAEOpt.buildPredecessors for analysis
Reuses buildOrigMap/buildRevMap/PeepholeOpt.buildSkipArr for compaction
Identity expression relations (semantics are definitionally equal via FloatTernOp.eval)
Zero sorrys — no new proof obligations
Modified files
CodeGen.lean — import + pipeline insertion after DAE, before CSE
PipelineCorrectness.lean — added hty_fma/htyO_fma hypotheses to all three correctness theorems
 f) Certificate does not check for simple fmadd programs at 1:18.
 g) Claude Code automatically launches debug session, finds problem
    Now I see the symbolic representations:

fbinop x fmul y z → x := .fbin .fmul y z
fbinop x fadd a t → x := .fbin .fadd a (.fbin .fmul y z) (after substituting t)
fternop x fmadd a b c → x := .ftern .fmadd a b c
These are structurally different symbolic expressions! .fbin .fadd a (.fbin .fmul b c) ≠ .ftern .fmadd a b c. The checkRelConsistency comparison will fail because the checker doesn't know the algebraic identity.

This means I can't use a simple compacting pass with identity relations. I need a different approach — either:

Keep both instructions (don't compact) and use a non-identity expression relation, or
Add a simplification rule that normalizes .ftern .fmadd a b c to .fbin .fadd a (.fbin .fmul b c), or
Do the fusion at the code generation level (in verifiedGenInstr) rather than as a TAC optimization pass

...

I need to normalize ftern to expanded binop form in both simplify and simplifyFast. Let me also fix the origLabels bug in FMAFusionOpt. Two changes needed:

ExecChecker.lean: Expand ftern to binops in simplify/simplifyFast
FMAFusionOpt.lean: Fix origLabels to include the fadd PC
  h) Certificate is still failing at 1:23, new debug session initiated. Claude Code conclusion is:
     I need to precompute the pc_orig for each trans instruction, then use those when computing paths. The key insight: each instruction's origLabels must end at the next instruction's pc_orig, not at origMap[i+1].
  i) Certificate is still failing at 1:27. Claude Code conclusion is:
     The identity relation claims (.var "__ft0", .var "__ft0") — asserting orig __ft0 == trans __ft0. But in orig, __ft0 was written by the fmul, while in trans, __ft0 is never written (the fused fternop writes to x directly).

The fix: I can't use a pure identity relation. I need to exclude __ft0 (the temp variable killed by fusion) from the post-relation, or use a non-identity relation that accounts for it.

The simplest approach: for fused instructions, filter the dead temp out of the relation at the fusion point.
  j) FMA certificate for simple test case checks at 1:29. But ConstProp certificate fails - ConstProp transfer function does not handle fmadd. Claude Code correctly diagnoses problem and fixes it at 1:30. 

  k) FMA certificate fails on Livermore Loops benchmark at 1:31. Claude Code diagnoses problem as follows:
     Since FloatBinOp.eval .fadd is opaque, the checker can't prove commutativity. I need to ensure the operand order matches. When the temp is in the lhs of fadd, the fmadd should put the mul result first: fmadd(rhs, mulL, mulR) is wrong because fmadd semantics is a + b*c, so the expanded form is fadd(a, fmul(b,c)). If the original is fadd(temp, rhs), I need the expanded fmadd to also be fadd(temp, rhs) = fadd(fmul(b,c), rhs). But fmadd is a + b*c = fadd(a, fmul(b,c)), so this would require a = fmul(b,c) and the addend on the "wrong" side.

I can't match this case with fmadd because fmadd is always a + b*c. When the original is fmul(b,c) + a (temp first), the expansion is fadd(fmul(b,c), a), but fmadd gives fadd(a, fmul(b,c)). These differ symbolically even though IEEE addition commutes.

The simplest fix: only fuse when the temp is in the second position of fadd (i.e., fadd(a, temp)), not the first.
  l) RegAlloc fails at 1:35 (does some but not all Livermore benchmarks). Does not handle fternop correctly. Diagnosis:
     I see — RegAlloc uses DAEOpt.instrDef for determining the defined variable. Let me check that instrDef handles fternop.

Read DAEOpt.lean (lines 48-62)
instrDef doesn't handle fternop! The _ => none catch-all returns none for fternop. This means RegAlloc's relTransfer treats fternop as a no-op (doesn't update the relation for the defined variable), which corrupts the expression relation
  m) Fixed at 1:43. Livermore benchmarks tested at 1:44, compile correctly. 
  n) Prompt at 2:04 - what about fmadd not dealing with commutativity and only working for some temp patterns.
     Response: 
Right — currently we only fuse fadd(a, t) (temp in second position) but not fadd(t, a) (temp first), because the checker can't prove fadd commutativity symbolically.

The fix: when the temp is in the first position, emit the fternop with swapped addend order so the symbolic expansion matches. Concretely:

t := fmul(b, c); x := fadd(t, a) — orig symbolic: fadd(fmul(b,c), a)
We need the fternop to expand to the same thing: fadd(fmul(b,c), a)
But fmadd(a, b, c) expands to fadd(a, fmul(b,c)) — wrong order
The solution: use fmadd with a = the mul result's position. Since FloatTernOp.eval .fmadd a b c = fadd(a, fmul(b,c)), to get fadd(fmul(b,c), a) we'd need a "reverse fmadd" — but that doesn't exist in the IR.

Two options:

Add fmaddRev to FloatTernOp with semantics fmul(b,c) + a — invasive, touches many files
Normalize the fadd operand order in the source before fusion — swap fadd(t, a) to fadd(a, t) as a pre-step, then fuse. But this also has the commutativity problem for the checker.
Actually, the simplest correct approach: teach Expr.simplifyFast to canonicalize fbin fadd operand order (e.g., sort by structural ordering). Then both fadd(a, fmul(b,c)) and fadd(fmul(b,c), a) normalize to the same form, and the checker accepts both patterns.

Want me to implement that canonicalization approach? It would let us fuse both fadd(a, t) and fadd(t, a), and also handle the fsub case where only fsub(a, t) is valid (subtraction isn't commutative, so that one's already correct).

 o) I suggest to add an axiom that fadd commutes. Claude says not worth it for now. At 2:32 come back after getting system to stable state and pushing, ask for plan. Plan for adding axiom that fadd commutes to enable fmadd for a + (b * c) and (b * c) + a. Here is the plan. 

Implementation Plan
4 files, 5 changes
1. Core.lean:291 — Add axiom (after FloatBinOp.eval)


/-- IEEE 754 addition is commutative for all values. -/
axiom FloatBinOp.fadd_comm (a b : BitVec 64) :
  FloatBinOp.eval .fadd a b = FloatBinOp.eval .fadd b a
2. ExecChecker.lean:71 — Normalize fbin .fadd in simplify

Change:


| .fbin op a b    => .fbin op (a.simplify inv) (b.simplify inv)
To:


| .fbin op a b    =>
    let a' := a.simplify inv; let b' := b.simplify inv
    match op, a' with
    | .fadd, .fbin .fmul _ _ => .fbin .fadd b' a'
    | _, _ => .fbin op a' b'
When fadd's left arg is an fmul, swap them so the product lands on the right. This is the only case the FMA pattern creates.

3. ExecChecker.lean:521 — Same normalization in simplifyFast

Change:


| .fbin op a b    => .fbin op (a.simplifyFast m) (b.simplifyFast m)
To:


| .fbin op a b    =>
    let a' := a.simplifyFast m; let b' := b.simplifyFast m
    match op, a' with
    | .fadd, .fbin .fmul _ _ => .fbin .fadd b' a'
    | _, _ => .fbin op a' b'
The ftern unfolding at lines 526-528 already puts the product on the right, so no change needed there.

4. FMAFusionOpt.lean:49 — Add t == lhs case

Change:


else if t == rhs && t != lhs then
  some (x, .fmadd, lhs, b, c)
else none
To:


else if t == rhs && t != lhs then
  some (x, .fmadd, lhs, b, c)
else if t == lhs && t != rhs then
  some (x, .fmadd, rhs, b, c)
else none
5. SoundnessBridge.lean:275 — Update simplify_sound for fbin case

Current proof:


| fbin _ _ _ iha ihb =>
    simp only [Expr.simplify, Expr.eval]
    rw [iha, ihb]
New proof needs to case-split on the normalization:


| fbin op _ _ iha ihb =>
    simp only [Expr.simplify]
    split
    · case h_1 _ _ _ _ _ heq =>  -- fadd with fmul on left → swapped
      simp only [Expr.eval]
      rw [iha, ihb, FloatBinOp.fadd_comm]
    · case h_2 =>                 -- everything else → unchanged
      simp only [Expr.eval]
      rw [iha, ihb]
Plus update the simplifyFast_eq_simplify proof at ExecChecker.lean:633 — the fbin case becomes a split + cases on both functions to show the match branches align.

Why refinement proofs go through
Checker pass/fail: After normalization, orig produces fbin .fadd (var a) (fbin .fmul b c) (product swapped right) and trans produces the same from ftern .fmadd unfolding. Structural equality holds.
simplify_sound: The swap case uses fadd_comm to show eval is preserved. One new rw.
simplifyFast_eq_simplify: Both functions do the same match, so the proof is simp + split with matching branches.
Everything downstream (PipelineCorrectness, ArmCorrectness) is untouched — they don't inspect simplifier internals.
No new sorrys expected.

Want me to implement it?

  p) Plan implemented, built, and tested at 2:50

Copy Propagation Implementation
