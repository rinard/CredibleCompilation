# Credible-Compilation Bug-Finding / Fixing Study — Protocol

Status: **draft v1** (2026-06-21). Consolidates the design from prior sessions into a
runnable, reviewable protocol. Items marked **⟨CONFIRM⟩** are reconstructed or need a value
from you; items marked **⟨BUILT⟩ / ⟨TO-BUILD⟩** flag implementation status.

---

## 1. Objective & unit of analysis

Measure how a bug-finding/fixing **process** (a headless Claude Code agent wielding a fixed
set of testing techniques) performs against a fixed, buggy snapshot of the credible
compiler — *what* defects each technique surfaces, *where* they sit in the soundness/
completeness taxonomy, and *what they cost* (tokens, time, turns, build cycles).

- **Unit of analysis:** one technique campaign = (technique × subject) → set of adjudicated
  findings + resource record. The agent run is the process under measurement.
- **Subject:** the quarantined May-7 baseline (below); the interleaved loop progressively
  hardens it bottom-up by trust layer (§5).

## 2. Subject & quarantine

- **Subject tree:** `rinard/CredibleCompilationICSEBase` (authentic May-7 `d869719`, severed
  history, neutral README, today's Livermore harness grafted so benchmarks run). Contains
  the genuine defects of that snapshot.
- **Quarantine rules:**
  - **What the agent has:** the subject tree + the pre-built technique tools (the test
    *generators* don't reveal bug locations) + its own `FINDINGS.md` and repro dir.
  - **Withheld** (so it discovers fresh, not by reading the answers): this protocol, the findings
    doc (`plans/cert-checker-findings.md`), the known-bug list, and any adjudication verdicts —
    none committed to the subject tree.
  - **Adjudication (§8) is post-hoc by you (the human),** never embedded in the agent's tree or
    its run.

## 3. Research questions

The defect space, and where the credible-compilation guarantee does/doesn't backstop it:

Two families partition along the **trust-surface / soundness chain**: **RQ1–RQ5 = product**
(where can the pipeline be wrong), **RQ6–RQ7 = process** (how well the agent finds/fixes).

- **RQ1 — Are the verified proofs sound?** (Lean itself can carry bugs, so a closed proof can
  still be unsound.) Three sub-experiments:
  - **RQ1a — automated audit:** 0 `sorry`, no unsound axioms. The sorry-grep is trivial; **the
    real work is the axiom audit, and the live risk is the opaque float layer**
    (`FloatBinOp.eval`, `intToFloatBv`, `floatToIntBv` + algebraic axioms such as `fadd_comm`).
    Each axiom must hold of IEEE-754 — **NaN/signed-zero break commutativity & identities** (cf.
    bug-audit bug 31). This is where float *spec* soundness actually lives (T1/RQ2 can't reach it).
  - **RQ1b — end-to-end** on random/fuzzed/targeted programs (= **T4a**): a verified compiler
    must never miscompile.
  - **RQ1c — checker rejects all randomly-generated *incorrect* certificates** (= **T4c**).
    *Same experiment/property as RQ4b — run once, report under both.*
- **RQ2 — Bugs in the assembly specification?** Random asm sequences: executable opsem vs the
  real machine (= **T1**). *Note:* float opsem is **opaque** (→ RQ1a), so T1 covers only the
  **concrete ISA**; float numeric behavior is exercised end-to-end by T4a on real hardware.
- **RQ3 — Bugs in the text interfaces (parser, asm printer)?** (= **T2** AST round-trip, **T3**
  text→parse). *The printer is shared* — T1 and T4 also surface printer bugs (e.g. the
  cbnz→w0 / cset→w0 / arrLd-x0-clobber discrepancies T1 found are RQ3, adjudicated to RQ3
  regardless of which technique surfaced them).
- **RQ4 — Checker anomalies/bugs?**
  - **RQ4a — too strict.** Transform + cert *right*, checker rejects → *anomaly*. **May-leave:**
    can't cause miscompilation (only effect: the optimization is dropped).
  - **RQ4b — too loose.** Transform or cert *wrong*, checker accepts → **bug, must-fix** — can
    cause miscompilation. The only must-fix in this layer.
- **RQ5 — Bugs in a transform or certificate generator?** **5a** transform wrong · **5b**
  transform right, cert wrong. **May-leave** as long as the checker rejects (only effect: a
  dropped optimization).
- **RQ6 — How effective is the coding agent** at localizing + fixing surfaced errors?
  Cross-cutting — from the metrics records, audit narratives, and escalation rate.
- **RQ7 — Does fixing introduce bugs?** **7a regression** · **7b new** (re-run techniques after
  each fix; `regression_or_new`).

## 4. Techniques & experiments

**Ordering — harden bottom-up, then go end-to-end.** Run **T1** (asm) and **T2/T3** (text)
first, finding *and fixing* their RQ2/RQ3 bugs to produce a hardened opsem+parser+printer
substrate; **then T4**. Rationale: on a hardened substrate a T4 end-to-end differential
failure is attributable to the **transform/checker/certificate** layer (RQ4/RQ5), not
confounded by a text or asm artifact.

| ID | Experiment | Targets | Generation strategy | Status |
|----|-----------|---------|---------------------|--------|
| **T1** | random asm seqs → print → run on machine, vs executable opsem (`execStep`, proven sound) | **RQ2** (+ RQ3 printer) | random opcode mix; edge operand pools (0, ±1, INT_MIN/MAX, 2ᵏ, shift amts 63/64/65); register aliasing/pressure; per-arm coverage; length sweeps | **BUILT** `Harness/{ArmExec,T1,T1Branch,T1Stack,T1Array}.lean` |
| **T2** | random AST → print to text → parse → recover the AST (oracle = `print = print∘parse∘print`) | **RQ3** (parser + printer) | grammar-directed, type-correct ASTs; cover every constructor + literal-format edges (negative/special floats, escaped strings, reserved-word-adjacent ids, deep nesting) | **BUILT** `Harness/T2.lean` + `Harness/T2Bench.lean` (Livermore round-trip). Printer↔parser desync it found is **FIXED** — 24/24 benchmarks + 300 random ASTs round-trip |
| **T3** | random text → parse, accept-or-reject | **RQ3** (parser) | grammar-valid (must parse + round-trip) · grammar-invalid (must reject) · mutational fuzz of valid seeds (token/char flips, delimiter imbalance, huge numerals, unicode, reserved-word collisions). **Oracle = parser totality (never crash/hang) + correct accept/reject** | **BUILT v1** `Harness/T3.lean` (mutates livermore `.w` seeds; 2700 parses total on the sample, panic-detecting; hang-detection = subprocess-timeout extension) |
| **T4** | random AST program → emit reference **C** + **Axon**; run both | **RQ1b/RQ4/RQ5** | **Csmith-style: UB-free, terminating, deterministic, well-typed** (bounded loops; guarded div & index; no uninit reads; bounded float magnitudes; defined output) + EMI/metamorphic | **BUILT v1** `stress/t4_gen.py` (int **+ float**) |
| → **T4a** | C and Axon outputs agree (ints exact, **floats tolerant** — FMA/reassoc bottom-bit diffs are *correct*, not flagged) | RQ1b | catches gross float miscompiles; a diff is also possibly a C-gen bug or C↔Axon mismatch | **BUILT v1** `stress/t4_run.py` (0 div / 40 seeds on the correct compiler) |
| → **T4b** | certificate-check failures while compiling generated programs | RQ4 / RQ5 | adjudicate each → 4a/4b, 5a/5b; diagnose with `certaudit -diag` | **BUILT** `stress/t4b_harvest.py` (wires `certaudit`; 0 rejections on the hardened dev tree) |
| → **T4c** | mutate transforms + certs → checker must reject | RQ1c / RQ4b | cert-structure-aware mutations (flip relation/invariant, alter pc-mapping, drop/add/dup/swap a transition, perturb values). **Equivalence-preserving (ACCEPT + output matches) → not a bug, COUNT; semantics-changing ACCEPT → RQ4b soundness hole** | **BUILT exe** `certmutate` + `stress/soundness_campaign.sh` |
| → **EMI** | Orion/Athena dead-region mutants ≡ seed on its input | RQ1b | mutate only non-executed code; any output diff is a miscompile | **BUILT exe** `emi` + `stress/emi_campaign.sh` (float-free; float-EMI needs tolerant compare) |

> **T4a's structural limit (demonstrated):** the generator must mask shift amounts `& 63` (unmasked
> shift is UB in C), so differential testing **cannot reach the shift bug** (needs amount ≥64) — that
> bug is found by **T1 co-sim** (model+machine, not C) and by **T4c** (out-of-distribution mutation).
> A concrete reason the multi-technique design is necessary, not redundant.

**EMI = Equivalence Modulo Inputs** (Le–Afshari–Su, PLDI'14): pick a seed program + an input,
profile to find code *not executed* on that input, then mutate only that dead region (Orion
deletes; Athena inserts/deletes; Hermes rewrites live code equivalently). By construction the
variant must produce identical output on that input — any divergence is a compiler bug.
Metamorphic testing with the relation "equivalent on this input"; needs **no reference
compiler**. We already have an `emi` exe (Orion/Athena).

## 5. Experimental design — one autonomous discover ↔ fix session per technique

Per technique, a **single autonomous agent session** runs the whole loop — no external
orchestration of the inner cycle:

1. **Discovery** — the agent runs the (pre-built) technique tool until it surfaces a bug.
2. **Fix** — it switches to fix mode, localizes, fixes (or gives up), then
3. **Resumes discovery** on the now-changed tree, and keeps going until the **session budget**
   (§7) expires.

When the session ends, **you review** the bugs and fixes **post-hoc**: resolve adjudication /
classification (§8), and optionally run an interactive cleanup pass. There is no mid-loop runner
and no mid-loop adjudication — the agent self-directs; judgment is post-hoc.

**Persistent findings log (required).** The agent **appends to `FINDINGS.md` in its workspace as
it goes** — one entry per bug: symptom · repro · localization · fix · status (`fixed` /
`escalated` / `not-a-bug-per-agent`). This is essential, not cosmetic: a 2–12 h session compacts
context repeatedly, so the log is the agent's only durable memory of what it already handled. It
**prevents rework, replaces a suppression set** ("already handled" = present in the log), is the
agent's first-person narrative, and is what you read afterward. The agent is instructed to
**re-read `FINDINGS.md` before each new discovery round** and to **flush each entry immediately**
(so it's inspectable mid-run, §6).

**Why interleave** (vs batch): root-cause dedup (fix once → symptoms vanish → each entry is a
*distinct* bug), cascade discovery (masked bugs surface after the unblocking fix), and **RQ7 for
free** — after each fix the agent **re-runs its accumulated tests** (regression check), and when
the fix touches code shared with an already-hardened technique (e.g. the **printer**, shared by
T1/T2/T4) it **re-runs that technique too**.

**Discovery-vs-fix statistics via in-session markers.** On each switch the agent emits a
transition line (`→ FIX <id>` / `→ RESUME DISCOVERY`); the metrics parser segments the transcript
on these to split output-tokens/time into **detection effort vs repair effort** (§10).

**Soft per-fix limit.** Within the single hard session budget, each fix is *guidance*-capped at
~30 min / ~170k output tokens: the agent is told to spend at most that per bug, then log it
`escalated` and move on. No hard external kill mid-fix — **the session budget is the only hard
gate.**

**Layered ordering ("T1,T2,T3 then T4"):** one session per technique, **bottom-up by trust
layer** — T1 (→ hardened opsem + printer), then T2, T3 (→ hardened parser/printer), then T4 on the
hardened substrate (so T4a/b/c attribute cleanly to RQ1b/RQ4/RQ5, not a lower-layer confound).
You review between layers.

*Tradeoff vs a frozen pass:* detection is measured on a **progressively hardened** tree, not a
pristine one — deliberately, since that yields distinct-bug counts, cascade discovery, and the
built-in RQ7 check.

## 6. Operational mode & live monitoring

- **One autonomous session per technique:** `study-harness/run_agent_task.sh` → `claude -p
  "<technique task>" --output-format stream-json --verbose --dangerously-skip-permissions`, with
  the pre-built technique tool, `FINDINGS.md`, and a repro dir in the workspace.
- The **launcher** (thin wrapper — *not* an inner-loop orchestrator) does only three things:
  start the session, **enforce the session budget** (kill at the wall-clock cap or when the live
  output-token count exceeds the cap, §7), and **tee the transcript to disk**.
- **Live, inspectable intermediate results (your requirement)** — everything is written
  **incrementally / append-only** so you can watch the run in progress:
  - `tail -f FINDINGS.md` → bugs + fixes as they land (the agent flushes each entry immediately,
    not buffered to the end);
  - the repro dir gains a folder per finding the moment it's found;
  - the stream-json transcript is tee'd live → `tail -f`, and `metrics_parse.py --follow` reads
    the *partial* transcript for a running tally of tokens / turns / build cycles and the mode
    markers as they pass.

## 7. Stopping criteria — **budget-based: token cap OR time cap, whichever expires first**

Applied uniformly at every level. **Budget is the only stop** — no loop-until-dry, no
coverage-saturation gate, and (per your decision) **no no-new-finding early exit** anywhere.
The gate is on **output tokens** (cost-aligned, monotone, what the metrics wrapper sums).

| Level | Stops when… | Parameters |
|-------|-------------|------------|
| **L1 — session (per technique)** — the **one hard budget** for the whole discover↔fix loop | `output_tokens ≥ TOK_SESSION` **or** `wall_clock ≥ TIME_SESSION` | **T1 / T2 / T3:** 2 h / **~670k** out-tok · **T4:** 12 h / **~4M** out-tok |
| **soft per-fix** (guidance, not a hard kill) | agent self-limits each bug, then logs `escalated` and moves on | ~30 min / ~170k out-tok |
| **L3 — whole study** | *emergent* — Σ session budgets | (derived) |

A bug the agent abandons at its soft per-fix limit is logged `escalated = true`,
`fix_correct = false`, and stays open — intended RQ6 data (how many defects are *quickly*
fixable). 30 min is deliberately short for a proof-heavy Lean fix, so complex repairs escalate by
design.

**On "tokens appropriate".** Same convention you set: token-time = half the wall-clock at a high
sustained ~670k output-tok/h. **T1/T2/T3** 2 h → ~1 h of tokens → **~670k out-tok**; **T4** 12 h →
~6 h of tokens → **~4M out-tok**. So a token-hungry session is cut at ~half its wall budget while a
token-light one runs the full wall. The rate is a guess — **recalibrate from the first session**.
The launcher enforces the session budget from the live transcript's output-token count + wall
clock; the per-fix ~30 min/170k is prompt guidance to the agent, not a separate hard gate.

**On L3 / total study budget (math).** No global cap to set — the four session budgets self-bound
the total: `T1+T2+T3 (2 h, ~670k each) + T4 (12 h, ~4M)` = **~18 h wall serial** (or ~14 h if
T1/T2/T3 run in parallel then T4) and **≈ 6M output tokens** (3 × 670k + 4M). Inner fixes are
already inside each session budget. **L3 is emergent**: whole-study budget = Σ session budgets;
no global TOK_TOTAL/TIME_TOTAL to set.

## 8. Ground truth & adjudication — **open-ended**

No pre-seeded denominator; the 14 known May-7 bugs are **not** the oracle (no recall rate). Every
finding (a co-sim divergence, a diff mismatch, a cert rejection, a checker acceptance of a mutant)
is adjudicated **fresh, post-hoc by you**, on **two orthogonal axes — record both**:

**(A) RQ class — *what kind* of defect:**
1. **Real miscompile** (shipped-path model / parser / on-path asm printer / float-trust) — must-fix.
2. **RQ4b checker-unsound** (accepted a bad cert) — must-fix.
3. **RQ4a checker-too-strict** (rejected a good cert) — may-leave.
4. **RQ5a transform-wrong** / **RQ5b cert-wrong** — pass-level; checker backstops; may-leave.

**(B) Locus — *where* the defect lives** (keeps the compiler-defect counts honest):
- **compiler-shipped** — in the compiler's trusted/shipped path (model, parser, codegen + on-path
  asm printer, checker, passes). The real study findings; these carry the RQ class above.
- **compiler-debug** — in a compiler component **not** on the shipped path. Canonical case: the
  **AST→text display printer** (`Program.toString`/`Stmt.toString`), never used in compile
  (text→AST→asm) and never debugged against the parser — **T2's printer↔parser findings are here.**
  A real codebase defect, but no miscompile risk; low priority, *not* a `real-miscompile`.
- **testing-infrastructure** — in the harness / generator / oracle, **not** the compiler. E.g. an
  unbounded `intToFloat` in `t4_gen` (overflow), a wrong reference-C emitter, or feeding inputs the
  codegen never emits (the cbnz→w0 / cset→w0 / arrLd-x0 cases T1 surfaced). Fix in the harness and
  **exclude from compiler-defect counts.**
- **not-a-bug** — correct behavior mis-flagged (e.g. an FMA / reassociation bottom-bit float
  difference — correct per the float note); locus n/a.

Adjudication is recorded out of the agent's view. The open T1 printer discrepancies and the T2
printer↔parser findings enter here as candidates: classify the T1 cbnz/cset/x0 ones (compiler-
shipped-vs-testing-infrastructure, depending on whether codegen can emit the trigger) and the T2
ones (compiler-debug) — **not** pre-judged during harness-building.

## 9. Audit record — every discovered bug and every fix

Every adjudicated finding (discovery mode) and every remediation (fix mode) gets a
**self-contained, reproducible record** so the whole campaign is auditable end-to-end. One record
per finding, extended with fix fields once fixed. The agent writes its half live to `FINDINGS.md`;
your post-hoc half lives at `study/findings/<id>/` (out of the agent's view). Together they hold:

- **ID, class & locus** — finding id; RQ class + **locus** (compiler-shipped / compiler-debug /
  testing-infrastructure / not-a-bug), both per §8.
- **Bug location** — `file:line(s)` / declaration in the subject tree; for a real miscompile,
  the layer (model / parser / printer) + site.
- **Reproduction (versioned repro repo)** — the exact inputs that surface it, committed to a
  **separate versioned repro repo** (`CredibleCompilationReproCases` ⟨name CONFIRM⟩), tagged by
  `finding-id` + subject commit hash, so re-running reproduces the divergence/rejection
  **deterministically**: generating seed + emitted `.s`/`.c` (T1), `.w` source + pass flags
  (diff/cert), or the mutated certificate (T4c). Include the one-line command to reproduce.
- **Discovery stamp** — wall-clock time **and** cumulative output tokens (reset per analysis,
  §10) at the moment the finding was surfaced — feeds saturation analysis.
- **Two narratives** (side by side): (a) **agent's `FINDINGS.md` entry** — first-person, written
  live during the run (its own account of surfaced → investigated → localized → fixed →
  validated); (b) **your post-hoc review** — independent, reconstructed from the transcript +
  artifacts after the session. The *divergence* between them is itself data (did the agent
  actually understand what it did?). Both cover: **surfaced** (which oracle fired; the symptom),
  **investigated** (hypotheses + diagnostics), **localized** (root cause + site), **fixed** (the
  change + location), **validated** (re-runs: full build, diff-tests, technique re-run + the
  regression check — incl. any shared-code re-run).
- **Fix location** — `file:line(s)` of the change; the snapshot/commit hash of the fixed state.
- **Validation evidence** — commands + outputs proving the fix closes the repro and regresses
  nothing.

## 10. Metrics & instrumentation

Per **session**, `metrics_parse.py` records: `cost_usd`; input/output/cache tokens +
`total_tokens`; `duration_ms` / `api_ms`; `num_turns`; `tool_calls_by_type`; `build_invocations`
+ `build_seconds_total`; `edit_attempts`; and post-hoc-set adjudication fields `localized_correct`,
`fix_correct`, `escalated`, `regression_or_new` (per finding).

**Discovery-vs-fix split from in-session markers.** The session is one transcript; the parser
segments it on the agent's `→ FIX <id>` / `→ RESUME DISCOVERY` lines, summing output-tokens/time
within discovery segments vs fix segments → **detection effort vs repair effort** per technique
(the separation you asked for). Output-token segmentation is clean (each segment's generated
tokens); input/cache tokens grow with context and aren't split. Runnable mid-stream
(`--follow`).

**Per-finding discovery series (for saturation):** for each campaign, log every finding's
discovery stamp — `(wall_clock_at_find, cumulative_output_tokens_at_find)` — as a series.
Plot **distinct bugs vs cumulative discovery-segment output tokens** (and vs discovery wall),
read against that session's budget (§7). Because the loop root-cause-dedups, each point is a
*distinct* bug, not a symptom-instance. If the curve flattens well before the session budget
expires, the technique **saturated** (budget wasn't the limiter); if it's still climbing at
cutoff, the technique was **budget-limited** with more to find. A primary RQ6 output, possible
only because budget (not a dry-pass) is the stop.

## 11. Artifact / file map

- Subject: `rinard/CredibleCompilationICSEBase` (May-7 baseline + Livermore harness).
- Technique tools (the agent uses these): `Harness/ArmExec.lean` + `Harness/T1*.lean` (co-sim),
  `stress/diff_test.py`, `emi` exe, `certaudit` exe.
- Agent workspace (live, append-only): `FINDINGS.md` (findings log = first narrative) + a repro dir.
- Launcher + metrics: `study-harness/{run_agent_task.sh, metrics_parse.py}` (`--follow` for live).
- Repro cases: `CredibleCompilationReproCases` ⟨name CONFIRM⟩ — versioned repo, one dir per
  `finding-id`, tagged with the subject commit hash.
- Post-hoc review records (your narrative + adjudication + stamps): `study/findings/<id>/`.
- **Withheld from the agent:** `plans/cert-checker-findings.md` (findings/analysis), the
  known-bug list, this protocol.
- Docs: `plans/study-protocol.md` (this), `plans/generation-algorithms.md` (the generators),
  **`plans/artifact-reproducibility.md`** (exact versions/commits + per-result repro recipes +
  the bundle manifest — everything needed to rebuild the paper artifact).

## 12. Parameters to set / open items before running

- **Set:** session budgets **T1/T2/T3 = 2 h / ~670k out-tok**, **T4 = 12 h / ~4M out-tok** (one
  hard budget for the whole loop); soft per-fix ~30 min / ~170k out-tok (prompt guidance); L3
  emergent (≈ 18 h serial / ≈ 6M out-tok). Recalibrate the ~670k out-tok/h rate from session 1.
- RQs (RQ1–RQ7) and technique mapping (T1–T4 + T4a/b/c) are **set** from your spec (§3–§4).
- ⟨TO-BUILD⟩ **Launcher**: session-budget enforcement (kill on wall-clock or live output-token
  cap) + transcript tee; **`metrics_parse.py --follow`** (live tally + `→ FIX`/`→ RESUME` marker
  segmentation); the **agent prompt template** (FINDINGS.md discipline + re-read before each round,
  mode markers, soft per-fix limit, re-run accumulated + shared-code tests after each fix).
- **BUILT + tested:** launcher (`run_session.py`), `metrics_parse.py` (mode split + `--follow` +
  `model` capture), prompts (`discover_fix_template` + `t1`/`t2`/`t3`/`t4`); **T1**, **T2 v1**,
  **T3 v1**, **T4a** (`stress/t4_gen.py`+`t4_run.py`, int+float), **T4b** (`stress/t4b_harvest.py`),
  **T4c** (`certmutate`+`soundness_campaign.sh`), **EMI** (`emi`+`emi_campaign.sh`). All ported to
  the baseline subject tree (T1-family/T2/T3/T4a compile + run there). Generators documented in
  `generation-algorithms.md`; reproduction in `artifact-reproducibility.md`. `study-harness/` +
  `CredibleCompilationReproCases` are git repos (local).
- ⟨REMAINING — documented extensions, not blocking⟩ **T2** float/bool/array/control coverage (v1
  int-subset; deeper round-trip is blocked until the printer↔parser desync T2 found is fixed —
  the agent does this in-session); **T3** hang-detection (per-input subprocess timeout; v1 catches
  panics); **EMI** float support (tolerant compare); port the cert/EMI **exes** to the May-7
  baseline (it has only `compiler`; `certaudit`/`certmutate`/`emi` need a baseline build for T4b/c
  on the subject).
- ⟨TO-BUILD⟩ Port T1Branch/T1Stack/T1Array + extended ArmExec into the subject tree
  (only `ArmExec`+`T1` are there now).
- **RQ1a axiom audit** (you, post-hoc): enumerate every `opaque`/axiom in the trusted base and
  check each against IEEE-754 — prioritize the float axioms for NaN/signed-zero unsoundness
  (cf. bug-audit bug 31). Distinct from the trivial `sorry`/`lake build` check.
- Establish ground-truth adjudication worksheet (you, post-hoc), seeded with the open printer
  discrepancies (RQ3 candidates) and the float-axiom audit results.
