# Artifact Reproducibility Record

Everything needed to rebuild and re-verify the artifact for paper submission. Captured
2026-06-21. Companion to `study-protocol.md` (the experiment) and `generation-algorithms.md`
(the generators). **Read §0 first** — the artifact has two reproducibility regimes.

## 0. Two reproducibility regimes

- **A — Deterministic (bit-reproducible).** The verified compiler, its Lean proofs, and the
  **seeded** test harnesses (T1, T2, …). A clean clone at the pinned commits rebuilds to
  identical results; a `(technique, seed)` pair reproduces any harness finding exactly.
- **B — The agent study (NOT bit-reproducible).** LLM agent sessions are inherently
  non-deterministic, and the model evolves. Reproducibility here means three concrete things:
  1. the **archived per-session artifacts** (transcript + metrics record + `FINDINGS.md` +
     repro cases) are kept verbatim;
  2. every finding has a **deterministic repro case** (regime A) so anyone can re-verify *that
     specific bug* independent of any agent;
  3. the harness + prompts + budgets are kept so the study can be **re-run** for
     statistically-comparable (not identical) results.
  The exact **agent model is pinned and recorded per session** (`metrics_parse.py` captures
  `message.model`; see §5). Quote the model in the paper; do not claim bit-reproducibility of
  agent runs.

## 1. Environment (exact, as used)

| Component | Version |
|-----------|---------|
| Lean | `leanprover/lean4:v4.28.0` (commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`, `arm64-apple-darwin`) — pinned by `lean-toolchain` |
| Lake | `5.0.0-src+7e01a1b` |
| mathlib | rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365` — pinned by `lake-manifest.json` |
| C compiler (T1 co-sim) | Apple clang 16.0.0 (`clang-1600.0.26.6`), target `arm64-apple-darwin24.1.0` |
| Python (study harness) | 3.14.4 used; harness is **stdlib-only**, any 3.9+ works |
| OS / arch | macOS, Darwin 24.1.0, **arm64** (T1 assembles + runs real AArch64 — an arm64 host is required) |
| Agent | Claude Code, model **`claude-opus-4-8`** (recorded per session in the metrics) |

> T1 (assembly co-simulation) **requires an Apple-silicon / AArch64 host** — it assembles the
> compiler's printed asm with `cc` and runs it natively. The proofs and T2/T3/T4 are
> host-independent.

## 2. Repositories & commits (pinned)

| Repo | Remote | Branch / HEAD | Role |
|------|--------|---------------|------|
| CredibleCompilation | `github.com/rinard/CredibleCompilation` | `fix/cert-checker-completeness` @ `dfc90f7` | development tree: full compiler + proofs + `Harness/` + `plans/` |
| CredibleCompilationICSEBase | `github.com/rinard/CredibleCompilationICSEBase` | `main` @ `a3f6de4` | **study subject** — May-7 baseline; **content = upstream `d869719` (2026-05-07)**, history severed for quarantine |
| CredibleCompilationRN | `github.com/rinard/CredibleCompilationRN` | `main` @ `632c869` | minimal shipped-compiler extract (what the shipped binary runs + its proofs) |
| CredibleCompilationReproCases | *(to create)* | — | one dir per `finding-id`, tagged by subject commit; deterministic repro inputs (regime B item 2) |
| study-harness | *local `/Users/mr/study-harness` — commit/archive it* | — | launcher, metrics, prompts (§5) |

## 3. Build from a clean clone (regime A)

```
git clone <repo>; cd <repo>
# lean-toolchain auto-selects Lean v4.28.0 via elan
lake exe cache get          # fetch prebuilt mathlib oleans (avoids a multi-hour rebuild)
lake build                  # expect: 0 errors, 0 sorry  (dev tree ~3139 jobs)
```
`lake-manifest.json` pins the mathlib rev and **must be committed**; `lake exe cache get` is
keyed to it. If the mathlib cache is ever unavailable, `lake build` rebuilds mathlib from source
(hours) — for long-term archival, consider bundling the prebuilt `.lake` oleans.

## 4. Reproduce each result (regime A — deterministic)

| Result (RQ) | Command | Expected |
|-------------|---------|----------|
| **Proof soundness, RQ1a** | `lake build` ; `grep -rnE "\bsorry\b\|^\s*axiom " CredibleCompilation/` | 0 `sorry`; only the **known float axioms** appear (these are the RQ1a audit targets — see findings doc / bug-31) |
| **Verified evaluator** | `lake env lean Harness/ArmExec.lean` | clean (no errors) ⇒ `execStep_sound` / `execRun_sound` hold |
| **T1 co-sim, RQ2** | `lake env lean --run Harness/T1.lean` (and `T1Branch/T1Stack/T1Array`) | `=== T1: 200 …, 0 divergences ===` on the **correct** (dev) model |
| **T1 catches the shift bug** | port `Harness/{ArmExec,T1}.lean` into the **baseline** tree + run | `DIVERGENCE … model=0 machine=<masked>` (the May-7 unmasked-shift bug) |
| **T2 round-trip, RQ3** | `lake env lean --run Harness/T2.lean` | printer↔parser syntax findings (var-block / if-else / while) — see findings doc `## T2` |

All harnesses are seeded by an LCG (constants in `generation-algorithms.md` §Common PRNG); the
seed range is in each `main`. A finding's seed + emitted `.s`/`.c` reproduce it deterministically.

## 5. Run / re-run the agent study (regime B)

Per technique, one autonomous session (budgets from `study-protocol.md` §7):

```
study-harness/run_session.py \
  --task t1 --work-dir <subject-tree> --prompt study-harness/prompts/t1.md \
  --out study/metrics.jsonl --max-wall-seconds 7200 --max-output-tokens 670000
# T1/T2/T3: 7200s / 670000 ;  T4: 43200s / 4000000
```
Live: `tail -f <subject>/FINDINGS.md` and `study-harness/metrics_parse.py --follow study-harness/transcripts/t1.jsonl`.

**Archived per session (all required for the artifact):**
- `study-harness/transcripts/<task>.jsonl` — full stream-json transcript (includes the model).
- one JSONL line in `study/metrics.jsonl` — resource record incl. `model`, `budget_hit`,
  discovery/fix token split, build counts, post-hoc adjudication fields.
- `<subject>/FINDINGS.md` — the agent's first-person findings log.
- `<subject>/repro/<id>/` → committed to **CredibleCompilationReproCases** (tagged by subject commit).
- `study/findings/<id>/` — your post-hoc review narrative + adjudication.

## 6. Determinism & seeds (the honesty paragraph for the paper)

The compiler, proofs, and harness findings are **deterministic** (seeded LCG; fixed Lean +
mathlib). The agent's discovery/fix *behavior* is **not** reproducible bit-for-bit — it depends
on the model and sampling. We therefore (a) pin and report the model, (b) archive every
transcript and metrics record verbatim, and (c) attach a deterministic repro case to every
finding so each bug is independently re-verifiable without re-running an agent. Re-running the
study reproduces the *qualitative* result (which defect classes each technique surfaces, the
saturation behavior, the resource profiles), not identical traces.

## 7. Artifact bundle manifest

Produce the submission bundle as **git bundles at the pinned commits** + the study outputs:
```
artifact/
  CredibleCompilation.bundle            # git bundle @ dfc90f7  (or RN extract for a smaller artifact)
  CredibleCompilationICSEBase.bundle    # @ a3f6de4  (study subject)
  CredibleCompilationReproCases.bundle  # all repro cases
  study-harness/                        # run_session.py, metrics_parse.py, prompts/
  study/                                # metrics.jsonl, findings/, saturation/
  transcripts/                          # per-session stream-json
  plans/                                # study-protocol.md, generation-algorithms.md,
                                        #   cert-checker-findings.md, this file
  README.md                             # entry point: §3 build + §4 reproduce + §5 study
  SHA256SUMS                            # checksums of every bundle + output file
```
`git bundle create X.bundle --all` per repo; `shasum -a 256 *` → `SHA256SUMS`. Optionally include
the prebuilt mathlib `.lake` oleans for offline build.

## 8. Status: recorded now vs produced when the study runs

- **Reproducible now:** the proofs (RQ1a), the verified evaluator + soundness, **T1** (RQ2 +
  the baseline shift-bug demo), **T2 v1** (RQ3 findings), **T3 v1** (parser totality), **T4a**
  (`stress/t4_run.py`, int+float differential), **T4b** (`stress/t4b_harvest.py`), **T4c**
  (`certmutate`+`soundness_campaign.sh`), **EMI** (`emi`+`emi_campaign.sh`); the orchestration
  tooling (launcher + metrics, self-tested); the generation-algorithms doc. All instruments built.
- **Produced when the study runs (must be archived then, per §5):** the per-technique
  transcripts, `metrics.jsonl`, `FINDINGS.md`, repro cases, post-hoc adjudication/audit records,
  and the saturation curves.
- **Documented extensions (not blocking a run):** T2 float/bool/array/control coverage (deeper
  round-trip is gated on fixing the printer↔parser desync T2 found); T3 hang-detection; EMI-float
  tolerant compare; building the `certaudit`/`certmutate`/`emi` exes against the May-7 baseline
  (the subject ships only `compiler`) for on-subject T4b/c.

## 9. Reproduction checklist (artifact evaluator)

- [ ] Clone the repos at the pinned commits (§2); confirm `lean-toolchain` + `lake-manifest.json`.
- [ ] `lake exe cache get` && `lake build` → 0 errors, 0 `sorry` (§3).
- [ ] Axiom audit: only the documented float axioms present (§4, RQ1a).
- [ ] `lake env lean Harness/ArmExec.lean` clean (evaluator soundness).
- [ ] Run T1 harnesses → 0 divergences on the dev model; baseline port → the shift-bug divergence.
- [ ] Run `Harness/T2.lean` → the recorded printer↔parser findings.
- [ ] (Regime B) re-verify N archived repro cases from CredibleCompilationReproCases, and/or
      re-run one `run_session.py` session and confirm a non-empty `FINDINGS.md` + metrics record.
- [ ] Verify `SHA256SUMS`.
