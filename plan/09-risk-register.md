# Plan 09 — Risk Register

**Program:** Dark Energy as Closure — a Six Birds resolution of the cosmological paradoxes
**Status:** PLANNING / BLUEPRINT. Executed later by a separate codex-driven process; nothing here is run now.
**Scope of this file:** the consolidated, pre-registered risk register for the whole `six-birds-de-closure` build phase. It enumerates the live risks to the program, scores each as **likelihood × impact** on a fixed scale, prescribes a **mitigation** (what to do to lower the probability or contain the blast radius), and pins a **concrete fallback** (the specific degraded path taken if the risk fires, including its AOR status), and names which **experiments / plan files** each risk threatens (using the authored plan index).

**Authoritative upstream:** the SHARED GROUNDING BRIEF (`GROUNDING_BRIEF.md`, Sections I–VI), `plan/00-overview.md` (thesis, §6 gates, §8 done, §7 AOR vocabulary), and `plan/02-environment-and-deps.md` (stack pins, build footguns §2.4, environment gates G-ENV-1 … G-ENV-9). This register does not introduce new datasets, new physics, or new gates; it cross-references the gates already locked elsewhere and adds only the risk-handling discipline. Where a fallback is invoked, the **No Unstatused Residual** rule (`thm:F9`; `Audited_Operational_Realisability`) applies: the fallback is recorded as a *statused residual* in the run manifest, never silently.

**Grounding references:** `idea.md` §§5–6 (experiments, ansatz), §10 (five hard standards), UPDATE block (Hubble route matrix / holonomy); corpus `docs/papers/` (Adequacy_Residuals for the Schur-complement reconciliation, AOR for statusing, A_Six_Birds_Eye_View_of_Dark_Energy for the surrogate-backend precursor weakness).

---

## 0. How to read this register

### 0.1 Scoring scale

Likelihood (L) and impact (I) are each scored **1–5**; the priority score is `R = L × I` (1–25). The register is sorted by descending `R`. Scores are pre-registered and may not be lowered after seeing results; if a risk materializes more strongly than scored, log a deviation in the affected run manifest.

**Likelihood (L):** 1 = rare (<5%), 2 = unlikely (~15%), 3 = possible (~40%), 4 = likely (~65%), 5 = near-certain (>85%) over the lifetime of the build phase.

**Impact (I):** 1 = cosmetic (a single non-headline leg degrades), 2 = local (one experiment loses a sub-claim but still reports), 3 = experiment-level (one of E0–E8 cannot meet a headline gate), 4 = multi-experiment (several experiments or a phase gate threatened), 5 = program-level (the §6.4 coherence gate or a §6.1 reproduction gate fails ⇒ the whole phase fails or the central thesis is unsupported).

### 0.2 Status conventions for fallbacks

Every fallback below resolves to one AOR base status from `plan/00-overview.md` §7 / `GROUNDING_BRIEF.md` §VI: `zero | budgeted | bridged | hidden | moduli | selected | probabilistic | out_of_scope | nonclaim | blocked | approved_other`. A fallback that lands `unstatused` is itself a defect. An honest **negative** result (e.g. "phantom crossing required a ghost", "Ξ fragmented per probe") is a *valid scientific outcome* when statused — it is not a risk to be mitigated away, only to be reported faithfully (`plan/00-overview.md` §8 closing paragraph).

### 0.3 Risk-to-experiment index (summary)

| # | Risk | L | I | R | Primary threatened experiments / files |
|---|---|---|---|---|---|
| R1 | Ξ_cosmo reconciliation / fudge-function ambiguity (overfitting critique) | 4 | 5 | **20** | E1, E2, E3, E4, E5, E6, E7, **E8**; plan/04, plan/05 |
| R2 | Surrogate-vs-real LSS backend (precursor weakness) | 4 | 5 | **20** | **E5**, E7; downstream E4/E8 coherence; plan/02 §1.4 |
| R3 | pyccl / classy / clik build failure | 4 | 4 | **16** | E1, E5, E6, E7 (and any CMB/BAO leg); plan/02 |
| R4 | MCMC convergence + compute-budget overrun | 4 | 4 | **16** | E1–E8, esp. **E8** (PolyChord), E4, E5; leave-one-out PPD |
| R5 | DES Y6 3×2pt likelihood unavailability | 3 | 4 | **12** | **E5**, E7, E8 (growth leg); plan/03 |
| R6 | Data-version drift (releases superseded/withdrawn mid-build) | 3 | 4 | **12** | E1–E8 (all data-touching); plan/03, plan/02 lockfiles |
| R7 | Coherence gate fails: Ξ fragments per probe | 3 | 5 | **15** | **all of E1–E7 jointly**, decided at E4/E8; plan/00 §6.4 |
| R8 | Lean mechanization stalls (P1/P4 do not close) | 3 | 3 | **9** | plan/05 targets; E0/E3/E4 structural receipts |
| R9 | Hubble-route public posteriors thin / non-independent ⇒ holonomy unmeasurable | 3 | 3 | **9** | **E4**; plan/03 hubble_routes |
| R10 | Phantom-crossing false positive (Keeley) / requires real ghost (P4 fail) | 2 | 3 | **6** | **E3**; E8 stable-readout column |
| R11 | Determinism / float-reproducibility breakage | 2 | 4 | **8** | all runs; plan/02 G-ENV-3; plan/00 §8 item 8 |
| R12 | CLASS-vs-CAMB tooling route mismatch beyond tolerance | 2 | 3 | **6** | E1 reproduction gate; plan/02 G-ENV-2 |
| R13 | Scope creep / out-of-phase work (manuscript, ops harness, new physics) | 3 | 2 | **6** | program governance; plan/00 §2 |

(R7 is scored separately from R1 even though both touch coherence: R1 is the *external* methodological critique that the model is too flexible; R7 is the *internal* empirical failure mode where the single residual does not actually reuse. They have different mitigations.)

---

## 1. R1 — Ξ_cosmo reconciliation ambiguity / the overfitting "fudge-function" critique  (L4 × I5 = 20)

**Statement.** The central scientific objection to the program: "you have invented a flexible function `Ξ_cosmo(z,ℓ,p)` and fit it to whatever the anomaly is — that is a fudge function, not an explanation." Closely tied is the *reconciliation ambiguity*: the formal claim (`plan/04`) that the variational least-rewrite `Δ_SBT` (idea.md §4) **is** the Schur-complement adequacy residual `Ξ_C(D|L) = K_DD − K_DL K_LL^† K_LD` (`Adequacy_Residuals`) must hold tightly enough that `Ξ_cosmo` is a *uniquely determined* algebraic object, not a free curve. If that identification is loose or only heuristic, the whole anti-fudge defense collapses.

**Threatens.** Every experiment that fits `Ξ` (E1-B, E2, E3, E4, E5, E6, E7) and the synthesis **E8** (the model-competition verdict is meaningless if SBT-Ξ is just an over-parameterized fit). Formally threatens `plan/04` (the Reconciliation Lemma) and `plan/05` (the Lean Schur-complement target T3).

**Why L4.** This critique is *near-inevitable* from any referee; and the looseness is genuinely easy to slip into when many probes are in play. Scored 4 not 5 because the architecture already contains the defenses below.

**Why I5.** If the critique lands, the program's thesis ("one residual, not nine fudge functions", `plan/00` §0) is unsupported and the phase fails on its own terms.

**Mitigation (already locked across plan files; this register enforces it):**
1. **Hard rank ceiling.** Total free Ξ params ≤ ΛCDM + 3 (minimal) / ≤ 5–7 (full carrier); **no probe-specific free `Ξ_p`** (`plan/00` §6.2 item 1; gates G-E1-SBT, G-E2-RANK, G-E3-RANK, G-E5-RANK, G-E6-RANK, G-E7-RANK, G-E8-RANK). The kernels `K_L/K_M/K_G/K_S/K_{r,ℓ}` are *fixed probe-shared shapes*; only the global amplitudes `(a0,a1,a2)` are fit.
2. **Out-of-sample is the decisive yardstick, not in-sample χ².** `plan/00` §6.2 item 3 and the binding `G-E8-OOS-DECISIVE`: an in-sample-only win is an explicit FAIL. A fudge function cannot win leave-one-probe-out PPD; a real low-rank residual can.
3. **The same amplitudes must improve multiple residuals at once** (`G-E1-SBT-DUAL`, `G-E5-DUAL`, `G-E2-OOS`): a single `(a0,a1,a2)` improving both geometry and growth is the anti-fudge signature.
4. **The Schur-complement reconciliation is made a theorem-or-witness obligation** in `plan/04` and Lean target **T3** (`plan/05`): `Ξ_C(D|L)` PSD and exact-adequacy ⇒ trivial chain. Pin the reconciliation gate "audit cost `J(Δ)` = Schur energy of residual readout to < 1%" (`plan/04` pass gates).
5. **λ·complexity penalty** in `Δ_SBT` (idea.md §4; `plan/00` §1) is reported with every fit so the "least rewrite" claim is auditable.

**Concrete fallback.** If, after honest fitting, the single low-rank `Ξ` *cannot* simultaneously win out-of-sample on ≥1 held-out block (G-E8-OOS-DECISIVE fails) using the rank-capped form, **do not** add parameters to rescue it. Report the program verdict as a statused **negative**: the residual-reuse claim is `blocked` (the data do not support a single low-rank residual) and E8 records SBT-Ξ as not preferred. This is a legitimate scientific result (`plan/00` §8). The reconciliation lemma, if it only holds heuristically rather than as a proved/witnessed identity, is downgraded to `[C]` conditional grade in `plan/04` and the corresponding Lean claim to `recognized_grade` (plan/02 G-ENV-9) — never asserted as `[T]`.

---

## 2. R2 — Surrogate-vs-real LSS backend  (L4 × I5 = 20)

**Statement.** The precursor (`A_Six_Birds_Eye_View_of_Dark_Energy`) made its `S₈`/growth claims under a **surrogate template backend** (`y^th = y^ref + Tφ`), which the precursor itself flagged as protocol-level only and warned that "identical optima across models are plausibly an artifact of the surrogate degeneracy" (quoted verbatim in `plan/experiments/E5-growth-staging-S8.md` §1.2). idea.md §2 explicitly mandates replacing it with a real physical likelihood. The risk: the executor falls back to a surrogate (because the physical CCL/pyccl 3×2pt forward model is hard to stand up), and the staging fingerprint `∂Ξ/∂ℓ ≠ 0` becomes a backend artifact rather than physics.

**Threatens.** **E5** (the staging-fingerprint experiment, headline) directly; **E7** (MG-as-repair reuses the CCL growth backend); and via the coherence ledger, E4 (LP4 residual reuse) and **E8** (the growth row). If the growth result is a surrogate artifact, the whole "S₈ is a chart of the same Ξ" claim is unsupported.

**Why L4.** Standing up a physical 3×2pt + RSD + CMB-lensing CCL likelihood that reproduces published `S₈` is genuinely the hardest single piece of physics tooling in the program, and the surrogate is a tempting shortcut.

**Why I5.** A surrogate-backed headline `S₈` claim would repeat the precursor's central, self-acknowledged weakness and is fatal to credibility.

**Mitigation (locked in `plan/experiments/E5` §1.2, §3.3):**
1. **Physical CCL/pyccl forward model is mandatory for the headline** (transfer functions, Halofit/HMcode nonlinear `P(k)`, IA, baryons, tomographic kernels). A surrogate template basis is **forbidden** as a headline result.
2. **5-tier real-vs-surrogate decision ladder** with explicit statused fallbacks (E5 §3.3); the headline staging fingerprint is computed **only** from tier-1/tier-2 physical-CCL legs (`G-E5-NOSURR`).
3. **`G_surr` cross-check**: deliberately reproduce the precursor's surrogate degeneracy AND demonstrate the physical CCL backend breaks it (`results/E5/surrogate_vs_physical.{csv,png}`).
4. **Residual staging slope `s_Ξ^resid`** = G2 slope minus a systematics-saturated null `G_sys`, so the dependence is charged to a closure residual only when it survives the survey's own IA/baryon/photo-z systematics (E5 `D_scale` verdict).
5. **Backend gate G-E5-BACKEND** (pyccl↔CLASS agreement, plan/02 G-ENV-4): if it fails, E5 is **blocked**, not run on a surrogate.

**Concrete fallback.** A survey leg whose official likelihood is unavailable and whose covariance is not separable runs under the **explicit staged fallback** of E5 §3.3 and is statused `budgeted` or `out_of_scope` and **excluded from the headline staging fingerprint** — never relabeled as physics. If *no* survey can be run with a physical CCL likelihood (worst case), the growth chart of the program is delivered as a clearly labeled **two-paper plan** per idea.md §2: E5 reports the staging machinery + the reproduction gate only, statuses the physical staging fingerprint as `out_of_scope (deferred to backend-enabled analysis)`, and E8's growth row is marked `budgeted`. The program does not claim a physical S₈ result it did not earn.

---

## 3. R3 — pyccl / classy / clik build failure  (L4 × I4 = 16)

**Statement.** The three hardest dependencies — `classy` (Cython wrapper compiled against a specific CLASS `libclass.a`, no manylinux wheel), `pyccl` (links compiled `libccl` = GSL + FFTW3 + CLASS-as-library), and `clik`/Planck (needs `cfitsio` + Fortran) — fail to build or import. `plan/02` §2.4 lists ten footguns, headed by the NumPy 2.0 ABI break and `classy` stale-object segfaults.

**Threatens.** E1 (CLASS/CAMB + Planck), E5/E7 (pyccl), E6 (CLASS + IDE module), and any CMB/BAO leg of E2/E3/E4/E8. A build failure is a hard stop for the affected experiment.

**Why L4.** These builds break frequently in practice; the NumPy-2.0 ABI issue alone is "the single most common stack failure" (`plan/02` §2.4 item 1).

**Why I4.** Multi-experiment, but contained — it is a tooling problem with known workarounds, not a scientific failure.

**Mitigation (locked in `plan/02` §1.3–§1.4, §2):**
1. **Conda-forge prebuilt binaries first** for `pyccl` (avoids the CMake source build) and the system libs (`libgomp`, `gsl`, `fftw`, `cfitsio`) so the ABI is consistent.
2. **`numpy<2.0` pin** across the whole env (plan/02 §1.1).
3. **`make clean` before any CLASS rebuild**; verify OpenMP linked via `ldd` (footguns 2–3).
4. **Digest-pinned container** (`plan/02` §2.2) bakes the CLASS+classy build and `cobaya-install` of Planck into an image layer and runs the smoke test as the final `RUN`, so a broken stack fails to build the image — not at experiment time.
5. **CI tier T0** (plan/02 §5) imports `numpy, scipy, classy, camb, pyccl, cobaya, getdist, arviz` on every commit and asserts `numpy.__version__ < 2.0` + CLASS OpenMP.

**Concrete fallback.** For each compiled backend there is an independent second leg: **CAMB ships Fortran wheels** and is the independent Boltzmann backend (plan/02 §1.3) — if `classy` cannot be built, E1 reproduction can proceed on CAMB alone (statused: the CLASS-vs-CAMB cross-check gate G-ENV-2 becomes `out_of_scope` for that run, not a silent skip). For `pyccl`, if neither the conda-forge binary nor the source build works, the affected growth leg falls back to a **Gaussian likelihood on the published data vector + covariance** (statused `budgeted`, plan/02 G-ENV-8) — but note this collides with R2: a Gaussian-on-data-vector fallback for growth is *not* a surrogate template and is acceptable for reproduction, but the physical staging fingerprint then inherits R2's deferral. For Planck `clik`, fall back to the Planck compressed Gaussian summary (plan/02 §1.5; statused `budgeted`).

---

## 4. R4 — MCMC convergence + compute-budget overrun  (L4 × I4 = 16)

**Statement.** Chains fail to converge (`R̂ ≥ 1.01`, ESS ≤ 400) or the campaign exceeds the budgeted wall-clock/cores. The publication-tier E8 model competition is 6 models × PolyChord nested sampling at 40–100× the ΛCDM baseline cost (`plan/02` §4: 120–360 h on 64 cores), and the leave-one-out PPD battery is another 6–12×.

**Threatens.** All MCMC experiments E1–E8; most acutely **E8** (evidence via PolyChord), **E4** (7 routes × staging + loop transport, 8–15×), **E5** (scale-cut grid, 8–15×), and the leave-one-probe-out PPD battery.

**Why L4.** High-dimensional nested sampling routinely under-converges or over-runs; the full campaign is "1–2 weeks wall-clock on a 64-core cluster" (`plan/02` §4) with real risk of overrun.

**Why I4.** A non-converged chain makes a result `unaudited` (plan/02 G-ENV-5), and a budget overrun can starve the synthesis E8; but both are recoverable with staging and reruns.

**Mitigation:**
1. **Convergence is a hard gate, not a target.** `R̂ < 1.01`, ESS > 400/chain on every reported chain (plan/00 §6.1; plan/02 G-ENV-5; per-experiment G-*-CONV). PolyChord `ln Z` stable to < 0.2 across two seeds.
2. **arviz health checks early** (trace, energy, ESS) to detect non-convergence before burning the full budget (plan/02 §1.1, §3).
3. **Phased campaign** (plan/02 §4 "campaign staging"): Phase A validates the pipeline on a single ΛCDM fit (~1 day) before committing to Phase C's 1–2-week publication runs. Cheap experiments (E0 at 0.1×, Lean at <0.01×) run first.
4. **Sampler choice is fixed and recorded** per experiment (plan/02 §1.2, §4): Metropolis for fast ΛCDM/wCDM/w0wa baselines, PolyChord *only* where evidence is required (E8).
5. **`OMP_NUM_THREADS` pinned** to avoid oversubscription that changes wall-clock and (rarely) float reduction order (plan/02 §2.4 item 9).

**Concrete fallback.** If a chain will not converge within the budgeted reruns: (a) reparameterize / tighten priors within the pre-registered prior ranges and log the change; (b) if evidence (`ln Z`) is the bottleneck for E8, fall back from PolyChord nested sampling to a **BIC/AIC/DIC + thermodynamic-integration estimate** as the model-comparison yardstick and status the evidence column `budgeted` (E8 still has three independent yardsticks: evidence, OOS battery, PPC — losing one is survivable). If compute is exhausted, deliver the experiment at **reduced scope** (fewer scale-cut grid nodes in E5, fewer route loops in E4) with the descoping statused `out_of_scope`, and prioritize the binding gates (G-E8-OOS-DECISIVE, the §6.4 coherence gate) over the corroborating ones.

---

## 5. R7 — Coherence gate fails: Ξ fragments into probe-specific corrections  (L3 × I5 = 15)

**Statement.** The make-or-break empirical failure mode: the *same* `Ξ_cosmo` does **not** reduce geometry (E1/E2), growth (E5), Hubble (E4), phantom (E3), and accounting (E6) residuals coherently — e.g. the E5 `K_S` amplitude differs from the E1 `K_L`/`K_M`-implied amplitude by > 10×, or signs disagree (`plan/00` §6.4; gates G-E*-COHERE across all experiments). Distinct from R1: here the model is *honestly* low-rank but the world simply does not admit one residual.

**Threatens.** **E1–E7 jointly**, adjudicated at E4 (LP4 residual reuse, G-E4-T4) and **E8** (G-E8-COHERENCE). This is the program-level gate.

**Why L3.** It is a genuine empirical open question whether one residual reuses; possible but not the base-rate expectation given the architecture's defenses.

**Why I5.** A coherence-gate break means **the entire phase fails** (`plan/00` §6.4 fail rule).

**Mitigation:**
1. **Coherence is checked continuously, not just at E8.** A shared `results/xi_cosmo_coherence.csv` / `results/coherence_ledger/` is written by all seven real-data-Ξ members — E1-B, E2, E3, E4, E5, E6, E7 — and read forward; each experiment runs its own `G-*-COHERE` gate against E1's geometry amplitude (within 10×, consistent sign) so a fragmentation is caught early, not at the end.
2. **Amplitudes are pinned, not re-fit per probe.** E5 inherits `a0` from E1 and fits only `a1` (E5 §model ladder); E6/E7 hold `(μ,Σ)=(1,1)` and inherit `a0`. This makes the reuse falsifiable rather than fudge-able (ties to R1 mitigation).

**Concrete fallback.** If the coherence gate fails, **report it as the program's headline scientific finding**, statused: the residual-reuse claim is `blocked`, the E8 verdict is "one low-rank Ξ does not win the field", and the AOR carrier terminates below `AOR` with the fragmentation documented in the coherence matrix. Per `plan/00` §8 this is an acceptable, honest outcome — what is forbidden is hiding the fragmentation by quietly admitting per-probe `Ξ_p`.

---

## 6. R5 — DES Y6 3×2pt likelihood unavailability  (L3 × I4 = 12)

**Statement.** The DES Y6 3×2pt official likelihood (arXiv:2601.14559, `S₈=0.789±0.012`, the prime growth probe) is not publicly installable at execution time, or the public release lags the arXiv posting.

**Threatens.** **E5** (prime growth probe), E7 (DES Y6 with Y3 fallback), and the growth leg of E8.

**Why L3.** A late-2025/2026 release; public likelihood availability for the freshest releases is genuinely uncertain (the brief notes the Y3 public version released May 2024 as the fallback).

**Why I4.** E5's prime probe; but multiple substitutes exist (KiDS-Legacy, HSC Y3, DES Y3), so it degrades rather than blocks.

**Mitigation (locked in `plan/03` and `plan/02` §1.5):**
1. **DES Y3 3×2pt (arXiv:2212.00091)** is the pinned fallback — fully public `DESLikelihood`, `S₈ ~ 0.77–0.79`.
2. **Three independent growth probes** in E5 (DES Y6, KiDS-Legacy, HSC Y3) plus DESI RSD and CMB lensing, so the staging fingerprint does not hinge on any one survey.
3. **Gaussian-likelihood adapter** on the published Y6 data vector + covariance if the data vector is released but the full likelihood object is not (plan/02 §1.5).

**Concrete fallback.** Run E5 on **DES Y3 + KiDS-Legacy + HSC Y3 physical CCL likelihoods**, status the DES-Y6 substitution `approved_other` (a published, peer-reviewed equivalent probe) with a one-line justification in the manifest, and record that the headline `S₈ = 0.789±0.012` Y6 value is reported but not independently re-fit. The coherence gate and staging fingerprint are still computable on the three available physical-CCL probes.

---

## 7. R6 — Data-version drift  (L3 × I4 = 12)

**Statement.** A dataset release referenced in the brief is superseded, re-versioned, withdrawn, or its access endpoint changes between planning and execution (e.g. DESI DR2 → a DR2 v2 reanalysis, a Zenodo record updated in place, an arXiv replacement changing central values). A run that silently picks up a drifted version is non-reproducible and may compare SBT against a moving baseline.

**Threatens.** Every data-touching experiment E1–E8; the §6.1 reproduction gates (you cannot reproduce a published number if the published number moved); plan/03 manifests and plan/02 lockfiles.

**Why L3.** Over a multi-month build phase with ~15 active datasets, at least one re-versioning is plausible.

**Why I4.** Reproduction gates and cross-experiment comparisons assume a frozen data surface; drift undermines them, but the integrity tooling catches it.

**Mitigation (locked in `plan/03` §8.1 manifest schema, plan/01 G-REPO-7, plan/02 §2.3):**
1. **sha256 per raw file, verified at load; load aborts on mismatch** (plan/01 G-REPO-7, plan/03 G-DATA-7). A drifted file fails the checksum and stops the run rather than silently propagating.
2. **Per-dataset tracked manifest** records exact release/DR, arXiv version, DOI/Zenodo record ID, and access method (plan/03 §8.1); the run manifest records which dataset manifests were used (plan/02 §3, Brief §III.B).
3. **Digest-pinned container + hash-pinned lockfiles** freeze the tooling surface (plan/02 §2.3).
4. **SN-dataset-dependence is recorded, not averaged away** (plan/03 G-DATA-9): Pantheon+ vs Union3 vs DES-SN5YR are kept distinct, so a drift in one is visible against the others.

**Concrete fallback.** Pin to the **specific arXiv version / Zenodo record ID** captured in the manifest at first download and continue against that frozen snapshot (status: `selected` — a deliberate version choice). If a withdrawn dataset has no archived snapshot, drop that leg and status it `out_of_scope (dataset withdrawn)`; if a *baseline* number drifts (e.g. published DESI w0wa contour), re-run the reproduction gate against the new published value and log the baseline change as a statused deviation in the affected experiment's manifest — never compare new SBT fits against an old baseline.

---

## 8. R8 — Lean mechanization stalls  (L3 × I3 = 9)

**Statement.** The certified-theorem track (`plan/05`) does not close: P1 (T2 route-mismatch) or P4 (T5 phantom-stable-readout finite witness) fail to compile under the pinned toolchain, mathlib pin drifts, or a target needs a `sorry`.

**Threatens.** `plan/05` targets T1–T7; the structural receipts for E0 (δ/RM), E3 (stable-readout eigenvalue claim), E4 (holonomy); `plan/00` §8 done-item 5; plan/01 G-REPO-14 / plan/02 G-ENV-9.

**Why L3.** Lean proofs are finicky and mathlib pins drift; but the targets are deliberately finite/decidable witnesses, lowering the risk.

**Why I3.** Lean is "optional but pinned" (plan/02 §1.5 design principle 5); the Python pipeline runs with zero Lean dependency. A Lean stall downgrades formal claims but does not stop the empirical program.

**Mitigation (locked in `plan/05`):**
1. **Pinned toolchain (`leanprover/lean4:v4.28.0`) + pinned `lake-manifest.json` mathlib commit**, with only the Schur module importing mathlib (mathlib-free core).
2. **Targets are finite verified-computation witnesses** (decidable stable-readout certificate, finite route graph, ≥2-state / ≥3-route / ≥3-grid-node non-vacuity, plan/05 L6) — proofs by `decide`/`#eval`, not deep mathlib chases.
3. **Hard prohibition on `sorry/admit/axiom/opaque/constant`** with a grep guard + axiom-audit in CI tier T5 (plan/05 L2–L4).

**Concrete fallback.** A target that does not close as `[T]` is delivered as a **scaffold + verified-computation witness** with the residual obligation statused, and the corresponding claim is downgraded to `recognized_grade` (plan/02 G-ENV-9) / `[C]` conditional in `plan/04`. P1 and P4 are the must-close targets (`plan/00` §8 item 5); P2/P3 are scaffolds by design. If even P1/P4 stall, status the formal claim `blocked` and proceed with the empirical program — the thesis stands or falls on the data gates (R1, R7), not on Lean.

---

## 9. R9 — Hubble-route posteriors thin / non-independent ⇒ holonomy unmeasurable  (L3 × I3 = 9)

**Statement.** The route matrix `H₀^{(r,ℓ)}` (E4) is populated from public posteriors (Planck, DESI BAO, SH0ES, CCHP TRGB/JAGB, TDCOSMO, GW170817). Some routes are single-source (GW170817 is one event with a `70.0^{+12}_{−8}` uncertainty) or share underlying calibration (SN anchoring across Cepheid/TRGB/JAGB), so the route loop needed for holonomy `𝔥_γ` may be too noisy or too correlated to show a nonzero residue distinguishable from measurement error.

**Threatens.** **E4** (the Hubble holonomy / lawful-plurality pillar, central to the idea.md UPDATE block); the holonomy gate G-E4-T3 and LP3.

**Why L3.** Public posterior quality varies a lot by route; the siren leg is genuinely thin.

**Why I3.** E4 has multiple sub-claims (route/staging structure, residual reuse) beyond holonomy. But a weak holonomy measurement **fails LP3 (G-E4-T3)**, and the decisive lawful-plurality gate `G-E4-DECISIVE` requires **all** of LP1–LP5 (incl. holonomy). So weak holonomy means `G-E4-DECISIVE` does **not** pass; the result degrades to the weaker **`G-E4-ROUTEREUSE`** (model comparison + residual reuse, `[E]`/partial) — which must NOT be reported as the lawful-plurality claim (REGISTRY §11.5).

**Mitigation (locked in `plan/03` G-DATA-6 and `plan/experiments/E4`):**
1. **≥6 distinct routes and ≥1 closed loop required** for holonomy (plan/03 G-DATA-6); thin routes are flagged at data load.
2. **Mandatory Protocol_Trap honest-internalization control** (E4): the holonomy must survive bridge internalization, distinguishing a real route-holonomy from a flattenable protocol-trap artifact.
3. **Flat-control loop** (G-E4-T3 requires the control loop < 0.5σ) calibrates the measurement-error floor.
4. **Inverse-ladder H₀ route derived in E1** adds an independent, well-constrained route (plan/03, E1 outputs `inverse_ladder_H0`).

**Concrete fallback.** If no loop yields `𝔥_γ/σ_γ ≥ 2` after internalization, status the holonomy claim `moduli` (the data cannot currently resolve the loop residue). Because LP3 then fails, `G-E4-DECISIVE` cannot pass, so the Hubble pillar delivers only the weaker **`G-E4-ROUTEREUSE`** finding (`[E]`/partial: a single low-rank `Ξ_cosmo` is favored by model comparison and reused across E1/E2/E5) — explicitly **NOT** the lawful-plurality claim (which requires all of LP1–LP5 incl. holonomy). It reports "route-reuse holds but the holonomy residue is below current resolution (`moduli`), so lawful plurality is not yet established" — an honest partial result, not a silent omission.

---

## 10. R11 — Determinism / float-reproducibility breakage  (L2 × I4 = 8)

**Statement.** A rerun from a pinned manifest does not reproduce the **deterministic likelihood/forward-model evaluations bitwise** or the **committed posterior summaries to the stated tolerance** — e.g. OpenMP thread-order non-determinism, an unseeded `np.random` call, or a relock that shifts a transitive dependency. (Raw MCMC/PolyChord chains are NOT required to be bitwise-identical across environments — they are validated by statistical equivalence per REGISTRY §11.6; the risk is to the likelihood/summary layer.)

**Threatens.** All runs; the determinism gate (plan/02 G-ENV-3, plan/01 G-REPO-4/G-REPO-5), and `plan/00` §8 item 8 (at least one experiment must rerun reproducing likelihood/forward-model bitwise + committed summaries to tolerance; E0 arrays bitwise).

**Why L2.** The architecture has strong seeding discipline; breakage is more likely from a stray unseeded RNG than from the core stack.

**Why I4.** Non-reproducibility makes a result `unaudited` and breaks a definition-of-done item.

**Mitigation (locked in `plan/02` §3, plan/01 G-REPO-4–G-REPO-6):**
1. **All four seeds set** (numpy, python random, cobaya sampler, PolyChord) + `OMP_NUM_THREADS=1` + float64 for the determinism gate (plan/02 §2.4 item 9, §3).
2. **Zero bare `np.random`/`random` calls outside seeded generators** (plan/01 G-REPO-5), enforced by a lint/test.
3. **Relock acceptance gate** (plan/02 §2.3): a relocked env must reproduce the smoke-test χ² to float64 epsilon.
4. **CI tier T3** runs a short ΛCDM fit twice with identical seed and asserts the **likelihood/forward-model evaluations are bitwise identical** and the **chain summaries are statistically equivalent** (`R̂<1.01`, means/cov within MC error) — not raw samples bitwise-identical.

**Concrete fallback.** If a forward-model/likelihood path cannot be made bitwise-deterministic (e.g. an irreducibly thread-nondeterministic reduction), relax to the documented `≤ 1e-12` committed-summary tolerance (plan/01 G-REPO-4) for that run and status the residual non-determinism `budgeted` with the source identified; chains continue to be validated by statistical equivalence regardless. The §8-item-8 reproduction demonstration is then run on an experiment whose likelihood/arrays *are* bitwise reproducible (E0 is data-free and the cleanest candidate: G-E0-0.1 requires bitwise array reproduction).

---

## 11. R12 — CLASS-vs-CAMB tooling route mismatch beyond tolerance  (L2 × I3 = 6)

**Statement.** At a fixed fiducial cosmology, CLASS and CAMB disagree on observables (`D_M/r_d`, `D_H/r_d`, `C_ℓ^TT`) beyond the gate tolerance (plan/02 G-ENV-2: < 0.1% on distances, < 0.2% on `C_ℓ`), usually from mismatched conventions (`A_s` vs `ln(10^10 A_s)`, neutrino-splitting defaults, k-binning) rather than a real bug.

**Threatens.** The E1 reproduction cross-check (plan/02 G-ENV-2, `plan/experiments/E1` G-E1-REPRO-BACKEND).

**Why L2.** Convention mismatches are common but well-understood and caught by comparing observables not raw params.

**Why I3.** It is a *tooling* route mismatch that must be statused before any physical Ξ claim (plan/02 design principle 4); contained to E1's backend control.

**Mitigation (locked in `plan/02` §1.3, §2.4 item 7, G-ENV-2):**
1. **Compare physical observables at matched cosmology, not raw parameters** (plan/02 §1.3 CAMB footgun, G-ENV-2).
2. **CI tier T1** independently matches CAMB to CLASS on the same observables every commit.

**Concrete fallback.** If the residual mismatch cannot be driven below tolerance after reconciling conventions, status it as a **tooling route mismatch** (`budgeted`/`bridged`, plan/02 G-ENV-2) with the magnitude recorded, choose CLASS as the single reference backend for the affected leg, and mark the CLASS-vs-CAMB cross-check `out_of_scope` for that run — explicitly *before* any physical `Ξ_cosmo` claim is made on that leg, per the idea.md UPDATE route-mismatch logic applied at the code level.

---

## 12. R10 — Phantom-crossing false positive / P4 requires a real ghost  (L2 × I3 = 6)

**Statement.** Two distinct sub-risks for E3: (a) the apparent `w_eff < −1` crossing is a *false positive* (Keeley arXiv:2506.15091 shows non-crossing mocks can fake a crossing), or (b) the data genuinely require a *ghost* — no positive, stable rewrite operator reproduces the data-preferred crossing, so Proposition P4's stable-readout claim fails on real data.

**Threatens.** **E3** (the P4 centerpiece) and the E8 stable-readout column.

**Why L2.** E3's Leg A *constructs* a stable-readout crossing as a finite witness (which is robust); the risk is only in Leg B (does the *data*-preferred crossing admit a stable-readout operator).

**Why I3.** Outcome (b) is a legitimate negative, not a defect. Contained to E3 and its E8 row.

**Mitigation (locked in `plan/experiments/E3`):**
1. **Keeley false-positive control** (G-E3-FALSEPOS): the data crossing significance must exceed the non-crossing-mock false-positive band (~3.2% reference).
2. **Dinda global-Bayesian control** (G-E3-BAYES): the crossing preference must persist under global model comparison, not in-sample Δχ² alone.
3. **Stable-readout certificate** (density positivity, operator PSD, spectral `max Re λ ≤ 0`) is the *definition* of the pass, with a Lean finite witness (T5).

**Concrete fallback.** If the data-preferred crossing cannot be realized by any positive, stable rewrite operator (the stable-readout certificate fails on Leg B), status the result `blocked` ("data require a ghost / P4 fails on data") — an **honest negative** that is a valid scientific result (`plan/experiments/E3`, `plan/00` §8). Leg A's *constructed* finite stable-readout witness still stands as the P4 `[T]` existence proof; the program reports that a stable-readout crossing is *possible* even if this dataset does not select it.

---

## 13. R13 — Scope creep / out-of-phase work  (L3 × I2 = 6)

**Statement.** The executor drifts into out-of-scope activity that `plan/00` §2 and the hard constraints forbid in this phase: writing the prose manuscript, invoking the `ops/` dispatch harness or codex, writing to a memory store, or inventing new datasets / new physics beyond the locked `Ξ_cosmo` ansatz.

**Threatens.** Program governance / phase discipline; risks diluting effort away from the binding gates and violating the hard constraints.

**Why L3.** Tempting, especially the manuscript and "just one more parameter" ansatz enlargement.

**Why I2.** Wastes effort and can violate constraints, but does not by itself invalidate the science if caught.

**Mitigation (locked in `plan/00` §0, §2):**
1. **Build-not-write phase** is stated up front; LaTeX section drafts are out of scope (plan/00 §0, §2).
2. **Ansatz is fixed by idea.md §5 + UPDATE block** and "may only be specialized, not enlarged without a logged justification" (plan/00 §2).
3. **No ops harness / codex / memory store / new datasets** (plan/00 §2 out-of-scope list; this task's hard constraints).

**Concrete fallback.** Any ansatz enlargement that proves unavoidable must be **logged as a statused deviation** with justification (plan/00 §2) and counted against the rank ceiling (R1). Manuscript/prose work is deferred to the later phase that consumes the E8 matrix and AOR master; if it is started, it is reverted and the artifacts (tables/figures/ledgers) are the only deliverables this phase commits.

---

## 14. Residual-risk summary and acceptance

After mitigation, the program's **irreducible** scientific risks are R1 (the fudge-function critique) and R7 (coherence-gate fragmentation) — both are scored I5 because they bear directly on the thesis, and both have the *same* honest fallback: if the single low-rank `Ξ_cosmo` cannot win out-of-sample with reused amplitudes, that negative is **reported and statused**, not engineered away. The tooling risks (R3, R4, R11, R12) and data risks (R5, R6, R9) are all containable to `budgeted`/`approved_other`/`out_of_scope`/`moduli` statuses without invalidating the program, because the architecture provides independent second legs (CAMB vs CLASS, three growth probes, multiple SN compilations, multiple H₀ routes) and a digest-pinned reproducible container.

**Acceptance bar for the phase (ties to `plan/00` §8):** the phase is deliverable even with several risks fired, *provided* (i) every fired risk's fallback is statused (zero `unstatused` entries, `thm:F9`); (ii) the §6.1 reproduction gates passed before any SBT object was added; and (iii) the binding decision gates — `G-E8-OOS-DECISIVE` (out-of-sample win) and the §6.4 coherence gate — are evaluated honestly and their verdict (positive *or* negative) is committed.

---

## 15. Consistency check against upstream

- **Scores and fallbacks reference only gates already locked** in `plan/00` (§6.1–§6.4, §7 AOR vocabulary, §8 done), `plan/02` (G-ENV-1 … G-ENV-9, §2.4 footguns, §4 budget, §5 CI tiers), `plan/03` (G-DATA-* and dataset fallbacks), and the per-experiment files (G-E1-* … G-E8-*, G-E4-T1–G-E4-T5). No new gate or threshold is introduced here.
- **AOR statuses** used in every fallback are drawn verbatim from the `plan/00` §7 / Brief §VI vocabulary; No-Unstatused-Residual (`thm:F9`) is the governing rule for all fallbacks.
- **The risk-to-experiment index (§0.3)** uses the authored plan/experiments file IDs E0–E8 and the plan/00–plan/05 numbering exactly as in the index.
- **R2 (surrogate backend)** and **R5 (DES Y6)** are consistent with `plan/experiments/E5-growth-staging-S8.md` §1.2/§3.3 and `plan/03` fallbacks; **R3/R4/R11/R12** with `plan/02` §1.3–§1.4/§2.4/§4/§6; **R1/R7** with `plan/04` (reconciliation) and `plan/00` §6.2/§6.4; **R8** with `plan/05` L1–L9; **R9** with `plan/03` G-DATA-6 and `plan/experiments/E4`; **R10** with `plan/experiments/E3` controls.
