# Plan 01 — Implementation Repository Layout and Conventions

> **Status:** PLANNING / BLUEPRINT. This file specifies the repository structure, naming, and
> determinism/reproducibility conventions for the Six Birds dark-energy-as-closure (SBT-DE) program.
> It is to be **executed later** by a separate codex-driven process; nothing here is run now.
>
> **Consistency anchors:** Conforms to `GROUNDING_BRIEF.md` (canonical dataset list, software
> stack, determinism standards, AOR audit gates) and to `idea.md` (the full program: §1–10 plus the
> UPDATE block on the Hubble readout field, Hubble holonomy, route matrix, and lawful plurality).
> Experiment IDs **E0–E8** are exactly those defined in the GROUNDING_BRIEF Part 2.
>
> **Scope of this file:** *only* the repository skeleton, module boundaries, naming, determinism
> rules, and the committed-vs-ignored deliverable policy. It does **not** specify the physics of any
> experiment (those live in `plan/experiments/E#.md`), nor the math of `Xi_cosmo` (that is plan
> 02+). This file is the contract every other plan and every runner must obey.

---

## 1. Purpose and design principles

The repository must let a **reviewer reproduce every numerical claim and figure without re-running any
expensive inference**. The build of trust is layered:

1. **Reproduce-without-rerun (primary).** Every experiment commits its final numeric results (tables,
   summary JSON, posterior summaries) and figures. A reviewer reads `results/` and the per-experiment
   `outputs/` and can audit all pass/fail gates from committed artifacts alone.
2. **Reproduce-by-rerun (secondary).** Every experiment is config-driven and seed-pinned, so a
   reviewer *with compute* can regenerate the deterministic forward-model/likelihood products bitwise
   and chains that are **statistically equivalent** (means/cov within MC error; not bitwise identical;
   REGISTRY §11.6) from `configs/` + `experiments/<E#>/config.yaml` + a pinned environment lockfile.
3. **Audit-as-first-class (SBT-specific).** Per `idea.md` §10 standard-of-evidence and the AOR
   carrier (`Audited_Operational_Realisability`), every result carries an **AOR status** and an
   audit ledger. No tension is left "unstatused" (`idea.md` §2: "No Unstatused Residual").

Design rules:

- **One Python package, many thin runners.** All physics/math lives in the installable package
  `sbt_cosmo/`. `experiments/<E#>/run.py` are *thin orchestrators* that import the package, read a
  config, and write artifacts. No physics is implemented inside a runner.
- **Config-driven, not argument-driven.** A run is fully determined by a committed YAML config plus a
  declared environment lock. No behavior depends on CLI flags beyond `--config` and `--outdir`.
- **The same `Xi_cosmo` everywhere.** The residual + rewrite operator is a single module
  (`sbt_cosmo/xi/`) imported by all experiments. The cross-experiment coherence gate (GROUNDING_BRIEF
  Part 4) is enforced *structurally* by forbidding per-experiment redefinitions of the residual.
- **Four audits are library functions.** `delta` (idempotence), `RM` (route mismatch), `LG`
  (local–global gluing), `PPD` (cross-probe posterior-predictive) are implemented once in
  `sbt_cosmo/audits/` and reused by every experiment that reports them.

---

## 2. Top-level tree

```
six-birds-de-closure/
├── README.md                      # tracked — repo map, how to reproduce-without-rerun
├── pyproject.toml                 # tracked — package metadata + pinned dep ranges; defines `sbt_cosmo`
├── requirements.lock              # tracked — fully pinned transitive lock (pip freeze / uv lock)
├── environment.yml                # tracked — conda env (CLASS/CAMB/CCL system deps)
├── .gitignore                     # tracked — see §8 for exact rules
├── .gitattributes                 # tracked — text/line-ending normalization; mark *.npy/*.h5 binary
├── CITATION.cff                   # tracked — citation + corpus DOIs
├── idea.md                        # tracked (exists) — research program
│
├── docs/
│   └── papers/                    # tracked (exists) — corpus .tex + INDEX.md
│
├── plan/                          # tracked — THIS planning layer (blueprints, not code)
│   ├── GROUNDING_BRIEF.md         # tracked (exists) — canonical grounding (datasets/stack/gates)
│   ├── REGISTRY.md                # tracked — machine-checkable source of truth (conventions)
│   ├── 01-repo-structure.md       # THIS FILE
│   ├── 02-*.md ...                # later plan files (Xi math, audits, per-experiment specs)
│   └── experiments/               # per-experiment blueprint specs E0.md … E8.md (tracked)
│
├── sbt_cosmo/                     # tracked — THE Python package (all physics + audits + Xi)
│   └── … (see §3)
│
├── lean/                          # tracked — Lean 4 project for certified closure receipts (see §5)
│   └── …
│
├── configs/                       # tracked — shared/base configs reused across experiments (see §6)
│   └── …
│
├── data/                          # MOSTLY gitignored — raw vs processed; provenance committed (§4)
│   ├── raw/                       # gitignored payloads
│   ├── processed/                 # gitignored payloads
│   ├── manifests/                 # TRACKED — provenance + checksum manifests (no payload)
│   └── README.md                  # tracked — how to fetch each dataset
│
├── experiments/                   # per-experiment dirs E0 … E8 (config+runner TRACKED, see §7)
│   ├── E0_synthetic/
│   ├── E1_desi_dr2_repro/
│   ├── E2_distance_duality/
│   ├── E3_phantom_crossing/
│   ├── E4_hubble_route_holonomy/
│   ├── E5_growth_staging_s8/
│   ├── E6_ide_accounting/
│   ├── E7_modified_gravity/
│   └── E8_model_competition/
│
├── results/                       # TRACKED — cross-experiment tables/figures + per-E# posterior summaries
│   ├── <E#>/posteriors/           # TRACKED — committed posterior summaries (mean/cov/thinned + sha256)
│   └── …
│
├── runs/                          # GITIGNORED — raw sampler chains (reproducibility byproducts; no gate depends)
│   └── **/chains/*.hdf5           # gitignored raw chains; never an authority for any gate (REGISTRY §7)
│
├── tests/                         # tracked — unit/integration/determinism/audit-contract tests
│   └── …
│
└── ops/                           # tracked (exists) — dispatch harness (NOT used by this program)
```

> **Note on `ops/`:** It exists in the repo but is explicitly **out of scope** for this program per
> the hard constraints (no ops dispatch harness, no memory store, no external agents). Plans must not
> add to or invoke `ops/`.

---

## 3. The `sbt_cosmo/` package

A single installable package (`pip install -e .` via `pyproject.toml`). Submodules map 1:1 onto the
formal objects of the Cosmological Closure Carrier
`𝔉_cosmo = (X, T, {f_p}, U_θ, E_{θ,p}, R, A)` (`idea.md` §4; GROUNDING_BRIEF Part 1).

```
sbt_cosmo/
├── __init__.py                    # version string, public API surface
├── constants.py                   # physical constants, unit conventions (all SI / km s^-1 Mpc^-1)
│
├── background/                    # FLRW completion U_θ + distances  (the "completion" layer)
│   ├── __init__.py
│   ├── flrw.py                    # H(z), E(z); ΛCDM / wCDM / w0wa (CPL) backgrounds
│   ├── distances.py               # D_C, D_M, D_A, D_L, D_H, comoving volume; r_d / sound horizon
│   ├── boltzmann.py               # thin wrapper over CLASS (classy) / CAMB; backend-selectable
│   └── duality.py                 # eta(z) = D_L / [(1+z)^2 D_A]  (CDDR readout, for E2)
│
├── growth/                        # growth-of-structure lens (the S8 / WL / RSD predictions)
│   ├── __init__.py
│   ├── linear.py                  # D(z), f(z), sigma8(z), f*sigma8(z)
│   ├── power.py                   # P(k,z) via CCL/pyccl; nonlinear (Halofit) hooks
│   ├── projection.py              # Limber / 3x2pt projections, scale cuts ℓ_min/ℓ_max
│   └── s8.py                      # S_8 = sigma8 sqrt(Om/0.3); staging-indexed readout (for E5)
│
├── probes/                        # lens family {f_p}: per-probe forward models + likelihoods
│   ├── __init__.py
│   ├── base.py                    # Probe ABC: .data_vector, .covariance, .model(theta), .loglike
│   ├── cmb.py                     # Planck2018 / SPT-3G(2018|D1) / ACT DR6 likelihood wrappers
│   ├── bao.py                     # DESI DR2 / DES Y6 / KiDS-Legacy BAO; D_M/r_d, D_H/r_d
│   ├── sn.py                      # Pantheon+ / Union3 / DES-SN5YR distance-modulus likelihood
│   ├── weaklensing.py             # DES Y6 / KiDS-Legacy / HSC Y3 cosmic shear (3x2pt)
│   ├── rsd.py                     # DESI DR2 full-shape / DES Y6 RSD; f*sigma8
│   └── ladder.py                  # local H0 routes: SH0ES, CCHP TRGB/JAGB, TDCOSMO, sirens
│
├── xi/                            # THE closure residual Ξ_cosmo + rewrite operator (the "R")
│   ├── __init__.py
│   ├── residual.py                # Xi_cosmo(z, ell, p): low-rank ansatz, ≤5–7 free params (§3 brief)
│   ├── kernels.py                 # observable-correction kernels K_L,K_M,K_G,K_S and K_{r,ℓ}
│   ├── rewrite.py                 # ΔΞ_SBT least-audit-closed rewrite operator; w_eff(z) readout
│   └── stability.py               # stable-readout (no-growing-mode) certificate: max Re λ ≤ 0 + operator PSD + ρ_eff > 0 (for E3 phantom crossing)
│
├── audits/                        # the four residual audits — ONE implementation, reused everywhere
│   ├── __init__.py
│   ├── delta.py                   # δ_p = d(E^2, E)  (packaging idempotence defect)
│   ├── route_mismatch.py          # RM_p = d(E T, T_θ E)  (does coarse-graining commute w/ dynamics)
│   ├── local_global.py            # LG_{p,q} = d(glue(f_p,f_q), global FLRW)  (gluing obstruction)
│   ├── ppd.py                     # PPD_{p→q} = d(q_obs, q_pred_from_p)  (cross-probe predictive)
│   └── metrics.py                 # the metric d(·,·): χ², KL, posterior-pushforward distances
│
├── hubble/                        # Hubble readout field, route matrix, holonomy (idea.md UPDATE)
│   ├── __init__.py
│   ├── routes.py                  # route registry r=(probe,anchor,z-depth,lens,completion,bridge)
│   ├── route_matrix.py            # H_0^{(r,ℓ)} table builder; rows=routes, cols=staging/bridge ℓ
│   ├── transport.py               # bridge transport B_γ between route posteriors
│   └── holonomy.py                # 𝔥_γ = transport-around-loop residual; lawful-plurality tests
│
├── inference/                     # sampling + model comparison orchestration (cobaya/polychord)
│   ├── __init__.py
│   ├── cobaya_iface.py            # build cobaya inputs from a config; likelihood registration
│   ├── samplers.py                # MCMC / nested-sampling wrappers; seed plumbing
│   ├── evidence.py                # log-evidence, BIC, AIC, Bayes factors (for E8)
│   └── convergence.py             # Gelman–Rubin R̂, ESS, KL-to-reference diagnostics
│
├── aor/                           # Audited Operational Realisability carrier (status ledger)
│   ├── __init__.py
│   ├── status.py                  # 11 base + 4 asymptotic statuses (GROUNDING_BRIEF §6 vocab)
│   ├── carrier.py                 # PreSB→RefStableAOR→CascadeStableAOR→AOR progression record
│   └── ledger.py                  # writes AOR status table (mandatory per-paper/per-run format)
│
├── io/                            # data + artifact I/O, provenance, run manifests
│   ├── __init__.py
│   ├── datasets.py                # loaders honoring data/manifests/*.json; checksum verification
│   ├── manifest.py                # run-manifest JSON writer (schema in §9)
│   ├── artifacts.py               # standard writers: .npy / .h5 / .json / .csv table dumps
│   └── checksums.py               # sha256 helpers for data + output integrity
│
├── viz/                           # figure generation (deterministic, seeded styling)
│   ├── __init__.py
│   ├── triangle.py                # getdist triangle/contour plots
│   ├── residual_plots.py          # Xi staging fingerprints, ∂Xi/∂ℓ, route-matrix heatmaps
│   └── style.py                   # fixed matplotlib rcParams; fixed colormaps; no random styling
│
└── cli.py                         # `sbt-cosmo run --config ... --outdir ...` entrypoint
```

### Module-boundary contract

| Module | Formal object (idea.md §4 / UPDATE) | Imports allowed from | Must NOT import |
|---|---|---|---|
| `background/` | FLRW completion `U_θ`, distances | `constants` | `probes`, `inference`, `xi` |
| `growth/` | growth lens predictions | `background`, `constants` | `probes`, `inference` |
| `probes/` | lens family `{f_p}`, likelihoods | `background`, `growth`, `xi`, `audits.metrics` | `inference`, `experiments` |
| `xi/` | residual `Ξ_cosmo`, rewrite `R` | `background`, `constants` | `probes`, `inference` |
| `audits/` | δ, RM, LG, PPD | `probes`, `xi`, `background`, `growth` | `inference`, `experiments` |
| `hubble/` | readout field, route matrix, holonomy | `probes.ladder`, `inference`, `xi`, `audits` | `experiments` |
| `inference/` | sampling, evidence | everything physical | `experiments` |
| `aor/` | AOR status ledger | none (pure) | physical modules |
| `io/`, `viz/` | I/O + figures | physical modules | `experiments` |

**Hard rule:** nothing under `experiments/` is importable by the package. Dependency arrows point
*into* the package only. This is enforced by an import-linter test (§10).

---

## 4. `data/` — raw vs processed, provenance-only tracking

```
data/
├── raw/            # gitignored — original downloads exactly as released
│   ├── desi_dr2_bao/        ├── planck_2018/        ├── pantheon_plus/   …
├── processed/      # gitignored — derived data vectors + covariances in internal format (§ V brief)
│   ├── <probe>/data_vector.npy
│   ├── <probe>/covariance.npy
│   └── <probe>/meta.json
├── manifests/      # TRACKED — one JSON per dataset; provenance + checksums, NO payload
│   ├── desi_dr2_bao.json
│   ├── planck_2018.json
│   └── …  (one per dataset in GROUNDING_BRIEF §I)
└── README.md       # TRACKED — exact fetch instructions per dataset (arXiv/DOI/Zenodo URLs)
```

**Rules:**

- `data/raw/` and `data/processed/` payloads are **gitignored** (large, license-bound, re-fetchable).
- `data/manifests/*.json` are **tracked** and are the single source of truth for *what* data a run
  used. Each manifest captures the exact release (arXiv/DOI), access method, file list, sha256 per
  file, internal-format shapes, and the processing-script commit hash. Schema:

```json
{
  "dataset": "DESI_DR2_BAO",
  "release": "arXiv:2503.14738",
  "access": "arXiv ancillary / desilike",
  "fetched_utc": "2026-05-29T00:00:00Z",
  "raw_files": [{"path": "data/raw/desi_dr2_bao/bao_table.txt", "sha256": "…", "bytes": 12345}],
  "processed": {"data_vector": {"path": "data/processed/desi_dr2_bao/data_vector.npy",
                                "sha256": "…", "shape": [15], "dtype": "float64"},
                "covariance": {"path": "…", "sha256": "…", "shape": [15, 15], "dtype": "float64"}},
  "processing_script": "sbt_cosmo/io/datasets.py",
  "processing_commit": "<git-sha>",
  "fallback": "DESI published likelihood `desilike` (GROUNDING_BRIEF §I.A)"
}
```

- `data/README.md` lists every dataset from GROUNDING_BRIEF §I with its fetch URL and the fallback to
  use if the primary is unavailable.
- **Integrity gate:** any run loading a dataset re-verifies the file sha256 against its manifest
  before use; mismatch is a hard error (`io/checksums.py`). This makes the committed manifests a
  verifiable provenance record even though payloads are not in git.

---

## 5. `lean/` — formal closure receipts

A standalone Lean 4 project (Lake-managed) producing **certified audit receipts** for the claims that
admit mechanization, per the corpus pattern (Lean + Python, e.g. `Foundations_IV`, `AOR`,
`Holonomy_with_Memory`). Lean is **not** on the critical path for the numerical pipeline — it
certifies discrete/structural lemmas only.

```
lean/
├── lakefile.lean                  # tracked — Lake build; mathlib pinned (toolchain in lean-toolchain)
├── lean-toolchain                 # tracked — exact Lean version (≥4.0.0; corpus tested v4.28.0)
├── lake-manifest.json             # tracked — pinned mathlib revision
├── SbtCosmo/
│   ├── Idempotence.lean           # δ-defect: E∘E = E fixed-point lemmas (packaging closure)
│   ├── RouteMismatch.lean         # RM certification on finite toy carriers (E0)
│   ├── Holonomy.lean              # loop-transport non-triviality (Hubble holonomy 𝔥_γ ≠ 0)
│   ├── PhantomStableReadout.lean        # `phantom_stable_readout_witness`: finite stable-readout (no-growing-mode) certificate for the rewrite operator (E3); negative-kinetic-DOF exclusion is out_of_scope
│   └── AORStatus.lean             # status-assignment well-formedness (no unstatused residual)
└── README.md                      # tracked — what each receipt certifies; `lake build` to check
```

**Rules:** Lean sources tracked; the `.lake/` build cache is gitignored. A green `lake build` is the
receipt; the CI/audit step records the toolchain + mathlib revision in the run manifest under
`audit_status`.

---

## 6. `configs/` — shared/base configs

Shared building blocks composed by per-experiment configs (DRY). Per-experiment configs live under
`experiments/<E#>/config.yaml` and *include/override* these.

```
configs/
├── base.yaml              # global determinism + I/O defaults (seeds policy, float64, outdir layout)
├── backends.yaml          # boltzmann backend choice (CLASS|CAMB) + accuracy settings (pick ONE/team)
├── datasets/              # one YAML per dataset: path-to-manifest, scale cuts, fallback policy
│   ├── desi_dr2_bao.yaml  ├── planck_2018.yaml  ├── pantheon_plus.yaml  …
├── models/                # parameterizations: lcdm.yaml, wcdm.yaml, w0wa.yaml, ide.yaml,
│   │                      #   mg_mu_sigma.yaml, sbt_xi.yaml  (the Ξ_cosmo low-rank model)
├── samplers/              # mcmc.yaml, polychord.yaml — convergence targets, live points, seeds
└── priors/                # parameter priors shared across experiments
```

**Rule:** every config carries an explicit `seed` block and a `schema_version`. Configs are tracked.
A config plus `requirements.lock` plus the dataset manifests fully determine a run.

---

## 7. `experiments/<E#>/` — config + runner + recorded outputs

Each experiment is a self-contained directory. The nine experiments are exactly E0–E8 from
GROUNDING_BRIEF Part 2. Directory naming: `E<n>_<slug>` (table in §2).

```
experiments/E1_desi_dr2_repro/
├── config.yaml         # TRACKED — fully determines the run (includes configs/*, sets seeds, model)
├── run.py              # TRACKED — thin orchestrator: load config → sbt_cosmo API → write outputs
├── README.md           # TRACKED — charter, link to plan/experiments/E1.md, pass/fail gate summary
└── outputs/            # mixed tracking — see policy below
    ├── manifest.json           # TRACKED — run manifest (§9 schema)
    ├── summary.json            # TRACKED — scalar results + pass/fail gate evaluations
    ├── tables/*.csv            # TRACKED — final numeric tables (χ², BIC, posterior summaries)
    ├── figures/*.png|*.pdf     # TRACKED — committed figures (triangle, residual, route-matrix)
    ├── aor_status.json         # TRACKED — AOR status ledger for this run
    ├── posterior_summary.npz   # TRACKED — means/cov/quantiles (SMALL derived summary)
    └── chains/                 # GITIGNORED — full MCMC chains / nested-sampling raw output (LARGE)
```

### The reproduce-without-rerun rule (mandatory)

> Every experiment **must commit** the artifacts a reviewer needs to verify all of its pass/fail
> gates **without re-running inference**: `manifest.json`, `summary.json`, all `tables/*.csv`, all
> `figures/*`, `aor_status.json`, and `posterior_summary.npz`. The full `chains/` are gitignored
> (regenerable from `config.yaml` + lockfile + seeds). A gate verifier (`tests/test_gates.py`) reads
> only the committed artifacts and re-checks each numeric threshold.

### Runner contract

- `run.py` signature: `python experiments/E#/run.py --config config.yaml --outdir outputs/`.
- It must (in order): (1) load config, (2) verify dataset checksums vs manifests, (3) set all seeds
  from config (§9), (4) call `sbt_cosmo` APIs, (5) write the committed artifacts, (6) emit the run
  manifest, (7) write the AOR ledger, (8) evaluate and record pass/fail gates into `summary.json`.
- No physics in `run.py`. If a runner needs new physics, it goes in `sbt_cosmo/` first.

### Cross-experiment coherence enforcement

Per GROUNDING_BRIEF Part 4, the *same* `Ξ_cosmo` must serve all experiments. Structurally:
`sbt_cosmo/xi/residual.py` defines the canonical residual; experiments select which terms/params are
active via `configs/models/sbt_xi.yaml` but **cannot** redefine the functional form. E8
(model competition) reads the committed `summary.json` of E1–E7 and checks the coherence gate
(e.g. kernel amplitudes consistent across probes within tolerance — see §11).

---

## 8. `results/` — committed cross-experiment deliverables

`results/` holds the *publication-grade, cross-experiment* committed artifacts (distinct from each
experiment's own `outputs/`). All tracked.

```
results/
├── tables/
│   ├── one_residual_nine_shadows.csv   # the §3 diagnosis map populated with measured residuals
│   ├── hubble_route_matrix.csv         # H_0^{(r,ℓ)} table (E4)
│   ├── model_competition.csv           # ΛCDM/w0wa/IDE/MG/SBT: χ², BIC, evidence, out-of-sample (E8)
│   └── aor_status_master.csv           # consolidated AOR statuses across the whole program
├── figures/
│   ├── hubble_holonomy.pdf             # 𝔥_γ loop-transport residual
│   ├── xi_staging_fingerprint.pdf      # ∂Xi/∂ℓ structured-vs-noise (E5)
│   └── w_eff_phantom_crossing.pdf      # w_eff(z) crossing −1 with stability witness (E3)
├── <E#>/
│   └── posteriors/                     # TRACKED — committed posterior summaries (REGISTRY §7)
│       ├── mean.npy                    #   posterior mean vector
│       ├── cov.npy                     #   posterior covariance
│       ├── thinned_samples.npy         #   (optional) thinned samples
│       └── manifest.json               #   sha256 per file + provenance
└── README.md                           # tracked — maps each figure/table to the gate it evidences
```

> **Artifact authority (REGISTRY §7).** All gate evidence MUST be derivable from **committed**
> artifacts. Per-experiment posterior summaries (mean vector, covariance, optionally thinned samples),
> each carrying a `sha256`, are committed under the tracked `results/<E#>/posteriors/`. Raw sampler
> chains under `runs/**/chains/*.hdf5` are **gitignored reproducibility byproducts** and **no gate may
> depend on them**. Cross-experiment posterior consumption — e.g. E4's inverse-ladder — reads the
> committed summary, never an ignored chain.

---

## 9. Determinism and reproducibility conventions

Conforms to GROUNDING_BRIEF §III. **Likelihood/forward-model evaluations are deterministic given
(config + lockfile + data); committed summaries are tolerance-reproducible; chains are validated by
statistical equivalence, not bitwise reproducibility (REGISTRY §11.6).**

### 9.1 Seeds

- Every config has a `seed` block: `{numpy: <int>, python: <int>, sampler: <int>}`. Defaults pinned
  in `configs/base.yaml`.
- `run.py` sets `numpy.random.seed`, `random.seed`, and the sampler seed (Polychord/MCMC) from config
  before any stochastic call. No unseeded RNG anywhere (enforced by a lint test forbidding bare
  `np.random.*` calls outside a seeded generator).
- **Deterministic likelihood / forward-model evaluations** (background, distances, `Cl`, `P(k)`,
  per-probe log-likelihood) are bitwise reproducible given fixed inputs. Committed posterior
  **summaries** are reproducible to a stated tolerance (REGISTRY §11.6).
- MCMC / PolyChord **chains are NOT required to be bitwise-identical** across environments; they are
  validated by **statistical equivalence** — parameter means/covariance agree within MC error,
  `R̂ < 1.01`, and ESS thresholds are met (§9.4). Only the E0 toy demos (no sampler) are bitwise
  reproducible.

### 9.2 Version pinning

- Python deps fully pinned in `requirements.lock`; system/boltzmann deps in `environment.yml`.
- `pyproject.toml` records *ranges* matching GROUNDING_BRIEF §II (cobaya ≥3.4, CLASS ≥3.2 / CAMB
  ≥1.5.7, pyccl ≥3.0, getdist ≥1.5, arviz ≥0.15). The lockfile records exact resolved versions.
- **One boltzmann backend per program** (CLASS *or* CAMB, not mixed in one run) — set in
  `configs/backends.yaml`; recorded per run.
- Float precision: **float64** for all cosmology/posterior math (GROUNDING_BRIEF §III.D).

### 9.3 Run manifest (mandatory per run)

`outputs/manifest.json` follows the GROUNDING_BRIEF §III.B schema, minimally:

```json
{
  "run_id": "2026-05-29_E1_w0wa_DESI-DR2_repro",
  "experiment": "E1",
  "date_utc": "2026-05-29T14:32:00Z",
  "git_commit": "<sha>",
  "config_path": "experiments/E1_desi_dr2_repro/config.yaml",
  "config_sha256": "<sha>",
  "seeds": {"numpy": 4242, "python": 7, "sampler": 1337},
  "datasets": [{"name": "DESI_DR2_BAO", "release": "arXiv:2503.14738",
                "manifest": "data/manifests/desi_dr2_bao.json", "verified": true}],
  "software": [{"name": "cobaya", "version": "3.5.4"}, {"name": "CLASS", "version": "3.2.1"}],
  "lean": {"toolchain": "leanprover/lean4:v4.28.0", "mathlib_rev": "<sha>", "build": "green"},
  "outputs": ["summary.json", "tables/…", "figures/…", "aor_status.json"],
  "audit_status": "AOR_certified | RefStableAOR | recognized_grade | unaudited"
}
```

### 9.4 Pipeline checkpoints

- Pre-inference: dump background `H(z)`, distances, BAO predictions, `Cl`, `P(k)` to inspect.
- Post-inference: compute R̂ (target < 1.01), ESS (target > 400/chain), KL vs reference posteriors.
- Cross-probe: per-block χ² summary table (observed, expected, residual).

---

## 10. Naming conventions

| Item | Convention | Example |
|---|---|---|
| Python package/module/func | `snake_case` | `route_mismatch.py`, `compute_rm()` |
| Class | `PascalCase` | `CosmologicalClosureCarrier`, `HubbleRouteMatrix` |
| Experiment dir | `E<n>_<slug>` | `E4_hubble_route_holonomy` |
| Experiment ID in code/config | `E<n>` | `E4` |
| Config files | `snake_case.yaml` | `desi_dr2_bao.yaml` |
| Model configs | physics short-name | `lcdm`, `wcdm`, `w0wa`, `ide`, `mg_mu_sigma`, `sbt_xi` |
| Probe IDs (the `p` index) | lowercase tokens | `cmb`, `bao`, `sn`, `wl`, `rsd`, `ladder` |
| Hubble route IDs (`r`) | `r<k>_<from>_to_<to>` | `r1_cmb_to_bao`, `r3_cepheid_to_sn` |
| Run ID | `<UTC-date>_E<n>_<model>_<datasettag>` | `2026-05-29_E1_w0wa_DESI-DR2` |
| Datasets in manifests/configs | `UPPER_SNAKE` matching brief §I | `DESI_DR2_BAO`, `PLANCK_2018` |
| Audit symbols in code | spelled out | `delta`, `route_mismatch`, `local_global`, `ppd` |
| Output tables | `snake_case.csv` | `model_competition.csv` |
| Figures | `snake_case.{png,pdf}` | `hubble_holonomy.pdf` |

Probe tokens and route IDs are a closed vocabulary defined once in `sbt_cosmo/probes/base.py` and
`sbt_cosmo/hubble/routes.py`; configs must reference only these tokens (validated at load).

---

## 11. Tracked vs gitignored — explicit policy

### MUST be tracked (non-ignored deliverables)

- All source: `sbt_cosmo/`, `lean/` sources, `tests/`, `configs/`, `experiments/<E#>/{config.yaml,run.py,README.md}`.
- All planning/docs: `plan/` (including `plan/GROUNDING_BRIEF.md` and `plan/REGISTRY.md`), `docs/`, `idea.md`, `README.md`, `data/README.md`.
- Environment: `pyproject.toml`, `requirements.lock`, `environment.yml`, `.gitattributes`, `.gitignore`, `CITATION.cff`.
- **Provenance:** `data/manifests/*.json`.
- **Per-experiment committed outputs:** `experiments/<E#>/outputs/{manifest.json, summary.json, aor_status.json, posterior_summary.npz}`, `outputs/tables/*.csv`, `outputs/figures/*`.
- **Cross-experiment deliverables:** all of `results/` (tables + figures + README), including the
  per-experiment posterior summaries under `results/<E#>/posteriors/**` (mean/cov/thinned + sha256;
  REGISTRY §7 — the committed authority for any cross-experiment posterior consumption).

### MUST be gitignored

- Dataset payloads: `data/raw/**`, `data/processed/**` (provenance manifests excepted — see below).
- Raw sampler chains: `runs/**/chains/*.hdf5` (reproducibility byproducts; **no gate may depend on
  them** per REGISTRY §7) and the legacy `experiments/**/outputs/chains/**`.
- Build/cache: `lean/.lake/**`, `**/__pycache__/**`, `*.pyc`, `.pytest_cache/`, `build/`, `dist/`, `*.egg-info/`.
- Local env: `.venv/`, `.env`, scratch `tmp/`, `scratch/`.

### `.gitignore` (authoritative content)

```gitignore
# --- data payloads (provenance manifests are force-tracked below) ---
data/raw/
data/processed/
!data/manifests/
!data/manifests/**
!data/README.md

# --- raw sampler chains (committed posterior SUMMARIES live in results/<E#>/posteriors/;
#     raw chains are gitignored byproducts and NO gate may depend on them — REGISTRY §7) ---
runs/**/chains/*.hdf5
experiments/**/outputs/chains/

# --- build / cache ---
lean/.lake/
__pycache__/
*.pyc
.pytest_cache/
build/
dist/
*.egg-info/

# --- local env / scratch ---
.venv/
.env
tmp/
scratch/
```

> The negations (`!data/manifests/**`, `!data/README.md`) guarantee provenance + fetch instructions
> stay in git even though their parent `data/` payload dirs are ignored. `experiments/**/outputs/`
> is **not** broadly ignored — only its `chains/` subdir is — so the committed deliverables in §7
> remain tracked by default.

---

## 12. `tests/` — what must be enforced

```
tests/
├── test_imports_layering.py    # import-linter: experiments not importable; dependency arrows (§3)
├── test_determinism.py         # deterministic likelihood bitwise; committed summaries tolerance-reproducible; chains statistically equivalent (REGISTRY §11.6)
├── test_seeding.py             # no bare np.random.* / random.* outside seeded generators
├── test_manifest_schema.py     # every outputs/manifest.json + data/manifests/*.json valid + checksums
├── test_gates.py               # reproduce-without-rerun: re-evaluate each gate from committed artifacts
├── test_xi_single_source.py    # Ξ_cosmo defined only in sbt_cosmo/xi; no per-experiment redefinition
├── test_audits_contract.py     # δ, RM, LG, PPD APIs stable; vanish on null/lumpable inputs (E0)
├── test_naming.py              # experiment dirs, probe/route tokens, run-id format conform to §10
└── test_registry.py            # REGISTRY lint over committed plan/ + artifacts (forbidden tokens etc. — see below)
```

**`test_registry.py` (the REGISTRY lint, specified by REGISTRY §1–§11).** It checks committed
artifacts and `plan/` files against the registry tables and, per REGISTRY §11.1, **rejects these
forbidden tokens anywhere except `plan/REGISTRY.md`**:

- the phantom tokens `PhantomNoGhost`, `no-ghost`, `no_ghost`, and `without ghost(s)` (genuine
  literature/risk mentions like "the data could require a ghost" are exempt — they scope a failure
  mode, not an SBT claim);
- a bare `G-T<n>` and a bare `G-DECISIVE` (must be namespaced, e.g. `G-E4-T1 … G-E4-T5`,
  `G-E4-DECISIVE`); and the obsolete gate id `G-E8-NOGHOST`;
- the phrases "within 3%" / "within 10%" / "win or tie" used as an OOS **pass** (only a strict OOS
  `win` passes `G-E8-OOS-DECISIVE`);
- "summary.json = PASS" / "upstream = PASS" used as the **E8 dependency** (E8 depends on
  `terminal_state ∈ {PASS, ACCEPTED_NEGATIVE}`, never universal PASS) and a `= PASS` E8-dep clause;
- a coherence ledger or artifact inventory **missing any of E1–E7**.

It also lints (REGISTRY §10): no bare `G<n>`; `unstatused` never in an accepted-status list;
terminal states ⊆ §2 enum; no gate references a gitignored path.

These run in CI (cheap, no inference). The expensive runs are out-of-band; CI verifies the
*committed artifacts and contracts*, embodying the reproduce-without-rerun principle.

---

## 13. Pass/fail gates (quantitative)

These gates govern the **repository structure and reproducibility contract** (not the physics of any
single experiment — those gates live in `plan/experiments/E#.md`). A program build is structurally
**PASS** only if all hold; otherwise **FAIL**.

| # | Gate | Threshold / criterion | Checked by |
|---|---|---|---|
| G-REPO-1 | **Package installs** | `pip install -e .` succeeds from `pyproject.toml`; `import sbt_cosmo` works | CI |
| G-REPO-2 | **Layering respected** | 0 forbidden imports (experiments not importable; arrows per §3 table) | `test_imports_layering.py` |
| G-REPO-3 | **Single Ξ source** | exactly 1 definition of `Xi_cosmo`/rewrite operator (in `sbt_cosmo/xi/`); 0 redefinitions under `experiments/` | `test_xi_single_source.py` |
| G-REPO-4 | **Determinism** | identical `config + requirements.lock + seeds` → deterministic likelihood/forward-model evaluations bitwise reproducible; committed posterior summaries reproducible to a stated tolerance (≤1e-12 relative on scalar summaries); MCMC/PolyChord chains validated by **statistical equivalence** (means/cov within MC error, `R̂ < 1.01`, ESS thresholds), NOT bitwise identity — only E0 toy demos (no sampler) are bitwise reproducible | `test_determinism.py` |
| G-REPO-5 | **No unseeded RNG** | 0 occurrences of bare `np.random.<fn>` or `random.<fn>` outside a `default_rng(seed)` / seeded path | `test_seeding.py` |
| G-REPO-6 | **Manifest completeness** | 100% of runs have a schema-valid `outputs/manifest.json` recording seeds, dataset releases+manifests, software versions, git commit | `test_manifest_schema.py` |
| G-REPO-7 | **Data integrity** | 100% of loaded dataset files match the sha256 in `data/manifests/*.json`; load aborts on mismatch | `io/checksums.py`, `test_manifest_schema.py` |
| G-REPO-8 | **Reproduce-without-rerun** | for every E0–E8: `{manifest.json, summary.json, tables/*.csv, figures/*, aor_status.json, posterior_summary.npz}` present and tracked; every pass/fail gate in `summary.json` re-derivable from committed artifacts with 0 missing inputs | `test_gates.py` |
| G-REPO-9 | **Chains excluded** | `git ls-files` returns 0 paths under any `experiments/**/outputs/chains/`; total tracked binary added per run < 25 MB (summaries/figures only) | CI + `.gitignore` |
| G-REPO-10 | **AOR status present** | every committed run has an `aor_status.json`; 0 residuals with status `unstatused` (per `idea.md` §2 "No Unstatused Residual") | `aor/ledger.py`, `test_gates.py` |
| G-REPO-11 | **Convergence recorded** | every inference run records R̂ and ESS; gate flags any param with R̂ ≥ 1.01 or ESS < 400 (GROUNDING_BRIEF §VI.2) | `inference/convergence.py` |
| G-REPO-12 | **Covariance sanity** | every loaded covariance is symmetric, positive-definite, condition number < 1e8, all-finite (GROUNDING_BRIEF §VI.1) | `io/datasets.py` |
| G-REPO-13 | **Reference agreement (E1)** | E1 reproduces a published baseline with total χ² within 5% of reference before any Ξ is added (GROUNDING_BRIEF §VI.3 / idea.md §6 Exp 1) | E1 runner, recorded in `summary.json` |
| G-REPO-14 | **Lean receipts build** | `lake build` is green; toolchain + mathlib revision recorded in manifest (or status `unaudited` declared explicitly) | CI / manifest |
| G-REPO-15 | **Cross-experiment Ξ coherence** | E8 verifies the same `Ξ_cosmo` parameters serve all probes: per-probe inferred kernel amplitudes agree within a factor 10 (program FAILS otherwise, per GROUNDING_BRIEF Part 4 failure rule) | E8 runner, `results/tables/model_competition.csv` |
| G-REPO-16 | **Naming conformance** | 100% of experiment dirs, probe tokens, route IDs, run IDs match §10 patterns | `test_naming.py` |

**Inputs to this plan:** `idea.md` (§4 carrier, §6 experiments, §10 evidence standard, UPDATE block);
`GROUNDING_BRIEF.md` (§I datasets, §II stack, §III determinism, §V formats, §VI gates, Part 2
E0–E8, Part 4 coherence, Part 5 AOR); corpus `AOR`, `Adequacy_Residuals`, `Foundations_IV`,
`Holonomy_with_Memory`.

**Method:** enumerate the formal carrier objects → assign each a package submodule → define the
config-driven, seed-pinned runner contract → fix the committed-vs-ignored deliverable policy so the
reproduce-without-rerun principle is structurally guaranteed → operationalize all of it as the G-REPO-1–G-REPO-16
gates above.

**Outputs of executing this plan:** the directory skeleton of §2–§8, `pyproject.toml` +
`requirements.lock` + `environment.yml`, the `.gitignore` of §11, the `tests/` suite of §12, and
stub modules under `sbt_cosmo/` with the §3 boundaries. No experiment results are produced here;
those come from `plan/experiments/E#.md`.

---

## 14. Corpus + idea.md grounding

- **Cosmological Closure Carrier** `𝔉_cosmo`, four residuals δ/RM/LG/PPD, low-rank `Ξ_cosmo`, kernels
  `K_L,K_M,K_G,K_S`: `idea.md` §4–§5; GROUNDING_BRIEF Parts 1–3. → `sbt_cosmo/{background,growth,probes,xi,audits}`.
- **Hubble readout field, route matrix, Hubble holonomy `𝔥_γ`, lawful plurality** (route/staging/
  closure-transport/residual-reuse/source-refinement tests): `idea.md` UPDATE block; GROUNDING_BRIEF
  §5 + E4. → `sbt_cosmo/hubble/`.
- **Adequacy residual = Schur complement, "least rewrite not a fudge function":** `Adequacy_Residuals`;
  GROUNDING_BRIEF §1. → `sbt_cosmo/xi/`.
- **AOR statuses + carrier progression + no-unstatused-residual:** `Audited_Operational_Realisability`,
  `idea.md` §2/§10; GROUNDING_BRIEF §6 + Part 5. → `sbt_cosmo/aor/`.
- **Phantom-crossing stable-readout (no-growing-mode) witness:** `idea.md` §6 Exp 3 / §4 Prop 4; corpus
  `Emergence_IS_the_Needle_Killer`. → `sbt_cosmo/xi/stability.py`, `lean/SbtCosmo/PhantomStableReadout.lean`.
- **Holonomy / route transport mechanics:** `Holonomy_with_Memory`, `Protocol_Trap`, `To_Plot`.
  → `sbt_cosmo/hubble/{transport,holonomy}.py`, `lean/SbtCosmo/Holonomy.lean`.
- **Cross-lens audit template (Lean+Python, null/driven controls, non-claims register):**
  `Six_Birds_for_Neutrino_Mass`. → the `experiments/<E#>/` + `tests/` discipline.
- **Named structural laws F2/F4/F9/F11** (descent-repair normal form, local-global obstruction,
  no-overread/access quotient): `Foundations_IV`. → mapped in `plan/experiments/E#.md`; relevant here
  only as the reason `xi/`, `audits/local_global.py`, and `aor/` are first-class modules.
