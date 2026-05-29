# Plan 02 — Software Environment and Dependencies

**Program:** Dark Energy as Closure — a Six Birds resolution of the cosmological paradoxes
**Status:** PLANNING / BLUEPRINT. To be executed later by a separate codex-driven process. Nothing here is run now.
**Scope of this file:** the exact, pinned, justified software environment; install plan; lockfile strategy; build footguns; per-experiment compute budget; CI/smoke-test plan; and quantitative pass/fail gates for the environment itself.
**Authoritative upstream:** the SHARED GROUNDING BRIEF (Sections I–VI) and `plan/GROUNDING_BRIEF.md`. Where this file pins a version it must not contradict the brief's Section II ("Recommended software stack"), Section III ("Determinism & reproducibility"), or Section IV ("Compute budget"). This file makes those tables concrete and installable.
**Grounding references:** `idea.md` Sections 6 (experiments E1–E7), 10 (five hard tests), and the post-Section-10 UPDATE block (Hubble route matrix / holonomy / lawful plurality → experiment E4). Corpus: `docs/papers/INDEX.md`; AOR statuses from `Audited_Operational_Realisability`; Lean methodology pattern noted in INDEX "Notes" (Lean 4 v4.28.0, frequently mathlib-free; see `Foundations_III`, `Foundations_IV`).

---

## 0. Design principles (why this environment is shaped this way)

1. **Reproduce-before-rewrite.** `idea.md` §6 Experiment 1 and §10 test 1 require that the pipeline recover *published* DESI DR2, Planck, Pantheon+, and weak-lensing contours **before** any Six Birds residual `Ξ_cosmo` is introduced. The environment must therefore be byte-for-byte capable of running the *same* public likelihoods used by those collaborations, not a re-implementation. This forces `cobaya` + native `CLASS`/`CAMB` + official survey likelihood packages, not bespoke code.
2. **One closure residual, many lenses.** `idea.md` §3, §5 require that a single low-rank `Ξ_cosmo(z,ℓ,p)` be tested across geometry (BAO/SN), growth (RSD/WL via 3×2pt), and calibration (Hubble routes). That spans Boltzmann (CMB/BAO), LSS (`pyccl`/CCL), and posterior tooling (`getdist`) in one coherent stack — they must share Python ABI, NumPy version, and float64 conventions.
3. **Determinism is a pass gate, not a nicety.** Brief §III and the AOR carrier (`Audited_Operational_Realisability`: "No Unstatused Residual") require that every run be exactly reproducible and every numerical residual be typed. Versions are pinned to hashes; seeds are mandatory; a run manifest is emitted by every experiment.
4. **Two independent backends as a cross-check, never mixed in one chain.** CLASS and CAMB are both pinned. Brief §II.A says "pick one; don't mix in same run." We use CLASS as primary and CAMB as an independent reproduction backend for the E1 reproduction gate (route-mismatch logic of `idea.md` UPDATE applies even at the level of two Boltzmann codes: if CLASS and CAMB disagree beyond tolerance on identical inputs, that is a *tooling* route mismatch that must be statused before any *physical* `Ξ_cosmo` claim).
5. **Lean is optional but pinned.** Only the certified-theorem deliverables (Propositions P1–P4 of `idea.md` §4, idempotence/route-mismatch certificates) require Lean. The Python pipeline must run with zero Lean dependency. Per INDEX, the corpus targets Lean 4 v4.28.0 and is frequently mathlib-free.

---

## 1. Pinned software stack

### 1.1 Language runtime and core numerics

| Component | Pin | Justification | Footgun / note |
|---|---|---|---|
| **Python** | `3.11.x` (build target `3.11.9`) | `cobaya>=3.5`, `camb>=1.5.7`, `pyccl>=3.0` all support 3.11; 3.11 is the newest CPython with mature wheels for the full stack as of the corpus cutoff. Avoid 3.12 (some Cython/`classy` build edges) and 3.13 (no guaranteed wheels). | Pin minor version in env; do not float to 3.12+. |
| **numpy** | `>=1.26,<2.0` | NumPy 2.0 broke ABI for compiled extensions (`classy`, `camb` C-extensions, older `pyccl`). Staying `<2.0` guarantees all wheels link. Brief §III.D mandates float64 everywhere. | NumPy 2.x ABI break is the single most common stack failure; keep `<2.0` until all of CLASS/CAMB/CCL ship 2.x wheels. |
| **scipy** | `>=1.11,<1.14` | Linear algebra (SVD for the low-rank `Ξ` ansatz of `idea.md` §5; Schur complement for the adequacy residual `Ξ_C` of `Adequacy_Residuals`), optimization, interpolation. | `scipy.linalg.cho_factor` used for covariance whitening — requires PD covariance (gate §6). |
| **pandas** | `>=2.0,<2.3` | Tabular handling of chains, BAO/SN data tables, route-matrix bookkeeping (E4). | Use `pyarrow` backend optional; not load-bearing. |
| **matplotlib** | `>=3.7,<3.10` | Diagnostic and residual plots; publication figures. Brief §II.C pins `>=3.5`; we tighten. | Set `MPLBACKEND=Agg` in CI/headless. |
| **arviz** | `>=0.17,<0.19` | MCMC health: `R̂`, ESS, energy/trace (Brief §II.C). | Overlaps getdist; use arviz for *health*, getdist for *posteriors* (Brief note). |
| **h5py** | `>=3.8` | HDF5 data vectors / covariances / posterior samples (Brief §V.A). | Must match the HDF5 C-lib of survey likelihood packages; install from conda-forge to share libs. |
| **pyyaml** | `>=6.0` | `cobaya` input YAML. | — |

### 1.2 Inference engine and samplers

| Component | Pin | Role | Justification |
|---|---|---|---|
| **cobaya** | `>=3.5,<3.6` | Master inference driver, likelihood interface, model wrapper | Brief §II.A: native CLASS/CAMB support, modular likelihood switching (required for the SPT-2018↔D1 lens swap of `Six_Birds_for_Neutrino_Mass` and E1/E4), used by DESI DR2 publications. |
| **MCMC (cobaya built-in Metropolis)** | bundled | Primary sampler for ΛCDM / wCDM / w0wa fast fits and convergence baselines | Fast, well-understood `R̂` convergence; the workhorse for E1 reproduction. |
| **PolyChordLite** (`pypolychord`) | `>=1.20` | Nested sampling for Bayesian evidence (model comparison E8, Brief §IV row "Bayesian model comparison") | Evidence `ln Z` and `Δ ln Z` are required for the model-competition synthesis of `idea.md` §6 Exp 9 / §9. Metropolis cannot give evidence. |
| **GetDist sampler utilities** | via getdist | Importance reweighting, derived params | Used to project route-indexed `H_0^{(r,ℓ)}` posteriors (E4). |

Sampler choice per experiment is fixed in §4 and is itself a reproducibility variable recorded in the run manifest (Brief §III.B).

### 1.3 Boltzmann / background codes

| Component | Pin | Role | Justification & footguns |
|---|---|---|---|
| **CLASS** via **classy** | CLASS `v3.2.x`, classy wrapper matching | **Primary** Boltzmann backend: `C_ℓ` (TT/TE/EE), matter power `P(k)`, `D_M(z)/r_d`, `D_H(z)/r_d`, `f σ_8(z)` | Brief §II.A: speed + numerical stability to high `k`. CLASS is the reference for the BAO/CMB predictions used by E1, E2, E5, E6. **Footgun:** `classy` is a Cython wrapper compiled against a specific CLASS `libclass.a`; it does **not** ship a manylinux wheel — it builds from source and needs `gcc`/`gfortran`, `OpenMP` (`libgomp`), and a `make` that matches the CLASS Makefile. On conda, install `c-compiler`, `cxx-compiler`, `fortran-compiler`, `make`, `libgomp` from conda-forge **before** `pip install classy`/building CLASS. **Footgun 2:** `classy` rebuilds must be forced (`make clean` in the CLASS dir) when switching compilers, else stale `.o` files link and segfault at import. |
| **CAMB** | `>=1.5.7,<1.6` | **Independent** Boltzmann backend for the CLASS-vs-CAMB reproduction cross-check (E1 tooling route-mismatch gate, §6) | Brief §II.A: equivalent accuracy, ships wheels (Fortran prebuilt), easier install than classy. Use for halofit nonlinear and as the second leg of the E1 agreement gate. **Footgun:** CAMB and CLASS use different default `k`-binning, `A_s` vs `ln(10^10 A_s)`, and reionization/neutrino settings; the agreement gate must compare *physical observables* (`D_M/r_d`, `C_ℓ`) at matched cosmology, not raw parameters. |

### 1.4 Large-scale structure (3×2pt, RSD, lensing)

| Component | Pin | Role | Justification & footguns |
|---|---|---|---|
| **pyccl / CCL** | pyccl `>=3.0,<3.2` (CCL C-lib `>=3.0`) | LSS predictions: 3×2pt (shear, galaxy clustering, GGL), RSD `f σ_8`, intrinsic alignments, baryonic feedback, scale cuts | Brief §II.A: handles scale cuts, baryonic models, transfer functions; verified against DES Y6 (E5 prime growth probe). **Footgun:** `pyccl` links a compiled `libccl` (GSL + FFTW3 + CLASS-as-library). Install from **conda-forge** (`conda install -c conda-forge pyccl`) to get a prebuilt `libccl`; `pip install pyccl` triggers a CMake source build needing `gsl`, `fftw`, `cmake`, and a compiler, which is the second most common build failure after `classy`. **Footgun 2:** pyccl bundles its own CLASS for transfer functions — version skew vs the standalone `classy` must be recorded; the agreement gate (§6) checks `P(k)` consistency between pyccl-internal and standalone CLASS at the percent level. |

### 1.5 Survey likelihood packages and data adapters

| Component | Pin / source | Role | Note |
|---|---|---|---|
| **planck native likelihood** (`clik` / `plc`, or `cobaya` `planck_2018_*`) | Planck 2018 release (arXiv:1807.06209) | CMB TT/TE/EE + low-E anchor (Brief §I.B) | `cobaya-install planck_2018_highl_plik.TTTEEE planck_2018_lowl.TT planck_2018_lowl.EE` fetches the data + builds `clik`. **Footgun:** `clik` needs `cfitsio` + a working Fortran toolchain; conda-forge `cfitsio` recommended. |
| **DESI `desilike`** | DR2 official (arXiv:2503.14738; full-shape arXiv:2411.12026) | BAO `D_M/r_d`, `D_H/r_d`; RSD full-shape | Brief §I.A/§I.E: PRIMARY battleground (E1). **Fallback (Brief):** published compressed BAO-only Gaussian likelihood if `desilike` not installable. The fallback choice is a statused residual (AOR `budgeted`). |
| **DES Y6 likelihood** (`DESLikelihood` / cosmosis-style or Gaussian adapter) | DES Y6 (arXiv:2601.14559); Y3 fallback arXiv:2212.00091 | 3×2pt growth probe (E5) | Brief §I.D: public likelihood if available, else Gaussian approximation on the published data vector + covariance (statused `budgeted`). |
| **KiDS-Legacy / HSC Y3 adapters** | arXiv:2503.19441 / arXiv:2511.18134 | cosmic-shear cross-checks (E5 staging sweep) | Loaded as Gaussian likelihoods over published data vectors + covariances. |
| **SPT-3G 2018 + D1, ACT DR6** | arXiv:2601.16277 / 2509.02945 | CMB lens-swap diagnostic (E4/E5; `Six_Birds_for_Neutrino_Mass` template) | Native likelihood objects where available; re-binned subset fallback. The 2018↔D1 swap is a *packaging-stability* probe per the neutrino-mass paper. |
| **Pantheon+ / Union3 / DES-SN5YR** | arXiv:2202.04077 / 2401.06956 / Zenodo:13827844 | SN Ia distance modulus + full covariance (E1, E2) | Loaded as `gaussian_likelihood_covmat(Δμ)` (Brief §V.B). |
| **Local-ladder / TDCOSMO / siren priors** | arXiv:2509.01667, 2408.06153, 2110.00517, 1709.05895 | Route-indexed `H_0` priors for the Hubble route matrix (E4) | Encoded as route-tagged Gaussian priors; this is the data substrate for `idea.md` UPDATE's lawful-plurality test. |

All adapters write to the internal representation of Brief §V.A: `.npy`/HDF5 data vector (float64), `.npy`/HDF5 covariance, JSON/HDF5 metadata sidecar (probe, z-bins, scale cuts, source arXiv/DOI, MD5 checksum).

### 1.6 Lean 4 toolchain (certified-theorem track only)

| Component | Pin | Role | Justification |
|---|---|---|---|
| **elan** (Lean version manager) | latest | toolchain installer | reproducible Lean install |
| **Lean 4** | `v4.28.0` | Formal proofs of P1–P4 (`idea.md` §4): descent-repair normal form, no-overread, local-global gluing, phantom stable readout (no growing mode); idempotence `δ` and route-mismatch certificates | Matches the corpus pin (INDEX "Notes"; `Foundations_III` validator at lean4 v4.28.0). |
| **mathlib** | revision matched to Lean `v4.28.0` (pinned commit in `lakefile`/`lean-toolchain`) | finite types, lattices, DPI lemmas (used for idempotence and route-mismatch in `To_Lay_a_Stone`, `Holonomy_with_Memory`) | Brief §II.D: imported *selectively*; many corpus papers are mathlib-free, so mathlib is opt-in per proof file. |

The Lean project is isolated under its own `lean-toolchain` + `lakefile.lean` with a pinned mathlib commit hash so `lake build` is deterministic and decoupled from the Python env.

---

## 2. Install plan

### 2.1 Primary: conda environment + pip overlay (recommended)

Rationale: the three hardest dependencies (`classy`, `pyccl`, `clik`) need compiled C/Fortran libraries (OpenMP, GSL, FFTW3, cfitsio) that conda-forge ships as prebuilt, ABI-consistent binaries. Conda manages the compiler toolchain and these system libs; pip overlays the pure-Python inference layer. This is the lowest-footgun path.

**`environment.yml` (specification to be created at execution time):**

```yaml
name: sbt-de
channels: [conda-forge]
dependencies:
  - python=3.11.9
  # toolchain (needed to build classy/pyccl/clik from source if no wheel)
  - c-compiler
  - cxx-compiler
  - fortran-compiler
  - make
  - cmake>=3.24
  - pkg-config
  # system libs the compiled cosmology codes link against
  - libgomp        # OpenMP for CLASS
  - gsl            # pyccl/CCL
  - fftw           # pyccl/CCL
  - cfitsio        # Planck clik
  # core numerics (conda-forge to share HDF5/BLAS)
  - numpy>=1.26,<2.0
  - scipy>=1.11,<1.14
  - pandas>=2.0,<2.3
  - matplotlib-base>=3.7,<3.10
  - h5py>=3.8
  - pyyaml>=6.0
  - arviz>=0.17,<0.19
  # LSS backend with prebuilt libccl (avoids CMake source build)
  - pyccl>=3.0,<3.2
  - pip
  - pip:
      - cobaya>=3.5,<3.6
      - camb>=1.5.7,<1.6
      - getdist>=1.5
      - pypolychord>=1.20      # nested sampling (evidence)
```

**Post-conda pip/source steps (ordered; ordering matters):**

1. `conda env create -f environment.yml` then activate.
2. Build CLASS + classy from source against the conda toolchain:
   - clone CLASS at tag `v3.2.x`; `make clean && make -j`; `pip install -e .` from `python/` (or `pip install classy` with `CC`/`OMPFLAG` pointing at conda compilers). Verify OpenMP linked (`ldd` shows `libgomp`).
3. `cobaya-install planck_2018_highl_plik.TTTEEE planck_2018_lowl.TT planck_2018_lowl.EE planck_2018_lensing.native` — fetches Planck data + builds `clik` against conda `cfitsio`.
4. Install `desilike` (pip from official source) and the DES Y6 / SPT / ACT likelihood adapters; if any is not installable, fall back to the Gaussian-likelihood adapter (§1.5) and record the fallback as an AOR `budgeted` residual in the run manifest.
5. Lean track (optional, isolated): `curl elan`; set `lean-toolchain` to `leanprover/lean4:v4.28.0`; `lake build` with pinned mathlib commit.

### 2.2 Alternative: container (for CI and clean-room reproduction)

A `Dockerfile` (to be authored at execution time) built `FROM mambaorg/micromamba:1.5-jammy` (or `condaforge/miniforge3`) that:
- copies `environment.yml`, runs `micromamba env create`,
- bakes the CLASS+classy source build and `cobaya-install` of Planck into an image layer,
- pins the base image by digest (`@sha256:...`) so the OS libc/HDF5 are frozen,
- runs the smoke test (§5) as the final `RUN` layer so the image fails to build if the stack is broken.

The container is the **canonical reproduction artifact** for any AOR-certified result (Brief §VI). The image digest is recorded in the run manifest.

### 2.3 Lockfile strategy

| Layer | Lock mechanism | Rationale |
|---|---|---|
| Conda packages | `conda env export --no-builds > env.lock.yml` AND `conda-lock` producing a per-platform `conda-lock.yml` with full hashes | `conda-lock` gives hash-pinned, multi-platform-resolvable locks; `--no-builds` export is the human-readable companion. |
| pip overlay | `pip freeze > requirements.lock.txt` with `--require-hashes` for the pip-installed set (cobaya, camb, getdist, pypolychord, desilike) | hash-pinned wheels → byte-identical installs (Brief §III demands exact reproduction). |
| CLASS / CCL C-libs | record git tag/commit + compiler version (`gcc --version`) + `CLASS_VERSION` string in the manifest; archive the built `classy`/`libclass.a` build log | source-built libs can't be hash-locked via pip; the commit+compiler+build-log triple is the lock. |
| Lean | `lean-toolchain` (exact Lean version) + `lake-manifest.json` (mathlib commit hash) | `lake` is already hash-deterministic. |
| Container | image digest `@sha256:` of base + final image | freezes the entire OS+lib surface. |

**Lock acceptance gate:** a fresh `conda-lock install` + `pip install --require-hashes` on a clean machine must reproduce identical package versions; a re-run of the smoke test under both the original and the relocked env must give identical χ² to float64 epsilon (gate G-ENV-3).

### 2.4 Known build footguns (consolidated checklist)

1. **NumPy 2.0 ABI break** — keep `numpy<2.0`; otherwise `classy`/`camb`/`pyccl` C-extensions fail to import with `_ARRAY_API not found`. *Highest-frequency failure.*
2. **`classy` stale-object segfault** — always `make clean` in CLASS before rebuild; never reuse `.o` files across compiler changes.
3. **`classy` OpenMP not linked** — if CLASS built without `-fopenmp`, multi-threaded calls segfault; verify `libgomp` in `ldd`.
4. **`pyccl` CMake source build** — prefer the conda-forge prebuilt `pyccl` (with `libccl`); only fall back to `pip` source build with `gsl`/`fftw`/`cmake` present.
5. **`clik`/Planck `cfitsio` mismatch** — build `clik` against conda `cfitsio`, not a system one, to avoid FITS-read segfaults.
6. **pyccl-internal vs standalone CLASS skew** — record both versions; reconcile `P(k)` at the percent level (gate G-ENV-4).
7. **CLASS vs CAMB parameter conventions** — compare observables not raw params (gate G-ENV-2); `A_s` vs `ln(10^10 A_s)`, neutrino mass splitting defaults differ.
8. **`MPLBACKEND`** — set `Agg` in headless/CI or matplotlib import hangs.
9. **OpenMP thread oversubscription** — set `OMP_NUM_THREADS` explicitly per chain; cobaya parallel chains × CLASS OpenMP can oversubscribe cores and *change* wall-clock and (rarely) reduction-order-dependent floats. Pin `OMP_NUM_THREADS=1` for the determinism gate.
10. **MPI** — PolyChord wants MPI; pin `mpi4py` from conda-forge with the matching `openmpi`/`mpich` to avoid launcher mismatch.

---

## 3. Determinism and provenance (operationalizing Brief §III)

**Inputs:** experiment config (cobaya YAML), declared seeds, dataset versions.
**Method:**
- Every run sets `numpy.random.seed`, Python `random.seed`, the cobaya sampler seed, and (if used) the PolyChord seed. Determinism is required at two levels (Brief §III.A): (a) **likelihood / forward-model evaluations** are bitwise-reproducible given fixed inputs (`OMP_NUM_THREADS=1`, float64); (b) **committed posterior summaries** (parameter means/covariance, optional thinned samples) are reproducible to a stated tolerance. Bitwise-identical MCMC/PolyChord *chains* across environments are NOT required — chains are validated by **statistical equivalence** (parameter means/covariance within MC error, `R̂ < 1.01`, ESS thresholds). Only the E0 toy demos (no sampler) are bitwise-reproducible end to end.
- Every experiment emits a **run manifest JSON** exactly per Brief §III.B: `run_id`, ISO date, `seeds{}`, `datasets[]` (name, version arXiv/DOI, access), `software[]` (every pinned version incl. CLASS commit + compiler + container digest), `parameters{}`, `output_files[]`, `audit_status` ∈ {`AOR_certified`, `recognized_grade`, `unaudited`}.
- Pipeline checkpoints (Brief §III.C): pre-inference dump of `C_ℓ`, `P(k)`, `D_M/r_d`, `D_H/r_d`, `f σ_8` to HDF5; post-MCMC `R̂`, ESS, KL-to-literature; cross-probe χ² table.
**Outputs:** `manifest.json`, `checkpoints/*.h5`, `chains/`, `posterior.h5`, `diagnostics/` per run.

---

## 4. Per-experiment compute / runtime budget

Calibrated to Brief §IV. Cores/RAM are per-node; "chains" = independent MCMC walkers unless nested. Wall-clock assumes the pinned stack on a commodity 64-core node; CLASS/CAMB call time dominates.

| Exp | Maps to `idea.md` | Sampler | Models | Cores | RAM | Chains × samples | Wall-clock | Cost factor |
|---|---|---|---|---|---|---|---|---|
| **E0** Synthetic null-Λ toy | §2, §5 | direct integration / least-squares | toy generator + `Ξ` refit | 8 | 4 GB | ~100 realizations | 0.5–2 h | 0.1× |
| **E1** DESI DR2 reproduction (ΛCDM, wCDM, w0wa) | §6 Exp1, §10.1 | cobaya MCMC | 3 base models × {CLASS, CAMB} | 16–32 | 8–16 GB | 4 chains × 20k | ΛCDM 4–6 h; w0wa 12–24 h | 1×–5× |
| **E2** Distance-duality local-global obstruction | §6 Exp2, §4 P3 | cobaya MCMC | M0/M1/M2 (η(z), `Ξ`) | 32 | 16 GB | 4 × 20k each | 24–48 h total | 3–6× |
| **E3** Phantom crossing with stable readout | §6 Exp3, §4 P4 | MCMC + eigenvalue stability check | `Ξ`-induced w_eff(z) | 16 | 8 GB | 4 × 15k + stability scan | 8–16 h | 2–4× |
| **E4** Hubble route matrix + holonomy (lawful plurality) | §6 Exp4 + **UPDATE block** | MCMC per route + importance transport | null / nuisance / `Ξ` route models over routes r1–r7 × staging ℓ | 32 | 16 GB | 7 routes × 4 × 15k + loop-transport | 48–96 h total | 8–15× |
| **E5** Growth/S₈ staging sweep | §6 Exp5, §10.4 | MCMC + scale-cut grid | DES Y6, KiDS, HSC, RSD, CMB-lens under scale cuts | 32 + pyccl | 16–32 GB | grid of scale cuts × 4 × 15k | 48–96 h | 8–15× |
| **E6** IDE as accounting shadow | §6 Exp6, §4 P2 | cobaya MCMC | IDE(Q) vs `Ξ` rewrite | 32 | 16 GB | 4 × 20k each | 24–48 h | 4–8× |
| **E7** Modified gravity as repair chart | §6 Exp7 | cobaya MCMC + pyccl μ/Σ | (μ0,Σ0) vs `Ξ` | 32 | 16–32 GB | 4 × 20k | 24–48 h | 4–8× |
| **E8** Model competition / evidence | §6 Exp9, §9, §10 | **PolyChord nested** | ΛCDM, w0wa, CDDR-only, IDE, MG, SBT-`Ξ` (6 models) | 64 (MPI) | 32 GB/run | ~1M live-point evals × 6 | 120–360 h total | 40–100× |
| **Leave-one-probe-out PPD** | §6 Exp4, §10.3 | MCMC × 6 holdouts | best model | 32 | 16 GB | 6 runs × 4 × 10k | 72–144 h total | 6–12× |
| **Lean P1–P4 + δ/RM certs** | §4 | `lake build` | n/a | 1 | 1–2 GB | proof check | 2–10 min | <0.01× |

**Campaign staging (Brief §IV "pragmatic guidance"):**
- *Phase A (validate pipeline):* E0 + E1 ΛCDM single fit → ~1 node, ~1 day. Gates the whole program (must reproduce published contours).
- *Phase B (main):* E1 w0wa, E2, E3, E6, E7 → 2–4 nodes, ~1 week.
- *Phase C (publication):* E4, E5, E8, leave-one-out PPD + Lean certs → 64-core cluster, 1–2 weeks wall-clock.

---

## 5. CI / smoke-test plan

Tiered so that cheap checks gate cheap PRs and the full reproduction runs nightly/on-release. All CI runs in the §2.2 container with `MPLBACKEND=Agg`, `OMP_NUM_THREADS=1`, fixed seeds.

| Tier | Trigger | Runtime budget | Checks |
|---|---|---|---|
| **T0 import/build** | every commit | < 5 min | env builds; `import numpy, scipy, classy, camb, pyccl, cobaya, getdist, arviz` all succeed; `numpy.__version__ < 2.0`; CLASS reports OpenMP; pyccl-internal CLASS version logged. |
| **T1 micro-physics** | every commit | < 10 min | CLASS computes `D_M(z=0.5)/r_d`, `D_H/r_d`, one `C_ℓ` at a fixed fiducial cosmology and matches a stored reference to < 0.1%; CAMB independently matches CLASS on the same observables to the agreement tolerance (gate G-ENV-2); pyccl computes `σ8`, one `f σ_8(z)`, one shear `C_ℓ` vs stored reference < 0.5%. |
| **T2 mini-likelihood** | PR to main | < 30 min | load each data adapter (or Gaussian fallback); assert covariance PD + condition number < 1e8 + all-finite (gate G-ENV-1); evaluate χ² at fiducial and assert finite + within stored band. |
| **T3 mini-MCMC determinism** | PR to main | < 20 min | assert likelihood/forward-model χ² evaluations bitwise-reproducible under identical seed; run a short ΛCDM chain (≤ 500 steps) twice and assert **statistical equivalence** of the summaries (means/covariance within MC error); assert manifest JSON emitted with all required keys. |
| **T4 reproduction (nightly/release)** | schedule | hours | run E1 ΛCDM to convergence; assert `R̂ < 1.01`, ESS > 400/chain, and `χ²_total` within 5% of stored published reference (gate G-ENV-6); regenerate one triangle plot artifact. |
| **T5 Lean** | change under `lean/` | < 15 min | `lake build` succeeds with pinned toolchain+mathlib commit; P1–P4 stub theorems and δ/RM certificate files compile. |

CI fails closed: any gate breach blocks merge. The relock acceptance gate (§2.3) runs in T4.

---

## 6. Pass/fail gates (quantitative)

These are the environment-level gates. Physics-level pass/fail belongs to the per-experiment plan files; here we gate that the *tooling* is correct and reproducible. Thresholds follow Brief §VI and `idea.md` §10.

- **G-ENV-1 — Data integrity.** Every loaded covariance is symmetric positive-definite, condition number κ < 1e8, all entries finite. *Fail → block.* (Brief §VI.1)
- **G-ENV-2 — Boltzmann cross-backend agreement (tooling route mismatch).** At a fixed fiducial cosmology, CLASS vs CAMB agree on `D_M(z)/r_d` and `D_H(z)/r_d` to < 0.1% across z∈[0.1,2.3], and on `C_ℓ^{TT}` to < 0.2% for ℓ∈[30,2000]. Treat any excess as a *tooling* route mismatch that must be statused (AOR `budgeted`/`bridged`) **before** any physical `Ξ_cosmo` claim. *Fail → block E1+.* (operationalizes `idea.md` UPDATE route-mismatch logic at the code level)
- **G-ENV-3 — Determinism.** Identical seed + `OMP_NUM_THREADS=1` + float64 reproduces **likelihood / forward-model χ² evaluations bitwise** and **committed posterior summaries to a stated tolerance** (parameter means/covariance within MC error); MCMC/PolyChord chains are validated by **statistical equivalence** (`R̂ < 1.01`, ESS thresholds), not bitwise chain identity across environments. E0 toy demos (no sampler) reproduce bitwise end to end. Relocked env reproduces the same. *Fail → block.* (Brief §III.A)
- **G-ENV-4 — pyccl/CLASS internal consistency.** pyccl-internal vs standalone CLASS `P(k)` agree to < 1% for k∈[1e-3,1] h/Mpc at z=0; `σ8` agrees to < 0.5%. *Fail → block growth experiments E5/E7.*
- **G-ENV-5 — Convergence.** Every reported chain: `R̂ < 1.01` on all sampled params, ESS > 400/chain (Brief §VI.2). Nested runs: PolyChord `ln Z` stable to < 0.2 across two seeds. *Fail → result is `unaudited`, not `AOR_certified`.*
- **G-ENV-6 — Reproduce-before-rewrite.** Computed `χ²_total` for ΛCDM/w0wa on DESI DR2+Planck+SN within 5% of the published reference, and recovered 1σ contour widths within 10% (Brief §VI.3; `idea.md` §10.1). *Fail → the entire program cannot proceed past Phase A.*
- **G-ENV-7 — Provenance completeness.** Every run emits a manifest with all Brief §III.B keys populated, including CLASS commit + compiler version + container digest + dataset arXiv/DOI + MD5 checksums. Any missing key ⇒ run is `unaudited`. *Fail → not citable.*
- **G-ENV-8 — Fallback statusing.** Any use of a Gaussian-likelihood fallback in place of an official survey likelihood is recorded as an AOR `budgeted` residual in the manifest with a one-line justification. *Unstatused fallback → block* (No Unstatused Residual, `Audited_Operational_Realisability`).
- **G-ENV-9 — Lean track.** If Lean deliverables are in scope, `lake build` succeeds under the pinned toolchain and the P1–P4 + δ/RM certificate files compile with no `sorry`. *Fail → Lean claims downgraded to `recognized_grade`.*

---

## 7. Outputs of this plan (artifacts the executor must produce)

1. `environment.yml`, `conda-lock.yml`, `env.lock.yml`, `requirements.lock.txt` (hash-pinned pip set).
2. `Dockerfile` (digest-pinned base) + built image digest recorded.
3. CLASS+classy build script + recorded commit/compiler/build-log; `cobaya-install` provisioning script for Planck/DESI/DES/SPT/ACT likelihoods (with Gaussian-fallback adapters).
4. `lean/` project skeleton: `lean-toolchain` (v4.28.0), `lakefile.lean`, pinned `lake-manifest.json`, P1–P4 + δ/RM certificate stubs.
5. CI workflow implementing tiers T0–T5 with the §6 gates wired as fail-closed checks.
6. A `manifest.schema.json` matching Brief §III.B that every experiment validates against.

---

## 8. Consistency check against the SHARED GROUNDING BRIEF

- Software pins are a tightened superset of Brief §II (cobaya≥3.4→`>=3.5,<3.6`; CLASS≥3.2; CAMB≥1.5.7; pyccl≥3.0; getdist≥1.5; Lean≥4.0→`v4.28.0`; mathlib pinned). No downgrades; no contradictions.
- Determinism, manifests, checkpoints, float64 follow Brief §III verbatim.
- Compute budgets in §4 are calibrated to Brief §IV rows and staging guidance.
- Data formats (§1.5, §3) follow Brief §V.A/§V.B internal representation and cross-tool handoff.
- Pass gates §6 instantiate Brief §VI items 1–7 plus the AOR statusing discipline of `Audited_Operational_Realisability` and the reproduce-before-rewrite standard of `idea.md` §10.1.
- Experiment-to-`idea.md` mapping in §4 covers §6 Exp1–7/9, §9 model competition, and the post-§10 UPDATE Hubble route-matrix/holonomy program (E4), keeping lawful plurality central per the UPDATE block.
