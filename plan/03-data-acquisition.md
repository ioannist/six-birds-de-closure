# Plan 03 — Data Acquisition: The Definitive Dataset Catalog

**Program:** Dark Energy as Closure — a Six Birds resolution of the cosmological paradoxes.
**Status:** PLANNING / BLUEPRINT. To be executed later by a separate codex-driven process. Nothing here is fetched or run now.
**Scope of this file:** the *definitive* data plan. For **every** dataset in the SHARED GROUNDING BRIEF (§I) it pins the exact release/DR, the arXiv/DOI/Zenodo/repository handle, the precise data product needed (data vector + covariance + redshifts/bins), the on-disk file format, the license + citation, a concrete loader spec (function signature + parsed shape), and a concrete FALLBACK for when the full likelihood is unavailable (compressed/Gaussian likelihood or published summary posterior). It then fixes the provenance/manifest convention so that every byte of data a run touches is auditable.
**Authoritative upstream:** the SHARED GROUNDING BRIEF (§I datasets, §III determinism, §V formats, §VI gates) and `GROUNDING_BRIEF.md`. Where this file repeats a release/version it must match the brief; this file makes the brief's §I table executable as loaders + manifests. Repo layout (where these files live, the tracked dataset-manifest schema, `io/datasets.py`/`io/checksums.py`) is fixed by `plan/01-repo-structure.md` §4; the install/version pins are in `plan/02-environment-and-deps.md` §1.5.
**Grounding references:** `idea.md` §6 (experiments E1–E7 and the data they consume), §10 (five hard tests — esp. test 1 "reproduce standard results first"), and the post-§10 **UPDATE** block (Hubble route matrix / holonomy / lawful plurality → the route-indexed `H_0^{(r,ℓ)}` data substrate). Corpus: the dark-energy precursor `A_Six_Birds_Eye_View_of_Dark_Energy` (demonstrated on DES-SN5YR + DES Y6 BAO; its lens/completion/route-mismatch framing is what every loaded probe instantiates); `Six_Birds_for_Neutrino_Mass` (the SPT-3G 2018→D1 lens-swap template, our model for treating a likelihood swap as a packaging-stability probe); `Audited_Operational_Realisability` (every fallback is a *statused* residual — never `unstatused`); `Adequacy_Residuals` (the Schur-complement `Ξ_C(D|L)` the cross-probe data feeds).

---

## 0. Design principles (why the data layer is shaped this way)

1. **A probe is a lens, not a fact (`idea.md` §1; precursor `A_Six_Birds_Eye_View_of_Dark_Energy`).** Each dataset is a packaging operator `E_{θ,p} = U_θ ∘ f_p` evaluated against a homogeneous FLRW completion. The data layer therefore loads, for every probe `p`, the *full information needed to evaluate route mismatch* `RM_p = d(E_{θ,p}T, T_θ E_{θ,p})` and the cross-probe adequacy residual — i.e. a **data vector + its full covariance + its exact redshift/multipole/scale binning + its scale cuts**. A bare best-fit number is never enough; the covariance is load-bearing.
2. **Reproduce-before-rewrite (`idea.md` §10 test 1; overview §0).** The data products must be the *same* ones the collaborations used, so the pipeline can recover published DESI DR2 / Planck / Pantheon+ / weak-lensing contours **before** any `Ξ_cosmo` is introduced. This forces: prefer the official likelihood + official data release; only fall back to a Gaussian/compressed surrogate when the official path is unavailable, and *status* that fallback.
3. **Every fallback is a typed residual, never `unstatused` (`Audited_Operational_Realisability`).** When the full likelihood is unavailable we degrade to a published compressed/Gaussian likelihood or a published summary posterior, and we record the degradation as an AOR status (`budgeted` by default — the information loss is bounded and accounted) in the dataset manifest and the run manifest. An undocumented fallback is a hard fail (gate G-DATA-8).
4. **Provenance is verifiable without the payload (`plan/01-repo-structure.md` §4).** Payloads in `data/raw/**` and `data/processed/**` are gitignored (large, license-bound, re-fetchable); the per-dataset manifest `data/manifests/<dataset>.json` is **tracked** and carries the exact release, fetch URL, sha256 per file, parsed shapes, and the processing-script commit. Any run re-verifies sha256 before use (gate G-DATA-7).
5. **The Hubble sector is data, with route structure (`idea.md` UPDATE).** Local-ladder, time-delay, and siren `H_0` determinations are not nuisances to be averaged away. They are loaded as **route-tagged** measurements `(probe, anchor, redshift depth, lens scale, completion, calibration bridge)` so that E4 can build the Hubble route matrix `H_0^{(r,ℓ)}` and test *lawful plurality* (structured, not random, route offsets). Each local `H_0` source therefore carries a `route` tag and a `staging` axis in its manifest.
6. **One internal representation (Brief §V.A).** Whatever the upstream format (FITS, HDF5, text tables, `clik`, Zenodo tarball), the processed product is normalized to: `data_vector.npy` (float64, shape `(N_obs,)`), `covariance.npy` (float64, `(N_obs, N_obs)`, symmetric PD), and `meta.json` (probe, bins, scale cuts, source release, sha256). This makes covariance-integrity and Schur-complement math uniform across probes.

---

## 1. Catalog conventions

- **Dataset key:** `UPPER_SNAKE` (matches `plan/01-repo-structure.md` §9 and Brief §I), e.g. `DESI_DR2_BAO`, `PLANCK_2018`. One tracked manifest `data/manifests/<lower_snake>.json` per key.
- **Loader spec:** every dataset has a Python loader in `io/datasets.py` (path fixed by `plan/01`). The signature returns a typed `ProbeData` dataclass; the "parsed shape" column states the exact array shapes the loader must produce after normalization to the internal representation.

```python
# io/datasets.py — common return type (spec, to be implemented at execution time)
@dataclass(frozen=True)
class ProbeData:
    key: str                      # e.g. "DESI_DR2_BAO"
    data_vector: np.ndarray       # float64, shape (N_obs,)
    covariance: np.ndarray        # float64, shape (N_obs, N_obs), symmetric PD
    bins: dict                    # probe-specific index → {z | ell | theta | route | sample}
    scale_cuts: dict              # applied cuts (ell_min/max, theta_min, k-range, z-range)
    route: str | None             # for Hubble-sector probes only (idea.md UPDATE); else None
    source: str                   # arXiv/DOI/Zenodo handle
    access: str                   # "official_likelihood" | "gaussian_fallback" | "summary_posterior"
    aor_status: str               # "zero" if official; "budgeted" if a fallback was used; etc.
    sha256: dict                  # {raw_file_path: sha256, ...} re-verified at load
```

- **License column** records the redistribution status. **We never commit payloads** (gitignored per `plan/01` §13); the license governs (a) whether the *processed* derived product could be redistributed and (b) the mandatory citation. When in doubt, treat as "cite, do not redistribute."
- **Fallback column** is mandatory and concrete: a *named* compressed/Gaussian likelihood or a *named* published summary posterior, plus the AOR status the fallback incurs.

---

## 2. Baryon Acoustic Oscillations (BAO) — Brief §I.A

`idea.md` §6 Exp1 anchors the whole program on DESI DR2; Exp2 (distance duality) needs `D_M/r_d` and `D_H/r_d` per z-bin with covariance.

| Key | Release / DR | arXiv / DOI / repo | Data product needed (vector + covariance + bins) | Format | License / citation | Loader spec (signature → parsed shape) | Fallback (+ AOR status) |
|---|---|---|---|---|---|---|---|
| **DESI_DR2_BAO** *(PRIMARY)* | DESI DR2 (3-yr) BAO | arXiv:2503.14738; data via DESI public release + `desilike` | Joint BAO: `D_M(z)/r_d`, `D_H(z)/r_d` (and `D_V/r_d` where only isotropic) across the 7 tracer bins → ~13–15-element vector; full analytic+mock covariance; per-bin effective `z_eff` | HDF5 / text tables (DESI) → normalized `.npy` | DESI data: public, CC-BY-style; cite DESI Collaboration 2025 (arXiv:2503.14738). Do not redistribute raw. | `load_desi_dr2_bao() -> ProbeData`; `data_vector` shape `(~13–15,)`; `covariance (~13–15, ~13–15)`; `bins[i] = {"z_eff":…, "obs":"DM/rd"|"DH/rd"|"DV/rd", "tracer":…}` | Published **compressed BAO-only Gaussian likelihood**: the released `(D_M/r_d, D_H/r_d)` means + covariance table read directly into `gaussian_likelihood_covmat`. AOR `budgeted` (loses full-shape/mock structure, bounded). |
| **DESI_RSD_FS** | DESI DR2 full-shape (RSD) — **default: compressed** | *Method/control:* arXiv:2411.12026 (DESI **DR1** full-shape + `μ_0,Σ_0` MG **methodology** — NOT a DR2 data product). *Primary data product (default):* the published DR2 compressed `(f σ_8, D_M/r_d, D_H/r_d)` summary + covariance; a full-shape `P(k)` DR2 likelihood is used **only if** a public `desilike` DR2 FS likelihood exists at execution time | **Default:** compressed `(f σ_8, D_M/r_d, D_H/r_d)` per z-bin (6–8 bins, z∈[0.1,1.5]) + covariance + `μ_0,Σ_0` inputs. Full-shape `P(k)` multipoles only via a confirmed public DR2 FS likelihood | HDF5 (DESI) → `.npy` | Public; cite DESI DR1 FS/MG method (arXiv:2411.12026) + the DR2 FS summary release. | `load_desi_rsd_fs(compressed=True) -> ProbeData` (**compressed is the default**); compressed `data_vector (3·n_bins,)`; full `(f σ_8(z))` extractable for E5/E7 growth | If no public DR2 FS likelihood exists at execution time, the compressed `f σ_8(z)`+geometry **IS the primary leg** (not a degraded fallback), AOR `budgeted` (loses full-shape `P(k)` info); DR1 FS retained only as a method control. |
| **CC_HZ** | Cosmic chronometers (differential-age `H(z)`) | Moresco et al. compilation (review arXiv:2201.07241; source compilations e.g. arXiv:1601.01701) | Model-independent `H(z_i) ± σ_i` at ~30 redshifts z∈[0.07,2.0] (differential-age method); diagonal statistical errors **plus** the Moresco systematic covariance block | text → `.npy` | Public; cite Moresco et al. (arXiv:2201.07241 review + source compilations). | `load_cc_hz() -> ProbeData(route="CC")`; `data_vector (~30,)` = `H(z_i)`; `covariance` = stat diag + Moresco systematic block; `bins[i]={"z":…}` | **Diagonal-only `H(z)±σ`** Gaussian likelihood (drops the systematic covariance). AOR `budgeted`; dropping the CC leg entirely → `out_of_scope` for the CC-anchored E6 sub-claim. |
| **KIDS_LEGACY_BAO** | KiDS-Legacy integrated BAO | arXiv:2503.19441 | Angular-diameter / Hubble BAO ratio (cross-correlation), mock-based covariance, source-bin tomography | FITS + catalog → `.npy` | Public KiDS DR; cite Wright et al. 2025 (arXiv:2503.19441). | `load_kids_legacy_bao() -> ProbeData` (weak constraint; cross-correlation only) | **Gaussian approximation** on the published ratio + covariance. AOR `budgeted`; if not separable from the shear product, mark `out_of_scope` for BAO use and keep only as shear (§5). |
| **DES_Y6_BAO** | DES Year 6 BAO | arXiv:2601.14559 (joint 3×2pt+BAO) | Redshift-space clustering `α_∥, α_⊥` (→ `D_M/r_d`, `D_H/r_d`), analytic+mock covariance, embedded in the Y6 3×2pt vector | FITS / HDF5 → `.npy` | Public DES Y6; cite DES Collaboration 2026 (arXiv:2601.14559). | `load_des_y6_bao() -> ProbeData`; extract BAO block from joint vector; `bins` carry `α` definitions | **Compressed BAO-only likelihood** (`α_∥, α_⊥` mean + 2×2 covariance). AOR `budgeted`. |
| **DES_Y3_BAO** *(FALLBACK anchor)* | DES Year 3 BAO | arXiv:2212.00091 | Galaxy clustering 2–60 Mpc/h radial/angular; simulation-based covariance (~10⁴×10⁴ full, BAO sub-block extracted) | FITS → `.npy` | Public; cite DES Y3 (arXiv:2212.00091). | `load_des_y3_bao() -> ProbeData` (use only if Y6 unavailable) | Public DES Y3 **compressed BAO likelihood object**. AOR `budgeted`; flagged `approved_other` if substituting for Y6. |

**Inputs:** DESI DR2 BAO + FS tables; DES Y6 (Y3 fallback); KiDS-Legacy integrated BAO.
**Method:** normalize each to `(data_vector, covariance, bins)`; verify covariance PD + κ<1e8 (gate G-DATA-1); store `z_eff` and observable label per element so E1/E2 can map to `D_M/r_d`, `D_H/r_d` and the distance-duality ratio `η(z)=D_L/[(1+z)²D_A]` (`idea.md` §6 Exp2).
**Outputs:** `data/processed/desi_dr2_bao/{data_vector,covariance,meta}.{npy,json}` (+ analogous for each key); tracked `data/manifests/desi_dr2_bao.json` etc.

---

## 3. Cosmic Microwave Background (CMB) — Brief §I.B

`PLANCK_2018` is the ΛCDM **anchor** prior (Brief §I.B). `SPT_3G` is the **lens-swap** diagnostic from `Six_Birds_for_Neutrino_Mass` (2018→D1 packaging stability). `ACT_DR6` cross-checks holographic/Ricci-DE constraints (`idea.md` §6).

| Key | Release / DR | arXiv / DOI / repo | Data product needed | Format | License / citation | Loader spec (signature → parsed shape) | Fallback (+ AOR status) |
|---|---|---|---|---|---|---|---|
| **PLANCK_2018** *(ANCHOR)* | Planck 2018 (PR3) | arXiv:1807.06209; PLA + `clik`/`plc`; cobaya `planck_2018_*` | TT (ℓ=2–2500), TE/EE (ℓ=2–2300), low-E (Planck+WMAP9 low-ℓ); lensing native. Native `clik` likelihood (not a Gaussian); baseline `H_0=67.4±0.5` @ ΛCDM | FITS maps + `clik` files; cobaya-installed | Planck Legacy Archive: open; cite Planck 2018 VI (arXiv:1807.06209). | `load_planck_2018(spectra=("TTTEEE","lowl","lowE","lensing")) -> ClikLikelihood`; not a flat vector — wraps native `clik`; expose `nuisance` params to cobaya | **Gaussian-likelihood summary** of the compressed CMB distance priors `(R, ℓ_A, ω_b, n_s)` + covariance (χ²≈150–200 @ ΛCDM band). AOR `budgeted` (drops nuisance marginalization). |
| **SPT_3G** *(LENS SWAP)* | SPT-3G 2018 **and** D1 | **arXiv:2506.20707** (SPT-3G **D1** TT/TE/EE power spectra + cosmology — *PRIMARY data product*, Camphuis et al. 2025) + arXiv:2212.05642 (SPT-3G **2018** TT/TE/EE); lens-swap *framing* per `Six_Birds_for_Neutrino_Mass` (neutrino-mass packaging app, arXiv:2601.16277 — a diagnostic template, **not** the power-spectrum release) | TT/TE/EE ℓ≈500–3000 (~2500 multipoles); analytic covariance; **two** packaged variants (2018, D1) for the swap; diagnostic = TT high-ℓ ℓ~2000–3000 mismatch | native likelihood objects → `.npy` band-powers | Public SPT release; cite SPT-3G D1 (Camphuis et al. 2025, arXiv:2506.20707) + SPT-3G 2018 (arXiv:2212.05642). | `load_spt3g(release="2018"|"D1") -> ProbeData`; `bins[i]={"ell":…,"spec":"TT"|"TE"|"EE"}`; loader exposes *both* releases for the swap audit | **Re-binned / subset** TT/TE to ℓ<2000 as a Gaussian band-power likelihood. AOR `budgeted`; the swap itself (2018↔D1) is the diagnostic, treated as a *packaging-stability* probe per `Six_Birds_for_Neutrino_Mass`. |
| **ACT_DR6** | ACT DR6 | arXiv:2509.02945 | TT/TE/EE ℓ≈340–3000 (~2500 modes); analytic model; cross-check for holographic/Ricci DE | HDF5 + likelihood wrapper → `.npy` | Public ACT release; cite ACT DR6 2025 (arXiv:2509.02945). | `load_act_dr6() -> ProbeData`; `bins[i]={"ell":…,"spec":…}` | **Planck-like compressed summary** (distance priors). AOR `budgeted`. |

**Inputs:** Planck 2018 native likelihood; SPT-3G 2018 + D1; ACT DR6.
**Method:** install Planck via `cobaya-install planck_2018_highl_plik.TTTEEE planck_2018_lowl.TT planck_2018_lowl.EE planck_2018_lensing.native` (per `plan/02` §2.1); wrap SPT/ACT native objects; for the lens-swap, load 2018 and D1 as two `ProbeData` and compute the held-out mismatch `δχ` and multipole localization exactly as in the neutrino-mass template.
**Outputs:** `clik` provisioned under `data/raw/planck_2018/`; SPT/ACT band-powers normalized to `data/processed/<key>/`; manifests with the `clik` package version + data sha256.

---

## 4. Type-Ia Supernovae (SN) — Brief §I.C

`idea.md` §6 Exp1 (SN combinations drive the 2.8–4.2σ DE preference) and Exp2 (SN luminosity distances vs BAO angular/radial distances → CDDR `η(z)`). The precursor was demonstrated on DES-SN5YR.

| Key | Release / DR | arXiv / DOI / Zenodo | Data product needed | Format | License / citation | Loader spec (signature → parsed shape) | Fallback (+ AOR status) |
|---|---|---|---|---|---|---|---|
| **PANTHEON_PLUS** *(PRIMARY SN)* | Pantheon+ | arXiv:2202.04077; public Pantheon+SH0ES data release | Distance modulus `μ(z_hel, z_cmb)` for 1550 SN (z=0.01–2.26); **full stat+sys covariance** `C_μμ` (1550×1550); host-mass + redshift columns | text + HDF5 → `.npy` | Public (Pantheon+ release); cite Brout et al. 2022 (arXiv:2202.04077). | `load_pantheon_plus(z_min=0.01) -> ProbeData`; `data_vector (N_sn,)` = `μ` or `m_B`; `covariance (N_sn, N_sn)`; `bins[i]={"z_hel":…,"z_cmb":…,"host_logM":…}` | **Gaussian distance-modulus** likelihood `gaussian_likelihood_covmat(Δμ)` using the released `μ(z)` + `C_μμ` (this *is* the standard path; "fallback" = binned `μ(z̄)` in 10–20 z-bins + binned covariance if memory-bound). AOR `zero` for full, `budgeted` for binned. |
| **UNION3** | Union3 | arXiv:2401.06956 | Standardized distance for 1258 SN; systematic block covariance; slightly weaker ∫w dz preference than Pantheon+ | HDF5 + FITS → `.npy` | Public Union3 release; cite Rubin et al. 2024 (arXiv:2401.06956). | `load_union3() -> ProbeData`; `data_vector (1258,)`; `covariance (1258,1258)` | **Compressed 5-bin distance–redshift** likelihood (released binned `μ` + 5×5 covariance). AOR `budgeted`. |
| **DES_SN5YR** | DES-SN5YR | Zenodo:13827844 (https://zenodo.org/records/13827844); arXiv:2401.02929 (DES-SN5YR cosmology) | 1470 SN Ia (spec+photo) `μ(z)`; detailed calibration covariance (selection, photo-z, calibration) | Zenodo tarball + FITS → `.npy` | Zenodo CC-BY; cite DES Collaboration 2024 (Zenodo:13827844 / arXiv:2401.02929). | `load_des_sn5yr() -> ProbeData`; `data_vector (1470,)`; `covariance (1470,1470)`; `bins` carry photo-z flag | **Fitted `μ(z)` polynomial + covariance of best-fit** published summary. AOR `budgeted`. *This is the precursor paper's demonstrated SN probe — keep as a cross-check even when Pantheon+ is primary.* |
| **DES_Y3_SN_INTERNAL** *(NOT primary)* | DES Y3 internal SN | arXiv:2212.00091 | ~850 spec-confirmed SN internal to the 3×2pt calibration; embedded in `DESLikelihood` | embedded | Public; cite DES Y3 (arXiv:2212.00091). | not independently released — `load_des_y3_sn_internal()` raises unless using the joint `DESLikelihood` | Use **Pantheon+ or Union3 as the external standard**; declare DES-Y3-internal SN `out_of_scope` as a standalone probe. AOR `out_of_scope`. |

**Inputs:** Pantheon+ (primary), Union3, DES-SN5YR (precursor cross-check).
**Method:** load `μ(z)` + full `C_μμ`; whiten with Cholesky of `C_μμ` (requires PD — gate G-DATA-1); expose `z_hel`/`z_cmb` so E2 can form the distance-duality ratio against BAO `D_A`. Run *each* SN compilation separately and jointly with DESI+Planck per `idea.md` §6 Exp1 (the 2.8–4.2σ range is *SN-dataset-dependent* — that dataset dependence is itself a Six Birds packaging signal, recorded, not hidden).
**Outputs:** processed `μ`/`C_μμ` per key; manifests recording SN count, z-range, photo-z fraction.

---

## 5. Weak Lensing + Large-Scale Structure (3×2pt) — Brief §I.D

`idea.md` §6 Exp5 (growth/staging sweep for `S_8`): the question is not "is `S_8` low?" but "does `∂Ξ_cosmo/∂ℓ ≠ 0`?" — so we need each shear/3×2pt vector **with its scale cuts** to run scale-cut sweeps.

| Key | Release / DR | arXiv / DOI | Data product needed | Format | License / citation | Loader spec (signature → parsed shape) | Fallback (+ AOR status) |
|---|---|---|---|---|---|---|---|
| **DES_Y6** *(PRIME GROWTH PROBE)* | DES Year 6 3×2pt | arXiv:2601.14559 | Shear + galaxy clustering + GGL; n_z=4 tomographic bins; ℓ_max~5000 (or ξ±(θ)); analytic+sim covariance; **scale cuts** per bin pair; `S_8=0.789±0.012` | FITS + published likelihood → `.npy` | Public DES Y6; cite DES Collaboration 2026 (arXiv:2601.14559). | `load_des_y6(scale_cut=...) -> ProbeData`; `data_vector (N_2pt,)`; `covariance (N_2pt,N_2pt)`; `scale_cuts` mutable for the sweep; `bins` carry `(bin_i,bin_j,probe∈{ξ+,ξ-,γt,w})` | **Gaussian approximation** on the published 3×2pt data vector + covariance (with the official scale cuts baked in). AOR `budgeted`. |
| **KIDS_LEGACY** | KiDS-Legacy cosmic shear | arXiv:2503.19441 | Cosmic shear only (no clustering); n_z=5; ℓ~30–1500 (band powers / COSEBIs); sim+analytic covariance; `S_8=0.815^{+0.016}_{−0.021}` | FITS + Python tools → `.npy` | Public KiDS; cite Wright et al. 2025 (arXiv:2503.19441). | `load_kids_legacy(statistic="bandpower"|"cosebis") -> ProbeData`; `data_vector`, `covariance`, `bins[i]={"ell"|"mode":…,"bin_pair":…}` | **Shear-only `P(κ)`** Gaussian likelihood without RSD coupling. AOR `budgeted`. |
| **HSC_Y3** | HSC Year 3 (+DESI redshift recal) | arXiv:2511.18134 | Cosmic shear + clustering; n_z=5–6; ℓ~200–10000; mock covariance; DESI-recalibrated photo-z → `S_8=0.805±0.018` | FITS / native tool → `.npy` | Public HSC; cite HSC Collaboration 2025 (arXiv:2511.18134). | `load_hsc_y3(photoz="desi_recal"|"original") -> ProbeData`; expose *both* photo-z calibrations (recal is a staging axis for E5) | **Original (pre-DESI-recal) HSC Y3** prior as the comparison leg. AOR `budgeted`; the recal-vs-original swap is itself a staging diagnostic (`idea.md` §6 Exp5). |
| **DES_Y3_3x2pt** *(FALLBACK)* | DES Year 3 3×2pt | arXiv:2212.00091 | Shear + clustering + GGL; n_z=4; ℓ_max~4000; full analytic+sim covariance; public `DESLikelihood` | FITS + likelihood object | Public; cite DES Y3 (arXiv:2212.00091). | `load_des_y3_3x2pt() -> DESLikelihood` (use if Y6 likelihood unavailable) | Published **compressed 3×2pt likelihood**. AOR `budgeted`; `approved_other` if substituting for Y6. |
| **CMB_LENSING** | ACT/SPT CMB lensing | arXiv:2509.02945 | Lensing-potential reconstruction `C_ℓ^{κκ}` ℓ~100–3000; analytic covariance; growth cross-check | HDF5 + wrapped likelihood → `.npy` | Public; cite ACT DR6 lensing 2025 (arXiv:2509.02945). | `load_cmb_lensing(source="ACT"|"SPT") -> ProbeData`; `data_vector (N_κ,)`; `bins[i]={"ell":…}` | **Planck-only lensing** (lower S/N) as the fallback leg. AOR `budgeted`. |

**Inputs:** DES Y6 (prime), KiDS-Legacy, HSC Y3 (both photo-z calibrations), DES Y3 (fallback), CMB lensing.
**Method:** every shear loader takes a `scale_cut` argument so E5 can sweep ℓ-cuts/θ-cuts and measure the *staging fingerprint* `∂Ξ_cosmo/∂ℓ`; predictions come from `pyccl`/CCL (pinned in `plan/02` §1.4) including baryonic feedback + intrinsic alignments, which must be reconciled with the survey's own modeling (gate G-DATA-4 cross-check on `σ_8`).
**Outputs:** processed 3×2pt/shear vectors with scale-cut metadata; manifests recording `S_8` published central value (for the reproduce gate) and n_z binning.

---

## 6. Local Distance Ladder, Time-Delay, and Sirens — Brief §I.F (the Hubble route substrate)

This is the data substrate for `idea.md` UPDATE: the **Hubble route matrix** `H_0^{(r,ℓ)}`. Each source is loaded **route-tagged** so E4 can test *lawful plurality* — that route offsets are structured by `(probe, anchor, redshift depth, lens scale, completion, calibration bridge)`, not random. The null model is `K_{r,ℓ}[Ξ]=0` (one `H_0`); the naive nuisance model is `H_0+ε_{r,ℓ}` (unrelated noise); the Six Birds model is `H_closed(0)+K_{r,ℓ}[Ξ_cosmo]` with the *same* `Ξ_cosmo` seen elsewhere.

| Key | Release | arXiv / DOI | Data product needed | Format | License / citation | Loader spec (signature → parsed shape) | Route tag `r` | Fallback (+ AOR status) |
|---|---|---|---|---|---|---|---|---|
| **SH0ES** | SH0ES Cepheid/SN (JWST+HST) | arXiv:2509.01667 (+ Riess et al. distance-ladder release) | `H_0=73.18±0.88`; Cepheid→SN Ia ladder; 42 anchors + 1550 SN; ± stat ± sys; posterior samples if released | posterior samples / Gaussian | Public; cite Riess et al. 2025 (arXiv:2509.01667). | `load_sh0es() -> ProbeData(route="Cepheid→SN")`; `data_vector (1,)`=`H_0`; `covariance (1,1)`=σ²; or full posterior if available | `Cepheid→SN` | **Gaussian prior** `N(73.18, 0.88²)`. AOR `zero` (this is the native form) / `budgeted` if combining stat+sys naively. |
| **CCHP_TRGB_JAGB** | CCHP JWST TRGB/JAGB | arXiv:2408.06153 | TRGB `H_0=70.39±1.22stat±1.33sys±0.70SN`; JWST-only TRGB `68.81±1.79±1.32`; JAGB `67.80±2.17±1.64`; 23 hosts; posterior ensemble | posterior ensemble / Gaussian | Public; cite Freedman et al. 2024 (arXiv:2408.06153). | `load_cchp(calibrator="TRGB"|"JWST_TRGB"|"JAGB") -> ProbeData(route=…)`; each calibrator a separate route | `TRGB→SN`, `JWST_TRGB→SN`, `JAGB→SN` | **Gaussian prior** per calibrator with quadrature-combined errors. AOR `budgeted`. |
| **TDCOSMO** | TDCOSMO + H0LiCOW time delays | arXiv:2110.00517 | `H_0` **posterior family**, NOT a single Gaussian scalar: the model/prior-dependent variants — TDCOSMO-only (mass-sheet free, `H_0≈73.3±5.4`) and TDCOSMO+SLACS (external-dataset informed, `H_0≈67–74` depending on the assumed mass profile / lens-density prior); 7–10 lensed quasars; lens-model + time-delay systematics; per-variant posterior samples | posterior-sample ensemble per variant / Gaussian | Public; cite Birrer et al. 2020 / TDCOSMO (arXiv:2110.00517). | `load_tdcosmo(variant="tdcosmo_only"|"tdcosmo_slacs"|"family") -> ProbeData(route="time_delay")`; with `variant="family"` returns the **family** of posteriors plus `model_dependent=True` (and `aor_status ∈ {moduli, selected}` flagging the prior/profile dependence); per-variant `data_vector (1,)` or full posterior | `time_delay` | **Published per-variant `H_0` posterior** (sampled, not a single Gaussian — the mass-sheet/lens-prior dependence is the point). AOR `moduli` (variant family) / `selected` (one variant chosen); `summary_only` if no recomputable likelihood is released (excluded from recomputation gates, see G-DATA-3/G-DATA-5). E4 runs the route matrix **with and without** the time-delay route (REGISTRY §9). |
| **SIRENS_GW170817** | Standard siren | arXiv:1709.05895 | `H_0=70.0^{+12}_{−8}`; single GW170817 + EM-counterpart redshift; very wide stat; joint posterior | posterior / asymmetric Gaussian | Public; cite LVC+ 2017 (arXiv:1709.05895). | `load_sirens() -> ProbeData(route="siren")`; asymmetric likelihood (store as sampled posterior, not Gaussian) | `standard_siren` | **Published `H_0` posterior** (asymmetric); if Gaussianized, AOR `budgeted` (loses tails — flag explicitly). |
| **INVERSE_LADDER** | Inverse distance ladder | derived from BAO+CMB+SN (no new download) | `H_0^{inv}` posterior from fitting ΛCDM/w0wa to BAO+CMB and propagating SN calibration; this is an *implicit route* in the matrix | computed | n/a (derived); cite DESI/Planck inputs. | `derive_inverse_ladder(chains) -> ProbeData(route="CMB+BAO→H0")`; not loaded — *produced* by E1 then fed to E4 | `inverse_ladder` | n/a — it is a derived posterior; statused `zero` if from official likelihoods, else inherits the upstream fallback status. |

**Inputs:** SH0ES, CCHP (3 calibrator routes), TDCOSMO (posterior family), GW170817 siren; plus the derived inverse-ladder route from E1.
**Method:** load each as a **route-tagged** `ProbeData`; prefer released *posteriors* over Gaussian summaries (asymmetric siren especially). For model/prior-dependent determinations — time-delay (TDCOSMO/H0LiCOW) above all, and any other anchor whose `H_0` shifts with an assumed prior/profile — ingest a **posterior family / set of model variants**, not a single Gaussian scalar: the loader returns the family plus a `model_dependent` flag, and the manifest statuses the dependence (`moduli` for the unresolved variant family, `selected` once a variant is chosen) per REGISTRY §9. E4 assembles the route matrix (rows = routes r1–r7, columns = staging `ℓ` = redshift cut, host cut, SN sample, anchor, BAO/SN compression, calibration bridge), runs the matrix **with and without** the time-delay route (so the result is not driven by the single most model-dependent leg), and computes the Hubble holonomy `𝔥_γ` (posterior transported around a route loop). Any route×staging cell backed only by a published summary with no recomputable likelihood is tagged `summary_only` and excluded from gates that require recomputation. The decisive test (`idea.md` UPDATE §"Why 'careful' still matters") is whether offsets are *structured* (lawful plurality) — quantified in §10.
**Outputs:** route-tagged `H_0` posteriors (full families for model-dependent legs) under `data/processed/hubble_routes/<route>/`; a `route_matrix.json` index (rows × staging, §6.1) consumed by E4; manifests recording the route tag, staging axis, `model_dependent`/`summary_only` flags, and AOR status per source.

### 6.1 E4 route-matrix data inputs (per route × staging cell)

E4 consumes a route matrix whose rows are the routes `r` (§6 sources) and whose columns are the staging axes `ℓ`. The data layer must populate, for **each occupied `(r, ℓ)` cell**, the exact product below so E4 can build `H_0^{(r,ℓ)}` and the holonomy `𝔥_γ`. `recomputability ∈ {recomputable, summary_only}` controls gate eligibility: `summary_only` cells (published posterior/summary, no re-runnable likelihood) are **excluded** from any gate that requires recomputation (G-DATA-3 reproduce, G-DATA-5 fallback-boundedness) but still count for coverage/route-taggedness (G-DATA-2, G-DATA-6). All cross-experiment posterior consumption reads the **committed posterior summaries** under `results/<E#>/posteriors/`, never an ignored sampler chain.

| Route `r` | Staging axis `ℓ` populated | Exact data product per cell | Recomputability | Covariance / shared-nuisance inputs |
|---|---|---|---|---|
| `Cepheid→SN` (SH0ES) | anchor (geometric anchors), SN sample, redshift cut | full `H_0` posterior if released, else `N(73.18, 0.88²)`; per-anchor sub-ladders where released | `recomputable` if ladder likelihood/samples released; else `summary_only` | SN-sample overlap with Pantheon+/DES-SN5YR (§4) — **shared SN calibration nuisance** (`M_B`, host-mass step) must be carried so the SH0ES and inverse-ladder legs are not double-counted; SH0ES↔SN covariance block via shared SNe |
| `TRGB→SN`, `JWST_TRGB→SN`, `JAGB→SN` (CCHP) | calibrator, host cut, SN sample | per-calibrator `H_0` posterior ensemble or Gaussian with stat/sys split | `recomputable` (ensemble) where released; else `summary_only` | quadrature stat+sys per calibrator; **shared SN second rung** with SH0ES (same SN Ia magnitudes) → cross-route correlation block |
| `time_delay` (TDCOSMO) | lens-density prior / mass-sheet profile (the family axis), lens-sample cut | **posterior family** (per §6 row): one posterior per model variant + `model_dependent=True`; AOR `moduli`/`selected` | `summary_only` unless the per-lens time-delay likelihood is recomputable | lens-model systematics covariance per variant; **shared lens-profile prior** is the model-dependence to be statused, not marginalized silently. E4 runs with and without this route (REGISTRY §9) |
| `standard_siren` (GW170817) | EM-counterpart redshift treatment, peculiar-velocity prior | sampled asymmetric `H_0` posterior (store posterior, not Gaussian) | `summary_only` (single-event published posterior) | none shared (independent distance); peculiar-velocity prior recorded as a staging column |
| `inverse_ladder` (`CMB+BAO→H0`) | BAO/SN compression, ΛCDM-vs-`w0wa` completion | **derived** posterior from E1: read E1's committed `results/E1/posteriors/` summary (mean+cov), `derive_inverse_ladder(...)` | `recomputable` (re-derivable from committed E1 summaries + official likelihoods) | inherits CMB+BAO covariance from §2/§3; **shared SN calibration** with SH0ES leg if SN enter the compression — flag to avoid circularity |

Notes:
- The staging columns above are the *physical* axes (REGISTRY §9, `idea.md` UPDATE lawful plurality); manifests distinguish these from pure nuisance columns so E4 can enforce §11 test 5 (source refinement vs. relabeled noise).
- A cell may be empty (route × staging combination not observed); `route_matrix.json` records occupancy. G-DATA-6 requires ≥6 distinct populated routes and ≥1 closed loop regardless of per-cell recomputability.

---

## 7. Coverage cross-check against the Brief §I

Every dataset named in Brief §I has a catalog row above. Map:

| Brief §I sub-table | Datasets | Covered in §§ |
|---|---|---|
| §I.A BAO | DESI DR2, KiDS-Legacy BAO, DES Y6 BAO, DES Y3 BAO | §2 |
| §I.B CMB | Planck 2018, SPT-3G 2018/D1, ACT DR6 | §3 |
| §I.C SN | Pantheon+, Union3, DES-SN5YR, DES Y3 internal SN | §4 |
| §I.D WL/3×2pt | DES Y6, KiDS-Legacy, HSC Y3, DES Y3 3×2pt, CMB lensing | §5 |
| §I.E RSD | DESI DR2 RSD (compressed fσ8 primary; DR1 full-shape = method control), DES Y6 RSD (in DES_Y6) | §2 (DESI_RSD_FS), §5 (DES_Y6) |
| §I.F Local ladder | SH0ES, CCHP TRGB/JAGB, inverse ladder, TDCOSMO, sirens | §6 |

DES Y6 RSD (Brief §I.E) is the clustering monopole/quadrupole sub-block of the `DES_Y6` 3×2pt vector (§5) and is extracted by `load_des_y6(...)`; DESI RSD/full-shape is `DESI_RSD_FS` (§2). No Brief §I dataset is omitted.

---

## 8. Provenance / manifest convention (auditability)

This makes data auditable end-to-end, per Brief §III (determinism), `plan/01-repo-structure.md` §4 (tracked manifests), and `Audited_Operational_Realisability` (no unstatused residual).

### 8.1 Per-dataset manifest (tracked) — `data/manifests/<dataset>.json`

Schema (extends `plan/01` §4 with the AOR/route/fallback fields this plan requires):

```json
{
  "dataset": "DESI_DR2_BAO",
  "release": "arXiv:2503.14738",
  "access": "official_likelihood",          // official_likelihood | gaussian_fallback | summary_posterior
  "fetch_url": "https://data.desi.lbl.gov/... (see data/README.md)",
  "fetched_utc": "2026-05-29T00:00:00Z",
  "license": "DESI public / CC-BY-style; cite DESI 2025",
  "citation": "DESI Collaboration 2025, arXiv:2503.14738",
  "raw_files": [{"path": "data/raw/desi_dr2_bao/bao_table.txt", "sha256": "<hex>", "bytes": 12345}],
  "processed": {
    "data_vector": {"path": "data/processed/desi_dr2_bao/data_vector.npy",
                    "sha256": "<hex>", "shape": [13], "dtype": "float64"},
    "covariance":  {"path": "data/processed/desi_dr2_bao/covariance.npy",
                    "sha256": "<hex>", "shape": [13, 13], "dtype": "float64"}
  },
  "bins": [{"index": 0, "z_eff": 0.51, "obs": "DM/rd", "tracer": "BGS"}, "..."],
  "scale_cuts": {"applied": true, "note": "as released"},
  "route": null,                              // non-null only for §6 Hubble-sector probes
  "staging_axis": null,                       // e.g. "anchor|sn_sample|bao_compression" for routes
  "model_dependent": false,                   // true for posterior-family/model-variant H0 (e.g. TDCOSMO); pairs with aor_status moduli|selected
  "recomputability": "recomputable",          // recomputable | summary_only (summary_only excluded from recomputation gates G-DATA-3/5)
  "aor_status": "zero",                       // exactly one of the 15 REGISTRY §1 statuses; never "unstatused"
  "fallback": "compressed BAO-only Gaussian likelihood (this plan §2)",
  "fallback_invoked": false,
  "processing_script": "io/datasets.py::load_desi_dr2_bao",
  "processing_commit": "<git-sha>"
}
```

Rules:
- One manifest per dataset key; **tracked in git**; payloads gitignored.
- `aor_status` is exactly one of the 15 canonical AOR statuses (REGISTRY §1): base `{zero, budgeted, bridged, hidden, moduli, selected, probabilistic, out_of_scope, nonclaim, blocked, approved_other}` plus asymptotic `{asymptotic_budgeted, summable, contractive, eventual_zero}`. `unstatused` is **NOT** a status — it is a validator-error sentinel; any residual that ends tagged `unstatused` is a hard fail (G-DATA-8 / No-Unstatused-Residual) and `unstatused` must never appear in an accepted-status list.
- If `fallback_invoked = true`, `access ≠ official_likelihood`, `aor_status` MUST be `budgeted` (or stronger) with a one-line `fallback` justification.
- `route`/`staging_axis` non-null **iff** the dataset is a §6 Hubble-sector probe (enables the E4 route matrix).
- `model_dependent = true` for any §6 `H_0` determination ingested as a **posterior family / model variants** rather than a single Gaussian scalar (time-delay TDCOSMO/H0LiCOW above all); such entries carry `aor_status ∈ {moduli, selected}` per REGISTRY §9, and E4 runs the route matrix with and without these legs.
- `recomputability = summary_only` for any source backed only by a published posterior/summary with no re-runnable likelihood; `summary_only` cells are excluded from recomputation gates (G-DATA-3, G-DATA-5) but still count toward coverage (G-DATA-2) and route-taggedness (G-DATA-6).

### 8.2 `data/README.md` (tracked) — fetch instructions

One section per dataset key with: the exact fetch URL (arXiv ancillary / DOI / Zenodo / DESI/PLA/KiDS/HSC archive), the command to fetch, the expected file list + sizes, and the fallback to invoke if the primary is unavailable. This is the human-readable companion to the manifests.

### 8.3 Run manifest (per run) — `experiments/<E#>/outputs/manifest.json`

Per Brief §III.B and `plan/01` §9.3, each run records `datasets[]` as `{name, version, access, manifest_path, verified:true, aor_status}` — so a run's data provenance is reconstructable from committed artifacts without the payloads.

### 8.4 Integrity verification (`io/checksums.py`)

On every load, `io/datasets.py` re-computes sha256 of each raw file and compares to the manifest; mismatch → hard error (gate G-DATA-7). Processed `.npy`/covariance also carry sha256 in the manifest so a re-derivation is detectable.

---

## 9. Acquisition workflow (inputs → method → outputs)

**Inputs:** the catalog (§§2–6) + `data/README.md` fetch URLs + `plan/02` environment (loaders, `cobaya-install` for Planck, `desilike` for DESI).
**Method (ordered):**
1. Fetch raw payloads into `data/raw/<dataset>/` exactly as released; record sha256 + bytes.
2. Run the per-dataset loader → normalize to the internal representation (`data_vector.npy`, `covariance.npy`, `meta.json`) in `data/processed/<dataset>/`; record processed sha256 + shapes.
3. Validate covariance: symmetric, PD, κ<1e8, finite (gate G-DATA-1); for asymmetric likelihoods (siren) keep the sampled posterior, not a Gaussian.
4. Write/update the tracked `data/manifests/<dataset>.json`; if any official path failed, invoke the named fallback and set `aor_status=budgeted` + `fallback_invoked=true`.
5. For Hubble-sector probes, set `route`/`staging_axis` and register the row in `data/processed/hubble_routes/route_matrix.json`.
6. Smoke-evaluate each likelihood at a fiducial cosmology and assert finite χ² within the stored band (ties to `plan/02` CI tier T2).
**Outputs:** populated `data/raw/**`, `data/processed/**` (gitignored); tracked `data/manifests/*.json` + `data/README.md` + `route_matrix.json`; a coverage report asserting every Brief §I dataset has a manifest.

---

## 10. Pass/fail gates (quantitative)

These gate the **data layer**. Physics pass/fail lives in the per-experiment plans; here we gate that the data is correct, complete, reproduced, and auditable. Thresholds follow Brief §VI, `plan/02` §6, and `idea.md` §10.

- **G-DATA-1 — Covariance integrity.** Every loaded covariance is symmetric (‖C−Cᵀ‖∞ ≤ 1e-10·‖C‖∞), positive-definite (Cholesky succeeds), condition number κ < 1e8, all entries finite. *Fail → block use of that probe.* (Brief §VI.1)
- **G-DATA-2 — Catalog completeness.** Every dataset in Brief §I has (a) a catalog row here, (b) a tracked `data/manifests/<dataset>.json`, (c) a `data/README.md` section. Missing any ⇒ fail. (cross-check table §7 must be 100%.)
- **G-DATA-3 — Reproduce-before-rewrite at the data level.** Loaded SN/BAO/CMB/WL products reproduce the published central values to tolerance at the *fiducial* published cosmology before any `Ξ`: DESI BAO χ² and Pantheon+ χ²_SN within 5% of published; reconstructed `S_8` (DES Y6) within published 1σ; reconstructed `H_0` (Planck) = 67.4±0.5 band. Cells tagged `recomputability=summary_only` (e.g. a published-posterior-only time-delay variant or single-event siren) are **exempt** from this recomputation check. *Fail → cannot proceed to E1.* (`idea.md` §10.1; Brief §VI.3)
- **G-DATA-4 — Cross-tool consistency.** `pyccl`-predicted `σ_8`/`f σ_8` for a survey's fiducial cosmology agrees with the survey's own quoted value within 0.5% (ties to `plan/02` G-ENV-4); BAO `D_M/r_d`, `D_H/r_d` from CLASS match the DESI z_eff convention used to read the data vector. *Fail → block growth/geometry use.*
- **G-DATA-5 — Fallback boundedness.** When a Gaussian/compressed fallback replaces a full likelihood, the fallback's χ² at the published best fit is within 10% of the full-likelihood χ² (where the full is ever available for spot-check), and the information loss is documented. `recomputability=summary_only` sources (no full likelihood ever available to spot-check against) are exempt from the χ² bound but MUST still document the information loss and carry the appropriate status. *Fail → escalate fallback status beyond `budgeted` or block.*
- **G-DATA-6 — Route taggedness (Hubble sector).** Every §6 source carries a non-null `route` and `staging_axis`; the `route_matrix.json` has ≥ 6 distinct routes (CMB→BAO/inverse-ladder, Cepheid→SN, TRGB→SN, JAGB→SN, time-delay, siren) so E4 can form a non-degenerate matrix and at least one closed route loop for `𝔥_γ`. *Fail → block E4 (Hubble holonomy / lawful plurality).* (`idea.md` UPDATE)
- **G-DATA-7 — Provenance integrity.** Every loaded raw file's sha256 matches its manifest; every manifest has all §8.1 keys populated; every run manifest records the dataset manifests it used. Any mismatch/missing key ⇒ data is `unaudited`, run not citable. *Fail → block.* (Brief §III.B, §VI.7; `plan/01` G-REPO-6/G-REPO-7)
- **G-DATA-8 — No unstatused fallback.** Any `access ≠ official_likelihood` has `fallback_invoked=true` and `aor_status ∈ {budgeted, approved_other, out_of_scope, …}` with a justification; `unstatused` anywhere is a hard fail. *Fail → block.* (`Audited_Operational_Realisability`: No Unstatused Residual)
- **G-DATA-9 — SN-dataset-dependence recorded, not hidden.** The Pantheon+ vs Union3 vs DES-SN5YR difference in the DE preference (2.8–4.2σ band, `idea.md` §6 Exp1) is computed and stored per SN compilation as a *packaging signal*, not averaged away. *Fail (if a single SN result is silently used) → block the E1 claim.*

---

## 11. Lawful-plurality acceptance for the Hubble route data (operationalizing `idea.md` UPDATE)

The UPDATE block insists local-local `H_0` disagreement is a *positive prediction* (route holonomy), but must satisfy pass/fail so critics cannot say "you relabeled scatter as theory." The data layer must deliver inputs that make these five tests runnable in E4:

1. **Route structure:** offsets between Cepheid→SN, TRGB→SN, JAGB→SN, inverse-ladder, time-delay organize by bridge route, not randomly → data must be route-tagged (G-DATA-6) with declared bridges.
2. **Staging structure:** changing redshift cuts / host cuts / anchor / BAO–SN compression moves `H_0^{(r)}` predictably → loaders expose the staging axes (e.g. `load_hsc_y3(photoz=…)`, SN sample selection, anchor choice) as mutable columns.
3. **Closure transport:** transporting a `H_0` posterior around a route loop exposes nonzero holonomy `𝔥_γ` → store full posteriors (not just means) for SH0ES/TDCOSMO/siren where released.
4. **Residual reuse:** the same `Ξ_cosmo` explaining Hubble fragmentation must also fit DESI `w(z)`, distance-duality, and growth → the Hubble data is loaded alongside, not instead of, the geometry/growth products (§§2–5).
5. **Source refinement:** adding genuine hidden-variable/heterogeneity proxies reduces the residual; adding unrelated route-specific nuisance terms does not count → manifests distinguish *physical staging columns* from *nuisance* so E4 can enforce this.

Quantitative bar (computed in E4, data-readiness gated here): the route-structured `Ξ_cosmo` model (≤3 free params, shared with §§2–5) must beat the unrelated-noise nuisance model `H_0+ε_{r,ℓ}` by ΔBIC ≥ 6 (positive evidence) on the route matrix; otherwise the Hubble-as-holonomy claim is downgraded to `recognized_grade`. Data-layer responsibility: ensure ≥6 routes × ≥2 staging columns are populated so this comparison is non-degenerate.

---

## 12. Consistency check against the SHARED GROUNDING BRIEF

- Releases/DOIs/Zenodo handles match Brief §I exactly (DESI DR2 2503.14738; Planck 2018 1807.06209; SPT-3G D1 2506.20707 (+ 2018 2212.05642); ACT 2509.02945; Pantheon+ 2202.04077; Union3 2401.06956; DES-SN5YR Zenodo:13827844; DES Y6 2601.14559; DES Y3 2212.00091; KiDS-Legacy 2503.19441; HSC Y3 2511.18134; DESI DR1 FS 2411.12026 (DR2 RSD leg = compressed fσ₈); SH0ES 2509.01667; CCHP 2408.06153; TDCOSMO 2110.00517; siren 1709.05895).
- File formats and the internal `(data_vector.npy, covariance.npy, meta.json)` representation follow Brief §V.A; SN/BAO Gaussian fallbacks follow Brief §V.B (`gaussian_likelihood_covmat`).
- Every "Fallback" cell names a *concrete* compressed/Gaussian likelihood or published summary posterior, as Brief §I requires, and assigns an AOR status (Brief §VI vocabulary; `Audited_Operational_Realisability`).
- Provenance/manifest convention (§8) is the Brief §III.B run manifest + `plan/01` §4 tracked dataset manifest, extended with the AOR-status, route, and fallback-invoked fields this program needs.
- Pass gates (§10) instantiate Brief §VI items 1, 3, 6, 7 plus the no-unstatused-residual discipline and the reproduce-before-rewrite standard (`idea.md` §10.1).
- The Hubble route substrate (§6, §11) operationalizes the `idea.md` post-§10 UPDATE (route matrix, holonomy, lawful plurality) as concrete, route-tagged, posterior-preserving data with quantitative acceptance.
