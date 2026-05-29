# E0 — Synthetic, Data-Free Demonstrations (the do-first sanity layer)

> **Charter (one line).** Before touching any real dataset, build four deterministic, fully
> self-contained synthetic demonstrations that exhibit the Six Birds mechanism end-to-end: a
> null-Λ heterogeneous patch generator that a homogeneous ΛCDM fit mis-reads as `Ω_Λ > 0`; a
> nonlinearity-driven route-mismatch sweep; a positive/stable audit-closed rewrite operator whose
> induced `w_eff(z)` crosses −1 with a stable readout (no growing mode); and a synthetic Hubble
> route-matrix with an injected `XiToy` that the fit recovers.
>
> **Why first.** E0 is the *mechanism proof* that the whole program rests on. It requires no data,
> no Boltzmann code, and no MCMC; it must run in minutes on one CPU and reproduce to float64 epsilon.
> If E0 does not pass, every downstream experiment (E1–E8) is built on sand. E0 is therefore the
> gate that unblocks the real-data pipeline.

**Grounding.**
- `idea.md` §2 ("What to keep and what to upgrade") — *"keep the toy result where a null-Λ,
  heterogeneous generator is fit by homogeneous ΛCDM and returns an apparent positive Ω_Λ. That is
  the cleanest Six Birds mechanism demo."*
- `idea.md` §5 ("Synthetic experiments") — *"Null-Λ heterogeneous generator; homogeneous ΛCDM fit
  recovers apparent Ω_Λ; effective w(z) crosses −1; no unstable scalar exists."*
- `idea.md` §4 (the four residuals `δ_p`, `RM_p`, `LG_{p,q}`, `PPD_{p→q}`) and §5 (the low-rank
  `Ξ_cosmo` ansatz and the rewrite `H(z)² = H_m(z)² + Δ_H(z)`).
- `idea.md` UPDATE block (Hubble readout field `H₀^{(r,ℓ)} = H_closed(0) + K_{r,ℓ}[Ξ]`, route
  matrix, Hubble holonomy `𝔥_γ`, lawful plurality) — the target of Toy 4.
- **Corpus precursor:** `docs/papers/Tsiokos_2026_A_Six_Birds_Eye_View_of_Dark_Energy_*.tex`
  (hereafter **DE-precursor**). Toy 1 and Toy 2 below are the *exact* constructions from
  §§4.1–4.4 of that paper (Eqs. `toy1_dynamics`, `toy2_rho_scaling`, `toy2_ai_ode`,
  `toy2_hi_closure`, `toy2_aD`, `toy2_Q_def`, `synthetic_z_def`, `chi_def`, `rewrite_general`,
  `rewrite_powerlaw`). The precursor reports the headline numbers we must reproduce:
  `RM_max ≈ 2.03e-2` at `β=0.5`, `RM_max ≈ 8.10e-2` at `β=2.0`; `Q_peak ≈ 1.74`, late-time
  `ä_𝒟 > 0` fraction `≈ 0.988`; and **homogeneous ΛCDM fit to the null-Λ generator recovers
  `Ω_Λ ≃ 0.60`**, with the heterogeneity-proxy rewrite matching ΛCDM fit quality and improving
  held-out prediction of a heterogeneity proxy by `~100×` in RMSE.
- `docs/papers/Tsiokos_2026_Adequacy_Residuals_*.tex` — the Schur-complement `Ξ`; here used only as
  the conceptual identity for "residual = what the native lens cannot see," not numerically in E0.
- `docs/papers/Tsiokos_2026_Holonomy_with_Memory_*.tex` and `…_Protocol_Trap_*.tex` — route
  transport and the discipline that *route dependence alone is not evidence*; Toy 4 must therefore
  separate structured (recoverable) holonomy from unstructured route noise.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_IV_*.tex` — `F2` (Descent-Repair Normal Form,
  ties to Toy 1/Toy 2 rewrite), `F4` (Local-Global Obstruction), `F9` (No Unstatused Residual),
  `F11` (No-Overread). Toy 3 is the finite witness underlying **Proposition P4** (overview §5).
- `docs/papers/Tsiokos_2026_Emergence_IS_the_Needle_Killer.tex` — the *membrane discipline*
  (positive native currency / stable operator) that the Toy 3 rewrite operator must satisfy.
- `docs/papers/Tsiokos_2026_Audited_Operational_Realisability_*.tex` — AOR statuses for the residual
  ledger (GROUNDING_BRIEF §6 vocabulary).

**Consistency note.** All datasets, software versions, seed policy, manifest schema, float64 rule,
and AOR status vocabulary follow `../GROUNDING_BRIEF.md`. E0 uses **only the "Toy heterogeneous
nonlinear closure" compute row** of the brief (8 CPU, 0.5–2 h, no GPU, ~100 realizations). No
network access, no `data/` payloads, no external likelihood code.

---

## 0. Scope, residuals exercised, shadow-map rows, AOR stratum

| Field | Value |
|---|---|
| Experiment ID | `E0` (dir `experiments/E0_synthetic/`) |
| Residuals exercised | `δ_p` (idempotence), `RM_p` (route mismatch); Toy 4 additionally exercises the Hubble-readout/holonomy diagnostics `K_{r,ℓ}`, `𝔥_γ` |
| Shadow-map rows (overview §3) | **1** (cosmological constant — Λ as constant chart), **3** (DESI `w(z)` — redshift chart), **5** (phantom crossing — derivative chart), **2** (Hubble — calibration-currency chart, via Toy 4) |
| AOR stratum | `PreSB → operator-rewrite`; Toy 3 produces a `RefStableAOR`-grade finite witness for P4; Toy 4 produces a `route`-grade holonomy witness feeding E4 |
| Propositions touched | **P4** (phantom crossing with stable readout) gets its finite numerical witness here; **P1 operator-rewrite extension of F2** (descent-repair: the rewrite is the P1 chart layered on F2's obstruction) is illustrated; **F9** (no unstatused residual) enforced on the E0 ledger |
| Compute | 8 CPU, < 2 h wall, ≤ 4 GB, deterministic; no MCMC, no Boltzmann code |
| Blocks (unblocks) | E1 (reproduction pipeline shares the `xi/rewrite.py` + `Δ_H` machinery), E3 (consumes the Toy 3 stable-operator witness), E4 (consumes the Toy 4 route-matrix recovery harness) |
| Blocked by | `plan/01-repo-structure.md` (package skeleton `sbt_cosmo/`), `plan/02-environment-and-deps.md` (numpy/scipy/matplotlib pinned), `plan/00-overview.md` + `../GROUNDING_BRIEF.md` (definitions, gates, manifest schema) |

**Determinism contract (hard).** Every toy fixes `numpy` and `python` seeds from
`experiments/E0_synthetic/config.yaml` (see §7). No RNG outside the seeded generators. Reruns with
the same seed reproduce all reported numbers to `|Δ| < 1e-12` (relative) for derived scalars and to
float64 bitwise equality for raw arrays. There is **no sampler** in E0; "fit" means deterministic
`scipy.optimize` minimization with a fixed method, fixed start, and fixed tolerances.

---

## 1. Software, modules, and artifact layout

**Stack (subset of GROUNDING_BRIEF §II).** `numpy ≥ 1.24`, `scipy ≥ 1.10`, `matplotlib ≥ 3.5`,
`pyyaml`, `h5py`. **No** cobaya / CLASS / CAMB / CCL / getdist / cobaya needed for E0. Optional
Lean 4 (≥ v4.28.0) only for the `RouteMismatch.lean` anchor (§6.5).

**Package modules used (from `plan/01-repo-structure.md`).**
- `sbt_cosmo/audits/route_mismatch.py` — `RM(x) = d(E∘T x, T∘E x)` (Toy 1, Toy 2 sanity).
- `sbt_cosmo/audits/delta.py` — `δ(x) = d(E²x, Ex)` (idempotence sanity).
- `sbt_cosmo/audits/metrics.py` — the metric `d(·,·)` (Toy 1/2 use L2 on `ℝⁿ`; Toy 4 uses a
  posterior-pushforward / mean-shift distance).
- `sbt_cosmo/cosmology/background.py` — `H(z; θ)`, `χ(z)`, `D_L(z)`, `D_M(z)` for ΛCDM and
  matter-only macro families.
- `sbt_cosmo/xi/rewrite.py` — `Δ_H(z)`, the rewrite `H(z)² = H_m(z)² + Δ_H(z)`, and the
  `w_eff(z)` readout (Toy 2 fit, Toy 3 operator).
- `sbt_cosmo/xi/residual.py` — the low-rank residual ansatz `(z, ℓ, p)` (real-data instance is
  `Ξ_cosmo`; Toy 4 injects and recovers a *synthetic* `XiToy` instance, using the `a₀` constant
  chart and the `a₂ φ₂(z) c_p` calibration chart).
- `sbt_cosmo/xi/stability.py` — Jacobian eigenvalue / stable-readout (no-growing-mode) audit (Toy 3).
- `sbt_cosmo/hubble/route_matrix.py`, `…/transport.py`, `…/holonomy.py` — Toy 4.
- `sbt_cosmo/io/manifest.py`, `…/artifacts.py`, `…/checksums.py` — manifests + dumps.
- `sbt_cosmo/aor/ledger.py`, `…/status.py` — the E0 AOR status table.
- `sbt_cosmo/viz/residual_plots.py`, `…/style.py` — figures (fixed rcParams).

**E0 is a thin orchestrator.** `experiments/E0_synthetic/run.py` imports the package and only wires
config → generators → fits → audits → artifacts. No physics lives in `run.py`.

**Output tree (committed unless noted; see `plan/01-repo-structure.md` §7).**
```
experiments/E0_synthetic/
├── config.yaml                       # TRACKED — seeds, grid sizes, β-grid, patch params, route-matrix spec
├── run.py                            # TRACKED — orchestrator
├── README.md                         # TRACKED — charter + link to this file + gate summary
└── outputs/
    ├── manifest.json                 # TRACKED — run manifest (GROUNDING_BRIEF §III.B schema)
    ├── summary.json                  # TRACKED — every scalar gate value + pass/fail flags
    ├── aor_status.json               # TRACKED — E0 AOR status table (machine-readable)
    ├── tables/
    │   ├── toy1_rm_vs_beta.csv       # TRACKED — RM summary per β
    │   ├── toy2_Q_summary.csv        # TRACKED — Q_peak, late-time positive fraction, hom vs het
    │   ├── toy2_fit_summary.csv      # TRACKED — Ω_Λ (matter-only vs ΛCDM vs rewrite), χ², AIC, PPD
    │   ├── toy3_weff_crossing.csv    # TRACKED — w_eff(z) grid + crossing z, eigenvalue spectrum
    │   └── toy4_route_recovery.csv   # TRACKED — injected vs recovered XiToy params per route/staging
    ├── arrays/                       # TRACKED (small, < few MB) — npy/h5 of the deterministic mocks
    │   ├── toy2_mock_distances.npz   # z grid, D_obs, σ, a_𝒟(t), H_𝒟(t), Var(H_i) proxy
    │   ├── toy3_operator.npz         # Ξ params, ρ_eff(z), w_eff(z), Jacobian, eigenvalues
    │   └── toy4_route_matrix.npz     # H_0^{(r,ℓ)} table, injected XiToy, recovered XiToy, holonomy loop
    └── figures/
        ├── fig_toy1_rm_vs_beta.png   # TRACKED — RM_max vs β (reproduces DE-precursor Fig.)
        ├── fig_toy2_Q_vs_time.png    # TRACKED — Q(t) hom (≈0) vs het (positive)
        ├── fig_toy2_distance_fit.png # TRACKED — mock D_L(z), matter-only, ΛCDM, rewrite overlays
        ├── fig_toy3_weff.png         # TRACKED — w_eff(z) crossing −1; eigenvalue inset
        └── fig_toy4_route_matrix.png # TRACKED — H_0^{(r,ℓ)} heatmap: null / noise / SBT-XiToy recovery
```

---

## 2. Toy 1 — Route mismatch rises with nonlinearity

**Purpose.** Isolate the *origin* of route mismatch: nonlinear micro-evolution + an
information-losing lens ⇒ `E∘T ≠ T∘E`. This is the cleanest illustration that closure failure is a
property of (lens, completion, dynamics), not of any added "dark" substance. (`idea.md` §2 "keep the
precursor's core framing `E = U∘f`, `RM(x) = d(E T x, T E x)`"; DE-precursor §4.1.)

### Inputs (exact)
| Symbol | Meaning | Default |
|---|---|---|
| `n` | microstate dimension (`x ∈ ℝⁿ`) | `128` |
| `x₀` | initial microstate | i.i.d. `Uniform(0.2, 0.8)` from seeded RNG, fixed |
| `α` | linear drift coefficient | `1.0` |
| `Δt` | step size | `0.05` |
| `β-grid` | nonlinearity strengths | `{0.0, 0.5, 1.0, 2.0}` (must include `0.0` and the precursor's `0.5`, `2.0`) |
| `n_steps` | one-step diagnostic is enough; also report after `n_steps = 1` | `1` |

### Method
1. **Micro-dynamics** (DE-precursor Eq. `toy1_dynamics`):
   `x_{t+1} = x_t + Δt (α x_t − β x_t^{⊙2})`, elementwise squaring `x^{⊙2}`. Linear case `β = 0`.
2. **Lens** = mean (Eq. `toy1_lens_mean`): `f(x) = x̄ = (1/n) Σ x_i`.
3. **Completion** = constant-vector embedding (Eq. `toy1_completion_const`):
   `U(x̄) = (x̄, …, x̄) ∈ ℝⁿ`. Packaging `E = U∘f` maps any state to the constant vector with its mean.
4. **Idempotence sanity** `δ(x) = d(E²x, Ex)` (Eq. idempotence): must be `≤ 1e-12` for all `β`
   (constant-vector packaging is exactly idempotent up to float).
5. **Route mismatch** `RM(x) = d(E(T x), T(E x))`, with `d` = Euclidean L2 on `ℝⁿ`
   (`audits/metrics.py`). For a population, report `RM_max := max_x RM(x)` over the seeded `x₀`
   ensemble (the precursor's reported statistic) and `RM_mean`.
6. Sweep `β` over the grid; emit `toy1_rm_vs_beta.csv` and `fig_toy1_rm_vs_beta.png`.

### Outputs
- Table `toy1_rm_vs_beta.csv`: columns `β, RM_max, RM_mean, δ_max`.
- Figure `fig_toy1_rm_vs_beta.png`: `RM_max` (and `RM_mean`) vs `β`, monotone-increasing curve, with
  the `β=0` point at numerical zero.
- Scalars into `summary.json`: `toy1.RM_max_at_beta0`, `toy1.RM_max_at_beta0p5`,
  `toy1.RM_max_at_beta2`, `toy1.delta_max`, `toy1.monotone` (bool).

### Expected numbers (from DE-precursor §5.1, Table `toy1`)
- `β = 0`: `RM_max` at numerical zero (`≤ 1e-12`).
- `β = 0.5`: `RM_max ≈ 2.03e-2`.
- `β = 2.0`: `RM_max ≈ 8.10e-2`.
> These are the published precursor values **for the precursor's exact `(n, x₀-distribution, α, Δt)`
> setting**. We pin the same constants so the demo reproduces them. If our chosen constants differ
> from the precursor's (the precursor records them in its run bundle, not the manuscript), the *gate*
> is the qualitative-plus-ratio form in §8 (monotone increase, zero at `β=0`, and the
> `β=2 / β=0.5` ratio in the right ballpark), not exact decimal equality — and the chosen constants
> are logged in the manifest so the numbers are reproducible regardless.

---

## 3. Toy 2 — Null-Λ heterogeneous patch generator → apparent `Ω_Λ > 0`

**Purpose.** The flagship E0 demo (`idea.md` §2, §5). A generator with **no cosmological constant**
(`Λ ≡ 0`, dust only) but **heterogeneous** patches, viewed through a homogeneous volume-average
lens, produces an effective acceleration; fitting the resulting mock distance–redshift data with a
homogeneous ΛCDM model returns `Ω_Λ > 0` as a **closure-induced inference artifact**. Then a
heterogeneity-proxy rewrite term (`Δ_H`) matches ΛCDM fit quality with comparable parameter count
and *wins out-of-sample* on a heterogeneity proxy. This is the constant/redshift chart of `Ξ`
(shadow rows 1, 3) made concrete.

### 3a. The generator (null-Λ, heterogeneous; DE-precursor §4.2)

| Symbol | Meaning | Default / prescription |
|---|---|---|
| `N` | number of patches | `4096` |
| `ρ_{i0}` | initial patch densities | mean `ρ̄₀ = 1.0`, log-normal heterogeneity with amplitude `A_het` (below); seeded |
| `κ_i` | curvature-like proxy per patch | drawn correlated with `(ρ_{i0} − ρ̄₀)` so under/over-dense patches expand systematically differently; seeded |
| `A_het` | heterogeneity amplitude | sweep `{0.0 (homogeneous control), 0.3, 0.6}`; `0.6` is the "het" headline case |
| `g_{4π}` | plays the role of `4πG` (normalized) | `1.0` |
| `t-grid` | integration times | uniform on `[t_init, t₀]`, `n_t = 512`, `t_init` set so `a_𝒟` spans `z ∈ [0, ~1.5]` |
| `a_i(t_init)` | initial scale factors | `1e-2` (well inside matter domination), equal across patches |

Generator equations (verbatim from DE-precursor):
- Dust scaling (Eq. `toy2_rho_scaling`): `ρ_i(t) = ρ_{i0} a_i(t)^{−3}`.
- Local expansion (Eq. `toy2_ai_ode`): `ȧ_i = a_i H_i`.
- Friedmann-like closure (Eq. `toy2_hi_closure`): `H_i² = (g_{4π}/3) ρ_i + κ_i / a_i²`.
  **No Λ term anywhere** — this is the load-bearing point.
- Integrate each patch ODE deterministically (`scipy.integrate.solve_ivp`, method `DOP853`,
  `rtol=1e-10`, `atol=1e-12`, fixed; or fixed-step RK4 with `n_t` steps — method pinned in config).

### 3b. The lens + completion (homogenization)

- **Domain-average lens** (Eq. `toy2_aD`): `a_𝒟(t) = ⟨a_i(t)³⟩^{1/3}` (arithmetic mean over patches).
  Domain Hubble `H_𝒟 = ȧ_𝒟 / a_𝒟`. Heterogeneity proxy `Var(H_i)(t)` retained as the rewrite shape.
- **Acceleration proxy / closure term** (Eq. `toy2_Q_def`):
  `Q(t) = 3 ä_𝒟 / a_𝒟 + g_{4π} ⟨ρ_i⟩`. Positive `Q` = departure from homogeneous dust closure in the
  direction of an effective acceleration.
  > Document, per DE-precursor §5.2, that `Q` is a *closure diagnostic* for this proxy, **not** the GR
  > kinematical backreaction term; E0 does not claim a relativistic backreaction calculation.

### 3c. Redshift mapping + mock distances (DE-precursor §4.3)

- Normalize `a_𝒟(t₀) = 1`; define `1 + z(t) = a_𝒟(t)^{−1}` (Eq. `synthetic_z_def`) — monotone over the
  modeled interval.
- Comoving distance proxy `χ(z) = c ∫₀^z dz' / H_𝒟(z')` (Eq. `chi_def`), `D_L(z) = (1+z) χ(z)`.
- Mock data on a grid `{z_k}` (`n_z = 30`, log-spaced on `[0.02, 1.4]`):
  `D_obs_k = D_L(z_k) + ε_k`, `ε_k ~ 𝒩(0, σ_k²)` (Eq. `distance_mock`), seeded. `σ_k` = fixed
  fractional error (e.g. `2%` of `D_L(z_k)`, floor `σ_floor`), pinned in config.

### 3d. Macro-model fits (DE-precursor §4.3, §4.4)

Fit three homogeneous background families to `(z_k, D_obs_k, σ_k)` by minimizing the Gaussian
`χ²(θ) = Σ_k (D_obs_k − D_k(θ))² / σ_k²` (Eq. `chi2_def`); deterministic `scipy.optimize.minimize`,
method `L-BFGS-B`, fixed start, fixed bounds, fixed tolerances.

| Model | `H(z)` form | Free params | Notes |
|---|---|---|---|
| **M0: matter-only** | `H² = H₀² (1+z)³` (`Ω_Λ = 0` imposed) | `H₀` (and an overall distance scale if degenerate) | the "no dark energy" null |
| **M1: ΛCDM** | `H² = H₀² [Ω_m(1+z)³ + Ω_Λ]`, flat `Ω_Λ = 1 − Ω_m` | `H₀`, `Ω_m` (so `Ω_Λ` free) | **the homogeneous mis-fit** |
| **M2: SBT rewrite** | `H² = H_m(z)² + Δ_H(z)`, `Δ_H = A·g(z)` (Eq. `rewrite_powerlaw`) with **`g(z)` fixed to the generator's `Var(H_i)` heterogeneity proxy mapped to redshift** (Eq. proxy-derived), amplitude `A ≥ 0` the only DE-like free param | `H₀`, `A` (and `Ω_m` for the matter part) | the *least rewrite* tied to a measured mismatch proxy; positivity enforced so `H(z)² > 0` over the fit range |

**Information criteria.** Report `χ²_min`, `AIC = χ²_min + 2k`, `BIC = χ²_min + k ln(n_z)`
(`k` = number of fitted params) per model.

### 3e. The PPD / out-of-sample audit (DE-precursor §4.5)

The decisive Six Birds claim is not in-sample fit but **predictive closure** (`idea.md` §10 standard
3). Define a held-out heterogeneity-proxy target: the generator-level `Var(H_i)(z)` (a quantity the
homogeneous models cannot represent at all). Procedure:
1. Fit each model on the *distance* block `𝒟_A = {z_k, D_obs_k}` → `θ̂_A`.
2. Predict the *heterogeneity-proxy* block `𝒟_B = {z_k, Var(H_i)(z_k)}` from `θ̂_A`:
   - M0/M1 predict `Var(H_i) ≡ 0` (homogeneous ⇒ no spread).
   - M2 predicts `Var(H_i)(z) ∝ Δ_H(z)/g_norm` via the proxy mapping (the same `g(z)` shape).
3. Report `RMSE_{B|A}` (and `χ²_{B|A}` where a covariance is defined) for each model.

> Expected: M2's `RMSE_{B|A}` is `~100×` smaller than M0/M1 (DE-precursor abstract:
> *"improves held-out prediction of a heterogeneity proxy by ~100× in RMSE"*). M0/M1 cannot predict
> the proxy at all (it is identically zero for them), so the ratio is large and is the cross-probe
> demonstration that the *same* `Ξ`-derived term that fixes geometry also carries the heterogeneity
> information.

### Outputs
- `toy2_Q_summary.csv`: `A_het, Q_peak, late_time_pos_fraction, max_abs_Q_homogeneous`.
- `toy2_fit_summary.csv`: per model `{χ²_min, k, AIC, BIC, H₀, Ω_m, Ω_Λ (M1), A (M2), RMSE_{B|A}}`.
- `toy2_mock_distances.npz`: `z`, `D_obs`, `σ`, `a_𝒟(t)`, `H_𝒟(t)`, `Var(H_i)(z)`, `Q(t)`.
- Figures `fig_toy2_Q_vs_time.png` (hom `Q≈0` vs het `Q>0`), `fig_toy2_distance_fit.png`
  (mock + three model overlays + residual panel).
- Scalars into `summary.json`: `toy2.OmegaLambda_LCDM`, `toy2.Q_peak_het`, `toy2.Q_pos_fraction`,
  `toy2.Q_max_abs_homogeneous`, `toy2.chi2_M1`, `toy2.chi2_M2`, `toy2.ppd_rmse_ratio_M0_over_M2`,
  `toy2.ppd_rmse_ratio_M1_over_M2`.

### Expected numbers (DE-precursor §5.2 + abstract)
- Homogeneous control (`A_het = 0`): `Q` at numerical zero (`max|Q| ≤ ~1e-8`, machine precision in
  the precursor); ΛCDM fit returns `Ω_Λ` consistent with 0.
- Heterogeneous headline (`A_het = 0.6`): `Q_peak ≈ 1.74`, late-time `ä_𝒟 > 0` fraction `≈ 0.988`.
- **Homogeneous ΛCDM mis-fit of the null-Λ generator: `Ω_Λ ≃ 0.60`** (the flagship result).
- M2 rewrite matches M1 ΛCDM fit quality (`Δχ² small`, comparable `k`) and beats M0/M1 by `~100×` on
  held-out `RMSE_{B|A}`.

---

## 4. Toy 3 — Positive, stable, audit-closed rewrite operator with `w_eff(z)` crossing −1 (stable readout, no growing mode)

**Purpose.** The finite numerical witness for **Proposition P4** (overview §5; `idea.md` §6
Experiment 3): construct a *positive, stable, audit-closed* rewrite operator whose induced
effective equation of state `w_eff(z)` crosses the phantom divide `w = −1`, while the underlying
object has **stable effective readout with no growing mode** (REGISTRY §5; the no-negative-kinetic-DOF / ghost-absence claim is `out_of_scope` absent a Lagrangian/kinetic-metric framework). This addresses, at the readout level, the ghost-instability
objection by showing phantom crossing is a property of the *effective readout*, not of a fundamental
Lagrangian d.o.f. (shadow row 5, the derivative chart). Discipline follows
`Emergence IS the Needle Killer` (positive native currency, stable operator membrane).

### Inputs (exact)
| Symbol | Meaning | Default |
|---|---|---|
| `z-grid` | redshift grid | `n_z = 400`, linear on `[0, 1.5]` (must bracket the crossing) |
| `Ω_m` | matter fraction (for the matter background) | `0.30` |
| `H₀` | normalization | `70.0 km/s/Mpc` (units cancel in `w_eff`) |
| `Δ_H` ansatz | rewrite shape | a **two-term** positive-definite rewrite: `ρ_eff(z) = c₀ + c₁ (1+z)^{p}` with `c₀ > 0`, `c₁ ≥ 0`, and a smooth low-rank modulation that makes `d ln ρ_eff/dz` change sign — see §4 method. Parameters pinned in config so the crossing is deterministic. |

### Method
1. **Effective DE density from the rewrite.** Write the macro `H(z)² = H₀²[Ω_m(1+z)³ + Ω_eff(z)]`
   with `Ω_eff(z) = ρ_eff(z)/ρ_crit,0`. The rewrite operator acts on the macro state; we require
   `ρ_eff(z) > 0` everywhere on the grid (positivity of the native currency — the "stable readout (no
   growing mode) in the *energy density*" condition). Choose `ρ_eff(z)` so that its logarithmic slope changes sign across
   the interval (this is what forces the crossing, see step 3). A concrete, deterministic choice:
   `ρ_eff(z) = ρ₀ [1 + ε·sin-free bump]`, implemented as a sum of two positive monotone pieces with
   opposite-sign slopes whose net `d ln ρ_eff/dz` passes through 0 inside `[0,1.5]`. The exact closed
   form is fixed in `xi/rewrite.py` and pinned in config; the *requirement* (not the exact bump
   shape) is: `ρ_eff > 0` everywhere and `d ln ρ_eff/dz` changes sign once.
2. **`w_eff(z)` readout** (`idea.md` §6 Eq. for `w_eff`):
   `w_eff(z) = −1 + (1+z)/3 · d/dz [ln ρ_eff(z)]`.
   Compute the derivative analytically where possible, else by a fixed central-difference stencil on
   the pinned `z-grid`. `w_eff < −1 ⇔ d ln ρ_eff/dz < 0` (ρ_eff decreasing in `z`, i.e. growing
   toward the future).
3. **Crossing.** By construction `d ln ρ_eff/dz` changes sign once on `[0,1.5]` ⇒ `w_eff` crosses
   `−1` exactly once at some `z_×`. Report `z_×` (bisection on the pinned grid) and the values
   `w_eff(0)`, `w_eff(1.5)` bracketing −1.
4. **Stability / stable-readout audit** (`xi/stability.py`, ties to `Emergence IS the Needle Killer`):
   - **(i) Energy-density positivity:** `ρ_eff(z) > 0` for all grid `z` (already imposed) — the
     effective component carries a *positive* native currency.
   - **(ii) Background dynamical stability:** linearize the discrete macro evolution map
     `(a, ρ_eff) ↦ (a', ρ_eff')` (one step of the deterministic forward map used to generate the
     history) about the trajectory; compute the Jacobian `J(z)` at each grid point and its eigenvalue
     spectrum `{λ_j(z)}`. **Stable-readout witness:** require `Re(λ_j) ≤ 0` for all `j`, all `z` (no growing
     mode), equivalently the discrete map is non-expanding in the audited norm. This is the finite
     analogue of "no wrong-sign kinetic term." Report `max_z max_j Re(λ_j(z))`.
   - **(iii) Optional sound-speed-style check:** confirm the effective fluid's perturbation proxy
     `c_eff² ≥ 0` where defined (a fixed finite-difference proxy on `ρ_eff`); record it but the
     binding witness is (i)+(ii).
5. Emit the spectrum, `w_eff(z)`, `z_×`, and the figure.

### Outputs
- `toy3_weff_crossing.csv`: columns `z, rho_eff, dln_rho_dz, w_eff`, plus a header block with
  `z_cross`, `w_eff(0)`, `w_eff(1.5)`, `max_Re_eig`, `min_rho_eff`, `c_eff2_min`.
- `toy3_operator.npz`: `z`, `rho_eff`, `w_eff`, `Jacobian` (stacked), `eigenvalues`.
- Figure `fig_toy3_weff.png`: `w_eff(z)` crossing the `−1` line, with an inset of the eigenvalue
  real parts (all `≤ 0`) and a `ρ_eff(z) > 0` panel.
- Scalars into `summary.json`: `toy3.z_cross`, `toy3.weff_min`, `toy3.weff_max`,
  `toy3.crosses_minus_one` (bool), `toy3.max_Re_eig`, `toy3.min_rho_eff`, `toy3.stable_readout` (bool).

### Expected behavior
- `w_eff(z)` is `> −1` on one side of `z_×` and `< −1` on the other ⇒ a genuine phantom crossing.
- `min_rho_eff > 0` (positive native currency) and `max_Re_eig ≤ 0` (no growing mode) ⇒
  the crossing is achieved by a **stable, positive** rewrite (a stable effective readout / no growing mode); the Lagrangian-level ghost-absence claim is `out_of_scope`.
- This is exactly the P4 witness consumed by E3 and the Lean `RouteMismatch`/stability anchor.

---

## 5. Toy 4 — Synthetic Hubble route-matrix with an injected `XiToy` that the fit recovers

**Purpose.** A data-free dress rehearsal for E4 (`idea.md` UPDATE block). Build a synthetic Hubble
route-matrix `H₀^{(r,ℓ)}` from a **known injected** synthetic closure residual `XiToy_inj` (the
data-free analogue of the real-data `Ξ_cosmo`; E0 fits `XiToy`, never `Ξ_cosmo`), then show that
(a) the SBT route-matrix fit **recovers** `XiToy_inj` (rows organize by route + staging =
*lawful plurality*), (b) the **null** model `K_{r,ℓ}[XiToy] = 0` is rejected, and (c) the **naive
nuisance** model (each route gets an unrelated free offset `ε_{r,ℓ}`) does *not* beat the low-rank
SBT model on parameter economy (BIC), even though it can fit any pattern. Also compute the **Hubble
holonomy** `𝔥_γ` around a route loop and confirm it is nonzero when `XiToy_inj ≠ 0` and zero when
`XiToy_inj = 0`. (Shadow row 2.)

### 5a. Routes and staging (mirror `idea.md` UPDATE block)
Rows `r` (routes), using the seven the UPDATE block names:
`r₁ = CMB→BAO`, `r₂ = BAO→SN`, `r₃ = Cepheid→SN`, `r₄ = TRGB→SN`, `r₅ = JAGB→SN`,
`r₆ = time-delay`, `r₇ = standard-siren`.
Columns `ℓ` (staging/bridge choices): e.g. `{z-cut_low, z-cut_high, host-cut, anchor-A, anchor-B,
BAO-compression, SN-sample}` — `n_ℓ = 6` (pinned in config). Each route has a known sensitivity
kernel `K_{r,ℓ}` (a fixed, hand-specified loading matrix in `hubble/route_matrix.py` reflecting how
each route depends on the constant `a₀` chart and the calibration `a₂ φ₂(z) c_p` chart of `XiToy`).

### 5b. The three generative models on the route matrix (`idea.md` UPDATE block)
| Model | `H₀^{(r,ℓ)}` | Free params |
|---|---|---|
| **Null** | `H_closed(0)` (single scalar; `K[XiToy] = 0`) | `1` |
| **Naive nuisance** | `H₀ + ε_{r,ℓ}`, independent offsets | `n_r · n_ℓ` (`= 42`) |
| **SBT (low-rank)** | `H_closed(0) + K_{r,ℓ}[XiToy]`, with `XiToy` the **low-rank ansatz** (`a₀` constant chart + `a₂ φ₂(z) c_p` calibration chart) | `1 + (≤3)` (`H_closed` + `a₀`, `a₂`, and a shape param) |

### 5c. Method
1. **Inject.** Choose `XiToy_inj = (a₀*, a₂*, shape*)` and a true `H_closed*` (pinned in config). Build the
   *true* route matrix `H₀^{(r,ℓ),true} = H_closed* + K_{r,ℓ}[XiToy_inj]`. Add seeded measurement noise
   `η_{r,ℓ} ~ 𝒩(0, s_{r,ℓ}²)` with realistic per-route scatter `s_{r,ℓ}` (informed by GROUNDING_BRIEF
   §I.F quoted ±: SH0ES `~0.9`, CCHP TRGB `~1.3` total, etc.) to make the recovery nontrivial but
   deterministic.
2. **Fit** all three models by deterministic least-squares / `scipy.optimize` (fixed start/tol).
   Report `χ²`, `k`, `AIC`, `BIC` per model.
3. **Recovery check.** Compare recovered `(â₀, â₂, shape, Ĥ_closed)` to the injected truth; report
   per-parameter relative error and a joint recovery flag.
4. **Holonomy** (`hubble/transport.py`, `…/holonomy.py`; `idea.md` UPDATE,
   `Holonomy_with_Memory`). Define a route loop `γ = r₁ → r₃ → r₄ → r₁`. Build the bridge transport
   `B_γ` (composition of declared exchange-rate maps between route posteriors; here Gaussian
   posteriors `P(H₀^{r})` summarized by mean+variance, so `B_γ` is an affine push). Compute
   `𝔥_γ = B_{γ#} P(H₀^{r₁}) ⊖ P(H₀^{r₁})` as the mean (and variance) shift after transport around the
   loop. Report `|𝔥_γ|` (mean component) for: (i) the injected-`XiToy` truth, (ii) the SBT-fit
   reconstruction, (iii) the `XiToy = 0` null.
5. **Lawful-plurality test** (the five UPDATE-block conditions, here in synthetic form): confirm the
   recovered route offsets are *structured by `(r, ℓ)` through `K_{r,ℓ}`* (low-rank explains them),
   not white noise — i.e. SBT's low-rank model achieves essentially the nuisance model's `χ²` with
   far fewer parameters (lower BIC), and the residual after SBT is consistent with the injected noise
   `s_{r,ℓ}`.

### Outputs
- `toy4_route_recovery.csv`: injected vs recovered `XiToy` params, relative errors; per-model
  `χ², k, AIC, BIC`; `|𝔥_γ|` for truth / SBT / null.
- `toy4_route_matrix.npz`: `H₀^{(r,ℓ)}` true / noisy / SBT-fit / null-fit / nuisance-fit; loadings
  `K_{r,ℓ}`; loop spec; transport operators.
- Figure `fig_toy4_route_matrix.png`: a `7×6` heatmap of `H₀^{(r,ℓ)}` (true vs SBT-recovered vs
  null residual), with the holonomy loop annotated.
- Scalars into `summary.json`: `toy4.a0_relerr`, `toy4.a2_relerr`, `toy4.Hclosed_relerr`,
  `toy4.recovery_ok` (bool), `toy4.BIC_SBT`, `toy4.BIC_null`, `toy4.BIC_nuisance`,
  `toy4.holonomy_truth`, `toy4.holonomy_SBT`, `toy4.holonomy_null`.

### Expected behavior
- SBT recovers `XiToy_inj` within tolerance (§8); `recovery_ok = true`.
- `BIC_SBT < BIC_null` (null rejected) **and** `BIC_SBT < BIC_nuisance` (low-rank beats per-route
  free offsets on economy) ⇒ lawful plurality, not random scatter.
- `holonomy_truth > 0` and `holonomy_SBT ≈ holonomy_truth` (nonzero, recovered); `holonomy_null ≈ 0`
  by construction in a separate `XiToy_inj = 0` control run.

---

## 6. AOR ledger, Lean anchor, and proposition linkage

### 6.1 AOR status table (mandatory; `aor/ledger.py`, GROUNDING_BRIEF §6)
Every E0 residual/diagnostic gets a status. Expected end-of-E0 statuses (machine-readable
`aor_status.json`):

| Residual / object | E0 result | AOR status |
|---|---|---|
| `δ` (idempotence, all toys) | `≤ 1e-12` | `zero` |
| `RM` linear control (Toy 1, `β=0`) | `≤ 1e-12` | `zero` |
| `RM` nonlinear (Toy 1, `β>0`) | strictly positive, monotone in `β` | `budgeted` (explained by nonlinearity, quantified) |
| `Q` homogeneous control (Toy 2, `A_het=0`) | `≈ 0` | `zero` |
| `Q` heterogeneous (Toy 2) | `Q_peak ≈ 1.74`, late `ä>0` | `budgeted` (sourced to heterogeneity proxy) |
| Apparent `Ω_Λ` (Toy 2 ΛCDM mis-fit) | `≃ 0.60` | `bridged` (re-expressed via `Δ_H` rewrite; documented as a closure artifact, not a substance) |
| Phantom crossing / ghost worry (Toy 3) | crossing with `Re(λ)≤0`, `ρ_eff>0` | `bridged` (P4 witness: effective readout, stable readout / no growing mode) |
| Hubble route plurality (Toy 4) | low-rank `XiToy` recovers the matrix; `𝔥_γ>0` | `bridged` (lawful plurality; structured, recovered) |
| Synthetic-vs-real gap | E0 uses no data | `out_of_scope` (E0 is mechanism-only; real-data closure deferred to E1–E8) |

**F9 enforcement.** No `unstatused` entries may remain. The ledger writer fails the run if any E0
diagnostic lacks a status.

### 6.2 Lean anchor (optional but targeted; `formal/.../RouteMismatch.lean`)
- **Toy 1 commutation lemma.** Mechanize the precursor's exact lemma (DE-precursor Lemma
  "Commutation implies zero route mismatch"): if `E∘T = T∘E` as functions then `RM(x) = 0` for all
  `x`. This anchors the `β=0` zero and the meaning of `RM > 0` as genuine non-commutation.
- **Toy 3 / P4 stability witness.** Provide a *verified-computation* witness that the finite Jacobian
  spectrum satisfies `Re(λ_j) ≤ 0` while the discrete `w_eff` sequence crosses `−1` — i.e. a
  finite, checkable certificate (interval/rational bound on the eigenvalues of the pinned operator)
  that there is a stable readout (no growing mode). This is the Lean side of Proposition P4 (overview §5). Full Lean
  proof of the abstract P4 is not required in E0; the finite witness is.
- These are the only Lean obligations E0 carries; everything else is numerical.

### 6.3 Proposition linkage (overview §5)
- **P1 / F2 (Descent-Repair Normal Form).** Toy 2 illustrates it: homogeneous FLRW descent of the
  heterogeneous generator fails (`Q > 0`); the admissible repair chosen is **operator rewrite**
  (`Δ_H`) — the **P1 operator-rewrite extension** layered on F2's failed-descent obstruction (NOT an F2 repair; F2 supplies only source refinement + minimal target coarsening). Logged, not proved, in E0.
- **P4 (phantom crossing with stable readout).** Toy 3 is its finite witness (§4, §6.2).
- **F9 (No Unstatused Residual).** Enforced by the E0 ledger (§6.1).
- **F11 (No-Overread).** Toy 2's framing of apparent `Ω_Λ` as a closure artifact (not the QFT
  vacuum scalar) is the synthetic illustration; the formal P2 lives in `plan/04-formal-foundations.md`.

---

## 7. Configuration, manifest, and determinism

`experiments/E0_synthetic/config.yaml` (TRACKED) fully determines the run. Required blocks:
```yaml
schema_version: 1
seed:
  numpy: 4242
  python: 4242
toy1:
  n: 128
  alpha: 1.0
  dt: 0.05
  beta_grid: [0.0, 0.5, 1.0, 2.0]
  x0_dist: {kind: uniform, low: 0.2, high: 0.8}
toy2:
  N_patches: 4096
  A_het_grid: [0.0, 0.3, 0.6]
  g4pi: 1.0
  n_t: 512
  a_init: 1.0e-2
  rho_bar0: 1.0
  integrator: {method: DOP853, rtol: 1.0e-10, atol: 1.0e-12}
  zgrid: {n_z: 30, z_min: 0.02, z_max: 1.4, spacing: log}
  sn_sigma: {frac: 0.02, floor: 1.0e-3}
toy3:
  zgrid: {n_z: 400, z_min: 0.0, z_max: 1.5, spacing: linear}
  Om: 0.30
  H0: 70.0
  rho_eff: {form: two_positive_pieces, params: {c0: ..., c1: ..., p: ..., bump: ...}}  # pinned so crossing is deterministic
toy4:
  routes: [CMB_BAO, BAO_SN, Cepheid_SN, TRGB_SN, JAGB_SN, time_delay, siren]
  staging: [zcut_low, zcut_high, host_cut, anchor_A, anchor_B, BAO_comp]
  H_closed_true: 70.0
  XiToy_inj: {a0: ..., a2: ..., shape: ...}    # pinned injected synthetic truth
  route_scatter: {CMB_BAO: 0.5, BAO_SN: 0.6, Cepheid_SN: 0.9, TRGB_SN: 1.3, JAGB_SN: 1.6, time_delay: 1.8, siren: 8.0}
  loop: [CMB_BAO, Cepheid_SN, TRGB_SN, CMB_BAO]
  run_null_control: true                    # second run with XiToy_inj = 0 for holonomy null
optimizer: {method: L-BFGS-B, maxiter: 10000, ftol: 1.0e-12}
float_dtype: float64
```

**Run manifest** (`outputs/manifest.json`, GROUNDING_BRIEF §III.B schema): `run_id`, ISO `date`,
`seeds`, `datasets: []` (empty — E0 is data-free; this absence is itself recorded), `software`
(numpy/scipy/matplotlib/h5py versions), `parameters` (the full resolved config), `output_files`,
`audit_status`. `run.py` order (mirrors `plan/01-repo-structure.md` §7): (1) load config,
(2) verify no external data is requested (assert `datasets == []`), (3) set all seeds,
(4) run Toy 1–4 deterministically, (5) write arrays/tables/figures, (6) write manifest, (7) write
AOR ledger, (8) evaluate + record pass/fail gates into `summary.json`.

**Reproducibility gate.** A second invocation with the same config reproduces `summary.json` scalar
fields to `|Δrel| < 1e-12` and all `arrays/*.npz` to bitwise equality. `tests/test_gates.py` reads
the committed `summary.json` and re-checks every gate below **without re-running** the toys.

---

## 8. Pass / fail gates (quantitative, pre-registered)

> All thresholds are **pre-registered** (overview §6): they may not be relaxed after seeing results;
> any relaxation must be logged as a statused deviation in the manifest. A gate verifier reads
> `summary.json` and emits `pass`/`fail` per row. **E0 passes iff all G-gates pass.**

### 8.1 Toy 1 (route mismatch vs nonlinearity)
| Gate | Quantity | Threshold |
|---|---|---|
| G-E0-1.1 | `δ_max` (idempotence, all β) | `≤ 1e-10` |
| G-E0-1.2 | `RM_max` at `β = 0` (linear control) | `≤ 1e-10` (numerically zero) |
| G-E0-1.3 | `RM_max` strictly increasing across the β-grid | monotone: `RM_max(β_{k+1}) > RM_max(β_k)` for all consecutive `β` |
| G-E0-1.4 | `RM_max` at `β = 0.5` and `β = 2.0` strictly positive | both `> 1e-3` |
| G-E0-1.5 | nonlinearity-scaling sanity | `RM_max(2.0) / RM_max(0.5)` in `[2.0, 8.0]` (precursor ratio `≈ 8.10e-2 / 2.03e-2 ≈ 3.99`; band allows constant-choice variation) |

### 8.2 Toy 2 (null-Λ generator → apparent `Ω_Λ`)
| Gate | Quantity | Threshold |
|---|---|---|
| G-E0-2.1 | homogeneous control `max|Q|` (`A_het = 0`) | `≤ 1e-6` (consistent with numerical zero) |
| G-E0-2.2 | heterogeneous `Q_peak` (`A_het = 0.6`) | `> 1.0` (precursor `≈ 1.74`); band: `Q_peak ∈ [1.0, 2.5]` |
| G-E0-2.3 | late-time positive-acceleration fraction (het) | `≥ 0.95` (precursor `≈ 0.988`) |
| G-E0-2.4 | **apparent `Ω_Λ` from homogeneous ΛCDM mis-fit (het)** | `Ω_Λ ∈ [0.4, 0.75]` (precursor `≃ 0.60`); **and** strictly `> 0.2` (the headline: a null-Λ generator yields apparent dark energy) |
| G-E0-2.5 | ΛCDM control on homogeneous generator | recovered `Ω_Λ < 0.1` (no spurious DE when there is no heterogeneity) |
| G-E0-2.6 | rewrite (M2) in-sample fit quality vs ΛCDM (M1) | `χ²_M2 ≤ χ²_M1 + 2·(k_M1 − k_M2 baseline)`; concretely `|χ²_M2 − χ²_M1| / n_z ≤ 0.1` with `k_M2 ≤ k_M1 + 1` |
| G-E0-2.7 | **out-of-sample heterogeneity-proxy prediction** | `RMSE_{B|A}(M1) / RMSE_{B|A}(M2) ≥ 10` (precursor `~100×`; gate set conservatively at 10×) |

### 8.3 Toy 3 (phantom crossing with stable readout — P4 witness)
| Gate | Quantity | Threshold |
|---|---|---|
| G-E0-3.1 | `w_eff` genuinely crosses −1 | `w_eff(0)` and `w_eff(z_max)` on opposite sides of −1; `min(w_eff) < −1 < max(w_eff)` |
| G-E0-3.2 | exactly one crossing on the grid | sign-change count of `(w_eff + 1)` over the grid `= 1`; `z_cross ∈ (0, z_max)` |
| G-E0-3.3 | **positive native currency** | `min_z ρ_eff(z) > 0` |
| G-E0-3.4 | **no growing mode / stable operator** | `max_z max_j Re(λ_j(z)) ≤ 0` (within tol `+1e-10`) |
| G-E0-3.5 | perturbation proxy non-negative (advisory) | `c_eff²_min ≥ −1e-8` (recorded; advisory, not blocking) |
| G-E0-3.6 | crossing is robust to grid refinement | doubling `n_z` keeps `z_cross` stable to `|Δ| ≤ 1e-2` and preserves G-E0-3.4 |

### 8.4 Toy 4 (Hubble route matrix + holonomy recovery — E4 rehearsal)
| Gate | Quantity | Threshold |
|---|---|---|
| G-E0-4.1 | `XiToy` parameter recovery | each of `a0_relerr`, `a2_relerr`, `Hclosed_relerr` `≤ 0.15` (15%) |
| G-E0-4.2 | null model rejected | `BIC_null − BIC_SBT ≥ 10` (decisive evidence against `K[XiToy]=0`) |
| G-E0-4.3 | **low-rank beats naive nuisance on economy** | `BIC_nuisance − BIC_SBT ≥ 6` (SBT achieves comparable fit with far fewer params ⇒ lawful plurality, not white noise) |
| G-E0-4.4 | SBT residual consistent with injected noise | reduced `χ²_SBT ∈ [0.5, 1.5]` |
| G-E0-4.5 | **Hubble holonomy nonzero and recovered** | `holonomy_truth > 0.3` km/s/Mpc; `|holonomy_SBT − holonomy_truth| / holonomy_truth ≤ 0.25` |
| G-E0-4.6 | holonomy null control | in the `XiToy = 0` run, `holonomy_null ≤ 0.05` km/s/Mpc (≈ 0) |

### 8.5 Cross-cutting gates
| Gate | Quantity | Threshold |
|---|---|---|
| G-E0-0.1 | determinism | rerun reproduces `summary.json` scalars to `|Δrel| < 1e-12` and `arrays/*.npz` bitwise |
| G-E0-0.2 | no external data | `manifest.datasets == []` (assert in `run.py`); any nonempty entry fails the run |
| G-E0-0.3 | AOR completeness (F9) | zero `unstatused` entries in `aor_status.json` |
| G-E0-0.4 | runtime budget | total wall time `< 2 h` on 8 CPU, peak memory `< 4 GB` |
| G-E0-0.5 | all figures + tables emitted | the five figures and five tables in §1 exist and are non-empty |

**Pre-registered failure modes (E0 is rejected if any holds).**
1. Toy 1 `RM` does not vanish in the linear case (G-E0-1.2 fails) ⇒ the route-mismatch construction or
   metric is wrong; the entire mismatch machinery is suspect.
2. Toy 2 fails to produce apparent `Ω_Λ > 0.2` from a null-Λ heterogeneous generator (G-E0-2.4) **or**
   produces spurious `Ω_Λ` in the homogeneous control (G-E0-2.5) ⇒ the flagship mechanism is not
   demonstrated; the whole program's central toy is broken.
3. Toy 2 rewrite does not win out-of-sample (G-E0-2.7) ⇒ the `Δ_H`/`Ξ` term is just an in-sample fudge,
   contradicting `idea.md` §10 standard 3; this would foreshadow failure of E1/E8.
4. Toy 3 achieves the `w_eff < −1` crossing **only** with a negative `ρ_eff` or a Jacobian with a
   positive-real-part eigenvalue (G-E0-3.3/G-E0-3.4 fail) ⇒ the crossing required a growing mode after
   all; Proposition P4 is unsupported and E3 is blocked.
5. Toy 4's low-rank `XiToy` cannot recover the injected matrix (G-E0-4.1) **or** the naive per-route
   nuisance model is preferred by BIC (G-E0-4.3 fails) ⇒ "lawful plurality" collapses into "any scatter
   fits," which is exactly the critique E4 must defeat; E4 is blocked.
6. Any `unstatused` residual remains (G-E0-0.3) ⇒ violates F9.

**On unblocking.** E0 passing is the precondition for E1 (shares `xi/rewrite.py` + `Δ_H` + the fit
harness), E3 (consumes the Toy 3 stable-operator / P4 witness), and E4 (consumes the Toy 4
route-matrix recovery + holonomy harness). E0 failing blocks all three; record the failing gate(s)
in `summary.json` and the AOR ledger before proceeding.
