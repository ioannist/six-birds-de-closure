# E5-SP Phase B — characterization status (FROZEN 2026-06-02)

```
G-E5SP-0 support / G-E5SP-2 slack-precondition = FAIL (no within-family slack in KiDS or HSC)
status   = characterization-only / not-decisive
pi computed = NO
```

This is a **precondition / support failure of the current data vector**, ruled by the external reviewer
(`results/provenance/decommissioned_plan_agent_sources.json#e5sp_dispatch_ruling`, round 5 / Phase B verdict) and matching our pre-registered
stop-gate. It is **NOT** a `π`-negative result, **NOT** a refutation of the shadow-price hypothesis, and **NOT** a
confirmation — no price `π` was computed.

## Per-family slack/binding census (`results/E5SP/H_proxy_table.csv`; `H_slack = 0.05`)
| family | slack | binding | within-family slack→binding support? |
|---|---:|---:|---|
| KiDS-Legacy (COSEBIs) | 0 | 3 | **No** (H 0.088–0.172) |
| HSC-Y3 (Fourier ℓ) | 0 | 4 | **No** (H 0.477–1.911) |
| ACT+SPT+Planck CMB-lensing | 2 | 1 | **Yes** (H 0.0 / 0.004 / 0.144) |

Stop-gate (each family needs ≥1 slack AND ≥1 binding shell) **FAILS** → halt before `π`.

## Why (the physical reason)
The available **public weak-lensing** data vectors (KiDS COSEBIs, HSC ℓ≥300) occupy **only the binding/nonlinear regime**
under the frozen `H` proxy — weak lensing is a projected, small-scale-weighted probe with no clean large-scale/linear
window. Only **CMB-lensing** spans linear→nonlinear (`k≈0.016` at `z≈2`). So the *within-family* slack→binding test is
**not executable** on the two WL families. This is exactly the reviewer's pre-run open-question #3 ("does a slack set
exist at `H_slack=0.05`?") answered empirically: not for WL.

## Robustness
- Driven **robustly by HSC** (ℓ≥300 → `H` 0.48–1.91, no plausible slack); the near-threshold KiDS 1–2 (`H=0.088`) is
  **immaterial** to the verdict.
- `H_slack` stays **0.05** (pre-registered; changing it post-hoc is forbidden). Even at `H_slack=0.10`, HSC-low (`H≈0.48`) is still binding → stop-gate still fails.
- Disclosed approximations (immaterial — all `H` far from 0.05): geometry context = posterior **mean** (`N=1`; full
  16/64-sample runs were CCL/CAMB-build-bound), `σ8=0.811`/`n_s=0.965` hard-coded; `z_eff=0.5·⟨z⟩_source`; Limber
  `k=(L+0.5)/χ`. Any *future decisive* Phase B should use the full window `W_{f,s}(k,z)` integral.

## Honest framing (reviewer's recommended language — use verbatim)
> "The Phase B heterogeneity precondition failed for the current KiDS/HSC/CMB-lensing E5-SP substrate: KiDS and HSC public
> weak-lensing vectors occupy only the binding regime under the frozen `H_slack=0.05` proxy, while CMB-lensing spans slack to
> binding. Therefore the decisive shadow-price test is not executable on this substrate, and no `π` was computed. The result
> localizes the missing support: decisive testing requires a growth probe with within-family linear-to-nonlinear coverage,
> such as public full-shape galaxy clustering / RSD."

Do **NOT** write "the shadow-price hypothesis failed" or "the H table confirms the shadow price."

## Next routes (reviewer-ruled — UPDATED 2026-06-02, `results/provenance/decommissioned_plan_agent_sources.json#e5sp_pathc_ruling`)
- **CMB-lensing diagnostic — DONE:** single-family `π` test ran → **GENUINE NULL** (gate proven live via anti-vacuity injection;
  `λ_max/q` 0.40/0.40/0.69 below budget → `π=0`). A vacuous-gate bug (mis-scaled row-null) was caught + fixed first. NOT promotable,
  NOT a program-level claim (`results/E5SP/cmbl_diagnostic/`). It disfavors the simple "price at `H_slack=0.05`" model but does not
  end the program (CMB-lensing only reaches `H≈0.144`, far below where the price is predicted to bind).
- **Path C — BOUNDED staged build (reviewer-approved, C0 first):**
  - **C0 feasibility/power preflight:** does public full-shape data provide within-family **slack (`H≤0.05`) → strong-binding (`H≥0.3`)** support,
    a usable covariance after shelling, and a theory pipeline that reproduces the published headline? **If C0 fails → STOP** (honest endpoint =
    characterization-only + CMB null).
  - **C1 one-probe** (BOSS DR12 first; DESI DR1 if manifest-verifiable; **NOT** DESI DR2) — diagnostic.
  - **C2 decisive:** ≥2 independent slack-spanning full-shape families + CMB-lensing as the **mild-nonlinearity null anchor**; **two-regime model**
    `π=A[H−H_star]_+`, `H_star=0.2` fixed; explicit-Schur carrier + numeric equivalence test; bias/amplitude-absorption control; beat `M_Λ/M_U/M_sys/M_row` by `ΔBIC≥6`.
- KiDS/HSC remain **binding-regime diagnostics** (no slack leg). **Proceed to C0 ONLY; no full Path C certificate yet.**

Provenance: `results/E5SP/H_proxy_table.csv` (sha256 preserved by `results/provenance/decommissioned_plan_agent_sources.json#e5sp_phaseb_dispatch_manifest`); script `scripts/e5sp_h_proxy.py`.
