# ⚠️ INVALID RUNS — DO NOT use these as science results (analysis-bug artifacts)

These E5 result files are **confounded or degenerate by construction** — they reflect MANAGER ANALYSIS ERRORS, not nature.
Disregard them for any scientific conclusion. See `plan/REPLAN_REQUEST_DE_SHADOWPRICE_PIVOT_2026-06-01.md` §4.

## Ignore these:
- **`E5_v3a_currency_certificate.json`, `E5_v3a_lofo_folds.json`** (the "ALL-3-of-3 scale-cut certificate" *attempt*; actual terminal
  state **BLOCKED** on `G-E5-COV` — cond ≈2.02×10⁹ > 1e8 — matching `results/aor_status_table.csv`, **not** an `ACCEPTED_NEGATIVE`)
  — confounded: `G-E5-HETERO` hard-coded `proxy:None` (unpassable regardless of data); reversed-scale-order zero control was
  permutation-invariant (`λ_max(PΞPᵀ)=λ_max(Ξ)`, can never fire); covariance conditioning failed (cond ~2×10⁹); staging passed
  on monotone rank alone. **The null is meaningless.**
- **`E5_shadowprice.json`, `E5_shadowprice_lambda_curve.{csv,png}`** (the "shadow-price characterization", N_post=4)
  — degenerate: the "emergence" observable `λ_max(residual·residualᵀ)` on a *cumulative* row set is the squared spectral norm,
  **monotone in row count by construction** (Spearman→1, "no slack" even for pure noise); and `N_post=4` → `L_geom` rank 3
  (grossly under-resolved). **Ignore the emergence curve entirely.**
- `xi_C_growth.{hdf5,json}` was produced under the same confounded v3a run.
- **`E5_status.json`** — this is the **v3A terminal run record** (`design_version=E5-minimal-physical-v3A`, `decisive_axis=scale_cut`), carrying the
  cumulative/un-normalized `λ_max(Ξ_C−Ω)` LOFO folds and the `N_post=4`/`L_geom rank 3` under-resolution bug. **Same defects as `E5_v3a_lofo_folds.json` — ignore it as a result.** (Its filename does not match the `E5_v3a_*` glob, so it is called out explicitly here.)

## Do NOT confuse with the KEPT v2 substrate files (near-identical names):
- **`E5_currency_certificate.json`** (NO `v3a` prefix) and **`e5_currency_status.json`** are the **v2 substrate/repro records**
  (`design_version=E5-minimal-physical-v2`, `REPRO_PASSED_AWAITING_REVIEW`, `aor_status` zero) — they are **KEPT and valid as
  substrate/repro only** (NOT a decisive result, NOT the cumulative-λ_max object). Do not discard them, and do not read them as a
  decisive verdict. Only the **`E5_v3a_*`** files (and `E5_status.json`, `E5_shadowprice*`, `xi_C_growth.*`) are the invalid v3A artifacts.

## What IS valid (build on these):
The **forward model** (`sbt_cosmo/`, reproduces published KiDS/HSC/CMB-lensing within ~1σ), the **real data** (`data/manifests/`),
the **frozen E1/E2 `w0wa` posterior** (`runs/E1/E1C_C3_w0wa`), the **`G-E5-NONVAC` eligibility idea** (now E5-SP **Gate 0 / `G-E5SP-0`**), and the
passing substrate audits (`G-ENV-4`, `G-E5-REPRO`, `KERNEL/RANK/NOSURR`).
We have NOT validly executed a decisive test; the program has **pivoted to E5-SP** (`plan/experiments/E5SP-shadow-price-obstruction.md`).
