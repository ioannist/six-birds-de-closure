# DE Audit Battery Preregistration

Packet: WP-DEA, real-data audit battery for rewrite-vs-fundamental-Lambda discriminators.

Status: preregistered before generating the DEA real-data audit tables.

## Scope

Inputs are the already-provisioned E1 compressed geometry products: Planck 2018 compressed distance priors, DESI DR2 compressed BAO, and Pantheon+ supernova distances. No new data are fetched in this audit. The audit is a statused discriminator battery, not a detection claim, and fitted rewrite amplitudes are never interpreted as retrodictions.

## B1 Model Battery

Primary combination: C3 geometry = Planck compressed + DESI DR2 BAO + Pantheon+.

Models:

- `lcdm`: flat LambdaCDM with sampled `omega_b`, `omega_cdm`, `H0`, and SN intercept `sn_M`.
- `w0wa`: flat CPL fluid with sampled `omega_b`, `omega_cdm`, `H0`, `w0_fld`, `wa_fld`, and `sn_M`.
- `rewrite_power`: additive closure chart with `E^2(z)=Omega_m(1+z)^3+Omega_r(1+z)^4+A(1+z)^m`, sampled `omega_b`, `omega_cdm`, `H0`, `A>=0`, `m`, and `sn_M`.

Readouts:

- `chi2`, `AIC=chi2+2k`, `BIC=chi2+k ln(n_data)`.
- `m_best` and a local Hessian estimate of `m_sigma` for `rewrite_power`.
- A rewrite is classified as "constant-compatible" if `|m_best| <= 2*m_sigma` or `|m_best| <= 0.25`, whichever is less permissive.

Implementation note: the already-produced E1 compressed dynesty summaries provide the `lcdm` and `w0wa` B1 rows, avoiding a duplicate inference campaign in this audit packet. The `rewrite_power` row is a DESI BAO + Pantheon+ shape audit at the C3 LambdaCDM physical anchor, fitting `(A,m)` plus the applicable SN intercept. This is reported as `fit_mode=fixed_lcdm_anchor_shape_fit`, not as a full posterior replacement for E1 or as a same-data AIC challenge to the C3 Planck-anchored rows.

## B1b Phantom-Chart Representation Audit

Using the B1 `w0wa` best fit, compute `w(z)=w0+wa*z/(1+z)` on `0<=z<=2.5`. A phantom crossing is recorded if `w(z)+1` changes sign. For the same expansion history, compute the additive chart

`Delta_H(z)=E_w0wa^2(z)-Omega_m(1+z)^3-Omega_r(1+z)^4`.

Readout: finite/smooth/sign behavior of `Delta_H` across the fluid-chart crossing interval. "Smooth" means all tabulated values are finite and the maximum adjacent finite-difference jump on the fixed grid is finite and reported; this is a representation audit only.

## B2 Staging-Sweep Audit

Declared splits:

- `joint`: DESI DR2 BAO + Pantheon+ for the B2 staging statistic. The B1 model table remains the C3 context including Planck compressed. Planck is intentionally excluded from B2 because the staging audit targets SN/BAO route/probe dependence, not CMB-anchor recomputation.
- `bao_only`: DESI DR2 BAO only.
- `sn_only`: Pantheon+ only.
- `sn_low_z`: Pantheon+ with `z_cmb < 0.35`.
- `sn_high_z`: Pantheon+ with `z_cmb >= 0.35`.

The staging statistic is the maximum split-to-joint standardized change in the rewrite shape parameter:

`S = max_split |m_split - m_joint| / sqrt(sigma_m_split^2 + sigma_m_joint^2 + 0.05^2)`.

For B2 only, the physical anchor `(omega_b, omega_cdm, H0)` is fixed to the B1 C3 LambdaCDM anchor and each split refits the declared rewrite shape `(A,m)` plus any applicable SN intercept. This isolates the staged rewrite-shape audit from background-geometry directions that are not part of the declared statistic. B1 remains the full model comparison.

Pantheon+ is compressed for B2 into six predeclared redshift-bin weighted summaries with covariance propagated as `W C W^T`, using bins `[0.01,0.10,0.20,0.35,0.60,1.00,2.50]`. This keeps the calibration bounded while retaining the declared low/high `z=0.35` staging boundary. The full E1 summaries remain the source for the published C3 `lcdm/w0wa` rows.

Calibration rule:

- Null calibration: 20 deterministic LambdaCDM synthetic realizations with the same redshifts and covariances. False-alarm threshold is the empirical 95th percentile of `S_null`.
- Rewrite calibration: 20 deterministic synthetic realizations from an injected rewrite with `m=1.0` and `A` equal to the fiducial non-matter closure density at `z=0`. The audit is anti-vacuous only if at least 50% of rewrite injections exceed the null threshold.
- Real-data staging fires only if `S_real` exceeds the null threshold and the anti-vacuity condition passes.

All declared splits are reported whether or not the real-data statistic fires.

## B3 Route-Residual Protocol

Routes are the available geometry routes only: `sn_only`, `bao_only`, and `joint`. This is not a SH0ES-vs-Planck audit.

Readouts:

- Shared parameter `Omega_m=(omega_b+omega_cdm)/(H0/100)^2`.
- Rewrite amplitude `A` where defined.
- Unsigned route residuals are normalized against the null-calibration scatter from B2. A route residual is statused as `above_null_calibration` only if it exceeds the null 95th percentile; otherwise `within_null_calibration`.

## Provenance And Determinism

All random draws use the fixed seed block in the runner. Outputs are written under `results/DE_audit/` and independently re-derived by `scripts/de_audit_validate.py`.

## Amendment 2026-06-12: WP-DEA-FIX

Reason: manager review found that the first-pass `rewrite_power` row was a fixed-anchor 19-point SN+BAO shape fit, not the same C3 likelihood as the frozen `lcdm/w0wa` rows, and that the B2 single-injection calibration was unpowered.

F1 replacement: the `rewrite_power` B1 row is refit on the same E1 C3 compressed likelihood used by the frozen `lcdm/w0wa` rows: Planck compressed + DESI DR2 BAO + Pantheon+. The fit uses the same sampled physical parameters and profiled SN intercept convention as the E1 compressed rows: `omega_b`, `omega_cdm`, `H0`, `A`, `m`, plus profiled `sn_M`. Bounds are widened to `A in [1e-4, 2.5]` and `m in [-6,3]`; bound-hit flags are reported. The old fixed-anchor shape fit is quarantined and no longer used for B1 readouts.

F2 replacement: B2 reports a sensitivity curve, not a single injection. Injection amplitudes are `A in {0.70, 1.40, 2.80, 5.60}` with 20 deterministic realizations each, plus 20 LambdaCDM null realizations. `A_detect` is the smallest tested amplitude with true-positive rate at least 0.8. If no tested amplitude reaches 0.8, the audit is statused unpowered and no real-data staging statement is made.

F3/F4: B3 inherits the F2 calibration status. B2 split rows include convergence and bound-hit flags for `A` and `m`.

## Amendment 2 2026-06-12: WP-DEA-FIX2

Reason: the first F2 injection class was global/coherent in the same rewrite family as the fitted split model. The staging statistic measures cross-split inconsistency, so a globally injected rewrite is the wrong alternative and cannot power B2 by construction.

Replacement alternatives:

- I1 `sn_localized`: add a redshift-dependent tilt to the SN distance-modulus vector only, `mu -> mu + epsilon*(z/0.5)`. BAO is untouched.
- I2 `bao_localized`: multiply the DESI BAO alpha-style vector by `1 + epsilon*(z-z_pivot)` with `z_pivot=0.80`. SN is untouched.

Calibration grid: `epsilon in {0.01, 0.02, 0.05, 0.10, 0.20}`, with 20 deterministic realizations per class and amplitude, plus the same 20 LambdaCDM null realizations. `epsilon_detect` is the smallest tested epsilon with true-positive rate at least 0.8 for that class.

Real-data interpretation: if the real staging score exceeds the null p95 and at least one probe-localized class is powered, the result is statused only as a structured probe-dependence/dataset-tension audit. It is not closure evidence and not a Lambda statement.
