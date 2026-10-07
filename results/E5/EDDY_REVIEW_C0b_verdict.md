# Eddy review — WP-C0b physical forward model + HSC-fix — VERDICT: FAIL (2026-06-01)
Reviewed commits `02926ad` + `c51efbd` per `ops/review_rubric.md`. Eddy reran REPRO (reproduces KiDS 0.8031, HSC 0.77527,
CMB-lensing χ²/dof 1.18; 14 tests pass) and found **no bandpower-ordering bug** in the HSC/CMB/KiDS plumbing — but FAILed the
package as "not sound enough to feed a decisive ALL-3-of-3 certificate." Blockers:

1. **BLOCKER — IA is NLA-only, TATT mislabeled** (`sbt_cosmo/growth/projection.py:87`): `_ia_bias` implements only NLA, yet
   *accepts* `"linearized_tatt"`/`"tatt_linear"` labels while computing the same NLA power law. Real TATT is unimplemented.
   Violates the manifest IA staging `{NLA,TATT}×{fiducial,wide}`. HSC fold's axis is photo-z; unmodeled TATT-vs-NLA residual can
   **masquerade as a photo-z staging signal → false positive.** Fix: implement TATT (or demote HSC — not viable under all-3).
2. **BLOCKER — false-positive readiness gate** (`scripts/e5_build_v2.py:211`, `results/E5/E5_v2_substrate.json:212`): the build
   detects `blocking_modules:["...projection.py"]` + `has_notimplemented:true` but still reports `READY_FOR_SCHUR`. Fix: non-empty
   blocking_modules MUST block the substrate gate.
3. **BLOCKER — Ω/nuisance marginalization not evaluated**: status records shared-WL stress + HSC-pipeline as
   `not_evaluated_stop_after_repro_review`; the photo-z/IA degeneracy is therefore uncovered. Fix: perform the IA(NLA+TATT,wide)
   marginalization + Ω floor/stress evaluation before forming decisive rows (this is part of building the certificate correctly).
4. **MAJOR — ENV4 provenance stale/inconsistent**: artifacts record `pyccl 3.1.2 / numpy 1.26.4 / classy 3.2.5` while Eddy reports
   the "current locked env" as `pyccl 3.3.4 / numpy 2.2.6`. A live ENV4 rerun passes, but status uses stale provenance. Fix:
   regenerate ENV4 in the EXACT certificate env + stamp those versions; reconcile `plan/E5_DESIGN_FREEZE.md` to the real run env.
5. **MINOR — units doc** (`sbt_cosmo/growth/power.py:17`): docstring says `(Mpc/h)^3` but CCL uses `1/Mpc`/`Mpc^3`. Didn't affect
   REPRO (uses `angular_cl`). Fix: document CCL-native units or convert + add a regression test.

REPRO genuineness: the HSC re-point to its own 0.776 baseline is **principled, not goalpost-moving**; the scalar-amplitude method is
a valid substrate sanity check but does NOT validate the decisive nuisance-marginalized certificate. **Certificate must not proceed
as decisive until blockers 1–3 are fixed.** → fixes dispatched as WP-C0b-FIX2.
