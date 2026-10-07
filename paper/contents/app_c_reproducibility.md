# Appendix C — Mechanization and reproducibility

## C.1 The Lean development

The theorems are mechanized in Lean 4 (v4.28.0) with a pinned mathlib, in the `lean/` directory of the repository. The
main modules, all under `lean/SbtCosmo/`, are:

| result | modules |
|---|---|
| closure price (\Cref{thm:price}) and variants | `Derivation/ConvexClosurePrice`, `ExtendedClosurePrice`, `NonsmoothConePrice`, `ExtendedNonsmoothConePrice`, `NonsmoothMatrixPrice`, `RelativeSchurStationarity` |
| adequacy residual (\Cref{prop:schur}) | `Adequacy/Support`, `Adequacy/Reconciliation`, `Derivation/SchurDifferential`, `SchurAdjointStationarity` |
| allocation model (Section 4.3) | `Derivation/AllocationPrice`, `AllocationSensitivity`, `AllocationScreening`, `AllocationSample` |
| min-cut comparison and entropy example (Section 4.4) | `Derivation/CapacityScale`, `TensorComposition` |
| record window (\Cref{thm:window}) and variants | `Derivation/GrowthPopulation`, `WindowRecords`, `WindowSample`, `WindowErasureWitness`, `WindowEternalRecords`, `WindowPatchCounts`, `WindowPatchCountRatio`, `WindowGlobalStarvation`, `WindowSensitivity`, `GrowthEndpointDerivative` |
| first-record ratios (\Cref{prop:nopinch}) | `Derivation/WindowFirstRecord`, `WindowSignedRecord`, `WindowEndpointRatio`, `WindowEternalRatioCertified` |
| orbit classification (\Cref{thm:orbits}) | `Derivation/GroundFixedPoint`, `GroundOriginalContinuation`, `GroundOriginalOffsetSeed`, `GroundOriginalOffsetSixty`, `NativeOriginalSampleResults` |
| readout nonidentifiability (\Cref{thm:readout}) | `Derivation/GroundOriginalAuditNonidentifiability`, `BackgroundSelection` |
| gauge modulus (\Cref{thm:gauge}) | `Derivation/GaugeClosure` |
| mediator (\Cref{thm:mediator}) and commuting completions | `Derivation/AccessFork`, `FieldAccessBlock` |
| measure bounds (Propositions \ref{prop:fixedsupport}, \ref{prop:smoothprior}) | `Derivation/PriorObstruction`, `WindowSmoothPrior` |
| CPL identities (Section 8.2) | `Derivation/CPLReadout` |
| rank rule and interpolation counterexample (Section 8.3) | `Derivation/StagingAudit` |

Brouwer's fixed-point theorem, used in \Cref{thm:orbits}, comes from a ported and transitively checked development pinned in
`lean/Gametheory/PROVENANCE.json`. Exact certificates for the orbit classification and the window brackets are generated
by scripts in the repository and checked by the Lean kernel; a few auxiliary certificates computed outside Lean are marked
as exact computations where they are used.

**Verification record.** A full registered build of the development completed with 11,775 build jobs. It was followed by
20,798 registered declaration and type queries and a cumulative audit of 32,574 queries for the axioms the proofs use. The only axioms that occur are `propext`, `Classical.choice` and `Quot.sound`; there are no
`sorry` placeholders, custom axioms or native-code trust extensions. The receipts are in
`results/native_registered_final_verification_2026-10-06/`. The recorded full run of the Python test suite passed 127
tests, before later corrected-helper and deterministic line-ending integrations; a subsequent focused check passed four
tests. No full-suite receipt exists for the final Python snapshot. These records are in
`results/ground_state_2026-10-02/verification.json`.

## C.2 Computations

The original model and geometry-audit computations have build scripts, independent validators and tests; additional
computations have their own documented checks:

- **allocation model:** build script `scripts/de_dual_carrier.py`, validator `scripts/de_dual_validate.py`, tests
  `tests/test_de_dual.py`, outputs `results/DE_dual/`;
- **record window:** `scripts/de_window_carrier.py`, `scripts/de_window_validate.py`, `tests/test_de_window.py`,
  `results/DE_window/`;
- **measure probe:** `scripts/de_measure_probe.py`, `scripts/de_measure_validate.py`, `tests/test_de_measure.py`; the
  measure tables of Section 7 are in `results/math_review_2026-10-01/`;
- **lattice model:** the vendored source with `scripts/step54_rederive.py` (an independent classifier), outputs
  `external/step54_repro/` and `results/DE_step54_repro/`; the floating-point traces of Figure \ref{fig:orbits} are produced by
  `paper/contents/figures/orbit_traces.py` from the unchanged source;
- **geometry audits:** `scripts/de_audit_run.py`, `scripts/de_audit_b2_fix.py`, validator `scripts/de_audit_validate.py`, tests
  `tests/test_de_audit.py`, outputs `results/DE_audit/`; the rank-rule recomputation is in `results/staging_rank_2026-10-02/`;
- **growth audit:** outputs in `results/E5SP/`;
- **figures:** `paper/contents/figures/make_figures.py`.

All sweeps and fits run with single-threaded numerical libraries and committed seeds.

## C.3 Provenance of the lattice model

The lattice model originates in another Six Birds repository. Its required source files were copied into
`external/step54_repro/` with a manifest recording source paths and SHA-256 hashes, with source commits where recorded
(the catalog file from the Foundations series has none); the hashes match, and one file differs from its source only by a disclosed path relocation. The sweep was re-run on this project's
hardware, and an independently written classifier, sharing no code with the source, recomputed pass or fail for every
offset and coupling from the regenerated residual tables. All rows agree with the source artifacts.

## C.4 Recomputing the geometry audits

The geometry audits run without a Boltzmann solver; an optional solver import was made lazy, and the acceptance suite was
executed with that import blocked. With the pinned requirements in `results/DE_audit_repro/`:

1. `pytest tests/test_de_audit.py` passes (4 tests);
2. `python scripts/de_audit_validate.py --results-dir results/DE_audit` re-derives the verdicts with no mismatch;
3. `python scripts/de_audit_repro_smoke.py --tolerance-chi2 5.0` performs a reduced optimizer refit of the B1 likelihood
   and reproduces the stored best-fit $\chi^2$ values within tolerance ($\Delta\chi^2=-0.008$ for $\Lambda$CDM and $-0.63$
   for the rewrite).

These are smoke-level comparisons, not a full replication of the posteriors. A skeptical reader can start with the test
suites and validators (seconds), then the model builds (minutes), the Lean build (hours on one machine) and the full audit
battery (hours, dominated by nested sampling).
