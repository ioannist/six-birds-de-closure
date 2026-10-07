# Additional-construction receipts

Baseline commit: `2a8a33a`. See the
[construction and scope note](../../math/RESTORATION_CONSTRUCTIONS_2026-10-01.md).
The paper and earlier experimental artifacts are untouched.

Run in the sbt-de environment from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python scripts/de_restoration_constructions.py --check-sibling
```

`construction_receipt.json` contains exact rational bounds for the frozen
measure samples, the reified Lean count check, and numerical checks of two
explicit new carriers: equality-ledger allocation and projected sourcing.
It records software/input/source hashes. The projected-sourcing run is not
claimed to satisfy the original Step26 convergence criterion.
The optional `--check-sibling` flag verifies the retained local force against
the original Step26 code in `../six-birds-sm-qm-gr`, without writing there.

`verification.json` records the build/test results and raw axiom-audit hash.
The exact-data bounds are not continuum ODE error certificates, and the
numerical trajectories have no interval integration error bounds.
