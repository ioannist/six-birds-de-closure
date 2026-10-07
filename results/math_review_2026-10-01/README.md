# Corrected mathematical review receipts

These files recompute frozen inputs using the repaired mathematics. Historical
preregistrations, raw samples, and verdict tables remain in their original
locations. The interpretation and claim boundaries are recorded in
[`math/MATHEMATICAL_REVIEW_2026-10-01.md`](../../math/MATHEMATICAL_REVIEW_2026-10-01.md).

From the repository root, using the `sbt-de` environment:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python scripts/math_review_recompute.py --check-sibling
```

The optional `--check-sibling` flag runs the original Step26 carrier in memory
from `../six-birds-sm-qm-gr`; it writes no sibling files. Without this flag all
other receipts use local inputs. `recomputation.json` records input/source
hashes, software versions, corrected measures, independent-validator agreement,
dual residuals, window/audit replay, and the corrected R0 power result. The
CSVs contain the measure tables and dual sweep.

These are finite floating-point checks, without rigorous continuum or interval
error bounds. `verification.json` records the final build, test, and axiom audit
checks; Lean's raw theorem axiom closures are committed separately under
`lean/manifests/`.
