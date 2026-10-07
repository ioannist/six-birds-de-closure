# Original-claim checks, 2026-10-02

Baseline `2e8c497`. `receipt.json` checks the frozen CPL chart against its exact
formula and existing expansion routine, gives an exact frozen-decimal crossing,
exhibits tag dependence in the original window carrier, constructs its aggregate
growth threshold, and checks the IID record expression by exact enumeration.

The chart and ODE comparisons are floating point. The decimal crossing,
reified-amplitude thresholds and finite IID enumeration use exact rationals.
The ODE comparison/interval proof and original-claim completion boundaries are
in [the mathematical note](../../math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md).

`verification.json` records 114 passing Python tests, a successful 3156-job
Lean build, and a 113-declaration axiom audit with only the usual kernel axioms.
The paper and historical results are unchanged. These results do not complete
the original physical or measure claims.

Recompute from the repository root with the sbt-de Python:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/de_original_claim_checks.py
```
