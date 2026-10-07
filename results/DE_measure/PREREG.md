# DE Measure Probe Preregistration

Date: 2026-06-12.

This probe reuses the frozen Leg-A record-bearing carrier and writes only to `results/DE_measure/`. It does not modify `results/DE_window/`.

## Measure Classes
- M1: flat `d_lambda` on the signed RS window.
- M2: flat `d log(lambda)` on the positive RS window; the negative sliver is reported separately.
- M3: flat `d_lambda * N_rec(lambda)`.
- M4: flat `d_lambda * f_coll(lambda)`.
- M5: flat `d log(lambda) * N_rec(lambda)`.
- M6: not declared. No additional carrier-native measure was defensible without adding new content.

## Collapse Criterion
A measure collapses the Leg-A degeneracy iff `P(log10 R >= max(log10 R)-1) >= 0.8` and the weighted 90% width of `log10 R` is <= `1.5` decades.
This criterion is declared before evaluating the measure verdict table. It can fail: broad flat-log measures are expected not to collapse.

## Grid and Aggregation
The positive side uses `36` log-spaced lambda points from `1e-05` to the refined positive RS inside edge. The negative sliver uses `8` log-spaced points from the refined negative inside edge to `-1e-5` plus zero for the raw observables. Continuous measure weights are trapezoid cell widths in either lambda or log-lambda.

No observed cosmological values enter this probe. All quantities are carrier-native.
