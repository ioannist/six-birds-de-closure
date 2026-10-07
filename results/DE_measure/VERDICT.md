# DE Measure Probe Verdict

Status: conditional measure audit in carrier-native units only. This is not a derivation of a lambda value and not a comparison to external measured cosmology.

## Main Verdict Table
- `M1_flat_lambda`: collapses=`False`, P_top_decade=`0.852498`, width90=`1.50233` decades, median a_lambda/a_rec=`1.18148`.
- `M2_flat_log_lambda`: collapses=`False`, P_top_decade=`0.156138`, width90=`4.91763` decades, median a_lambda/a_rec=`7.95449`.
- `M3_flat_lambda_times_N_rec`: collapses=`False`, P_top_decade=`0.684599`, width90=`1.91504` decades, median a_lambda/a_rec=`1.48789`.
- `M4_flat_lambda_times_f_coll`: collapses=`False`, P_top_decade=`0.685534`, width90=`1.92071` decades, median a_lambda/a_rec=`1.48514`.
- `M5_flat_log_lambda_times_N_rec`: collapses=`False`, P_top_decade=`0.0521546`, width90=`4.36694` decades, median a_lambda/a_rec=`12.6513`.

## Can-fail Control
Collapsing classes: `[]`.
Non-collapsing classes: `['M1_flat_lambda', 'M2_flat_log_lambda', 'M3_flat_lambda_times_N_rec', 'M4_flat_lambda_times_f_coll', 'M5_flat_log_lambda_times_N_rec']`.
The criterion is non-vacuous if at least one class collapses and at least one class does not.

## Robustness
- `N32` `M1_flat_lambda`: collapses=`True`, width90=`1.48262`.
- `N32` `M2_flat_log_lambda`: collapses=`False`, width90=`4.46381`.
- `N32` `M3_flat_lambda_times_N_rec`: collapses=`False`, width90=`1.72376`.
- `N32` `M4_flat_lambda_times_f_coll`: collapses=`False`, width90=`1.7242`.
- `N32` `M5_flat_log_lambda_times_N_rec`: collapses=`False`, width90=`4.19715`.
- `N128` `M1_flat_lambda`: collapses=`True`, width90=`1.47269`.
- `N128` `M2_flat_log_lambda`: collapses=`False`, width90=`4.95273`.
- `N128` `M3_flat_lambda_times_N_rec`: collapses=`False`, width90=`1.90929`.
- `N128` `M4_flat_lambda_times_f_coll`: collapses=`False`, width90=`1.90929`.
- `N128` `M5_flat_log_lambda_times_N_rec`: collapses=`False`, width90=`4.38546`.
- `delta_c_2p0` `M1_flat_lambda`: collapses=`True`, width90=`1.46769`.
- `delta_c_2p0` `M2_flat_log_lambda`: collapses=`False`, width90=`4.57996`.
- `delta_c_2p0` `M3_flat_lambda_times_N_rec`: collapses=`False`, width90=`1.83243`.
- `delta_c_2p0` `M4_flat_lambda_times_f_coll`: collapses=`False`, width90=`1.83243`.
- `delta_c_2p0` `M5_flat_log_lambda_times_N_rec`: collapses=`False`, width90=`4.14657`.

Robustness flips relative to the base verdict: `['M1_flat_lambda']`.

## Validator
Validator match: `True`; mismatches: `0`.

## Honest Grade
This is RECOGNITION + DEMARCATION only. In the base carrier no declared measure satisfies the pre-registered collapse criterion. The flat-linear class is near the top-edge threshold but misses it in the base run and flips under robustness variants; flat-log and record-weighted classes keep broad lower-edge degeneracy. The choice of measure remains the irreducible E021-P2 content.
