# Record-bearing lambda-window carrier verdict

Status: RUN-frame toy computation in carrier-native units only. This does not derive a lambda value and does not compare to external measured values.

## Four readouts
1. Strictness: `True`. RS is strictly inside the bare integration-admissible grid.
2. Two-sidedness: `True`. Negative edge is crunch erasure; positive edge is no-collapse/growth shutoff.
3. Coincidence readout: order-unity-bounded across the whole RS window = `False`.
   Positive-ratio spread: `7.11402` decades; min/median/max = `1.33886139164e-06`, `0.0001762351025155`, `17.4084263094`.
   Epoch ratio min/median/max = `0.385845549706`, `14.22686378945`, `90.7308112325`.
4. Window width: `4.29409` signed-edge decades inside the refined RS brackets; bare grid width `8` decades.

## Refined edge brackets
- Negative crunch edge: inside `-0.00011844666116572434`, outside `-0.00027000000000000006`, factor `2.279507056954778`.
- Positive no-collapse edge: inside `2.331385631724953`, outside `5.314410000000002`, factor `2.2795070569547775`.

## Controls
- `C1_homogeneous`: pass=`True`.
- `C2_gate_can_fire`: pass=`True`.
- `C3_record_irrelevant_tag_sweep`: pass=`True`.
- `C4_robustness`: pass=`True`.
- `C5_verdict_rederivation`: pass=`True`.

## Honest grading
The two-sided window shape is expected from the declared toy physics: negative lambda can crunch and erase records, while positive lambda can shut off growth. The computed content is the strictness, edge brackets, window width, coincidence-ratio spread, and can-fail controls.
The coincidence readout is a clean negative for the strong claim as phrased across the entire RS window: near-zero lambda runs are record-bearing but have a small lambda-to-matter ratio at first record.
