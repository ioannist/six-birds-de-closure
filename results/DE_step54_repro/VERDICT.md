# Step54 Local Reproduction Verdict

Reproduced: `True`.

## Independent Re-Derivation
- Background pass count: `15/18`.
- Background fails: `[-5.0, -3.0, 10.0]`.
- Background degeneracy: `15`.
- Classification: `bounded_moduli`.
- Verdict: `BACKGROUND_IS_F50_BOUNDED_MODULI_NO_INLAYER_VALUE_LAW`.
- Kappa pass values: `[0.0, 0.1, 0.3, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0]`.
- Kappa fail values: `[15.0, 20.0, 30.0]`.
- Kappa boundary found: `True`.

## Comparison
- Regenerated-vs-source pass/residual comparison OK: `True`.
- Vendored source validator OK: `True`.

This is a local reproduction of the dependency-corpus finite sweep. It does not modify the source corpus and does not derive a physical cosmological value.
