# Singular-support Lean verification

Baseline `18a0ca2`. `verification.json` records a successful 3157-job default
Lean build and an axiom audit of all 155 delivered theorem declarations,
including the 42 new support theorems. Their axiom closures contain only
`propext`, `Classical.choice`, and `Quot.sound`, with no proof holes.

The inverse, Penrose uniqueness, projector, full exact-adequacy cycle, optimal
residual, whitening return, scalar-weight detection and singular examples are
kernel-checked proofs. Their scope and derivations are in
[the mathematical note](../../math/SINGULAR_ADEQUACY_PROOFS_2026-10-02.md).
The paper is unchanged; empirical/physical realization is not inferred.

Reproduce from `lean/`:

```sh
lake build
lake env lean manifests/check_axioms.lean
```

The expanded raw audit is
`lean/manifests/axiom_audit_support_2026-10-02.txt`. Earlier receipts are
preserved. This packet changes Lean and mathematical documentation only;
the Python suite was not rerun as a substitute for proof checking.
