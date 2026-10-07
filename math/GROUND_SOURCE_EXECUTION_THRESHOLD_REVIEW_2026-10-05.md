# Threshold and execution-domain self-review

No repair to the existing normalization/execution theorems is needed. Their
threshold assumptions are substantive and correctly scoped. `returned_unit`
and the successful-return unit bounds require a nonnegative threshold;
`unit_preserved` and candidate-normalization preservation require threshold
strictly below one. The generic branch/iterate equality and guard equivalence
need neither assumption: `NativeLegal` uses precisely the same square-root
norm comparison as the modeled normalization attempt, rather than squaring a
possibly negative threshold.

Four private Lean boundary controls passed fresh checks with standard axioms:

- In the mathematical extension at threshold−1, zero is accepted and returns
  zero, which has norm squared0 rather than1.
- Threshold0 rejects zero, including the equality boundary.
- Threshold1 rejects an explicitly proved unit basis vector, including equality.

The negative-threshold case is outside the experiment's fixed configuration;
it does not describe a floating-point zero division. It shows why removing the
nonnegative premise would make the mathematical unit-return statement false.
The threshold1 case shows why the below-one premise cannot be dropped.

The original Python normalization rejects `norm <= TOL`, with positive
`TOL=1e-10`. The Lean input reification retains the original binary threshold,
not an idealized decimal replacement. For the checked original orbits, the
input is unit and the exact ground candidate is independently proved unit;
their extra normalizations therefore preserve them at this threshold. The
`Option` recurrence models the final normalization branch from that normalized
seed. It does not model every earlier runtime exception, arbitrary thresholds
in the whole eigensolver, an IEEE eigensolver trace or floating-point arithmetic.
These boundaries were already explicit in the execution-return note.

Evidence is in `results/source_normalization_threshold_review_checked_2026-10-05`.
The first private control proof failed to discharge a function equality; its
actual error and `sorryAx` diagnostic are preserved in
`results/source_normalization_threshold_review_history_2026-10-05` as failure.
The corrected proof uses function extensionality, completes with actual exit0,
and all four audited statements have only standard axioms. This is adversarial
self-review, not independent review. Production declarations/inventories,
registered sources, paper and runtime are unchanged.
