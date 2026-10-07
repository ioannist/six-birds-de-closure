# Semantic verifier migration after the aggregate proof repair

The migrated verifier passed its actual source-stage command with exit0
(exec session72177). It checks1738 qualified source modules and20634 exported
declarations, preserves the exact1070-step/535-pair arithmetic replay and its1831
input pins, and retains the original import translation, DAG, source identity,
declaration enumeration, statement-shape and no-hole/no-local-axiom checks.

The only source override is the audited `NativeOriginalSampleResults` repair.
Its private gate is anchored to the actual checked repository packet; its11
theorem types, imports and definitions must match the historical source.
Every other main source row and every real-return supplemental source row must
remain unchanged. Adversarial controls for a different module hash, a changed
aggregate declaration and an alternate repair gate all failed as required.
Ten unchanged parser/replay/audit functions have identical Python ASTs.

The future qualified gate checks the993 retained module receipts against their
actual original terminal records, source/object/log hashes and closed dependency
set. It separately checks741 fresh recovery modules and four fresh supplemental
modules, plus the full20634 fresh statement/axiom queries. Retained compiler
checks are not relabeled as fresh compilations. The old `fresh_modules=1738`
field is replaced by explicit checked/retained/fresh counts for this recovery.

Evidence: `results/native_aggregate_semantic_verifier_candidate_2026-10-06`.
The qualified success path remains pending; no qualified-verifier completion,
registered integration or whole-paper restoration is claimed. The finish driver,
remaining supplement drivers and final installer/verifier candidates still need
the corresponding path/count migration. The source proofs, paper and original
runtime are unchanged by this verifier migration. This is adversarial self-review,
not independent review.
