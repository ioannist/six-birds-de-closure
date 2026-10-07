# Explicit runtime scheduling for the final registered commands

The final build/audit runner now has a separate resource-control candidate:
`results/native_registered_resource_candidate_2026-10-05`. It supplies
`LEAN_NUM_THREADS=4` to the actual subprocess environment and records that
explicit override in each command receipt. Its verifier requires the matching
override. The commands remain a genuine default `lake build`, the full default
axiom manifest and the complete native statement query. Source registration,
all proof gates and the 1771/20789/32565 inventories remain unchanged. Earlier
installation and verifier candidates are preserved unchanged.

This addresses actual compiler resource use observed during the live campaign:
roughly 6–8 GiB per Lean process, on a machine with 128 cores and 125 GiB RAM.
The exact installed Lake sources schedule build actions asynchronously. The
pinned Lean runtime reads the standard worker setting from this environment
variable, otherwise selecting hardware concurrency. Its dedicated tasks and
blocked-task replacement workers mean this setting is not a proved universal
bound on processes or memory. No such mathematical or operational guarantee
is claimed.

Two isolated default Lake builds, each with twelve independent small Lean
modules, passed with observed compiler peaks of two and four for the respective
settings. The fixture uses a short elaboration-time sleep so concurrency can
be measured. It proves nothing about the project's mathematical declarations.
Its exact sources, outputs, observed process samples, receipts and the pinned
runtime source are preserved in 235 verified archive members. Runtime source:
https://raw.githubusercontent.com/leanprover/lean4/7e01a1bf5c70fc6167d49c345d3bf80596e9a79b/src/runtime/object.cpp

AST comparison confirms preservation of all verifier functions after accounting
for the explicit receipt path and new environment assertion. The runner's
changes are limited to constructing/passing the override and recording it.
Four missing/incorrect environment receipt controls are rejected. These are
adversarial self-review and isolated scheduling tests, not independent review
or a registered proof-completion audit.

Candidate mode passes. Both registered entry points return pending/exit 2 on
the absent final qualified summary before starting a registered command or
creating registered receipts. Final publication/path adjustment, full inherited
success-path review and actual registered commands remain pending. Apply the
same explicit setting when running the earlier whole-offset registered gate;
preserve the actual command environment in its integration records. The source
freezes, paper and original runtime have not been changed.
