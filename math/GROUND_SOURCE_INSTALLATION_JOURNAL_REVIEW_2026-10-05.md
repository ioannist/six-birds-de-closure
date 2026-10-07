# Source-installation failure journals: actual boundary repair

An actual isolated fault reproduction found a reporting gap in the original
1786-file native installer. Its atomic writer replaced the target, then an
injected directory-flush error raised before the caller appended that path to
the completed list. The file contained the proposed bytes while the completed
list was empty. The exception remained explicit, but the attempted write was
missing from that list. No registered source was changed by this reproduction.

The exact executed original source, before/observed-after bytes and actual fault
result are preserved in
`results/native_installer_postreplace_failure_history_2026-10-05`.
This is a file-operation finding, not a Lean theorem failure or mathematical
downgrade. The historical normal helper controls retain their recorded scope.

## Corrected source writers and journals

The corrected native installer is:

`/tmp/de_native_registered_install_original_audit_journal_candidate.py`

Its packet is
`results/native_registered_original_audit_journal_installer_candidate_2026-10-05`.
Every attempted target is journaled before writing. Completed writes are recorded
separately. On failure, the journal and terminal record contain attempted/completed
paths, pending targets and observed target hashes with explicit comparisons to
both original and proposed bytes. An observation failure is itself explicit.
No automatic overwrite or rollback conceals partial installation.

All inherited native source/proof/freeze/whole-offset/preimage/snapshot guards
and the atomic writer have unchanged ASTs. Three actual fault cases pass:
directory-flush failure after replacing an existing target, the same failure
after creating a new target, and file-flush failure before replacement. Normal
existing/new writes also pass. The first two cases correctly record pending
writes whose proposed bytes are present; the third records an attempted write
whose original bytes remain. Candidate preflight exits0 and apply preflight
exits2 for the live source-freeze owner, before registered mutation or receipts.

The preceding21-file whole-offset installer now uses the same checked writer
and journal functions:

`/tmp/de_offset_header_install_journal_candidate.py`

Its packet is
`results/ground_offset_header_journal_installer_candidate_2026-10-05`.
It preserves the candidate/private11776/source-freeze gates, adapts the exact
before/after target columns to the shared writer, and uses the original-audit-
extended native verifier for its private proof dependency. The shared writer/
journal functions have identical ASTs to the corrected native installer. The
five actual file-operation cases pass for this stage as well. Its candidate
preflight exits0; apply exits2 for the same live source owner before mutation.

These fault fixtures exercise real file operations and journals; they are not
Lean builds or full registered installation success paths. Both complete apply
paths and their ensuing registered builds/audits remain pending. No proof object
was copied into the repository. Paper/runtime and protected proof inputs are
unchanged. Review is adversarial self-review, not independent review.

## Explicit collector failure history

The first21-file-stage review collector exited1 after its isolated file-operation
cases because it expected a native-only `proof_objects_installed` field in that
stage's pending response. The failed collector and completed fixtures are
preserved in
`results/offset_header_journal_review_preparation_history_2026-10-05`.
Its tool-observed terminal records the actual returned exit/error; missing
captured subprocess output is not reconstructed. The corrected collector checks
each stage's actual response schema and passed. This collector error does not
change any mathematical statement or proof receipt.

Use these two corrected installers in the established order:21-file source
repair, genuine10003/11776 whole-offset verification, then1786 native source
installation and genuine1772-module/20798-statement/32574-cumulative verification.
All existing prerequisites and source-freeze release rules remain mandatory.
