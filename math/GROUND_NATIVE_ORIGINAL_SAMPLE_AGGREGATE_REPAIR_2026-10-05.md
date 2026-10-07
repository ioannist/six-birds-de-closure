# Original twelve-sample aggregate: checked proof repair

The original regular entry campaign completed all598 single-step certificates
(597 scheduled plus the separately recorded pilot) and all299 paired
certificates. Its eight stable infinite-return audits completed72 exact
statement/transitive-axiom checks, using only standard axioms. This includes
the regular178-update entry and infinite return at coupling15. The previously
checked sixty-update and prefix-failure audits remain valid.

The first actual compilation of `NativeOriginalSampleResults` failed. Its
`fin_cases` branches needed index reduction before arithmetic reasoning;
literal-index rewrites also failed to match the case expressions. Uniform
simplification lists additionally triggered unused-argument lint errors.
These were proof assembly errors, not counterexamples to the component results.

An isolated repair now compiles with actual compiler exit0 and passes all11
printed statement/transitive-axiom checks with actual audit exit0. Every
exported theorem header is byte-for-byte unchanged. The repair reduces case
indices, transports stable returns using the already-proved orbit/target
equalities, and transports cycle nonconvergence in the reverse direction of
the corresponding orbit equality. It adds no assumptions, changes no model
definition, and weakens no theorem. Only the unused-simplification-argument
linter is disabled for the generated uniform binding lists; general
`warningAsError` remains enabled and kernel/axiom checks remain mandatory.

## Exact conclusions

- Every original sample orbit has the declared phase and normalization guards
  and unit norm at every update. Its Euclidean norm is always1.
- The ten original samples through coupling15 converge to their actual
  negative coupled roots. Their site densities have the corresponding limits.
- Couplings20/30 approach distinct unit two-cycle states. The declared site's
  density gaps exceed1/4 and9/20 respectively; the whole state and that site's
  density have no limit.
- The sixty-update four-test conjunction passes exactly at the nine original
  samples below15. A successful prefix within updates1..60 has the same
  classification. Failure of a conjunction does not mean every component fails.
- Eventual success of every declared source test holds exactly at the ten
  stable samples through15. Thus the coupling15 sample fails at60 and eventually
  passes. No earliest successful update is asserted.

The family is the exact twelve original literal couplings, including the binary
reifications of0.1/0.3. These are mathematical source orbits, not certified IEEE
traces or a classification of every intermediate coupling. Physical frame
transfer remains outside the user-authorized revised scope.

## Evidence and integration boundary

Checked packet: `results/native_original_sample_aggregate_repair_checked_2026-10-05`.
It preserves29 archive members, the repaired source/object, both failed local
repair iterations, the original failed source/driver/logs, all11 printed
statements/axiom closures, and3705 revalidated frozen inputs. It records2435
project/private source/object bindings: the archived aggregate object and2434
imported dependencies. The latter objects are hash bindings, not archived copies. The collector completed with actual exit0.

The successful compilation was exec session71021; the successful audit was
session26900. Earlier local repair compilations98876/65807 exited1 and are
preserved. The old Python driver exit code was not separately captured;
its recorded Lean compiler exit1 is preserved rather than rewritten as success.
No original frozen source or registered proof source changed during this repair.
This is adversarial self-review, not independent human review.

The old qualification pipeline subsequently stopped at its failed-parent check.
It printed990 completed modules and left993 independently recorded terminal-zero
module receipts. The three extra receipts come from workers finishing during
shutdown and must be individually validated before reuse. All five old campaign
driver handles are absent. The repaired aggregate has not yet been adopted by
that pipeline or registered in the repository. The next work is to validate and
retain those unchanged modules, qualify the repaired public aggregate, resume
the remaining checks and migrate the verification/installation gates. Fresh
registered builds, complete statement/axiom audits, semantic/provenance checks
and the concluding commit remain mandatory. The paper is unchanged.
