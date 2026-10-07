# Exception-aware source normalization and successful-return bounds

The literal Step26 routine computes a norm, raises `ValueError` when that norm
is at most its threshold, and returns the divided field otherwise. It does not
leave a small-norm input unchanged or return the total Lean division formula at
zero. The native update's total mathematical formula is a valid representation
of source executions only where its normalization guard has been earned.

`GroundSourceNormalization.attempt` represents this exact mathematical branch
with `Option ComplexField`: `none` represents normalization failure and `some w`
represents a returned normalized state. For any nonnegative threshold, every
successful return has squared L2 norm one. Small norms are rejected exactly;
zero is rejected; an already unit state is preserved when the threshold is
strictly below one. These are direct normalization identities and inequalities,
not a claim that an arbitrary update or run succeeds.

`run` starts with an already supplied initial state and then applies an arbitrary
raw update followed by this normalization attempt. Failure is absorbing: a
normalization exception gives no state at that or any later truncation of the
same execution. Every successful truncation at a positive update count has norm
one. If the supplied initial state has norm one, the same is true also at update
zero, and every coordinate density of a successful returned state is at most
one. No all-time normalization/phase guard, coupling window, ground-entry,
convergence or basin premise is needed for these successful-return implications.
The success premise is explicit; it is not assumed for all runs.

The source bridge is restricted to the mathematical normalization subroutine.
The original source raises an exception, rather than returning Python `None`;
`none` is the representation of no returned state. The run models stopping on
that failure. It does not model every possible earlier exception, an eigenvector
algorithm, IEEE arithmetic, NaNs or overflow. Its arbitrary raw update makes no
assertion about sign choices when the source phase guard is inactive. Any source
execution that reaches and completes a normalization has this exact mathematical
successful-return property, independently of what supplied the input field.
Initial normalization is not silently skipped for a raw seed: the run's initial
state is supplied separately, and the original normalized-seed lemmas provide
that state in existing concrete theorems. The original double normalization is
preserved by the already-unit identity at the original threshold.

Adversarial self-review explicitly checks the rejected-zero branch and the
absorbing-failure theorem as controls against totalization smuggling. The norm
bound excludes amplitude growth among successful exact normalized states; it
does not establish convergence or exclude periodic dynamics. It says nothing
about a state after an aborted update. Existing populated finite/infinite guards
remain necessary for concrete source-execution and attractor claims. This closes
a normalization scope issue; it does not repair an unproved physical Lambda
bridge. The paper and original runtime are unchanged. Registration and commit
remain pending. Review is adversarial self-review, not independent review.
