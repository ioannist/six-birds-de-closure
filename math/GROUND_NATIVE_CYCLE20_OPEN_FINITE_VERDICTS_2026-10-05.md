# Coupling 20: open finite convergence-verdict failure

## Target and exact source

The target is the original doubly normalized complex seed, original background,
original coupling 20, half mixing, original conjugated phase convention and exact
binary-rational phase/normalization and convergence thresholds. The returned
statement concerns the exact mathematical source update, not an IEEE execution.
The original source performs a fixed number of updates and evaluates convergence
afterward. It has no early-exit branch. For a truncation at N updates, the final
old/new pair is indexed by n=N-1.

`GroundOriginalCycle20FiniteVerdicts.open_first_sixty_fail` constructs a positive
radius in the full parameter space `(Fin 8 → ℝ) × ℝ`. For every background/coupling
pair in that closed ball about the original input, every truncation N=1,...,60
has a failed original four-test conjunction. Both update guards hold before all
sixty updates, and the original seed and all sixty resulting states have norm
one. The conclusion includes a strictly excessive actual L2 update length for
each update; it does not merely exclude eventual convergence.

## Construction

The generic finite-iteration continuity theorem needs joint continuity only at
the baseline states of the finite prefix. The source parameter-smoothness theorem
earns that continuity from the literal phase and normalization guards. The
already checked `NativeCycleSeed20.Sixty.finite_guards` supplies those guards for
n<60. No infinite-orbit premise, original-seed cycle-entry premise, basin premise
or global smoothness premise enters this proof.

For n<59, populated previous/current rational box enclosures and
`PrefixFailures.gap_arithmetic` give a coordinate gap strictly greater than the
exact original convergence tolerance. The actual L2 update length dominates
that coordinate gap. For n=59, the separately populated sixty-update geometry
gives an actual L2 gap greater than 1/4, which is strictly above that tolerance.
Continuity preserves each of the sixty strict inequalities and both guards.
A finite intersection gives one positive parameter radius. The update-length
component alone then contradicts the original conjunction. Normalization follows
from the guarded literal update, with unit norm at time zero supplied by the
original seed.

## Adversarial self-review

The baseline is the actual coupling-20 input, not an arbitrary cycle point or
assumed fixed point. All prefix guards and enclosures are populated proofs.
Strict inequalities are necessary to infer an open neighborhood; a non-strict
bound at the tolerance would not suffice. The radius is an existence witness;
no numerical lower bound or coverage of a whole coupling interval is asserted.
The norm-one conclusion at update60 uses the guard at update59 and makes no
claim of a guard at update60. The theorem covers N=1,...,60 and makes no
zero-update claim. The background and coupling may both vary; this is not merely
a one-dimensional slice. The exact source is continuous only where the original
branch guards are active, and the proof derives their persistence rather than
assuming smoothness across branch boundaries.

This finite theorem leaves the original coupling-20 infinite-time seed-entry,
real attracting two-cycle and final combined sample theorem as separate pending
obligations. It cannot establish an infinite-time claim by itself. The public
paper and original runtime are unchanged. Production qualification of the older
private imports, registration and commit remain pending. Review is adversarial
self-review, not independent review. Current build and audit evidence is in the
separate checked packet; a rendered source or earlier candidate alone is not
completion evidence.
