# Coupling 30: full complex attraction neighborhoods at both cycle phases

The earlier concrete continuation theorem constructs, on a positive full joint
background/coupling neighborhood of the original coupling-30 input, one exactly
real, unit two-cycle with site-four density gap greater than 9/20. The original
complex seed has the earned even/odd limits at those same phases, both literal
source guards forever, and unit norms from time zero. That theorem exports a
full complex attraction neighborhood about its first phase.

`GroundOriginalCycle30TwoPhaseBasin.open_both_phases_attracting_cycle` retains
those witnesses and the original-seed return, and additionally exports full
complex attraction neighborhoods at both phases. Near the first phase, the
even/odd limits are the first/second phases. Near the second phase, they are the
second/first phases. All local initial states have both literal source guards
from time zero and unit norms after update one. They need not start real or unit.
The parameter radius stays positive; no numerical radius or global basin is
asserted. This is an exact mathematical source statement, not an IEEE trace.

The additional construction does not assume a second basin. The first phase
belongs to its own neighborhood. Its guarded first update supplies both guards
at the second phase, since the update carries the first phase to the second.
The already proved source smoothness gives continuity at that second phase,
and the literal strict guards persist locally. Intersect that guard neighborhood
with the preimage of the first-phase basin under one source update. It is a
neighborhood of the second phase because the second phase maps back to the first.
Every state in it has a guarded first update in the earned first-phase basin.

The tail's even/odd limits give the reversed limits of the original orbit. The
shifted even subsequence loses only its initial term; the natural-number
finite-shift filter equivalence restores the full even limit. The odd limit is
the even limit of the one-update tail. Tail guards and the initial guard give all
guards; the initial guarded normalization gives unit norm after update one,
while the tail gives subsequent unit norms. No inverse map, global regularity,
realness of initial states or eventual-guard assumption enters this argument.

Adversarial self-review checks that both neighborhoods use the same constructed
cycle witnesses and the same original parameter input. The conditional shift
and preimage lemmas expose their guard and basin hypotheses; the final concrete
theorem derives all of them. The neighborhoods are full ambient complex
neighborhoods, not neighborhoods only in the real or unit locus. Initial norms
for arbitrary nearby states are not asserted to be one. Distinctness follows
from the retained strict density gap. The already checked finite-verdict
neighborhood is a separate result; this statement does not substitute infinite
limits for finite failure proofs. The paper and original runtime are unchanged.
Production qualification, registration and commit remain pending. Review is
adversarial self-review, not independent review.
