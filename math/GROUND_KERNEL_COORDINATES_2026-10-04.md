# Actual coordinate norms and original coupling attraction

This packet returns fixed rational basis proposals and interval arithmetic to
actual real and imaginary derivative operators for the unchanged original
complex half-mixing update. It concerns the twelve original coupling samples,
not the eighteen background-offset samples or the original frozen initialization.
The paper and runtime source remain untouched.

## Exact mathematical route

The basis proposals use simpler dyadic entries with denominator at most 2^24.
For every proposed rational basis S and proposed inverse P, both P S = I and
S P = I are explicit arithmetic obligations, checked by entrywise `norm_num` proofs whose terms the kernel verifies. Casting their entries to real numbers earns an actual continuous
linear equivalence on the original finite field with its sup norm. Its forward
map uses S and its inverse uses P; the orientation is tested in both directions.
No matrix inverse, orthogonality, isometry, or eigenbasis theorem is supplied.

For any actual continuous linear map L, the entry of its conjugate is

    (S⁻¹ L S)ᵢⱼ = ∑ₐ ∑ᵦ Pᵢₐ L(eᵦ)ₐ Sᵦⱼ.

A computable rational expression encloses this signed sum. Interval containment
of every actual entry of L gives containment of every conjugated entry. Bounds
on the sums of their absolute values then bound the actual induced operator
norm in the coordinate sup norm. This is an operator-norm proof; it is stronger
than a spectral-radius bound and is the input needed by the nonlinear theorems.

The real entry intervals are precisely the preceding packet's intervals for
the actual normalized sourced ground-map derivative. Literal proposed boxes
must equal those computed intervals, by a separate kernel check. They are not
accepted as a supplied spectral matrix. The imaginary entries are enclosed
from the actual field box and the actual derivative

    D_imag = ½ (I − u uᵀ).

Both coordinate bases are retained in the product coordinates. The product sup
norm bounds the full derivative by the maximum of the two block norms. Packing
real and imaginary parts into a complex field is an equivalence, not an assumed
isometry, and the earlier native convergence theorem earns the returned orbit.

## Concrete scope and strength

All twelve proposed real row budgets are nonnegative. The first ten are strictly
below one: coupling 0, the exact binary64 values represented by 0.1 and 0.3,
0.5, 1, 2, 3, 5, 10, and 15. At 15 the proposed real bound is
955899/1048576, approximately 0.911616325. Every imaginary row budget is 501/1000.
The strict full-product bound, actual fixedness, actual smoothness, and original
phase-tolerance guard give actual local attraction for all complex starting
fields in an earned neighborhood of each of those ten real fixed fields.
Every native iterate remains in the active phase and normalization domain.
There is no supplied attraction, smoothness, neighborhood, or row-bound premise
on the final concrete theorem other than its finite sample index.

At coupling 20 and 30 the proposed full derivative bounds are 3/2 and 3. These
suffice for the earlier nonlinear escape gap when combined with independently
earned expanding eigenvalue brackets, respectively (−1.44,−1.42) and
(−2.49,−2.47). This packet does not populate those eigenmode premises.

Local attraction at 15 preserves the already established obstruction to the
literal claim that all coupling values at least 15 run away. Local attraction
of these fixed fields does not place a frozen initial seed in their basins or
prove attraction throughout any coupling interval. The positive branch itself
already exists and is smooth throughout [0,30].

## Evidence obligations and pending work

The generation script uses exact Fraction computations only to propose rational
data. Kernel source checks both inverse identities, both box identities, and
both coordinate row budgets for each sample. The aggregate theorem constructs
every field from those closed proofs. The negative controls reject a zero
inverse and a zero induced-row budget at coupling 15.

Fresh leaf builds, the default library build, exported statement checks and
transitive axiom audits are required before treating this packet as verified.
The review is a distinct adversarial self-review, not independent review.
No IEEE execution or JSON parser is formalized by reifying rational constants.

Pending constructive work includes kernel determinant-sign/eigenmode tests at
20 and 30 and at the crossing probes, native nonlinear escape instantiation,
the remaining eighteen sample roots and their derivatives, and a basin return
for the original frozen initialization. There is no claim of first, unique,
simple, or transverse minus-one contacts, nor universal runaway.
