# Finite actual coupling-branch assembly in Lean

## Exact target and landing

The preceding packet constructs quantitative Newton tubes for the actual
nine-coordinate self-consistent eigen/norm residual and verifies a concrete
finite cover of the original coupling interval [0,30] by exact Python arithmetic.
This packet mechanizes the finite assembly and its original-target returns.
It does not edit the paper or frozen runtime/data.

`GroundParameterPatch.TubeCover` contains actual tube certificates, closedness
of their parameter sets, and quantitative common-root certificates for each
nonempty overlap. At a coupling in two patches, the overlap certificate is a
smaller Newton tube whose whole root ball lies in both large balls. Existence
in that smaller ball and uniqueness in each large ball derive root identity.
There is no supplied root function, root-identity axiom, or continuity premise.
For the previous consecutive closed intervals, only shared endpoints and
self-overlaps need certificates; different nonadjacent intervals have no overlap.
The former are the previously verified small anchor balls. For a self-overlap,
the same tube and reflexive ball inclusions suffice.

The function `TubeCover.root` chooses an owning tube on the union of the
parameter sets and is zero outside that union. Every owning tube gives the
same value by the derived overlap identity. All conclusions concern the
certified union; the value outside it has no execution or smoothness claim.
The empty-index case is harmless: its union is empty, while a concrete nonempty
interval coverage obligation cannot hold in that case.

## Continuity and smoothness through seams

For a finite index type, finite closed pasting derives continuity from the
previously earned continuous tube roots. At any point of the union, any owning
tube supplies a strict Newton defect at the chosen actual root. This earns an
invertible actual state partial and a local smooth implicit branch. The finite
patched function is continuous into the root neighborhood and satisfies the
actual nonlinear equation throughout its domain. Local implicit uniqueness
therefore identifies it with the same smooth germ across every adjoining patch.
This works even when the owning tube contains only one side of a seam.

Lean proves both a C-infinity germ extending through every domain point and
`ContDiffOn` the entire union. At the outer endpoints it proves smoothness
within the union and existence of an ambient smooth extension germ. It does
not claim that the arbitrary zero totalization is smooth outside the union.
There is no global uniqueness assertion for all self-consistent roots.

## Actual selector, sample, and native-mode returns

The full field/energy pair returns to the actual `groundPair`, not merely an
auxiliary eigenvector. Unit norm, positivity, and actual `groundMap` fixedness
follow from the residual and the quantitative tube positivity condition.
`certified_sample_return` returns any independently certified sample-tube root
to the same global branch when its center distance plus radius lies inside
an owning large ball. The metric ball-containment lemma proves that implication;
closeness without enclosure and uniqueness would not identify roots.

The branch field is C-infinity and continuous on its certified domain. For
any actual threshold 0<=tau<1, it returns to legal fixed points of the unchanged
native complex iteration, retaining its original phase rule. Normalization and
phase guards are proved at these branch points for every real mixing parameter.

`minus_one_contact` now takes finite tube data, interval coverage and opposite
actual determinant signs. It derives the formerly supplied continuous unit
fixed-point branch and returns an interior nonzero real tangent -1 mode, its
full complex derivative embedding and the actual native derivative.
`two_distinct_contacts` earns ordered contacts in two disjoint open intervals
from two sign reversals on the same constructed branch. Both use actual
`crossingDet` of the full normalized half-mixing Jacobian. Neither supplies an
assumed mode, spectral gap, branch or derivative inverse.

## Numerical and original-paper coverage boundary

The previous exact integer/Fraction replay verifies286 original-background
tubes,287 anchors, all12 original coupling sample-root identities, and signs
at15.8,15.9,20. Those immutable artifacts remain protected. This packet changes
only analytic construction and returns; it does not claim a fresh numerical
replay. The global finite-patch construction is now mechanized generically.
The concrete286-tube `TubeCover` and its inequality/coverage/sign proof terms
are still not instantiated inside the Lean kernel. The original connected
branch and two contacts remain supported by exact computational certificates
composed with mechanized analytic theorems. Kernel-only completion remains open.

No first/unique/simple/transverse contact, all-interval stability, nonlinear
escape, frozen-initialization basin, finite-budget runtime verdict, or background
offset continuum follows. Coupling15 remains locally attracting on this branch;
its literal inclusion in a universal kappa>=15 runaway regime is not restored.
Physical Lambda, background blindness and unrestricted selector impossibility
retain the previously recorded obstructions. The whole original-paper goal
remains incomplete. Review is a distinct adversarial self-review, not independent
review. The next construction is concrete kernel certificate instantiation or
an original-initialization basin bound, not an assumed global branch.
