# Original coupling continuum: connected ground branch and minus-one modes

The original nonconstant background now has exact computational continuation
certificates across the entire coupling interval [0,30]. They construct one
positive normalized self-consistent ground branch through all twelve original
coupling-sample roots. Two distinct couplings on that branch have actual
half-mixing multipliers -1: one in (15.8,15.9), another in (15.9,20).
This restores a continuous-branch/mode-boundary result rather than inferring a
crossing from isolated stable and unstable samples.

The analytical local branch, uniform tube root construction, boundary smoothness,
common-root uniqueness return, Jacobian continuity, determinant IVT and native
complex derivative return are Lean-checked. The 286 concrete interval tubes,
287 common-root anchors, sampled inclusions and determinant signs are exact
Python integer/Fraction computations, **not yet Lean kernel instantiations**.
The final finite patch selection is a mathematical construction from these
certificates; this packet does not provide its concrete global Lean definition.

## Actual equations and earned nondegeneracy

The original field is `Fin 8 → ℝ`. Root coordinates are `(u,e)` in the product
sup norm, so a radius-r ball is the nine-coordinate box with coordinate errors
at most r. The equations are

```
F(b,κ,u,e) = ((K + diag(sourcePotential b κ u) - e I)u,
             (sum_i u_i² - 1)/2).
```

They are the unchanged sourced nonlinear eigen and normalization equations.
`GroundParameterEquations` proves joint C-infinity regularity in the whole
background, coupling, field and energy, and proves that the actual root partial
derivative is `GroundRootCertificate.residualDerivative`.

For any fixed proposed preconditioner C, if

```
‖I - C DF‖ < 1,
```

then DF is injective: a vector killed by DF would equal its image under a
strict contraction. Finite dimensionality earns bijectivity. C is also proved
bijective from the same defect bound. Neither a derivative inverse, a spectral
gap nor a branch witness is supplied as an oracle.

The actual implicit-function hypotheses now follow from the actual polynomial
equation and this numerical bound. `GroundParameterBranch` constructs the local
C-infinity implicit branch, proves its center and equation, earns positivity by
continuity, and returns the full pair to the actual ground/energy selector.
Local uniqueness is proved in a product neighborhood; global root uniqueness
is not inferred.

## Uniform root tubes and return through boundaries

For a fixed original background and coupling interval I, a tube certificate has
a fixed center, preconditioner, radius r and rate q<1. Its explicit quantitative
obligations are positivity of the root box, the uniform defect bound at every
κ in I and every root coordinate in that box, and

```
‖C F(κ,center)‖ + q r < r       for every κ in I.
```

`GroundParameterTube` earns a unique positive root inside that ball for every
κ in I, from the existing contraction construction. Preconditioner injectivity
is derived, not separately assumed. The strict residual inequality puts the
root strictly inside the box. Its chosen root function returns to the actual
implicit branch near every κ, within the interval, proving C-infinity boundary
regularity and continuity without a supplied continuity premise.

Adjacent tubes are joined by a separately certified small common root box at
their shared endpoint. That entire small box lies strictly in both tube boxes.
Existence in the small box and uniqueness in each large box force the same
actual endpoint root. Floating proximity of proposed centers is not used to
identify roots.

This gives a finite continuous patching over [0,30]. At a seam the common root
is strictly in both boxes and its nonlinear equation derivative is invertible.
The actual local implicit branch stays in both boxes near the seam. On either
side it must equal the respective tube root by uniqueness. Thus the patched
branch has the same C-infinity germ on both sides, not just matching values.
At0/30 it is the restriction of a local implicit branch. This argument also
shows why the numerical tubes earn smooth continuation rather than merely
existence at each parameter separately.

## Original coefficient and sample identity

`scripts/de_ground_branch_certificate.py` reuses the immutable original-root
certificate engine and freshly replays all thirty prior sample certificates.
It then fixes the original eight background coefficients, exactly reified
from their binary64 values, and constructs coupling tubes covering every real
κ in [0,30]. This is the mathematical real model with those coefficients;
floating rounding at each runtime operation is not emulated.

NumPy1.26.4 proposes centers and fixed inverse matrices. Exact replay uses
integer dyadic intervals at scale2^80 and Fraction inversion of point matrices.
All tube radii are1/256. The largest uniform Newton defect is below0.550364;
the largest earned root displacement is below0.003904967, strictly below1/256.
Every proposed interval is replayed with the entire coupling interval as an
interval variable, not just its midpoint or endpoints.

The exact matrix rows represent the nine-coordinate derivative in this product
sup norm. For any error vector h, each output coordinate is bounded by its
absolute row sum times ‖h‖, so the maximum row sum bounds the actual operator
norm. The residual enclosure is likewise the maximum of its nine coordinate
bounds. This is the analytical link from the integer checks to the stated
Newton-defect and invariance inequalities; concrete coefficient/inequality
proof terms remain part of the disclosed kernel-instantiation gap.

The286 consecutive tubes have no gaps;287 certified common-root anchors join
the pieces and cover the two external endpoints. All twelve original coupling
sample boxes lie in the appropriate large tube boxes, so their prior certified
roots equal the continued branch roots by uniqueness. The source and original
coefficient data are hash pinned by the inherited replay. A wrong background,
a parameter gap, a false common root and a singular preconditioner are rejected
by adversarial controls.

This packet does not construct the background-offset continuum. In particular,
the binary64 coefficient addition used for those original samples must not be
silently identified with a single exact affine offset path.

## Actual mode contacts from continuity and determinant signs

`GroundParameterSpectrum` proves joint smoothness of the actual ground map,
identifies its state partial with the previously earned actual source Jacobian,
and proves continuity of the full normalized half-mixing Jacobian A in background,
coupling and field. The coordinate-entry matrix has the correct row/column action.
The determinant of A+I is continuous along any actual continuous fixed branch.

Exact signs on the continued original branch are

| Coupling | Enclosed determinant of A+I |
| --- | --- |
|79/5 =15.8 | [0.0029260698,0.0029265322] |
|159/10 =15.9 | [-0.0020897511,-0.0020893020] |
|20 | [0.0439364433,0.0439391299] |

The new15.8/15.9 root boxes are independently certified and identified with the
same continued branch by tube inclusion. Their actual normalized matrices use
the earned inverse ground border, enclosed by a Neumann defect argument. The20
matrix is the unchanged prior exact certificate. The displayed decimal bounds
are outward summaries of the saved integer intervals, not the gate arithmetic.

The determinant IVT earns zeros in both disjoint open intervals. Singularity
earns nonzero real vectors h with A h=-h. Unit normalization makes these vectors
tangent. The mode and the actual derivative return to the unchanged native
complex update via `(h,0)`, with the original threshold in[0,1).

Both statements are contacts with the half-mixing linear unit-disk boundary.
No simple eigenvalue, transversality, exactly-one or first-crossing assertion is
inferred. No stability verdict for every κ below or above either contact,
nonlinear escape, divergent field amplitude or frozen-initialization basin is
inferred. The15/20 determinant endpoints alone have equal signs, so using them
alone would not have proved these contacts.

## Coverage and remaining work

This adds continuous original-coupling branch support and earned mode contacts
to the previous isolated-root and local-convergence results. It does not restore
the literal κ>=15 runaway interpretation:15 remains locally attracting on this
positive branch, while a contact is certified strictly above15.
Existence does not end at either contact; the positive branch continues through30,
and the prior all-parameter existence theorem remains valid beyond that interval.

Concrete tube/root/basis/sign proofs inside Lean, a concrete global finite-patch
definition, an original-initialization basin or finite-budget theorem, and any
desired sharper first/simple/transverse crossing classification remain separate.
Background blindness, physical Lambda identification and unrestricted selector
impossibility remain in their previously recorded status. Paper, frozen runtime
and original data are unchanged. Review is adversarial self-review, not independent
review; the overall goal is incomplete.
