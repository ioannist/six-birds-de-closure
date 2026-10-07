# Canonical scalar sensitivity and qualified stationarity, 2026-10-03

Baseline: `c61cf67`. Review is adversarial self-review, not independent review.
The paper, runtime, external artifacts and earlier proof/evidence remain fixed.

This packet assembles the scalar Theorem S in
`math/DERIVATION_LT1_2026-06-02.md`, sections 2.1–2.2, with one and the same
price. It retains the general finite convex energy extension, including
nonsmooth energies. It does not substitute the affine Schur subclass for the
general scalar theorem. The actual fixed-native affine Schur application then
earns its energy derivative and returns the literal matrix trace-dual adjoint.
No new downgrade is needed. Broad paper completion remains unproved.

## Actual statement and dependency return

The primal space is a finite-dimensional real normed space. A is convex;
the original extended objective J has no minus-infinity values and an ambient
convex real epigraph. There is an actual common point of ri(dom J) and ri(A).
The energy has a finite convex extension to the full ambient space. An
ordinary finite primal optimum star is supplied. The original complete-lattice
budget value is finite on an open interval about B and its actual toReal
readout has derivative d<0 at B.

`ScalarPriceStationarity.positive_price_stationarity` constructs

```
p=-d>0, energy(star)=B,
DualCertificate(A,J,energy,B,p,star), dualValue(B,p)=value(B),
q in partial J(star), r in partial energy(star), eta in N_A(star),
q+p*r+eta=0.
```

These are simultaneous conclusions about the single constructed p. The
certificate contains nonnegativity, original feasibility, complementarity and
global extended Lagrangian minimization at every admissible point, including
infinite-cost points. Dual and primal values are the original EReal infima,
not infima of an unrestricted toReal objective.

The price/activity/dual certificate is constructed by the earlier convex
primal-mixing derivative argument after the exact guarded objective-domain
return. To earn stationarity for that price, set g=p*(energy-B). Its finite
global convexity earns continuity. Actual epigraph/hypograph separation yields
a restricted J support -k and a global g support k. The earlier common-RI
construction then splits -k into an ambient J support q and admissibility
normal eta. Since p>0, r=k/p is a genuine ambient energy support. Scaling and
joining give q+p*r+eta=0. No energy differentiability, support, normal,
stationarity, sum rule or dual conclusion is supplied to the full endpoint.

This proves Theorem S under weaker assumptions than the corrected LT1 text:
closedness of A/J, a separate Slater witness and activity are unnecessary once
ordinary finite attainment and a locally finite negative actual value derivative
are available. The common RI qualification remains essential for the ambient
objective/normal split. Primal attainment and differentiability of the value
remain supplied hypotheses, not new existence/regularity conclusions.

`certificate_stationarity` is a composition lemma accepting an already earned
positive dual certificate. The full theorem constructs that certificate and
applies the lemma; its endpoint does not assume a dual output. In contrast,
`positive_price_smooth_stationarity` legitimately accepts an actual energy
HasFDerivAt witness and identifies the energy support with its genuine
derivative. The nonsmooth full theorem needs no such premise.

## Scalar price identification and uniqueness

`certificate_real_domain_return` proves the reverse original-to-finite-domain
certificate conversion, with both endpoints of every toReal comparison guarded
against top/bottom. `certificate_price_identification` transfers the derivative
of the actual locally finite EReal value to its exactly matching real-domain
value. The earned certificate's budget supporting inequality and local minimum
then identify every certificate price as -d. No convexity is needed for this
identification once a certificate and actual value derivative are known.

`certificate_price_unique` compares certificates at potentially different
optimizers and proves equality of their scalar prices. It does not claim
uniqueness of optimizer, objective subgradient, energy subgradient or normal.
It does not assert uniqueness of a matrix price from one scalar budget readout.

## Original Schur return

`ScalarSchurStationarity.hasFDerivAt_energy` derives the actual energy
derivative from the original residual derivative and trace calculus. Fixed L
uses the actual spectral support projector; no native invertibility is required.
The affine probe derivative is earned, and PSD W earns ambient energy convexity.

The final Schur theorem constructs the same p=-V'(B)>0 as the scalar theorem,
with its scalar certificate, strong duality and derived activity, and returns

```
q + traceAdjoint(fderiv actual_Xi(star))(p*W) + eta = 0,
q(h)+2*p*trace(W D(star) R (D.linear(h))^T)+eta(h)=0 for every h,
R=I-projector(L).
```

The scaling identity follows from the actual linear trace-dual adjoint.
The matrix price here is the audit weight scaled by the scalar price; it is
not an independently chosen matrix-budget certificate. The energy constraint
is scalar, and complementarity does not mean the full residual matrix equals
a matrix budget. The existing elementwise matrix norm is retained. L is fixed;
moving native probes and physical interpretation remain separate obligations.

## Concrete returns and discriminating scope check

The earlier genuine extended objective J(x)=(x-2)^2 for x>=0 and infinity
otherwise is reused without alteration, with the actual Schur energy x^2,
budget1 and optimizer1. Its RI qualification is proved from interior(Ici0).
The full Schur endpoint returns the scalar price1, original objective support,
normal, literal matrix-adjoint stationarity, certificate and actual dual value1.
All value derivatives, local finiteness and optimizer inputs are proved in the
earlier source. Every certificate for this actual program has scalar price1,
even if supplied at another optimum. The bad unrestricted-toReal control remains
unchanged and is not used as the objective return.

A second program uses E=R^2, energy(x,y)=x+abs(y), J(x,y)=-x and A=univ.
For every budget B the actual optimum is (B,0) and the actual EReal value is
-B. Its actual value derivative is -1. At budget0 the energy is not
differentiable at the optimizer: composing with the vertical line returns abs,
whose differentiability at zero is formally refuted. Nevertheless the full
nonsmooth theorem constructs scalar price1, separate ambient objective/energy
supports and a normal satisfying stationarity, original certificate and dual0.
The concrete endpoint has zero premises. This distinguishes the general
nonsmooth theorem from its smooth Schur specialization.

## Verification and remaining scope

Full `lake build`: 8140 jobs. All 19 fresh theorem statements and transitive
axiom closures checked; standard Lean axioms only, no holes or native_decide.
Cumulative 1130 preserves the exact immutable earlier 1111 raw prefix plus the
fresh 19 suffix; the full cumulative command was not rerun. The verifier checks
source/toolchain identity, original-return statement tokens and protected prior
evidence. Receipts: `results/scalar_stationarity_2026-10-03/`.

This closes the corrected generic scalar Theorem S sensitivity/stationarity
assembly. The actual fixed-native affine Schur return is also mechanized.
Remaining work is the original-target coverage audit, including the general
matrix-map formulation versus the earned affine Schur application, and any
other feasible outstanding constructions. Physical Lambda identification,
primal attainment, moving-native calculus and previously parked false or
project-sized claims are not revived. The full user goal is not complete.
