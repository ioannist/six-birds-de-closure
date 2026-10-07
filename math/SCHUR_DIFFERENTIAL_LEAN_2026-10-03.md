# Explicit Schur derivative and trace-dual adjoint, 2026-10-03

Baseline: `8c77586`. Review is adversarial self-review, not independent review.
Paper, original runtime and all earlier proof/evidence remain unchanged.

This packet closes the explicit matrix Jacobian/adjoint return left separate in
the earlier qualified extended-objective stationarity construction. The actual
fixed-native, affine-probe residual has an earned matrix derivative, a computed
trace-dual pullback, and stationarity in the literal D_Xi*P form. Singular native
Gram matrices and rectangular probes are retained. No new downgrade is needed.
Broad paper completion and the physical Lambda bridge remain unestablished.

## Actual norm and matrix calculus

`MatrixDifferential` uses the repository's existing finite elementwise matrix
norm, not a silently substituted operator norm or Frobenius inner-product norm.
Fixed left/right multiplication, transpose and trace pairing are explicitly
linear. Finite dimensionality of the matrix spaces earns their continuity.
The rectangular matrix product rule is derived from the scalar entry product
rule and finite sums, then returned through actual pi-type derivatives. No
matrix derivative is supplied to this construction. Transpose and trace rules
follow by composing their actual continuous linear maps.

## Fixed-native Jacobian

Write R=I-projector(L), with the actual spectral generalized inverse already
constructed in `Adequacy.Support`. The exact projection identity is

```
Xi_L(Z)=Z R Z^T,
J_L,Z[H]=H R Z^T + Z R H^T.
```

`SchurDifferential` constructs J as a continuous linear map, proves its explicit
evaluation and symmetric range, and proves `HasFDerivAt` for the original
`Adequacy.Support.residual L`. Consequently the actual fderiv equals this map;
it is not used as a fallback before differentiability is established. The
complement's symmetry is earned from the prior spectral support construction.
No native invertibility hypothesis is imposed. L is fixed throughout; a moving
native projector would require additional derivative terms and is not claimed.

For a finite-dimensional normed primal space and an actual affine matrix probe D,
the continuous linear derivative is its actual D.linear, with continuity earned
from finite dimensionality. The chain rule gives

```
D_Xi(x)[h]=J_L,D(x)[D.linear(h)].
```

The actual fderiv identity is proved. A general chain-rule version also accepts
an arbitrary genuinely differentiable D and its actual HasFDerivAt witness, with
no finite-dimensional primal-space requirement. This generic input is a probe
derivative, not a supplied Schur derivative or stationarity field. The affine
application earns the probe derivative rather than assuming it.

## Trace-dual adjoint and factor two

The primal space is a general real normed space; no primal inner product is
invented. The adjoint is the actual dual pullback with the trace identification
of matrix prices:

```
(traceAdjoint J P)(h)=trace(P J(h)).
```

It is defined as a linear map from matrices into the continuous dual, by composing
the actual trace-price functional with J. The pairing identity is definitional;
the substantive return is the independently proved equality between the actual
trace-Lagrangian derivative and the pullback of the earned matrix derivative.
This is a transpose map into the continuous dual, not a Hilbert-space adjoint
vector under an unspecified inner product. The symmetric Jacobian range makes
it the same trace-dual action used by the original symmetric budget problem.

For an arbitrary real matrix P the proved formula is

```
trace(P J_L,Z[H])=trace(((P+P^T) Z R) H^T).
```

The proof transposes the first product-rule term, uses the symmetry of R, and
cycles the trace; the second term remains explicit. PSD P is Hermitian over the
reals, hence symmetric, earning the factor-two specialization

```
(D_Xi(x)* P)(h)=2 trace(P D(x) R (D.linear(h))^T).
```

The fixed matrix budget has zero derivative. The actual original scalar
trace-Lagrangian derivative equals this price pullback for any fixed budget.
It also equals `traceAdjoint (fderiv actual_Xi) P`, with actual matrix
differentiability established beforehand.

## Original qualified extended stationarity return

`SchurAdjointStationarity` applies the earlier constructed original extended
Slater price and relative-interior-qualified ambient objective/normal split.
Its hypotheses are the original ambient no-bottom convex epigraph, convex A,
an actual common relative-interior domain point, ordinary finite optimizer,
and a finite-cost positive-definite Slater slack. No derivative, adjoint,
stationarity, objective subgradient, normal or dual output is supplied.

It returns P PSD, q in partial J(star), eta in N_A(star), complementarity, and

```
q + traceAdjoint(fderiv actual_Xi(star)) P + eta = 0,
q(h)+2 trace(P D(star) R (D.linear(h))^T)+eta(h)=0 for every h.
```

Strict decrease of the original complete-lattice value in a PSD budget direction
also returns P!=0. This inherits the prior proof including a possible
minus-infinity competing value. The original infinite-cost objective points are
included in the ambient objective support, not silently discarded. Ordinary
primal attainment remains a hypothesis, as in the original theorem.

## Discriminating examples and review

`SchurDifferentialExamples` uses the prior actual 2-by-3 rank-one native matrix,
whose Gram singularity was already proved. Its 1-by-3 affine probe is (3,3,x).
The actual computed price pullback evaluates to 2*x*h and the actual residual
trace has the corresponding Frechet derivative. This is a rectangular
singular-native application of the general derivative construction.

Dropping one product-rule term gives the wrong actual price at x=h=1. A separate
off-diagonal nonsymmetric 2-by-2 price, column probe and column direction show
that the factor-two shortcut fails without price symmetry. Both are proved
controls of the actual Jacobian/trace mechanism, not deletion of a conjunction
field. The general P+P^T formula remains valid. No support or price positivity
is supplied in these controls.

Full `lake build`: 8137 jobs. All 28 fresh exported theorem types and transitive
axiom closures checked; only standard Lean axioms, no holes or native_decide.
Cumulative 1111 closures preserve the exact immutable earlier 1083 raw prefix
plus the fresh 28 suffix; the full cumulative command was not rerun. Source,
toolchain and protected earlier evidence identity are checked by
`scripts/de_schur_differential_verify.py`. Receipts are in
`results/schur_differential_2026-10-03/`. No Python suite, original solver, RNG or
empirical carrier reruns were needed for this pure Lean packet.

The explicit fixed-native affine-probe Jacobian/adjoint obligation is now closed.
Remaining coverage work includes assembling the differentiable-value scalar
price and qualified stationarity with the same canonical price, and checking
other original-target gaps. Physical identification, moving-native calculus,
primal attainment and previously parked false/project-sized claims are separate.
