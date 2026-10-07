# Same-price matrix sensitivity and stationarity, 2026-10-03

Baseline: `b059931`. Adversarial self-review, not independent review. Paper,
original runtime, external artifacts and earlier proofs/evidence stay fixed.

The previous packet constructed general matrix/Loewner Slater prices and full
qualified stationarity. This packet identifies every such price with the actual
full matrix-budget value derivative, proves uniqueness of the symmetric matrix
price across certificates at different optimizers, and assembles sensitivity,
stationarity and original strong duality using the same price. Local value
guards are earned from Slater. No new downgrade is needed.

## Actual conic-value identification

`ConePriceSensitivity.real_price_identification` starts with an earned actual
conic certificate and the actual real budget-value HasFDerivAt d at B. Nearby
feasible cost sets are nonempty. The certificate supplies the budget support

```
V(B)-price(T-B) <= V(T).
```

Consequently V(T)+price(T) has an actual local minimum at B. Its genuine
derivative is d+price, so d+price=0 and price=-d. No convexity, primal topology,
or finite budget dimension is needed once these inputs are established. The
support bound itself supplies the necessary lower bounds on cost infima;
no empty or unbounded real-infimum fallback is used.

`certificate_real_domain_return` earns the reverse original extended-to-real
certificate conversion. Every Jstar/Jx toReal comparison is guarded against
both infinities. `price_identification` uses the exact local equality of the
actual EReal value's toReal readout and the real finite-domain infimum, then
applies the preceding construction. `price_unique` compares certificates at
possibly different optimizers. It identifies the whole continuous budget
functional; it does not prove optimizer or support/normal uniqueness.

## Slater supplies the value guards

`slater_local_finiteness` is an explicit return to the original EReal value
from the earlier Slater midpoint finite-domain cost construction. Ordinary finite
attainment, convex original epigraph, conic convexity and an actual interior
Slater slack earn nearby nonempty bounded-below real costs. Exact original-value
return makes the EReal value a finite real coe on that neighborhood. No actual
value finiteness or value derivative is supplied to this lemma.

The local-finiteness and identification constructions work for a general real
normed budget space; finite budget dimension is not needed there. Existing
price existence by separation is a separate earlier construction with its
own finite-dimensional hypotheses. `slater_price_identification` uses the
earned local guards before reading actual toReal value sensitivity. This
prevents infinite-value conversion from manufacturing a derivative certificate.

## Whole symmetric price versus partial readouts

`MatrixPriceSensitivity.priceMatrix_tracePrice` reconstructs a Hermitian real
matrix P from its whole trace dual on the original symmetric budget subspace.
Evaluation on actual symmetrized matrix units returns Pij: the two terms give
half*(Pij+Pji), and actual Hermitian symmetry yields Pji=Pij. No positivity
is necessary for this reconstruction. Thus `tracePrice_injective` is valid
on symmetric prices, not on all real matrices.

Every original matrix certificate has tracePrice(P)=-d when the actual full
EReal budget value is locally finite and differentiable. For PSD P,

```
P=priceMatrix((-d).toLinearMap),
trace(P H)=-d(H) for every original symmetric budget H.
```

`certificate_matrix_unique` identifies any two PSD certificate matrices at
the same budget, even at different optimizers. The full derivative is on the
whole symmetric budget space, not just one direction. The existing matrix norm
and symmetric-budget domain remain unchanged. PD matrix Slater earns the
original-value finiteness before identification in the final application.

Two controls delimit the statement. A nonzero antisymmetric two-by-two matrix
has zero trace price on every symmetric budget, proving that whole symmetric
duals cannot reconstruct arbitrary nonsymmetric prices. Two different PSD
diagonal matrices agree on the same PSD budget direction, proving that one
directional sensitivity number cannot identify a matrix. Neither control
refutes full symmetric-budget derivative identification.

## The same price in full stationarity

`MatrixSensitivityStationarity.matrix_stationarity` constructs general smooth
Slater stationarity first, then identifies that actual P using earned local
value finiteness and the original full budget-value derivative. Inputs are the
original ambient no-bottom convex extended objective, convex A, actual common
ri(dom J)/ri(A) point, arbitrary Loewner-convex Xi on A, actual matrix derivative
at the optimizer, ordinary finite optimizer, finite PD Slater and actual full
budget-value derivative. Strict negative derivative in one PSD budget direction
earns P!=0. No local finite-value guard, price, objective support, normal,
stationarity or dual output is supplied.

The single returned P has PSD/nonzero, exact sensitivity and reconstructed-matrix
identities, original objective/normal supports, actual matrix derivative's
trace-dual adjoint stationarity, complementarity, original conic certificate and
finite original EReal primal/dual equality. Matrix-map differentiability and
budget-value differentiability are distinct actual hypotheses; neither supplies
the other. No unspecified primal Hilbert inner product is introduced.

The nonsmooth endpoint instead assumes a finite ambient Loewner-convex Xi
extension and earns an actual support k of trace(P Xi). It has no matrix
derivative input. The full budget value may still be differentiable and identify
P=-d as a whole budget functional. It returns q+k+eta=0, sensitivity, nonzero
price, complementarity, certificate and original strong duality for that same P.
The ambient extension remains explicit; convexity only on A is not promoted.

## Original Schur and actual nonsmooth examples

The earlier original infinite-cost objective (x-2)^2 on x>=0, infinity otherwise,
and actual Schur matrix energy [x^2] are reused unchanged. Actual matrix derivative
at1 is earned as2 times the original scalar-to-matrix continuous linear map.
Ordinary optimizer1, actual finite PD Slater at0, common RI at1 and the earlier
actual full value derivative -coordinate at budget[1] are independently proved.
The generic endpoint constructs P=1, actual-adjoint stationarity, original
certificate and dual value1, without a supplied local value-finiteness guard.
Every PSD certificate for this same actual program has matrix price1, including
a certificate at another optimizer. The concrete final construction has zero
premises; the uniqueness test legitimately accepts a candidate certificate.

For the earlier general map [x+abs(y)] with objective -x, feasibility is returned
exactly to the scalar coordinate budget. Its original complete-lattice matrix
value is -coordinate(B) for every symmetric one-by-one B. Its actual full budget
derivative is -coordinate everywhere. Actual finite PD Slater, common RI and
optimizer0 are proved before applying the nonsmooth sensitivity endpoint. The
constructed price is P=1 and the actual dual is0, with earned trace-energy support
and full stationarity. The previous formal no-matrix-derivative result at the
optimizer remains fixed. This is a general Loewner-map example that may have
negative values, not a relabeled adequacy-PSD residual; the Schur example above
supplies the actual adequacy return.

## Verification and remaining scope

Full `lake build`: 8148 jobs. All26 new exported theorem statements and
transitive closures checked; standard Lean axioms only, no holes/native_decide.
Cumulative1184 preserves exact immutable earlier1158 raw prefix plus fresh26;
the full cumulative command was not rerun. Verifier checks source/toolchain
identity, actual-return statements and protected prior evidence. Receipts:
`results/matrix_sensitivity_2026-10-03/`.

This closes the matrix sensitivity/stationarity identification gap and strengthens
the conditional structural theorem with whole-price uniqueness under actual
value differentiability. Primal attainment and differentiability remain actual
hypotheses. Physical Lambda identification, moving native calculus and prior
false/project-sized claims remain separate. The next step is the broader
original-target coverage audit and feasible outstanding toy constructions;
the full user goal is not complete.
