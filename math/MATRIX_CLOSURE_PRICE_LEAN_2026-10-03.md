# Constructed differentiable-value matrix closure price, 2026-10-03

Baseline: `ac531fe`. Paper, original runtime and prior proof/evidence are
unchanged. Review is adversarial self-review, not independent review.

This constructs the matrix/Loewner price in the actual Schur domain when the
actual finite matrix-budget value is Frechet differentiable. It earns cone
positivity, complementarity, a nonzero PSD trace representative, global
Lagrangian minimization and finite primal/dual equality. It is not a claim to
have mechanized general nonsmooth Slater duality or split normal-cone KKT.

## Actual conic value and constructed price

`ConeClosurePrice` works with a real normed budget space F and a cone described
only by closure under zero, addition and nonnegative scalar multiplication.
The primal coordinate space needs only a real-module structure. For convex
admissible A and real-valued convex J, a conic-convex energy map obeys

```
a*energy(x)+b*energy(y)-energy(a*x+b*y) is in the cone
for a,b>=0 and a+b=1.
```

The actual value is

```
V(B)=inf {J(x) : x in A, B-energy(x) is in the cone}.
```

Suppose an ordinary primal optimizer star exists, actual feasible-cost sets
are nonempty and bounded below on a budget neighborhood, and this actual
infimum has Frechet derivative d at B. These hypotheses remain visible. No
dual, supporting functional, complementarity or activity is supplied.

For a cone direction H, positive perturbations B+tH keep star feasible.
Hence V(B+tH)<=V(B), and the actual right derivative gives d(H)<=0.
Thus the explicitly constructed price p=-d is nonnegative on the cone.

For any admissible x, mix it with star. Conic convexity and the original
feasibility show that the mixed candidate is feasible at B+t(energy(x)-B).
Convex J bounds its cost. The actual infimum and its right derivative earn

```
J(star)+d(energy(x)-B)<=J(x).
```

At x=star this and cone positivity on B-energy(star) force
p(energy(star)-B)=0. Rearrangement supplies global Lagrangian minimization.
It returns primal optimality and genuine guarded equality of the actual real
primal and dual infima. The certificate supplies its dual nonempty/lower-bound
guards via an attained global minimum; no unbounded or empty real default
infimum is an optimization answer. A negative d(H) makes p nonzero.

This argument does not force the whole slack vector to vanish. Complementarity
is a scalar evaluation by the price. Full vector or matrix activity would be
an unjustified strengthening without a price that is strictly positive on
every nonzero cone element.

## Exact symmetric budget space and PSD trace representation

`MatrixPriceRepresentation.Symmetric n` is the proved real submodule of
matrices satisfying M.transpose=M. Matrix-price differentiation uses its
elementwise norm and subspace topology, not the full matrix space. For symmetric
Schur residuals, a nonsymmetric budget cannot be feasible: the sum of a
symmetric residual and PSD slack is symmetric. Local finite value on the full
matrix space would therefore be an inappropriate hypothesis.

The representation construction is independent of the optimization problem.
For any real linear functional p on symmetric matrices define

```
sym(M)=(M+M.transpose)/2,
P(i,j)=p(sym(E(j,i))),
```

where E(j,i) is the actual matrix unit. Symmetrization fixes every symmetric
matrix and is unchanged by transpose. The matrix P is symmetric and the exact
finite matrix-unit expansion proves

```
trace(P*H)=p(H)  for every symmetric H.
```

If p is nonnegative on PSD matrices, test the actual rank-one PSD direction
v*v.transpose. Its pairing is v.transpose*P*v, so P is PSD. Positive evaluation
at any symmetric H proves P is nonzero. No Riesz representative, matrix dual,
self-duality field or desired trace relation is assumed as input; the entries
and PSD property are constructed.

## Actual Schur Loewner convexity and matrix return

`MatrixClosurePrice.residual` bundles the actual previously constructed
`Adequacy.Support.residual L D` as a symmetric budget vector, using its proved
PSD property. Its generalized Gram inverse, including singular native rank,
is unchanged. The fixed-native blind-Gram identity gives the exact matrix
mixing identity

```
a*Xi(L,X)+b*Xi(L,Y)-Xi(L,aX+bY)=a*b*Xi(L,X-Y).
```

For a,b>=0 and a+b=1 the right side is PSD. Thus actual Loewner convexity is
earned, including after an affine dissolving-probe map D. This is a matrix
inequality, rather than a scalar weighted-trace surrogate. The fixed native
L restriction remains substantive; the earlier varying-native nonconvexity
control is preserved.

`matrix_price` applies the conic theorem to the actual PSD cone on symmetric
budgets and constructs the exact matrix P representing minus the actual
budget-value derivative. Under strict sensitivity in at least one PSD
direction it proves

```
P is PSD and nonzero,
trace(P*H)=-d(H) for all symmetric H,
trace(P*(Xi(star)-B))=0,
J(star)<=J(x)+trace(P*(Xi(x)-B)) for every x in A,
actual finite Lagrangian dual infimum = actual primal value V(B).
```

No Loewner-convexity field, matrix price, complementarity or full activity
is supplied. Ordinary primal optimum, local finite actual value and its
Frechet derivative are explicit generic inputs. Closedness, finite dimension
and Slater are not claimed to supply that derivative; general nonsmooth
Slater duality remains separate. The objective here is real-valued on A;
the prior scalar extended-objective reduction is preserved, but its general
matrix-budget analogue is not silently assumed.

## Inhabitation and complementarity control

`MatrixClosurePriceExamples` uses the actual one-by-one singular-native Schur
residual x^2 and objective (x-2)^2. Every symmetric one-by-one budget is
independently identified with its coordinate B00. Actual matrix feasibility,
feasible costs and infimum return exactly to the prior quadratic scalar
program, not just to a supplied cost formula. The actual Frechet derivative
at budget1 is minus this coordinate functional, derived by the exact value
return and the earlier independently constructed scalar derivative.

The zero-premise `actual_matrix_price` earns a nonzero PSD price matrix, its
trace representation, complementarity and global inequality by applying the
generic matrix theorem. Optimizer, local finite value and strict PSD-direction
sensitivity are proved. The example does not supply desired certificate
fields to a constructor.

An exact two-by-two control takes P=diag(1,0) and slack S=diag(0,1). Both are
PSD and nonzero, yet trace(P*S)=0. This refutes the false implication from
nonzero PSD price plus complementarity to zero matrix slack. It preserves
the correct matrix theorem and introduces no new paper downgrade.

## Verification and remaining work

Full default build8114; all32 new statements/transitive closures freshly
checked with warnings treated as errors. Cumulative985 is the exact immutable
earlier953 prefix plus fresh32 suffix, with proof/toolchain identity checked.
The entire cumulative command was not rerun. Only propext, Classical.choice
and Quot.sound occur; no proof holes/native_decide. Raw suffix, combined audit,
statement and self-review receipts are retained. Pinned Lean/mathlib proof
bytes, prior protections and cumulative fingerprints are checked by the verifier.

From `lean/` run `lake build`,
`lake env lean -DwarningAsError=true manifests/check_matrix_closure_price_statements.lean`
and `lake env lean -DwarningAsError=true manifests/check_matrix_closure_price_axioms.lean`.
Run `python3 scripts/de_matrix_closure_price_verify.py` from the repo root.
Receipts are in `results/matrix_closure_price_2026-10-03/`.

No original numerical carrier, solver, RNG reification or Python test suite was
rerun. Next obligations include general nonsmooth Slater duality, qualified
split subdifferential/normal-cone stationarity and the matrix extended-objective
return. Physical Lambda identification remains a separate parked project.
The broader original paper is not declared complete. This constructs a
substantive differentiable-value matrix endpoint without a new downgrade.
