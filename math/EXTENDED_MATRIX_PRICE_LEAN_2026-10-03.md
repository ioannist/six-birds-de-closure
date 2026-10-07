# Extended-objective conic and Schur matrix price, 2026-10-03

Baseline: `bdbf27f`. Paper, original runtime and all earlier proof/evidence are
unchanged. Review is adversarial self-review, not independent review.

This closes the extended-objective reduction gap in the differentiable-value
matrix theorem. General nonsmooth Slater duality and qualified split
subdifferential/normal-cone stationarity remain separate obligations.

## Actual extended conic optimization

`ExtendedConeClosurePrice` uses the original extended-real objective J,
original admissible A, actual cone-valued budget B and actual cone-feasibility
condition. Its value is the complete-lattice infimum

```
V(B)=inf {J(x) : x in A, B-energy(x) in the positive cone}.
```

Assume J is nowhere minus infinity on A and its ordinary real epigraph is
convex. Energy is cone-convex on A. An ordinary finite primal optimizer star
exists, actual V is neither infinity on a budget neighborhood, and the actual
finite value has Frechet derivative d there at B. These are explicit premises.
No dual, complementarity, supporting value field, restricted infimum identity
or constraint activity is supplied.

The prior epigraph proof earns convexity of the finite objective domain
F=A intersect {J not plus infinity} and of J.toReal on F. The new conic
reduction earns nonempty/bounded-below real feasible-cost guards from actual
extended value finiteness. It proves the exact original-value return

```
V(B)=coe (inf {J(x).toReal : x in F, B-energy(x) in the cone}).
```

No scalar budget proxy replaces the vector or matrix feasibility condition.
The equality compares actual cost sets and their lower bounds, treats infinite
original objectives separately, and protects real infimum semantics. Local
equality transfers the actual original Frechet derivative to the restricted
real conic infimum.

The previous conic primal-mixing theorem then constructs the cone-positive
linear price p=-d, with

```
p(energy(star)-B)=0,
J(star)<=J(x)+p(energy(x)-B) for every original x in A.
```

The original domain is restored: at finite objective points the real bound
converts exactly to EReal; at plus-infinity points a finite price evaluation
leaves the Lagrangian value plus infinity. The certificate earns ordinary
primal optimality and actual extended primal/dual equality. Its dual value
equals the attained finite J(star), proving it is neither infinity. Competing
cone-positive linear prices obey complete-lattice weak duality even when their
dual infimum is minus infinity; no arbitrary real fallback value is used.

This argument supplies global combined Lagrangian minimization. It does not
split objective, energy and admissibility subdifferentials without their
separate qualifications. No claim is made that Slater alone supplies actual
value differentiability, or that complementarity forces the whole slack vector
to vanish. The earlier nonzero PSD slack control is unchanged.

## Actual extended Schur matrix theorem

`ExtendedMatrixClosurePrice.matrix_price` uses the existing real symmetric
matrix budget space with its elementwise norm topology. The energy is exactly
the previously constructed singular-support residual

```
Xi(x)=Support.residual L (D(x)).
```

Native L is fixed and D is affine. The already proved exact blind-Gram mixing
identity earns Loewner convexity; it is not supplied as a convexity field.
PSD cone zero/add/scaling laws are independently established. The original
extended objective is used throughout the actual infima and final Lagrangian.

From the actual finite value derivative and a negative derivative in at least
one PSD budget direction, the theorem constructs a nonzero PSD matrix P with

```
trace(P*H)=-d(H) for every symmetric H,
trace(P*(Xi(star)-B))=0,
J(star)<=J(x)+trace(P*(Xi(x)-B)) for every original x in A,
actual extended trace-Lagrangian dual infimum = actual extended primal value,
that dual infimum is neither plus nor minus infinity.
```

The price matrix is the prior explicit symmetrized matrix-unit construction;
its PSD property follows from cone positivity on actual rank-one directions.
No matrix dual/Riesz field is assumed. Singular native Gram blocks and the
unchanged positive-definite Schur return are preserved. No allocation-sum
budget or physical stress-energy object is substituted.

## Complete extended matrix example and conversion control

`ExtendedMatrixClosurePriceExamples` uses the actual one-by-one Schur residual
x^2 and a genuinely extended objective: (x-2)^2 for x>=0 and plus infinity
otherwise. Every symmetric one-by-one matrix budget is identified with its
B00 coordinate. Actual extended feasible-cost sets and infima return exactly
to the earlier extended scalar program.

The actual matrix value derivative at budget1 is constructed as minus the
coordinate functional by composing the proved scalar extended-value derivative
with this exact matrix-value return. Ordinary optimizer x=1, local finite
actual value and strict PSD-direction sensitivity are independently proved.
The final zero-premise theorem applies the generic extended matrix theorem and
returns a nonzero PSD matrix price, trace identification, complementarity,
global extended Lagrangian bound and actual extended primal/dual value1.

An exact control omits the finite-domain restriction. For any real K the
converted matrix value is proved equal to the corresponding actual scalar
infimum. With K=J.toReal the forbidden feasible x=-1 has cost zero, because
J(-1)=plus infinity is mapped to zero by toReal. Lean proves the bad converted
matrix value is zero, while the actual original extended matrix value is one.
This exercises the actual matrix-budget operation and preserves the finite
domain as an earned, necessary bridge.

## Evidence and next obligations

Full default build8117; all18 new statements/transitive closures freshly
checked with warnings treated as errors. Cumulative1003 is the exact immutable
earlier985 prefix plus fresh18 suffix, with prior proof/toolchain identity
checked. The full cumulative command was not rerun. Allowed axioms are propext,
Classical.choice and Quot.sound; no proof holes/native_decide. Raw suffix,
combined audit, statement output and adversarial self-review are retained.
The verifier checks pinned Lean/mathlib proof bytes, prior artifact protections,
actual declaration domains, complete-infimum controls and cumulative fingerprints.

From `lean/` run `lake build`,
`lake env lean -DwarningAsError=true manifests/check_extended_matrix_price_statements.lean`
and `lake env lean -DwarningAsError=true manifests/check_extended_matrix_price_axioms.lean`.
Run `python3 scripts/de_extended_matrix_price_verify.py` from the repo root.
Evidence is in `results/extended_matrix_price_2026-10-03/`.

No original carrier/solver, RNG reification or Python test suite was rerun.
The differentiable-value scalar and matrix price constructions now cover
extended objectives with proved domain/infimum returns. General nonsmooth
Slater duality and qualified split stationarity remain open. Physical Lambda
identification remains a separate parked project. No new paper downgrade is
introduced; the broader original paper is not declared complete.
