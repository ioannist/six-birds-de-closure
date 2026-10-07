# Certified original-population endpoint bracket, 2026-10-03

The exact original twelve-seed continuum model now has a kernel-certified
positive window endpoint between 3 and 4. This strengthens the original
reported inside/outside bracket 2.33 to 5.31. Both original witnesses are
proved for the same reified population and native growth IVP. The paper,
original runtime, reified population and frozen external source are unchanged.

## Exact statement and return

`WindowEdgeCertified.exists_unique_certified_window` proves, without theorem
hypotheses, that there is a unique upper with

```
3 < upper < 4,
D_native(a0=1/1000, lambda=upper, A=20) = T*,
for every real lambda,
  realizedGate(lambda) iff -1/8000 < lambda <= upper.
```

Here T*=971912828383572000768/1012057850670495125 is the previously checked
aggregate rank threshold of the original twelve reified populations.
`upper_eq_scaled_endpoint` identifies this upper with the already constructed
scaling endpoint at d=delta0=843/500 and s=1. It is therefore the same endpoint
whose C1 sensitivity was proved in the previous packet.

The exact model uses declared decimal a0,A,delta and exact IEEE rational input
amplitudes/tags. The original sampler-to-input provenance remains the earlier
computational bridge. The statement concerns the exact continuum history gate;
it does not certify total correctness, integration status, interpolation or
error of the original SciPy solver. The original paper witnesses 2.33 and 5.31
are represented as exact decimal rationals 233/100 and 531/100.

## Native quadrature with the finite-start term retained

`GrowthQuadrature` derives a native-scale expression for the same constructed
family, for a0>0, A>=a0 and nonnegative lambda:

```
F(lambda,a) = sqrt(a^3) / sqrt(1+lambda*a^3)^3,
J(lambda,a0,A) = integral from a0 to A of F(lambda,a) da,
R(lambda,a) = sqrt(1/a^3+lambda),
alpha(lambda,a0) = lambda*a0^2 + 5/(2*a0),
D_native(lambda,A) = R(lambda,A) * (1/R(lambda,a0) + alpha(lambda,a0)*J).
```

This is an exact identity, not a growing-mode or large-horizon approximation.
The parameter-dependent finite-start term and prefactor are both retained.

The bridge first proves exp(-n*log(a/a0))=(a0/a)^n and the exact sqrt root
identities. The log integrand times the native Jacobian 1/a is then proved to
be a0^2/sqrt(a0^3)^3 times F. The change-of-variables theorem is applied with
actual log derivatives, continuous 1/a on the positive native interval and
continuous original integrand on its image. The live-root property is derived
from nonnegative lambda. Algebra cancels the sqrt(a0^3) factors and returns
exactly the displayed native expression. No native quadrature identity is
supplied as a hypothesis.

The native quadrature theorem is scoped to lambda>=0, sufficient for these
positive-edge certificates. Earlier existence, uniqueness, ordering and
sensitivity theorems retain their full live-lambda domains, including negative
lambda. No narrowing of those results is introduced.

## Whole-cell enclosures and finite sum return

For a>=0 and lambda>=0,

```
F(lambda,a)^2 = a^3 / (1+lambda*a^3)^3,    F(lambda,a)>=0.
```

For a cell [a,b] and nonnegative rational bounds lo,hi, the inequalities

```
lo^2 * (1+lambda*b^3)^3 <= a^3,
b^3 <= hi^2 * (1+lambda*a^3)^3
```

imply lo<=F(lambda,x)<=hi for every x in [a,b]. The proof uses monotonicity
of the numerator and denominator polynomials and nonnegative-square
comparison. It does not infer an unsampled interval bound from endpoint
function samples or assume monotonicity of F itself.

`integral_grid_bounds` proves that summing cell width times lo/hi bounds J.
Continuity and interval-integrability are derived on every positive cell;
interval integral monotonicity gives each cell bound; the adjacent-interval
sum theorem returns the finite sum to the entire integral. The exact grid
starts at a0 and ends at A, and each neighboring pair bounds a full cell.
There is no omitted initial segment or tail.

## Exact generated certificates

`de_growth_quadrature_certificate.py` uses only standard-library Fraction
arithmetic and integer isqrt. It generates 264 cells with fine spacing near
the peak and coarser spacing in the tail. The grid and bound values are exact
rationals; the denominator used to enclose square roots is 10^6. No floating
arithmetic, random sampling or ODE solver enters the certificate generation.

For lambda=3 the lower enclosure is computed by an integer square-root floor
of a^3/(1+3*b^3)^3. For lambda=4 the upper enclosure uses a floor plus one for
b^3/(1+4*a^3)^3. The generator checks every rational cell inequality and both
finite sums. A deliberately false lower enclosure is rejected as a control.
Its default invocation recomputes expected bytes and checks both committed
artifacts; --write explicitly regenerates them.

`GrowthQuadratureData` independently checks the generated statements with
`decide +kernel`: exact endpoints, all lower cells, all upper cells and the two
finite-sum bounds. The lambda=3 upper filler hi=1 and lambda=4 lower filler
lo=0 also satisfy the generic theorem's hypotheses. Each applicable filler
inequality is proved, not silently assumed. Fin indices are coerced to natural
indices; the adjacent endpoint of cell 263 is grid 264, not a wrapped index.
The real-domain return is checked by rational casts and the generic cell theorem.

The resulting inequalities are

```
J(3,1/1000,20) >= 2227/10000,
J(4,1/1000,20) <= 187/1000.
```

## Growth bounds, endpoint ordering and original witnesses

At lambda=3, square comparison proves R(3,20)>=1732/1000 and alpha>=2500.
The initial inverse root is nonnegative, so the exact quadrature gives D(3)>964.
At lambda=4, R(4,20)<=200004/100000, R(4,a0)>=30000, and therefore the initial
inverse root is at most 1/30000. The exact upper integral bound and exact
prefactor give D(4)<936. All remaining numerical inequalities are exact rational
norm_num proofs in Lean.

The checked original rank threshold satisfies 960<T*<961. Hence D(3)>T* and
D(4)<T*. Strict decrease of the actual native family and the previously
constructed unique threshold root imply 3<upper<4. `upper_spec` returns that
root to the exact original aggregate gate for every real lambda.
`inside_three_outside_four` proves the new witnesses. `paper_bracket_certified`
and `paper_inside_outside` prove the old decimal witnesses as a consequence.

Positive lambda=4 satisfies the persistence cutoff, so its gate failure is
failure to reach the aggregate growth threshold, not cutoff erasure. The result
does not assert that every individual seed or patch has the same failure
verdict or record count. The gate counts histories with both tag values and
requires ten of twelve passes.

## Adversarial self-review and limitations

This is constructive work and adversarial self-review by one reviewer. The
review checks the log Jacobian, exact finite-start normalization, positivity
and sqrt cancellations, whole-cell rather than sampled bounds, contiguous
coverage and exact endpoints, all certificate casts, initial-root inverse
bounds, nonnegative multiplication directions, decreasing-family ordering,
uniqueness, and identity with the previous endpoint function.

The analytic certificate never assumes G(3)>T*, G(4)<T*, a supplied endpoint
bracket, a quadrature error field, or solver convergence. The finite data supply
rational arithmetic inequalities that are separately kernel-checked. The
scouting floating calculation is not an artifact or a proof dependency.

The endpoint lies in the interval (3,4); this packet does not compute an exact
value or claim a tighter decimal error bar. The exact continuum result does
not turn the original floating solver into a certified algorithm. It also
does not prove the numerical coincidence-ratio values at first record times,
all separately reseeded robustness populations, an integrated physical crunch,
or a physical Lambda identification. Previously contradicted claims and the
separate spacetime bridge remain as recorded in the original-claim table.
The original paper is still not fully substantiated.

## Verification and next construction

The full default build passes 8076 jobs with warnings treated as errors. All
29 new theorems (12 quadrature, 5 data, 12 endpoint) are in the fresh
593-declaration transitive axiom audit, limited to the disclosed standard
axioms. Twenty-three exported statements are checked separately. The exact
certificate generator replay and false-certificate control pass. Source
fingerprints and receipts are in `results/growth_quadrature_2026-10-03/`, with
raw audit `lean/manifests/axiom_audit_growth_quadrature_2026-10-03.txt`.
The original Python test suite, growth solver and population reification tools
were not rerun; their sources and reified inputs are unchanged.

The same cell-bound route can next certify record-time/ratio bounds or return
numerical brackets to other explicitly reified robustness populations. Further
precision is possible by refining cells, but the current bracket already
strengthens and certifies the original positive-edge witnesses. The broad
research goal remains active.
