# Actual growth derivatives and C1 endpoint return, 2026-10-03

This packet closes the strict parameter-sensitivity and continuous first
endpoint-derivative obligations for the constructed growth family. It returns
the derivatives to the original scale-factor IVP and the original fixed
population under exact coupled delta/amplitude rescaling. The paper, original
Python runtime, reified population and frozen external source are unchanged.
This is constructive work and adversarial self-review by one reviewer.

## Exact target and premises

For a0>0, A>=a0, lambda>-A^-3 and a in [a0,A], the actual native growth and
its native scale derivative have parameter derivatives. For a>a0 both
lambda derivatives are strictly negative. At the initial time the sensitivities
are zero, consistent with the parameter-independent initial data.

For a0>0 and log horizon L>0, let G(lambda) be the already constructed
final growth. It is C1 throughout the entire open live horizon and G'(lambda)<0.
On Ginf<T<exp(L), the previously constructed unique positive endpoint E(T)
is C1, with

```
E'(T) = 1 / G'(E(T)) < 0.
```

For the original twelve-seed realization, exact common real amplitude
multiplier s and threshold d give T(d,s)=T0*d/(delta0*s). The actual aggregate
window endpoint is C1 as a function of the pair (d,s) wherever s>0 and this
threshold is admissible. Every point of d in [6/5,2], s in [1/3,3] is admissible
by the previous exact population proof. C1 holds on an open neighborhood of
each rectangle point, including its boundary points. The delta partial is
strictly negative; the scale partial is strictly positive for positive delta.

The result asserts continuous first derivatives. It does not assert infinite
order differentiability, a derivative in discrete patch count N, derivatives
through arbitrary finite maximum/rank switches, or identity with separately
rounded or reseeded runtime populations.

## Differentiating the actual quadrature

`GrowthParameter` uses the earlier definitions, with c=lambda*a0^3:

```
u(c,x) = exp(-3x)+c,    r(c,x) = sqrt(u(c,x)),
f(c,x) = 3 exp(-3x)/(2u(c,x)),
I(c,x) = exp(-2x)/r(c,x)^3,
P(c,x) = integral from 0 to x of I(c,t) dt,
h(c) = c+5/2,
D(c,x) = r(c,x) * (1/r(c,0) + h(c)P(c,x)).
```

The ordinary parameter derivatives are proved by sqrt, product and quotient
rules. In particular I_c=-3 exp(-2x)/(2r^5). To differentiate the integral,
nonnegative final time L and u(c,L)>0 supply epsilon=u(c,L)/2>0. For every
parameter d in [c-epsilon,c+epsilon] and every t in [0,L],

```
u(d,t) >= epsilon.
```

The exponential ordering and the parameter lower bound prove this margin.
A globally continuous auxiliary derivative integrand uses max(u,epsilon).
It equals the actual I_c everywhere on that full rectangle. Compactness gives
an upper bound K for its norm; the constant bound is interval-integrable.
Measurability, integrability of the original integrand, and pointwise parameter
differentiation are all discharged before applying mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
The conclusion proves integrability of I_c and P_c=integral I_c. No domination
or parameter derivative is assumed, and the model integrand is never replaced.

`primitiveParameter_time_derivative` proves the ordinary FTC for this actual
parameter derivative integral. It uses continuity at the evaluation point,
integrability on the interval and global measurability, including at closed
endpoints. Both mixed equations below are then established by direct time
differentiation of explicit formulas, not by an assumed interchange theorem.

## Derived variational system and strict sign

`growthParameter` and `velocityParameter` are explicit expressions. Product and
quotient rules first identify them with D_c and v_c. Their time derivatives
are then proved to satisfy

```
(D_c)' = v_c,
(v_c)' = f D_c + (f-2)v_c + f_c(D+v),
D_c(0) = v_c(0) = 0,
f_c = -3 exp(-3x)/(2u^2) < 0.
```

The initial zero equations are algebraic consequences of the same quadrature
and the original finite-start values. The actual growth solution has D,v>0
and a nonnegative bounded coefficient on the compact live interval, by the
previous IVP construction and cone proofs. Therefore (-D_c,-v_c) satisfies the
already proved cooperative system with forcing -f_c(D+v)>0 and zero initial
data. `cooperative_strict_forcing` gives D_c,v_c<0 at every positive time.
This argument establishes the strict derivative sign; strict monotonicity
alone would not suffice.

The actual lambda derivative of final growth is
`finalSensitivity=a0^3*growthParameter(lambda*a0^3,L)`. The chain factor is
positive when a0>0. Native growth is the same D evaluated at log(a/a0), and
native p is v/a. Thus the native parameter derivative formulas include the
correct a0^3 factor and the extra division by positive a for p. The horizon
positivity theorem supplies every live parameter, including negative lambda;
no restriction to nonnegative lambda is introduced.

## Continuous derivatives and constructed inverse

A locally agreeing continuous integral of the auxiliary derivative integrand
proves continuity of P_c in c. Product/quotient rules for continuity then give
continuity of D_c and of G'(lambda). `finalGrowth_c1` combines the actual
derivative with its continuity on the open native live horizon.

`endpoint_parameter_derivative` applies mathlib's
`HasDerivAt.of_local_left_inverse` to the earlier constructed endpoint. Its
continuity is already proved; G'(E(T)) is nonzero by the strict sign theorem;
G(E(t))=t holds on a neighborhood of T because every nearby threshold remains
inside the open admissible interval and satisfies `endpoint_spec`. No inverse
identity or endpoint derivative is supplied as a hypothesis. Composition and
nonzero reciprocal continuity prove continuous E', hence `endpoint_c1`.

For the original coupled rescaling, ordinary rational differentiation gives

```
partial_d E(d,s) = E'(T(d,s)) * T0/(delta0*s),
partial_s E(d,s) = E'(T(d,s)) * (-d*T0/(delta0*s^2)).
```

Exact original positivity of T0 and delta0 gives the strict signs. Composition
of the C1 endpoint with the two-variable rational threshold proves
`scaled_endpoint_c1`. The previous rectangle admissibility certificate yields
`robustness_rectangle_c1`, with no new supplied population or rank premise.
The earlier native window theorem continues to identify this exact endpoint
with the actual aggregate history gate.

## Adversarial self-review and scope boundaries

The review checks the lower root margin over every integration time, ordinary
parameter differentiation on an open neighborhood, interval-integrability
and measurability, the initial zeros, both variational equations, the forcing
sign and coefficient bound, the lambda chain factor, the native p division,
the locally valid inverse identity, and threshold-domain restrictions.

Neither clipping, a supplied derivative-sign field, monotone-to-strict-derivative
inference, nor mixed-derivative interchange enters the proof. The derivative
and continuous derivative results concern the same explicit family that was
proved to solve both native IVP equations. Boundary root-square zero is excluded;
initial time is included for derivatives and excluded for strict negativity.
Threshold fallback values outside the admissible interval are not included in
the endpoint C1 theorem.

C1 common scaling is compatible with ties: every seed threshold scales by
the same positive factor, so the exact rank formula survives. Arbitrary
amplitude perturbations can switch maximizing patches or rank branches and
produce corners; the earlier continuity theorem allows these switches, while
this packet does not claim their differentiability.

This improves the original toy edge-drift claim to a mechanized C1 statement
for the exact fixed-population delta/scale family. It does not certify the
floating solver's edge locations, convergence or error. It does not prove an
integrated physical crunch or identify the toy parameter with physical Lambda.
Previously contradicted claims and the separate spacetime bridge remain
unchanged; the full original paper is not thereby complete.

## Verification and next construction

The full default `lake build` passes 8073 jobs with warnings treated as errors.
All 40 new theorems (29 growth, 11 endpoint) are added to `check_axioms.lean`.
The fresh transitive audit contains 564 declarations, with only propext,
Classical.choice and Quot.sound. Twenty-five exported statements are checked
separately. Source fingerprints and receipts are in
`results/growth_parameter_2026-10-03/`; the raw audit is
`lean/manifests/axiom_audit_growth_parameter_2026-10-03.txt`.
The original Python test suite, growth solver and reification tools were not
rerun; their sources and original inputs are unchanged. Historical receipts
remain unchanged.

A next feasible window construction is certified numerical bracketing of the
actual native positive endpoint, with explicit quadrature or ODE error bounds.
General fixed-branch amplitude derivative returns and higher-order regularity
are additional possible constructions. These are not substituted for a
physical bridge or for restoration of claims already contradicted in the
original-claim coverage table. The broad research goal remains active.
