# Original positive endpoint ratio, 2026-10-03

The original realized twelve-seed continuum toy now has an explicit certified
ratio bound at its actual unique positive endpoint. For every original seed,

```
3 < lambda_plus < 17/5,
3/8 < R_j(lambda_plus) < 425/8.
```

Thus 0.375<R_j(lambda_plus)<53.125. Moreover, R_j<425/8 throughout the entire
nonnegative admitted window, and 3/8<R_j<425/8 throughout [3,lambda_plus].
The earlier continuum no-pinching result remains unchanged. This supports
the original qualitative upper-edge ratio claim in declared native units
with explicit constants for the original population. It does not certify
an arbitrary-population or physical coincidence theorem, nor promote the
paper's sampled maximum 17.4 to a continuum maximum.

The paper, original runtime, original reified population and frozen external
source are unchanged. All earlier evidence packets are retained unchanged.

## Original target and unchanged endpoint/readout

The endpoint is exactly `WindowEdgeCertified.upper`, previously constructed
from the original twelve populations, the 80%/ten-seed gate and the exact native
IVP. Its original all-real-parameter specification is still

```
realizedGate(lambda) iff -1/8000 < lambda <= lambda_plus,
D_native(lambda_plus,20)=T*,  960<T*<961.
```

The first-time function and ratio are exactly the earlier `WindowFirstRecord`
functions. The first threshold is delta divided by the largest amplitude among
all original patches, irrespective of tag. The first readout is not the epoch
when both tag values have appeared. Its threshold lies in (500,897) for every
original seed. Nothing is re-sampled and no new population/first-time witness
is supplied as a theorem premise.

The new specifications extend the domain from [0,3] to [0,lambda_plus] for the
same functions. The all-patch maximum is already proved positive and attained.
For every lambda in this larger domain, actual endpoint antitonicity gives
D_native(lambda,20)>=T*>960>T_first,j. The unique first root is therefore
reachable. The choice definition's default is excluded throughout the domain.
`time_iff_any_collapse` and `time_is_first_collapse` return this root to an actual
original patch collapse with no earlier collapse, including the endpoint.

## A sharper enclosure derived from the actual integrand

The previous numerator/denominator cell enclosure was valid but lost their
correlation. `GrowthQuadratureSharp` derives a sharper law for the same actual
native integrand, without replacing it:

```
F(lambda,a) = sqrt(a^3)/sqrt(1+lambda*a^3)^3,
F(lambda,a)^2 = Q(lambda,a) = a^3/(1+lambda*a^3)^3,
dQ/da = 3*a^2*(1-2*lambda*a^3)/(1+lambda*a^3)^4.
```

The derivative is proved by quotient/power rules with the positive denominator
verified. The real mean-value theorem returns monotonicity on every nonnegative
cell below 2*lambda*a^3=1 and antitonicity above it. Since F>=0, these order
statements for its square return to F itself.

For positive lambda, the exact polynomial factorization

```
4*(1+z)^3 - 27*z = (2*z-1)^2*(z+4),  z=lambda*a^3>=0,
```

gives F^2<=4/(27*lambda). This proves the global upper bound even for a cell
crossing the turning point. A lower bound lo valid at both cell endpoints is
valid throughout the cell: for any interior x, either the increasing interval
from the left endpoint to x or the decreasing interval from x to the right
endpoint supplies the needed comparison. No cube-root selection or location
approximation is used in this proof.

Consequently whole-cell certificates can use

```
lo^2*(1+lambda*a^3)^3<=a^3,
lo^2*(1+lambda*b^3)^3<=b^3,
```

for the lower bound. An upper bound hi is certified by one of

```
2*lambda*b^3<=1 and b^3<=hi^2*(1+lambda*b^3)^3,
1<=2*lambda*a^3 and a^3<=hi^2*(1+lambda*a^3)^3,
4<=27*lambda*hi^2.
```

`integral_grid_bounds` then returns actual pointwise bounds to interval integrals
and telescopes all adjacent cells. It verifies positive ordered cells and
actual integrability; there is no sampled interpolation or assumed quadrature
error law.

## Exact rational certificate and native growth return

`scripts/de_endpoint_ratio_certificate.py` constructs bounds using only
Fraction and integer isqrt at precision 1/1000000. `WindowEndpointRatioData`
checks them with `decide +kernel`, not `native_decide`. The same grid covers
[1/1000,20] with 704 cells; its first 512 cells end exactly at 5/2. Numeric vector
syntax is emitted in chunks of at most 128 entries; the polynomial certificates
and integral indices remain natural-number cells across the entire grid.
All existing linter and warnings-as-errors settings remain enabled.

The exact prefix lower sum is 1551183777/8000000000, at least 1938/10000.
The exact full upper sum is 19985237/96000000, at most 2082/10000. The certified
parameter is lambda=17/5. Both artifacts are replayed byte-for-byte; false
lower and false upper cell bounds are deliberately rejected. The Lean proof
checks all actual rational inequalities independently of the generator.

The native quadrature identity retains the exact finite-start term and
parameter-dependent prefactor. Using native root bounds at 5/2 and 20 gives

```
D_native(17/5,5/2)>901,
D_native(17/5,20)<960.
```

The first inequality uses J_prefix>=1938/10000, nativeRoot>=1861/1000,
prefactor>=2500 and the nonnegative finite-start term. The second uses
J_horizon<=2082/10000, nativeRoot<=1844/1000, nativeRoot at the start>=30000,
and the exact prefactor. The positive endpoint satisfies D_native=T*>960,
so strict antitonicity proves lambda_plus<17/5. Its earlier lower bracket 3
is retained.

For every nonnegative admitted lambda, parameter antitonicity at 5/2 gives
D_native(lambda,5/2)>=D_native(17/5,5/2)>901>T_first,j. Hence every first root
is at most 5/2. Matter comparison gives a_first,j>1/2. Therefore

```
R_j(lambda)<=125*lambda/8<425/8 on [0,lambda_plus],
R_j(lambda)>3/8 on [3,lambda_plus].
```

The actual endpoint belongs to both domains. Its ratio readout is the unchanged
abs(lambda)*a_first,j^3, with matter density a^(-3). First time and ratio are
strictly increasing throughout [0,lambda_plus]. This ordering does not assume
continuity or differentiate a rank/max switch.

## Adversarial self-review

- The rational certificates concern the actual native integrand whose bridge
to the original IVP was proved in the previous packet, including initial term
and log Jacobian. The sharper enclosure changes the estimate, not the model.
- The derivative and mean-value hypotheses are derived, including continuity
and differentiability on the needed interval. A desired unimodality field is
not inserted into a witness record.
- The global peak factorization is an identity with a nonnegative right-hand
side; cancellation uses strictly positive lambda and denominator. The numeric
certificate uses lambda=17/5. The general lower-cell law also permits lambda=0.
- Every cell is checked, including the initial interval and the turning-point
cell. Lower bounds check both endpoints; upper branches check their critical
side condition or the global peak inequality.
- Prefix and horizon share one grid with exact indices 512 and 704; Fin indices
are coerced before adding one, with no wraparound. Full adjacent integrals,
not an omitted tail, supply the endpoint bracket.
- The endpoint is the original aggregate ten-seed endpoint. All twelve seeds
have a first collapse there because their all-patch thresholds are below the
aggregate threshold; this does not claim that all twelve pass the both-tag
record predicate there.
- Every first-time premise is discharged throughout [0,lambda_plus]. The
functions are unchanged; their fallback is excluded. Collapse attainment and
absence before first time are explicitly returned to the original patches.
- Numeric bounds have explicit original-population/native-unit scope. No
claim of the finite-grid maximum being a continuum maximum, typicality under
a measure, SciPy correctness, or physical Lambda/crunch is made.
- This was adversarial self-review without an independent reviewer.

## Evidence and remaining scope

The full default build passes 8082 jobs. The fresh 663-declaration axiom audit
includes all 34 new theorems (9 sharp-integrand, 5 data, 20 original-return)
and uses only propext, Classical.choice and Quot.sound. All 34 exported
statements are separately checked. See
`results/endpoint_ratio_2026-10-03/verification.json` and
`lean/manifests/axiom_audit_endpoint_ratio_2026-10-03.txt`.

The original positive-edge qualitative ratio claim and the no-pinching negative
now have continuum backing for the original fixed population. The first-time
API still treats nonnegative parameters; admitted negative first times require
a live-domain extension rather than using its default. Other patch-count and
newly sampled robustness populations remain separate. The existing full
coupled delta/amplitude-scale endpoint sensitivity rectangle is unchanged.
Physical identification and known false original claims retain their earlier
coverage boundaries; the broader restoration goal remains incomplete.
