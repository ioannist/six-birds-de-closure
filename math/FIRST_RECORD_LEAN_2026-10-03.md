# Constructed original first-record times and ratios, 2026-10-03

This packet constructs the first collapse of any patch for the unchanged original
12×64 population and exact native growth IVP. It proves simultaneous arbitrarily
small positive coincidence ratios while the aggregate record gate passes. It
also certifies bounded ratios in an interior band near the positive edge. The
paper, original Python runtime, original reified population and frozen external
source are unchanged.

## Target and original readout

The original `scripts/de_window_carrier.py` takes `first_record_a` to be the
minimum of all patch collapse times. It does not require both tag values to
have appeared at that time. With matter density a^(-3), it returns

```
R_j(lambda) = |lambda| / rho_m(a_first,j) = |lambda| * a_first,j^3.
```

In contrast, the previously proved two-tag seed record threshold is
max(delta/m_false,delta/m_true). Substituting that threshold as the first-record
threshold would change the readout. This packet instead constructs

```
m_j = max(m_false,j,m_true,j),
T_first,j = delta / m_j,
a_first,j(lambda) = the unique a in [1/1000,20] with D_native(lambda,a)=T_first,j.
```

Both tagged maxima were already kernel-checked against all original amplitudes.
`maximum_spec` proves that m_j bounds every patch amplitude and is attained by
an original patch. A twelve-case exact rational certificate proves
500<T_first,j<897. It imports the unchanged original population rather than
replacing it or supplying a second realization.

## Constructed time and readout return

`GrowthFirstRecord.exists_unique_first_time` derives existence by continuity
and the intermediate value theorem, and uniqueness by strictly positive native
growth derivative. The native initial value is 1. For lambda>=0, the previously
proved matter comparison returns D_native(lambda,a)<=a/a0.

The choice-based `firstTime` definition has a default a0 outside the certified
domain. Its specification theorems require positive a0, A>=a0, nonnegative
lambda, T>1 and T<=D_native(lambda,A). This default is never used in the
original-population claims here: all these premises are discharged for
0<=lambda<=3 using T_first,j<897 and the earlier certificate D_native(3,20)>964.

`time_iff_any_collapse` proves for every native a in [1/1000,20] that

```
exists an original patch i with delta <= amplitude[j,i]*D_native(lambda,a)
  iff a_first,j(lambda) <= a.
```

`time_is_first_collapse` also exports attainment at the chosen time and absence
of any collapse before it. No first-record witness or root-finding correctness
law is supplied as a theorem hypothesis. Strict parameter ordering of the
actual IVP proves strict increase of first time and R_j on [0,3].

`ratio_density_readout` returns the algebraic density formula. The certified
time is positive, so its density is finite and positive on the asserted domain.
All statements concern exact real histories with the declared decimal model
constants and reified IEEE rational amplitudes. They do not certify the
original SciPy integration/interpolation or rounded CSV epoch values.

## Prefix quadrature and numerical bounds

A separate 384-cell certificate covers [1/1000,2], with lambda=3 and the same
native integrand as the previous packet:

```
F(lambda,a)=sqrt(a^3)/sqrt(1+lambda*a^3)^3.
```

Its grid uses 256 subdivisions to a=1 and 128 more to a=2, retaining the exact
initial point. Every lower bound lo_i is constructed with rational arithmetic
and integer square root, then checked in Lean via

```
lo_i^2 * (1+3*b_i^3)^3 <= a_i^3.
```

The auxiliary upper bound 1 is also checked on every cell, as required by the
existing integral-grid theorem. Adjacent cells use a natural-number index;
there is no wraparound at the last Fin index. The exact lower sum is
3264992879/16000000000, greater than 204/1000. The generator replays both output
artifacts byte-for-byte and rejects a deliberately false lower certificate.
Python output is not trusted by the Lean proof: `decide +kernel` checks all
rational inequalities and the finite sum, without `native_decide`.

The actual integral is consequently at least 204/1000. Combining this with
R_native(3,2)>=1767/1000, alpha(3,1/1000)>=2500 and the nonnegative finite-start
term gives D_native(3,2)>901. Every first threshold is below 897, so every first
collapse at lambda=3 occurs by a=2. The matter bound and T_first,j>500 give
first collapse strictly after a=1/2. Therefore, for every original seed,

```
0<=lambda<=3:  1/2 < a_first,j(lambda) <= 2,  R_j(lambda)<=8*lambda;
1<=lambda<=3:  1/8 < R_j(lambda) <= 24;
lambda=3:      3/8 < R_j(3) <= 24.
```

The original exact inside witness 233/100 belongs to [1,3]. The earlier
certified 3<lambda_plus<4 implies 3/4<3/lambda_plus<1, so lambda=3 is an
explicit interior near-edge parameter. These finite numerical bounds are
scoped to the original population and declared units. They do not establish
an input-independent order-unity theorem.

## No coincidence pinch

For every epsilon>0, `ratios_arbitrarily_small` constructs a single positive
lambda<=1 such that the aggregate original record gate passes and
0<R_j(lambda)<epsilon simultaneously for every one of the twelve seeds.
The proof can take lambda=min(1,epsilon/16000): the general horizon bound
R_j<=8000*lambda already suffices. This theorem does not need time continuity,
a numerical near-zero sweep, or an assumed limiting collapse time. Additionally
R_j(0)=0 and the entire [0,3] aggregate gate is proved.

This strengthens the paper's finite-grid negative on universal coincidence
pinching into a continuum statement for its original realized population.
It neither introduces nor proves a measure making a coincidence typical.

## Adversarial self-review

- The all-patch maximum is constructed from attained original tagged maxima;
  neither the both-tag threshold nor an aggregate rank is used as first time.
- The IVT root lives in the original positive scale interval. Its fallback is
  excluded by derived original-population premises in every asserted readout.
- Collapse equivalence uses nonnegative actual growth and a positive attained
  amplitude maximum, including equality at the threshold. The earliest-time
  statement follows from this equivalence, rather than from a definition alone.
- The matter comparison has the direction needed for the lower epoch bound:
  T=D(a_first)<=a_first/a0 implies a_first>=a0*T.
- Every quadrature cell is enclosed throughout its interval; no sampled
  interpolation is promoted to an integral estimate. The initial interval,
  log Jacobian and finite-start term are retained from the prior exact bridge.
- The small-ratio result retains both strictly positive lambda and the actual
  aggregate gate. It does not use the zero-lambda case as its witness.
- The numerical band reaches lambda=3, below the unique positive endpoint.
  No claim is made here about ratios at the exact endpoint or at all admitted
  lambda, about the finite-grid median/max, or about arbitrary populations.
- Review was adversarial self-review, without an independent reviewer.

## Evidence and remaining original scope

The default build passes 8079 jobs. The fresh 629-declaration axiom audit includes
all 36 new theorems (9 general, 4 data, 23 original-return) and uses only
propext, Classical.choice and Quot.sound. All 36 exported statements are checked
separately. See `results/first_record_2026-10-03/verification.json` and
`lean/manifests/axiom_audit_first_record_2026-10-03.txt`. Earlier evidence packets
are retained unchanged.

Next mathematical construction: sharpen the positive endpoint bracket and
prefix enclosures enough to bound first-record ratios at the actual endpoint,
then return the bound to the full relevant admitted parameter band. The
current 3<lambda_plus<4 bracket alone is too coarse for a useful endpoint-ratio
bound for the slowest first-collapse seed. A sharper whole-cell enclosure using
the integrand's unimodality is a promising way to reduce certificate size.
Other robustness populations, negative-parameter first times, physical crunch
and physical Lambda identification retain their previously documented scope.
The broader restoration goal remains incomplete.
