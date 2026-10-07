# Actual N32/N128 first-record edge ratios, 2026-10-03

Baseline: `0e29ce6`. Adversarial self-review, not independent review. Paper,
runtime, reified inputs and prior proof/evidence remain fixed.

## Target and return

Original section5/appendixA reports robustness under N in{32,64,128}, including
population-dependent endpoint ordering and an upper-edge coincidence-ratio scale.
The actual separately realized N32/N128 continuum windows and strict ordering
were already constructed. This packet supplies their actual first-ANY-patch
readouts and explicit numerical endpoint/ratio certificates, using the unchanged
original native IVP with a0=1/1000, horizon20, initial D=1.

For v=false(N32),true(N128), let T_v be the independently certified actual
10-of-12 aggregate threshold and c_v=T_v/965. This is an analytic normalization,
not a rescaling or identification of the input populations. The actual native
endpoint u_v satisfies

```
3<u_v*c_v^3<7/2,
13/10<u_32<17/10,
5<u_128<25/4.
```

For all12 seeds in each population, the actual first collapse of ANY patch at
the endpoint satisfies

```
(9/20)*c_v<a_first(u_v)<=(8/3)*c_v,
2187/8000<R_first(u_v)<1792/27.
```

Every actual signed admitted parameter has0<=R<1792/27. Every nonpositive
admitted parameter hasR<1/1000. These are explicit continuum certificates,
not interpolated sweep values, sharp numerical estimates or typicality.
The historical grid endpoints are not identified with these continuum roots.
The earlier actual N32<N64<N128 endpoint ordering remains unchanged.

## Mathematical chain

`WindowPatchCountFirstData` defines first threshold from the maximum across both
tag-specific maxima of the immutable N32/N128 reified inputs. Kernel rational
certificates earn1<Tfirst<2000 and450*c_v<Tfirst<897*c_v. They also earn
c32 in(129/100,131/100),c128 in(83/100,84/100), hence c_v in(1/5,4).
An existential false-target kernel theorem shows the original N64 bound
500*c_v<Tfirst fails for at least one N32 seed. No transfer is assumed.

`WindowPatchCountRatio.maximum_spec` obtains actual attained global maxima from
both original tag maxima and bounds every original patch. The aggregate is
965*c_v by arithmetic; first thresholds lie strictly below it independently for
every seed. Thus actual gate membership earns threshold attainability at20.
`GrowthFirstRecordLive` supplies the unique original native root. ANY-patch
collapse iff time<=a and minimality return it to the original runtime's intended
first-record readout, rather than the later two-tag epoch.

Previous exact finite-start quadrature/covariance gives original growth>970*c_v
atlambda3/c_v^3, scale5*c_v, and original horizon growth<960*c_v atlambda
(7/2)/c_v^3. Actual scale monotonicity transfers the lower prefix to20. These
straddle965*c_v; actual lambda strict ordering and actual endpoint equality yield
3<u_v*c_v^3<7/2. Tight rational scales earn the displayed unnormalized brackets.
The initial term and lambda-dependent prefactor remain exactly as previously
certified; no new asymptotic model or quadrature computation is substituted.

Nonnegative matter comparison gives a_first>=Tfirst/1000>(9/20)*c_v. Previous
actual growth>897*c_v atlambda(7/2)/c_v^3 and scale(8/3)*c_v, together with the
earned endpoint upper bound and actual lambda comparison, gives the upper time
bound. Scale(8/3)*c_v is inside the original interval. The actual first-threshold
equivalence returns the time bound. Combining these independently earned bounds
with R=abs(lambda)*time^3 gives2187/8000<R<1792/27.

First times are strictly increasing on each full signed admitted interval.
Nonnegative ratios are strictly increasing and bounded by the endpoint ratio.
For nonpositive admitted lambda, actual matter comparison gives time<2 and
abs(lambda)<1/8000, henceR<1/1000. These cover the entire signed window.
The exact density readout is abs(lambda)/rho_m with rho_m=time^(-3).

## Strong no-pinching and controls

One lambda=min(u32,u128,epsilon/16000)>0 lies in both actual gates. The actual
interval bound time<=20 givesR<=8000*lambda<epsilon for all24seeds, withR>0.
There is no positive global floor, median, probability or universal coincidence
claim. N is discrete and no smooth-in-N theorem is asserted.

`de_patch_ratio_certificate.py` uses Fraction only and reads immutable population
JSON. It independently reconstructs every actual tag maximum, two-tag threshold,
10th rank and first-ANY-patch threshold before checking the new inequalities.
It records seeds failing the tempting500 lower bound and detects replacement of
the first-ANY-patch readout by the two-tag threshold. It performs no RNG/ODE/float
calculation. Default exact report replay passes.

## Verification and remaining work

Two new roots add33 theorems. Full lake build8158 jobs passes; all33 exported
statements and transitive axiom closures pass with standard Lean axioms only.
No holes or native_decide. Cumulative1284 preserves exact immutable prior1251
raw prefix plus fresh33; the full cumulative command was not rerun. Toolchain,
prior proof/source/evidence identity and exact report replay checked by
`de_patch_ratio_verify.py`. Receipts are in `results/patch_ratio_2026-10-03/`.

The separately realized population endpoint/first-record numerical obligation is
closed at the stated broad constants. Joint first-time regularity, combined new
population-and-knob sweeps, sharp ratio typicality and broader original-target
audit remain separate. Physical Lambda, moving native calculus, ordinary primal
attainment and earlier false/project-sized claims remain unaffected. The full
user goal is incomplete; no new original claim downgrade is introduced here.
