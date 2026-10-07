# Avenue C Memo: Light-Cone/Fitting Closure-Quotient Magnitude Gate

> **Mathematical review correction (2026-10-01):** the argument below is
> conditional on its declared interface, physics, and approximation assumptions.
> Its limits are neither a universal impossibility result nor a proof that a
> run supplies the missing magnitude. Emergence alone does not forbid proof:
> finite deterministic runs can be formalized. A no-shortcut result requires
> an explicit resource model; a no-descent result requires a fixed access quotient.
> An unspecified coefficient remains unspecified until a lawful construction
> or supplied selection fixes it.

Status: theory magnitude-assessment memo. No Lean, data, plan, or results
changes.

Governing inputs:

- `math/DERIVATION_AVENUE_D_2026-06-02.md`, sections 3.2 and 4.
- `plan/SIXBIRDS_DE_AVENUES_MAP_2026-06-02.md`, Avenue C.
- `math/DERIVATION_LT2_2026-06-02.md`, sections 6 and 7.

## 0. Verdict

**NO.** The closure-structured light-cone/fitting residual does not presently
reach `O(0.1)` in a controlled, no-amplifier way. Avenue C remains a
principled applicability evasion of Green--Wald/Ishibashi--Wald
stress-energy no-go theorems, but the magnitude gate fails.

The decisive distinction is:

```text
robust mean fitting/light-cone bias       small: 10^-5--10^-3, sometimes percent-level in parameters
irreducible scatter / lensing variance   can approach 10%, but is scatter, not mean DE
narrow-beam / opaque-clump toy effects   can be ~0.1 mag or larger, but model-dependent and not closure-derived
timescape / large void-lapse physics     O(1)-capable, but imported physics, not SBT-selected
```

Therefore Avenue C banks at **C/B**. It is still useful as a precision
systematics and closure-audit formalism, but it is not a derivation of the
dark-energy magnitude. The blocker is not the old spatial `Q_D ~ 10^-5`
argument; the blocker is that the light-cone/fitting literature itself gives
small robust mean biases unless one adds extra small-beam, opaque-clump,
large-void, or lapse physics. The Schur/F4 closure layer can classify and
audit those residuals, but it does not supply their scale.

Decision: do **not** build the full Avenue-C dark-energy derivation formalism
as an outcome-A route. If pursued, build it only as a banked light-cone
closure-audit / precision-systematics formalism.

## 1. Literature Magnitudes

### 1.1 GMNV / Ben-Dayan--Gasperini--Marozzi--Nugier--Veneziano

The 2011 GMNV paper is a formalism paper: it introduces covariant,
gauge-invariant light-cone averages, geodesic-light-cone coordinates, and
expressions for averaging luminosity-redshift and redshift-drift observables
in generic inhomogeneous geometries. It explicitly presents a method, not a
dark-energy-scale computation. It states that detailed magnitudes must be
computed in explicit models and even notes that if the effects are small, the
calculation would sharpen the conclusion that dark energy is unavoidable.

The follow-up computations are the relevant magnitude test.

- In the leading linear-regime light-cone calculation, induced backreaction on
  the luminosity-redshift relation is larger than naive expectations, but it
  cannot by itself reproduce observed dark-energy effects at large redshift.
  With a cutoff `k_UV = 1 Mpc^-1`, a contribution estimated from the lensing
  term is `O(10^-3)` at `z ~ 1`, not `O(0.1)`. The authors warn against reading
  an apparent `Omega_Lambda ~ 0.1` compatibility in a CDM+IBR plot as a real
  dark-energy mimic.
- In the second-order concordance-model treatment, the mean bias is smaller
  still for the best behaved observable: dark-energy parameters remain
  determinable to order `10^-3--10^-5`, depending on observable and power
  spectrum regime. Nonlinear corrections can produce an irreducible scatter
  approaching `10%`, but that is scatter/variance, not a mean residual that
  replaces `Omega_Lambda`.
- The energy flux, or luminous intensity, is repeatedly singled out as least
  biased. Distance modulus and distance variables can be more biased, but the
  mean effect still does not simulate a substantial fraction of dark energy.

Assessment for Avenue C. This is the strongest direct light-cone-averaging
evidence, and it is negative for the magnitude gate. It gives a real
light-cone residual, but its controlled mean scale is `10^-5--10^-3`, with
large scatter only in the precision/noise sense.

### 1.2 Rasanen Light-Propagation Results

Rasanen's statistically homogeneous/isotropic light-propagation work is not a
small-spatial-`Q_D` argument. It asks what light rays measure in a lumpy
universe on scales longer than the homogeneity length.

The key mathematical point is that, under statistical homogeneity/isotropy
and slow evolution of the distribution, redshift and angular-diameter
distance are controlled by average expansion and matter variables, plus null
geodesic shear. The Dyer--Roeder smoothness prescription is not the right
description of clumping. The observer-relevant averaging hypersurface is
selected by redshift and statistical symmetry, not by an abstract coordinate
choice.

Magnitude implication:

- Local density and expansion variations can be order unity, but their
  line-of-sight contribution cancels over scales longer than the homogeneity
  scale under the stated assumptions.
- Light deflection and image shear are argued/observed to be small for
  typical rays.
- A large distance effect is possible only if the **average expansion history**
  itself differs substantially from FLRW or if discreteness/narrow-beam
  effects invalidate the continuous-fluid approximation.

Assessment for Avenue C. Rasanen gives the correct non-circular object:
observed redshift and distance, not spatial `Q_D`. But it does not deliver a
closure-only `O(0.1)` fitting bias. It says the distance residual follows the
average expansion/shear model. SBT has no independent theorem fixing an
`O(1)` average expansion change.

### 1.3 Ellis Fitting Problem, Kolb, Marra/Notari, and Swiss-Cheese Work

Ellis--Stoeger formulate the fitting problem: one must specify how an
idealized smooth FLRW model is fitted to a lumpy universe. Kolb--Lamb sharpen
this by showing that even exact light-cone observables such as luminosity
distance and light-cone mass density may not uniquely determine a cosmological
model without extra assumptions. This supports the closure reading of
fitting as a quotient problem. It does **not** provide a magnitude by itself.

Swiss-cheese and large-scale-inhomogeneity studies mostly give small robust
effects unless the model is deliberately large/special:

- Brouzakis--Tetradis--Tzavara find luminosity-distance dispersion/bias from
  large inhomogeneities, but too small to explain acceleration without dark
  energy, even for very large inhomogeneity scales.
- Flanagan--Kumar--Wasserman--Vanderveld find, for randomized voids of radius
  `35 Mpc` at source redshift `z_s = 1`, a mean magnitude shift about
  `0.003 mag` and standard deviation about `0.027 mag`; varying assumptions
  changes the standard deviation roughly within `0.005--0.06 mag`. These are
  precision-systematics numbers, not dark-energy-magnitude numbers.
- Marra--Notari review that Copernican large-void realizations give small,
  potentially non-negligible corrections, while non-Copernican giant-void
  models can mimic acceleration. The latter is not an SBT closure derivation;
  it imports a large special geometry and is already constrained by other
  observables.

Assessment for Avenue C. The fitting problem is conceptually aligned with
closure, but the numerical literature does not give a controlled `O(0.1)`
mean fitting residual from ordinary statistically homogeneous structure.

### 1.4 Clarkson--Umeh--Maartens / Bonvin--Durrer / Fleury--Clarkson--Maartens

The second-order distance and source-averaging literature is the cleanest
answer to the "fitted-parameter bias" question.

- Bonvin--Clarkson--Durrer--Maartens--Umeh show that ensemble and directional
  averages do not commute at second order. At the CMB, `kappa_1^2` reaches
  about `0.6%`; some first-order squared lensing effects shift mean distances
  at about the percent level, while subdominant terms are much smaller
  (`~10^-6` or `~10^-5` in the estimates they give).
- Bonvin--Clarkson--Durrer--Maartens--Umeh also show that a `1%` expectation
  shift in distance to the CMB is already accounted for in standard CMB
  lensing analyses and does not explain the Hubble tension or a dark-energy
  magnitude.
- Fleury--Clarkson--Maartens derive the source-average appropriate for the
  Hubble diagram and compute the bias at second order. Their key result for
  Avenue C is direct: the fractional bias in usual distance indicators remains
  below `10^-3` over `0.05 < z < 10`; standard cosmological parameter biases
  are at most percent-level for `w_a` and sub-percent for other parameters,
  with optimal indicators reducing the bias further.

They also discuss a separate clumpiness problem: in a universe made of
opaque clumps, distance-redshift bias could be as large as `10%` at `z = 1`,
but it is dramatically reduced for transparent clumps. That is not a robust
closure prediction; it is a matter-discreteness / opacity / beam-physics
model.

Assessment for Avenue C. The actual source-averaged Hubble-diagram bias is
too small for the gate. Direct `w(z)` reconstructions can be badly biased at
high redshift because differentiation amplifies tiny distance biases, but
that is not an `O(0.1)` distance residual and not a stable dark-energy
magnitude mechanism.

### 1.5 Clarkson--Ellis--Faltenbacher--Maartens--Umeh--Uzan Narrow-Beam Warning

This paper is the main apparent loophole. Supernova beams are extremely
narrow and may not sample the fluid mean. The authors argue that standard
analyses can predict huge variance at tiny beam sizes, nonlinear corrections
may be nontrivial, and underdense regions may dim or brighten sources
depending on how local expansion is modeled.

Important magnitudes:

- The perturbative convergence estimate gives `sqrt(<kappa^2>) ~ 2e-2` on
  arcminute scales, and becomes unreliable for true SN beam scales.
- In one shell approximation, a SN on the far side of a `100 Mpc` void could
  be about `0.1 mag` brighter than without the void, but the paper states
  this is likely an overestimate and the sign is model-dependent.
- A modified Dyer--Roeder approximation can mimic dark-energy-like behavior
  more readily than standard DR, but the authors use this to show that the
  problem is under-modeled, not to claim a settled dark-energy replacement.

Assessment for Avenue C. This is not a decisive positive. It says there is an
open modeling problem for ultra-narrow beams. It does not provide a fixed,
covariant, no-amplifier closure map. The effect may be `O(0.1)` in special
approximations, but the sign and magnitude depend on beam physics and local
expansion modeling not supplied by Schur/F4.

## 2. Closure-Mapping Assessment

Let

```text
delta_LC(z) = Obs_lumpy(z) - Obs_FLRW(q_FLRW)(z)
```

for a chosen light-cone observable, such as flux, distance modulus,
luminosity distance, angular-diameter distance, redshift drift, or a fitted
parameter functional.

The Avenue-D target required five conditions.

| requirement | status | assessment |
|---|---|---|
| 1. `F_LC` covariant/gauge-invariant on the light-cone domain | **Pass as imported formalism** | GMNV/GLC and covariant source-averaging provide viable fixed light-cone averaging/fitting functionals. SBT does not need to invent this. |
| 2. `delta_LC` factors through F4/Schur `Xi_C` | **Fail/nonunique** | One can define `Xi_C` to include the missing light-cone observable family, but then factorization is tautological. A non-vacuous theorem would require: if two lumpy geometries have the same Schur/F4 closure residual, then they have the same `delta_LC`. This is false unless `Xi_C` carries the full beam/metric/source-selection data. |
| 3. Not a Green--Wald trace-free `t_ab` claim | **Pass** | This remains an observational quotient/fitting residual, not an effective stress-energy tensor. The applicability evasion from Avenue D is real. |
| 4. Sign and order from predeclared geometry/statistics, no `Omega_Lambda` normalizer | **Fail for `O(0.1)`** | Controlled predeclared perturbative/source-averaged estimates give small mean bias. Larger narrow-beam estimates are sign-ambiguous or depend on added beam/opacity/void-expansion modeling. |
| 5. Predict at least two non-SN consistency checks | **Fail as closure derivation** | Literature suggests possible checks: BAO/CMB vs SN distance comparison, CMB lensing accounting, source-size dependence, line-of-sight density splits, redshift drift. But no single closure map predicts their joint amplitude from `Xi_C`. |

Conclusion. Closure can honestly **audit** light-cone fitting residuals:

```text
native FLRW quotient misses a light-cone observable family
=> Schur/F4 residual diagnoses the missing family
=> F11/no-overread blocks interpreting one chart as objective DE
```

But the desired stronger statement fails:

```text
Xi_C nonzero  ==>  delta_LC has dark-energy-sized magnitude.
```

There is no such theorem in the literature, and the robust numbers point the
other way.

## 3. Honest Magnitude Estimate

For ordinary statistically homogeneous structure with transparent matter and
standard perturbative/light-cone treatment:

```text
mean distance/Hubble-diagram bias:      |delta D|/D ~ 10^-5--10^-3
parameter bias in standard fits:        sub-percent to percent-level
irreducible scatter/lensing variance:   up to ~10% in some regimes
CMB distance expectation/lensing scale: ~1%, already modeled
```

For narrow-beam or opacity/discreteness models:

```text
possible local/special effects:         ~0.1 mag in some toy approximations
robust sign:                            not fixed
robust closure derivation:              absent
non-SN consistency map:                 absent
```

Therefore the honest no-tuning estimate for a closure-structured mean
light-cone fitting residual is

```text
|delta_LC| = O(10^-3) robustly, maybe percent-level in parameter propagation,
not O(0.1).
```

The only ways to reach `O(0.1)` are:

1. import a large clock/lapse/void-volume model, which LT2 already classified
   as timescape-class and non-SBT-selected;
2. use giant/special void or LTB-style light-cone reconstruction, which is
   model fitting and observationally constrained;
3. rely on unresolved ultra-narrow-beam matter-discreteness physics, whose
   sign and magnitude are not fixed by closure.

None is a closure derivation.

### Pre-Mortem: How This Negative Could Be Wrong

This memo would be overturned by a theorem and calculation satisfying all of
the following:

1. a fixed, covariant `F_LC` on lumpy light-cone observables;
2. a non-tautological Schur/F4 factorization theorem for `delta_LC`;
3. a predeclared matter/beam/source-selection model giving a mean
   `|delta D|/D = O(0.1)`;
4. stable sign through the SN redshift range without fitting `Omega_Lambda`;
5. at least two non-SN predictions with matching amplitude, such as BAO/SN
   distance-ratio split plus CMB acoustic/lensing consistency, or line-of-sight
   density split plus source-size dependence.

No cited source currently supplies this package.

## 4. Decision

Do **not** proceed to a full Avenue-C dark-energy derivation build. The
applicability evasion remains mathematically clean, but the magnitude does not
survive the direct light-cone/fitting literature check.

Banked outcome:

```text
Outcome C/B:
  C: closure gives a useful quotient/audit language for fitting residuals;
  B: robust mean residuals are too small to derive dark energy.
```

Empirical implication. A density-split or line-of-sight environment test may
still be valuable as a systematics/closure-audit test, but it should not be
pre-registered as a dark-energy magnitude derivation. If the fitting residual
is `O(small)`, Avenue B would mainly re-detect nonlinear light-cone
systematics rather than reopen outcome A.

## References

- Ellis, G. F. R. and Stoeger, W., "The fitting problem in cosmology",
  Class. Quantum Grav. 4 (1987) 1697.
- Gasperini, M., Marozzi, G., Nugier, F., Veneziano, G.,
  "Light-cone averaging in cosmology: formalism and applications",
  arXiv:1104.1167.
- Ben-Dayan, I., Gasperini, M., Marozzi, G., Nugier, F., Veneziano, G.,
  "Backreaction on the luminosity-redshift relation from gauge invariant
  light-cone averaging", arXiv:1202.1247.
- Ben-Dayan, I., Gasperini, M., Marozzi, G., Nugier, F., Veneziano, G.,
  "Do stochastic inhomogeneities affect dark-energy precision measurements?",
  arXiv:1207.1286.
- Ben-Dayan, I., Gasperini, M., Marozzi, G., Nugier, F., Veneziano, G.,
  "Average and dispersion of the luminosity-redshift relation in the
  concordance model", arXiv:1302.0740.
- Rasanen, S., "Light propagation in statistically homogeneous and isotropic
  dust universes", arXiv:0812.2872.
- Rasanen, S., "Light propagation in statistically homogeneous and isotropic
  universes with general matter content", arXiv:0912.3370.
- Kolb, E. W. and Lamb, C. R., "Light-cone observations and cosmological
  models: implications for inhomogeneous models mimicking dark energy",
  arXiv:0911.3852.
- Brouzakis, N., Tetradis, N., Tzavara, E., "Light Propagation and
  Large-Scale Inhomogeneities", arXiv:astro-ph/0703586.
- Flanagan, E. E., Kumar, N., Wasserman, I., Vanderveld, R. A.,
  "Luminosity distance in Swiss cheese cosmology with randomized voids. II",
  arXiv:1109.1873.
- Marra, V. and Notari, A., "Observational constraints on inhomogeneous
  cosmological models without dark energy", arXiv:1102.1015.
- Clarkson, C., Ellis, G. F. R., Faltenbacher, A., Maartens, R., Umeh, O.,
  Uzan, J.-P., "(Mis-)Interpreting supernovae observations in a lumpy
  universe", arXiv:1109.2484.
- Bonvin, C., Clarkson, C., Durrer, R., Maartens, R., Umeh, O.,
  "Cosmological ensemble and directional averages of observables",
  arXiv:1504.01676.
- Bonvin, C., Clarkson, C., Durrer, R., Maartens, R., Umeh, O.,
  "Do we care about the distance to the CMB?", arXiv:1503.07831.
- Fleury, P., Clarkson, C., Maartens, R.,
  "How does the cosmic large-scale structure bias the Hubble diagram?",
  arXiv:1612.03726.
