# Criticality F4 Memo: Singular-Limit/Critical Reading and the Dark-Energy Magnitude

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

- `results/DARK_ENERGY_AS_CLOSURE_RESULT_2026-06-02.md`.
- `math/DERIVATION_TOPOLOGICAL_F4_2026-06-02.md`.
- `math/DERIVATION_AVENUE_D_2026-06-02.md`.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex`,
  especially F4, F36, and F44.

## 0. Verdict

**NO.** The criticality / singular-limit reading of the cosmological F4
obstruction does not presently deliver the dark-energy magnitude, the onset,
or a fixed `w(z)` shape from F4 structure alone.

The best criticality-shaped translation is:

```text
control parameter:
  late-time structure/void/nonlinearity variable, e.g. f_v(a), sigma(R,a),
  or a Schur/F4 residual amplitude;

order parameter:
  closure readout failure, e.g. ||Xi_C||, compatible-non-global fraction,
  or a light-cone fitting residual;

susceptibility:
  chi_F4 = response of the closure readout to a small bare audit forcing.
```

This is a coherent way to ask the question, but the decisive facts are
negative:

1. The late-time structure/void transition is not presently a demonstrated
   critical point of the F4 closure system. It is a broad, model- and
   threshold-dependent nonlinear crossover unless extra timescape/backreaction
   physics is supplied.
2. No divergent `chi_F4`, no diverging correlation length, and no universal
   critical exponents are derived for the closure variables.
3. No self-organized-criticality attractor or F4-fixed critical coupling is
   proved. Tuning the system to `z_crit ~ 0.7`, `f_v ~ 0.59`, or any chosen
   critical surface is R14/fine-tuning.
4. Even genuine criticality would usually fix scaling form and exponents, not
   the absolute energy-density normalization `rho_Lambda ~ Omega_Lambda
   rho_crit`. The amplitude/stiffness/scale remains a physics input.

Outcome by component:

| target | delivered by F4-criticality? | reason |
|---|---:|---|
| `Omega_Lambda ~ 0.68` magnitude | **No** | No F4-fixed amplitude or energy scale. |
| onset `z_onset ~ 0.7` | **No** | Structure formation supplies broad coincidence, not a predicted critical redshift. |
| fixed `w(z)` shape | **No** | Requires universality class and map from order parameter to pressure/density; F4 does not supply them. |

The catalog's two O(1)-by-structure engines have now both failed as
dark-energy magnitude derivations under the no-normalizer rule: topology
failed on invariant/scale; criticality fails on actual criticality, tuning,
and scale. The banked C/B result stands.

## 1. Susceptibility: Is the F4 Obstruction Actually Critical?

### 1.1 Minimal Criticality Data

To make the critical reading non-vacuous, the cosmological F4 system would
need the following declared data.

```text
Control space C:
  cosmological closure states over time or scale.

Control parameter c:
  a fixed scalar or finite vector such as:
    c_1 = f_v(a)       void/volume fraction,
    c_2 = sigma(R,a)   nonlinear amplitude at a predeclared scale R,
    c_3 = p_perc(a)    percolation/connectivity statistic,
    c_4 = ||Xi_C(a)||  Schur/F4 closure residual.

Order parameter m:
  the closure readout that changes phase:
    m = inferred acceleration residual,
    m = light-cone fitting bias,
    m = failure of FLRW globalization,
    m = normalized closure shadow price.

Susceptibility chi_F4:
  derivative or amplification factor
    chi_F4(c) = d m / d epsilon_bare
  or
    chi_F4(c) = d m / d c
  in a controlled limit.
```

A genuine criticality claim needs more than a rapid change. It needs a
limit in which

```text
chi_F4 -> infinity
or
xi_corr -> infinity
or
response is non-uniform with a universal finite-size scaling law.
```

The anti-vacuity gate is:

```text
same declared F4 closure system + same predeclared control parameter
=> demonstrable divergence or universal scaling in the closure readout.
```

No current Six Birds artifact proves this. F44 supplies the correct structural
shape:

```text
critical = phase boundary + (margin vanishes or response is non-uniform)
           + residuals are still statused.
```

But F44 is a descent/status theorem. It does not assert a physical
susceptibility, an exponent, a thermodynamic limit, or a cosmological scale.
F36 likewise says when a singular-limit readout completes through a quotient
or requires path memory. It does not declare which cosmological limit is
singular or what its renormalized amplitude is.

### 1.2 Backreaction and Void-Domination Precedents

Rasanen's backreaction work is the closest favorable precedent. In exact
Buchert-type averaging, large-scale smoothness does not by itself imply small
backreaction, and toy models can connect gravitational collapse with
acceleration. This establishes a possible mechanism class: nonlinear
structure can matter in averaged variables.

The magnitude-sensitive paper cuts the other way. In the peak-model treatment
of a realistic evolving ensemble of nonlinear structures, the average
expansion rate increases relative to FRW as fast-expanding voids dominate, on
a `10--100` Gyr timescale, but not rapidly enough to correspond to
acceleration. This is not a divergence of a susceptibility. It is a finite
crossover in a model of evolving structures.

Timescape is the favorable O(1) clock/crossover precedent. It ties apparent
acceleration to wall/void clock calibration and to a void-fraction threshold:
apparent acceleration is said to register when the void fraction reaches
about `59%`, typically near `z ~ 0.9`; later timescape summaries quote
present void fractions around `0.7` and apparent-acceleration onset near
`z_acc ~ 0.46` with large uncertainty. That is a concrete clock model, not an
F4-only critical theorem. LT2 already found that F4/F18 does not select the
timescape lapse, void fraction law, or clock bridge without importing
timescape physics.

Conclusion. Rasanen and Wiltshire supply reasons to audit the coincidence
between structure formation and apparent acceleration. They do not supply a
closure susceptibility `chi_F4 -> infinity`, nor an F4-derived critical
surface.

### 1.3 Choptuik Critical Collapse

Choptuik's scalar-field collapse is genuine GR criticality. Families of
initial data have a codimension-one threshold `p = p_*` separating dispersal
from black-hole formation; near the threshold black-hole mass scales as

```text
M_BH proportional to |p - p_*|^gamma,  gamma approximately 0.37,
```

with universality and echoing. Reviews describe the critical solution as an
attractor only within the black-hole threshold, i.e. a codimension-one
surface in phase space.

This is useful as a warning. GR can have true critical phenomena, but the
known example requires tuning to a threshold. It is local strong-field
collapse, not generic late-time weak-field structure formation, and it does
not create a cosmological energy density or a smooth acceleration readout.
Without an SOC mechanism, importing "GR criticality" simply relocates
fine-tuning to `p = p_*`.

### 1.4 Critical / Phase-Transition Dark-Energy Models

Critically emergent dark energy (CEDE) models explicitly use critical
phenomena language: the dark-energy density behaves like an Ising
magnetization and emerges at a transition redshift `z_c`. This demonstrates
that phase-transition DE is a legitimate phenomenological model class.

It does not solve the closure problem. The order parameter, transition
redshift, and density normalization belong to an added dark-energy model and
are constrained by cosmological data. The model is not derived from F4. It is
the kind of physics bridge Claim P would have to supply, not evidence that
F4 supplies it.

### 1.5 Cosmic-Web Percolation and SOC

The cosmic web has threshold/percolation descriptions: voids, filaments,
walls, and clusters can be classified by density or tidal/velocity-shear
thresholds, and percolation functions can show transitions as a threshold is
varied. Persistent-homology studies similarly track topology across redshift
and scale.

These are not automatically thermodynamic critical points:

- the threshold is often an analysis parameter, not a dynamical control
  variable fixed by F4;
- the percolation redshift or threshold depends on smoothing, tracer,
  classifier, and survey selection;
- no universal exponents or diverging closure susceptibility are established;
- percolation of a cosmic-web classifier is not an energy-density source.

Self-organized criticality would be the principled escape from tuning. The
Bak--Tang--Wiesenfeld sandpile has the required ingredients: slow drive,
threshold dynamics, avalanches, and dissipation at boundaries; in that class
the critical state is an attractor of the dynamics.

For F4 cosmology, no analogous closure dynamics has been supplied:

```text
no declared toppling/avalanche variable;
no conserved transported quantity;
no slow-drive plus boundary-dissipation law;
no proof that the invariant measure concentrates on a critical surface;
no derivation that the attractor redshift is z ~ 0.7.
```

Therefore SOC is not available as an argument. It would have to be a new
theorem, not an analogy.

## 2. Fine-Tuning Crux

Critical amplification has a standard form:

```text
delta_readout(c) = A * epsilon_bare * |c - c_*|^{-gamma}
```

or a finite-size version cut off by system size, smoothing, or nonlinear
saturation. If the bare closure price is perturbative,
`epsilon_bare ~ 10^-5`, then an O(1) response requires approximately

```text
|c - c_*|^gamma ~ 10^-5
```

unless the dynamics self-organizes to `c_*`. That is the fine-tuning trap.
Choosing the present epoch to sit near `c_*` is not an explanation; it is the
cosmological-constant problem rewritten as a critical-surface problem.

The only two principled escapes named in the packet fail at present.

### 2.1 SOC Attractor

Required theorem:

```text
For generic initial closure states, the F4 closure dynamics evolves toward a
critical invariant set C_* with no tuned parameter, and the induced readout
has chi_F4 -> infinity or universal finite-size scaling.
```

Current status: not proved, not specified.

F4 has local families, compatibility, and globalizability. F44 has a formal
phase-boundary/status criterion. Neither provides a dynamical update rule,
drive/dissipation balance, avalanche law, or invariant measure. Gravity plus
cosmic expansion may generate hierarchical structure, but that is not the
same as a proven SOC attractor of the closure residual.

### 2.2 F4-Fixed Critical Coupling

Required theorem:

```text
c_* = c_F4
```

where `c_F4` is a structural constant of the closure apparatus, not fitted
from SN distances, `Omega_Lambda`, local `H_0`, or the observed acceleration
onset.

Current status: not available.

F4's primitives are sets, local-family data, a compatibility predicate, and a
restriction map. They define status, not a numeric critical coupling. Adding
`c_* = 0.59`, `z_* = 0.7`, or a threshold chosen to align with observed
acceleration is a normalizer. It fails the same anti-tautology rule as
topological F4.

### 2.3 Singular-Limit Completion

F36 permits a legitimate singular-limit story:

```text
raw readout fails to descend through a limit quotient;
path-memory or renormalized readout completes it.
```

But this is still formal. To make it a dark-energy engine, one must identify
the limiting process `P`, quotient `ell`, raw readout `u`, renormalized
readout `u^ren`, and show that the completion changes the cosmological
readout by O(1) without an inserted normalization.

Shell crossing and caustics in cold dust are real singularities of idealized
structure formation. However, cosmological observables are coarse-grained by
finite velocity dispersion, virialization, baryonic physics, beam averaging,
and survey selection. Existing light-cone and backreaction estimates do not
show a universal singular completion that converts a `10^-5` closure price
into `Omega_Lambda`. F36 therefore supplies a useful audit template, not a
magnitude theorem.

Fine-tuning verdict:

```text
No SOC attractor.
No F4-fixed critical coupling.
No completed singular-limit map with O(1) amplitude.
=> criticality route fails the no-tuning gate.
```

## 3. Magnitude Versus Shape

Even if a genuine critical point were found, the usual outputs of critical
phenomena are:

- exponents;
- scaling functions;
- universality classes;
- divergent or finite-size-scaled susceptibility;
- onset/threshold behavior if the control trajectory is known.

They do not by themselves fix the absolute energy-density normalization.
Landau/Ising-type descriptions require coefficients in a free energy.
Phase-transition dark-energy models require a potential, latent heat, vacuum
energy difference, or emergent-density amplitude. SOC models require drive,
dissipation, conservation rules, and a mapping from avalanche statistics to
the readout. These are physics inputs, not consequences of F4.

### 3.1 Magnitude

To derive the magnitude one would need

```text
rho_eff(a) = rho_scale * Phi_crit(c(a), exponents, ...)
```

with `rho_scale` fixed by F4. No such `rho_scale` exists in F4/F36/F44.
Using `rho_crit` or `M_Pl^2 H_0^2` as the scale is circular unless F4 first
predicts `H_0`, the onset, and the coefficient. Using a structure-formation
energy scale imports growth/clock/backreaction physics that LT2 and Avenue C
already found non-SBT-selected.

### 3.2 Onset

In flat `Lambda`CDM, acceleration begins when

```text
Omega_m (1 + z)^3 = 2 Omega_Lambda,
```

which gives `z_acc` of order `0.6--0.7` for the usual Planck-like parameter
values. This is a useful benchmark, but it is not a prediction of F4.

Structure formation gives a broad family of possible "now" markers:

- nonlinear scale crossing `sigma(R,z) = 1`, depending on chosen `R`;
- void volume fraction crossing a threshold, depending on void definition and
  model;
- cosmic-web percolation threshold, depending on classifier and smoothing;
- timescape apparent-acceleration threshold, depending on the timescape clock
  bridge.

F4 does not select one. Therefore it does not predict `z_onset ~ 0.7`.

### 3.3 Shape and `w(z)`

A critical model could in principle predict a running equation of state:

```text
w(z) = w_crit(z; exponents, c_*, trajectory, amplitude).
```

But F4 supplies none of the required ingredients: universality class,
trajectory through control space, pressure/density map, amplitude, or
conservation law. The P4 stable-readout work can certify a finite
phenomenological witness, but it is not a derivation of a critical
universality class.

Shape verdict:

```text
F4-criticality currently predicts no fixed w(z).
At most it motivates a future finite-crossover audit of residuals around
late-time structure formation.
```

## 4. Decision

No fixed prediction follows. The criticality/singular-limit reading does not
produce:

- a declared divergent `chi_F4`;
- a demonstrated SOC attractor;
- an F4-fixed critical coupling;
- an F4-fixed energy scale;
- a computed `Omega_Lambda`;
- a predicted onset redshift;
- a fixed `w(z)`.

The precise failures are:

1. **Finite-crossover failure.** The actual late-time structure/void/cosmic-web
   transition is presently a smooth, threshold-dependent crossover in the
   closure variables, not a proved critical point with divergent
   susceptibility.
2. **Tuning failure.** Known true GR criticality, such as Choptuik collapse,
   sits on a codimension-one threshold. No F4/SOC mechanism puts the universe
   on the needed critical surface without tuning.
3. **Scale failure.** Criticality can amplify and shape responses, but the
   absolute `rho_Lambda` normalization requires a scale or free-energy
   coefficient not supplied by F4.
4. **Onset failure.** `z ~ 0.7` is not derived. It can be read from
   observational cosmological parameters or from fitted/extra-physics
   structure models, but not from F4 alone.

Banking statement:

```text
Critical F4 is a useful audit hypothesis for late-time residual morphology.
It is not a no-amplifier dark-energy magnitude derivation.
Outcome C/B remains banked; the catalog O(1) engines screened here are
exhausted under the present construction.
```

Reopen condition. This route reopens only if a future theorem supplies all of:

1. a covariant F4 closure control space and order parameter;
2. a susceptibility with a proven divergence or universal finite-size scaling;
3. an SOC attractor or F4-fixed critical coupling;
4. a non-circular scale and amplitude;
5. a no-fit prediction of onset and at least one non-SN observable shape
   check.

## References

- Six Birds Foundations IV catalog: F4 Local--Global Obstruction Normal Form;
  F36 Singular Limit Completion; F44 Criticality / Phase Boundary.
- S. Rasanen, "Cosmological acceleration from structure formation",
  arXiv:astro-ph/0605632.
- S. Rasanen, "Accelerated expansion from structure formation",
  arXiv:astro-ph/0607626.
- S. Rasanen, "Evaluating backreaction with the peak model of structure
  formation", arXiv:0801.2692.
- D. L. Wiltshire, "Cosmic clocks, cosmic variance and cosmic averages",
  arXiv:0712.3984; "Average observational quantities in the timescape
  cosmology", arXiv:0909.0749.
- P. R. Smale and D. L. Wiltshire, "Supernova tests of the timescape
  cosmology", Mon. Not. Roy. Astron. Soc. 413 (2011) 367.
- C. Gundlach, "Critical phenomena in gravitational collapse",
  arXiv:gr-qc/9712084.
- M. W. Choptuik, "Universality and scaling in gravitational collapse of a
  massless scalar field", Phys. Rev. Lett. 70 (1993) 9.
- P. Bak, C. Tang, and K. Wiesenfeld, "Self-organized criticality: an
  explanation of 1/f noise", Phys. Rev. Lett. 59 (1987) 381.
- M. Aschwanden et al., "25 Years of Self-Organized Criticality: Concepts and
  Controversies", Space Sci. Rev. 198 (2016) 47.
- A. Banihashemi, N. Khosravi, and A. Shafieloo, "Dark Energy as a Critical
  Phenomenon: a Resolution for Hubble Tension", arXiv:2012.01407.
- E. Chingangbam, C. Park, K. P. Yogendran, and R. van de Weygaert,
  "The clustering of critical points in the evolving cosmic web",
  arXiv:2011.04321.
- E. van de Weygaert et al., "Persistent homology of the cosmic web. I:
  Hierarchical topology in LambdaCDM cosmologies", Mon. Not. Roy. Astron.
  Soc. 507 (2021) 2968.
