# Avenue D Memo: Magnitude-Wall Loophole Analysis

> **Mathematical review correction (2026-10-01):** the argument below is
> conditional on its declared interface, physics, and approximation assumptions.
> Its limits are neither a universal impossibility result nor a proof that a
> run supplies the missing magnitude. Emergence alone does not forbid proof:
> finite deterministic runs can be formalized. A no-shortcut result requires
> an explicit resource model; a no-descent result requires a fixed access quotient.
> An unspecified coefficient remains unspecified until a lawful construction
> or supplied selection fixes it.

Status: theory assessment memo. No Lean, data, plan, or results changes.

Governing inputs:

- `plan/SIXBIRDS_DE_AVENUES_MAP_2026-06-02.md`, Avenue D.
- `math/DERIVATION_LT2_2026-06-02.md`, especially sections 6 and 7.
- `plan/EXTERNAL_RULING_DERIVATION_LT1_2026-06-02.md`.

## 0. Verdict

There is one principled *applicability* evasion of the standard
backreaction wall:

```text
evasion (ii): observational / fitting / light-cone effect.
```

This evades Green--Wald-style stress-energy no-go theorems because it does
not claim that small-scale inhomogeneities produce a cosmological-constant-like
effective stress-energy tensor. It claims instead that the smooth FLRW
readout is a fitted quotient of lumpy light-cone observables. That points to
**Avenue C**, not Avenue A.

This is not yet a magnitude evasion. It opens a precise next theorem target,
but it does not show `Omega_eff = O(0.1--1)`.

The other two proposed evasions are not currently principled SBT evasions:

- **(i) global F4 obstruction** is a formal scope objection to local/weak-limit
  averaging, but SBT has no dimensioned global obstruction functional mapping
  F4 to a lapse, curvature, or distance scale. This does not currently open
  Avenue A.
- **(iii) non-perturbative effect** is only a possibility unless a specific
  non-weak-limit GR/light-cone construction is supplied. Nonlinear structure
  alone is not enough; weak-field/Newtonian nonlinear structure is precisely
  where many small-backreaction arguments are strongest.

Banking statement. Six Birds still does not derive the observed dark-energy
magnitude through any established bridge. The only live deep derivation route
after Avenue D is a scoped Avenue C theorem about closure as a light-cone /
fitting residual. Stress-energy and direct Buchert routes remain C/B.

## 1. Literature Claims and Load-Bearing Assumptions

### 1.1 Ishibashi--Wald / Green--Wald

Ishibashi and Wald argue that acceleration from inhomogeneity backreaction is
not plausible in GR without a cosmological constant or dark energy if the
universe is accurately described by a Newtonianly perturbed FLRW metric. They
also stress that an accelerating spatially averaged scale factor is not enough
to show an observable acceleration, and that a large second-order
stress-energy tensor would be gauge-dependent and outside a controlled
perturbative expansion. [IW06]

Green and Wald introduce a weak-limit framework for one-parameter families of
metrics close to a smooth background. The metric perturbation is uniformly
small, derivatives may be large, matter obeys the weak energy condition, and
the leading small-scale contribution is represented by an effective
stress-energy tensor `t_ab`. In that framework `t_ab` is traceless and obeys
the weak energy condition, like gravitational radiation; it cannot mimic a
cosmological constant. [GW11, GW13, GW14]

Load-bearing assumptions:

- the relevant backreaction is representable as a weak-limit effective
  stress-energy tensor on a background metric;
- the metric is uniformly close to the background, even if derivatives are not;
- matter satisfies the weak energy condition;
- the theorem targets large-scale dynamics through `t_ab`, not the full
  observational fitting problem;
- in the Ishibashi--Wald critique, observable acceleration must be shown by
  observables, not by a chosen averaged scale factor.

### 1.2 Rasanen / perturbative and weak-field backreaction

Perturbative backreaction calculations in Newtonian gauge find an effective
energy density of order `10^-5` of the matter density, with quasilinear
extensions still of that order. [BBR08] Rasanen's peak-model treatment gives
an average expansion rate that increases relative to FRW as voids dominate,
but not rapidly enough to be acceleration in that model. [Ras08]

Rasanen also argues against overusing linearly perturbed FLRW reasoning in the
nonlinear-density regime, emphasizing the distinction between Newtonian
gravity and the weak-field, small-velocity limit of GR in cosmology. [Ras10]
His light-propagation work shows that redshift and angular-diameter distance
in statistically homogeneous and isotropic universes are tied to average
expansion, density, and null-geodesic shear, not to a naive clumping
prescription. [Ras09a, Ras09b]

Load-bearing assumptions of the `10^-5` wall:

- perturbative or weak-field expansion around a Robertson--Walker background;
- small metric potentials, even if density contrasts become nonlinear;
- spatial averaging or Newtonian-gauge perturbative backreaction variables;
- no large lapse/clock recalibration or nonlocal light-cone fitting map;
- domains where Newtonian/weak-field structure formation is the right
  approximation.

### 1.3 Buchert vs Green--Wald

Buchert's scalar averaging formalism describes an inhomogeneous universe by
spatially averaged scalar variables and effective Friedmann equations with
matter and backreaction source terms; the latter can be represented as a
minimally coupled "morphon" field. [Buchert06]

Buchert-side critiques of Green--Wald argue that the trace-free theorem is not
a general proof about cosmological backreaction: the scheme does not perform
the relevant nonlocal averaging, the trace-free result is claimed to be too
narrow or unphysical as a general statement, and some arguments are
coordinate-dependent or miss published backreaction definitions. [Buchert15]

Load-bearing point. This dispute is about *scope*. It says Green--Wald has
not ruled out all averaging/backreaction frameworks. It does not by itself
provide an `O(1)` magnitude.

### 1.4 Wiltshire / timescape

Timescape relaxes the assumption that a single global FLRW clock and scale
factor are the correct operational variables for wall observers and void
regions. Apparent acceleration arises from calibrating average cosmological
parameters in the presence of spatial-curvature and gravitational-energy
gradients that grow with late-time inhomogeneity. [Wiltshire11, SW11]

The key relaxed assumption is not "small local stress-energy becomes a
cosmological constant." It is that wall observers use clocks/rulers that are
not the same as the volume-average clocks/rulers once voids dominate. The
effect is observational/calibrational and quasilocal-clock based.

Load-bearing point. Timescape is a concrete way to get an apparent `O(1)`
effect, but its scale comes from added wall/void/lapse physics. LT2 found no
SBT-only F4/F18 rule that selects those variables or their magnitude.

## 2. Wall Argument by Candidate Evasion

| wall argument | key assumptions | (i) global F4 obstruction | (ii) observational / fitting | (iii) non-perturbative |
|---|---|---|---|---|
| Ishibashi--Wald / Green--Wald stress-energy no-go | Weak-limit small-scale inhomogeneity framework; uniformly small metric perturbation; WEC matter; effective `t_ab` is the object; `t_ab` traceless and WEC, not Lambda-like. | **No current principled magnitude evasion.** A genuinely global F4 obstruction may be outside a local weak-limit `t_ab`, but SBT has not supplied a dimensioned global obstruction functional or a map to geometry. Scope evasion only. | **Yes, principled applicability evasion.** A fitted light-cone/distance residual is not an effective stress-energy tensor, so the trace-free `t_ab` theorem does not apply. This is Avenue C. It still needs a fixed light-cone theorem and magnitude calculation. | **No current SBT reason.** If the metric is not uniformly close or the weak-limit hypotheses fail, Green--Wald may not apply; but closure has not shown that cosmological F4 residuals force such a regime. |
| Perturbative / weak-field `10^-5` backreaction | Newtonian-gauge or weak-field expansion; small potentials; spatial/perturbative backreaction variables; no clock/light-cone bridge. | **No current principled magnitude evasion.** F4 may be nonlocal, but unless it changes the observable or physical averaging map, it remains an audit classification with no scale. | **Yes, principled applicability evasion.** A light-cone/fitting effect targets `D_L(z)`, redshift, and inferred smooth parameters, not the perturbative energy density. Rasanen light-propagation results make this a real formal direction. Magnitude remains unproved. | **Conceded unless specified.** Nonlinear density alone is not enough; weak-field nonlinear structure is exactly where the wall is argued. Need a specified relativistic/non-weak-field construction. |
| Buchert vs Green--Wald scope dispute | Green--Wald uses weak-limit effective stress-energy, not Buchert's nonlocal scalar averaging; Buchert uses averaged scalar variables and `Q_D`, averaged curvature. | **Partly principled as a scope critique, not as magnitude.** F4 resembles a local-global/nonlocal objection, but without an `O_F4` with units it does not improve on Buchert's general scope critique. | **Yes as a different problem.** The fitting problem and light-cone averaging are observational, not merely spatial `Q_D`. This points to Avenue C rather than a direct Buchert morphon derivation. | **Not enough.** Buchert variables are nonperturbative scalars in principle, but no SBT argument makes them large; ordinary `Q_D` remains the conditional B route. |
| Wiltshire / timescape | Relaxes single global FLRW clock/ruler calibration; uses wall/void lapse, quasilocal gravitational energy, void domination; apparent acceleration for wall observers. | **No current SBT distinction.** F4 can audit wall/void chart objectivity, but LT2 found no fixed F4 rule selecting `gamma(t)` or `f_v(t)`. Without that, this is timescape with SBT vocabulary. | **Yes in kind, but not SBT-derived.** Timescape is an observational/calibration evasion of stress-energy no-go. It supports the plausibility of Avenue C-style fitting, but the magnitude comes from timescape physics. | **Yes for timescape, not for closure alone.** Timescape is the concrete O(1) non-perturbative/clock route. SBT currently contributes no independent selector or scale. |

## 3. Candidate Evasion Assessment

### 3.1 Evasion (i): Global F4 obstruction

Verdict: **not presently principled as a magnitude-wall evasion.**

Reason. A global local--global obstruction is outside the literal target of
Green--Wald's local weak-limit effective stress-energy theorem. That is a
valid scope observation. But Avenue D asks for a principled reason to reach
`O(1)`, not merely a reason a theorem does not apply. F4 currently provides a
classification of gluing failure. It does not provide:

- a dimensioned obstruction functional `O_F4`;
- a map from `O_F4` to curvature, lapse, or distance;
- conservation/Bianchi consistency;
- a scale in units of `rho_crit`;
- a no-free-parameter prediction of onset or chart behavior.

Therefore global F4 does not currently open Avenue A. It would open Avenue A
only if the next theorem constructed a dimensioned global obstruction
functional whose extremal/evolution equations produce a physical clock,
curvature, or light-cone effect without fitting `Omega_Lambda`.

### 3.2 Evasion (ii): Observational / fitting / light-cone

Verdict: **principled applicability evasion; the only live route.**

Reason. Green--Wald constrains an effective stress-energy tensor `t_ab`.
Perturbative `10^-5` estimates constrain spatial/metric backreaction
variables. They do not rule out the possibility that fitting a smooth FLRW
model to lumpy light-cone observations induces a large inferred distance or
parameter bias. Ishibashi--Wald themselves emphasize that an averaged scale
factor is not enough; observable consequences must be computed. Green--Wald
2014 also distinguishes large-scale dynamics from potentially significant
differences in observables such as geodesics.

This is a principled evasion because it changes the mathematical object:

```text
not:  Xi_C or lambda -> t_ab ~ Lambda
but:  lumpy light cone -> best smooth quotient -> observable residual.
```

It points to **Avenue C**: light-cone averaging / fitting formalism.

Limitation. This is not yet a magnitude result. The next theorem must compute
the sign and order of the induced `D_L(z)` or parameter residual from fixed,
predeclared data of the lumpy spacetime and closure quotient.

### 3.3 Evasion (iii): Non-perturbative

Verdict: **not presently principled for SBT.**

Reason. Perturbative or weak-field results do not cover every possible
non-perturbative GR construction. But nonlinear density contrast is not by
itself enough: Green--Wald allows large stress-energy fluctuations under a
small metric perturbation; Newtonian/weak-field analyses argue nonlinear
structure can still leave the background expansion essentially unchanged.

Timescape is a concrete nonperturbative/clock-class evasion, but LT2 found
that SBT does not presently derive the timescape lapse or void-fraction law.
Thus evasion (iii) is a possible physics avenue only after adding a specific
non-perturbative averaging/light-cone/clock model. It is not supplied by the
closure formalism alone.

## 4. Decision for Deep Avenues

### Avenue A: global-obstruction theorem

Not opened by Avenue D. The global F4 loophole is only a scope gap unless SBT
first constructs:

```text
O_F4 with units + evolution/extremality + map to geometry/light-cone variables.
```

This is exactly the missing LT2 section 7 machinery. Without it, Avenue A is
likely to reproduce outcome C or B.

### Avenue C: light-cone / fitting formalism

Opened as the only principled loophole.

Precise next theorem target:

```text
Light-cone closure quotient theorem.
```

Data:

- a lumpy spacetime or statistically homogeneous/isotropic model with a past
  light-cone observable algebra;
- a native smooth FLRW quotient `q_FLRW`;
- a fixed fitting functional `F_LC` from light-cone observables to smooth
  parameters/readouts;
- the Schur/F4 residual `Xi_C` measuring failure of the native smooth quotient.

Theorem target:

1. `F_LC` is covariant or gauge-invariant on the chosen light-cone domain.
2. The induced residual

   ```text
   delta_LC(z) = Obs_lumpy(z) - Obs_FLRW(q_FLRW)(z)
   ```

   factors through the F4/Schur closure obstruction, not through an arbitrary
   chart fit.
3. `delta_LC` is not representable as a Green--Wald trace-free `t_ab` claim;
   it is an observable/fitting residual.
4. The sign and scale of `delta D_L(z)` are estimated from predeclared
   geometry/statistics, with no `Omega_Lambda` normalizer.
5. The same map predicts at least two non-SN consistency checks, such as BAO
   distance ratios, CMB acoustic angle reinterpretation, local clock/Hubble
   quotient behavior, ISW/void observables, or age/lapse constraints.

If this theorem cannot produce `O(0.1)` distance-scale effects without
post-hoc normalization, Avenue C also banks at C/B.

## 5. Final Answer to Avenue D

There is **no principled closure evasion of the magnitude wall as a
stress-energy/backreaction derivation**. Direct `Q_D`, perturbative
backreaction, and generic non-perturbative claims remain blocked or
underdefined.

There is a **principled evasion of the Green--Wald/Ishibashi--Wald
stress-energy no-go as a theorem of applicability**: make the closure price an
observational/light-cone/fitting residual rather than an effective
stress-energy tensor. This points to **Avenue C** and to the light-cone
closure quotient theorem above.

That loophole is narrow. It does not yet reach `Omega_eff=O(0.1--1)`. It only
justifies doing Avenue C if the owner wants one deep theory attempt. Avenue A
should not proceed until a dimensioned global F4 obstruction functional is
specified.

## 6. Sources Checked

- Akihiro Ishibashi and Robert M. Wald, "Can the Acceleration of Our Universe
  Be Explained by the Effects of Inhomogeneities?", CQG 23 (2006),
  arXiv:gr-qc/0509108.
- Stephen R. Green and Robert M. Wald, "A new framework for analyzing the
  effects of small scale inhomogeneities in cosmology", PRD 83 (2011),
  arXiv:1011.4920.
- Stephen R. Green and Robert M. Wald, "Examples of backreaction of small
  scale inhomogeneities in cosmology", PRD 87 (2013), arXiv:1304.2318.
- Stephen R. Green and Robert M. Wald, "How well is our universe described by
  an FLRW model?", CQG 31 (2014), arXiv:1407.8084.
- Juliane Behrend, Iain A. Brown, and Georg Robbers, "Cosmological
  Backreaction from Perturbations", JCAP (2008), arXiv:0710.4964.
- Syksy Rasanen, "Evaluating backreaction with the peak model of structure
  formation", JCAP (2008), arXiv:0801.2692.
- Syksy Rasanen, "Light propagation in statistically homogeneous and isotropic
  dust universes", JCAP (2009), arXiv:0812.2872.
- Syksy Rasanen, "Light propagation in statistically homogeneous and isotropic
  universes with general matter content", JCAP (2010), arXiv:0912.3370.
- Syksy Rasanen, "Applicability of the linearly perturbed FRW metric and
  Newtonian cosmology", PRD 81 (2010), arXiv:1002.4779.
- Thomas Buchert, "Backreaction Issues in Relativistic Cosmology and the Dark
  Energy Debate", AIP Conf. Proc. 910 (2007), arXiv:gr-qc/0612166.
- Thomas Buchert et al., "Is there proof that backreaction of inhomogeneities
  is irrelevant in cosmology?", CQG 32 (2015), arXiv:1505.07800.
- M. Gasperini, G. Marozzi, F. Nugier, and G. Veneziano, "Light-cone averaging
  in cosmology: formalism and applications", JCAP (2011), arXiv:1104.1167.
- David L. Wiltshire, "Gravitational energy as dark energy: Cosmic structure
  and apparent acceleration", arXiv:1102.2045.
- David L. Wiltshire and P. R. Smale, "Supernova tests of the timescape
  cosmology", MNRAS 413 (2011).
