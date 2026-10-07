# Topological F4 Memo: Quantized Gluing Obstruction and the Dark-Energy Magnitude

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
- `math/DERIVATION_AVENUE_D_2026-06-02.md`, section 3.3.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex`,
  especially F4, F48, F27, and F40.

## 0. Verdict

**NO.** Reading the cosmological F4 obstruction as a quantized topological
invariant does not presently yield `Omega_Lambda ~ 0.68` with an F4-fixed
scale and a fixed no-free-parameter prediction.

The topological reading is mathematically coherent as a possible **status** or
**quotient readout**:

```text
local FLRW/observer charts fail to globalize
=> possible Cech/defect/orbit/anomaly obstruction class
=> the class may be integer-valued in a suitably declared topology/gauge problem.
```

But the dark-energy claim needs more:

```text
integer/topological class  +  F4-fixed dimensional scale  ->  rho_Lambda.
```

That step fails. F4/F48/F27/F40 supply descent and gluing criteria; they do
not supply a Lorentzian gravitational action, a four-form sector, a membrane
charge lattice, a topological susceptibility, a torsion coupling, or any
dimensionful scale. The moment one chooses `M_Pl^4`, `M_Pl^2 H_0^2`, QCD
`chi_top`, a horizon scale, or a flux charge by hand, the construction becomes
a normalizer and triggers R14. If one imports the four-form literature, it
inherits the known discretuum/anthropic-selection wall rather than deriving
the value.

Failure mode:

```text
(a) the scale must be inserted by hand;
(b) the invariant is not established as nonzero for the actual cosmological gluing;
(c) four-form/topological-vacuum precedents require tuning, many fluxes, or anthropics.
```

The banked C/B result stands.

## 1. Concrete Invariant and Anti-Vacuity

### 1.1 Best Candidate: Cech Obstruction of the Local-FLRW-Fit Sheaf

The closest honest translation of F4 into topology is:

```text
base X:
  the coarse-graining / observational cover of the cosmological domain;

cover U = {U_i}:
  patches carrying local closure data, local observer frames, or local FLRW fits;

fiber:
  local smooth-FLRW readout data, e.g. (H_i, Omega_m,i, curvature_i, calibration_i, ...);

structure group:
  declared transition group of chart/calibration transformations between local fits;

object:
  a sheaf or stack F_FLRW of admissible local smooth-fit sections;

candidate invariant:
  a Cech obstruction class [g_ij] for descent/globalization of local sections.
```

This is the only candidate that is directly F4-shaped: F4 already gives a
finite patch system, overlap compatibility, a global state set, and a
restriction map `R`. In sheaf language, compatible local sections globalize
when the relevant Cech descent obstruction vanishes.

### 1.2 Why This Does Not Yet Give a Quantized Cosmological Invariant

For the actual cosmological gluing used in the dark-energy program, the local
data are smooth fit parameters and observational calibrations. Their natural
parameter spaces are affine/convex real domains, not compact order-parameter
spaces with nontrivial homotopy. On a good cover, sheaves of smooth real-valued
sections are fine/soft in the standard mathematical setting; topological
`H^1` obstructions are not the generic object. The failures found in the
program are analytic/statistical: route mismatch, Schur residual, support
failure, nonlinear carrier failure, and light-cone fitting bias.

Therefore:

```text
F4 compatibleNonGlobal status != automatically nonzero integer class.
```

A nonzero integer can certainly be manufactured in nearby mathematics:

- local circle-valued phases over `S^1` give winding in `H^1(S^1,Z)`;
- principal `U(1)` bundles carry first Chern class;
- order parameters with space `G/H` carry defect charges in `pi_n(G/H)`;
- frame bundles can carry characteristic classes.

But none of these is the declared local-FLRW-fit bundle unless the theory adds
that structure.

### 1.3 Other Candidate Readings

| candidate | concrete object | anti-vacuity result |
|---|---|---|
| Cech `H^1` class | Sheaf/stack of local FLRW-fit sections over the observational cover | Best F4-shaped object, but not naturally integer/nonzero for ordinary real-valued local fit data; nonzero only after adding extra topology/gauge structure. |
| Characteristic class of frame bundle | Euler/Pontryagin/Stiefel-Whitney classes of the spacetime or spatial-slice frame bundle | Real GR topology object, but not the F4 FLRW-fit residual and not known to encode `Omega_Lambda`; observed large-scale cosmology does not select a nonzero class with DE scale. |
| Defect charge `pi_n(G/H)` | Topological defect of an order-parameter space | Requires a physical order parameter `G/H`. SBT has not declared one for cosmological closure. |
| F27 Noether/gluing-orbit charge | Conserved quantity descending through a declared symmetry orbit | F27 says conservation is orbit descent; it does not create a Noether charge without an action and a symmetry. |
| F40 anomaly coefficient | Failure of symmetry descent, possibly classified by anomaly polynomial | F40 is structural. A quantized anomaly coefficient requires a quantum field content, gauge group, regulator/measure, and anomaly polynomial. None is supplied by F4. |
| F48 topological readout | Readout constant on gluing-quotient classes | F48 tells when a readout is topological; it does not force discreteness, nonzero value, or energy scale. |

Anti-tautology conclusion. Defining a scalar

```text
Q_top := Omega_Lambda / 0.68
```

or defining the obstruction number to be the fitted dark-energy residual is
not a topological derivation. It encodes the answer in the invariant and fails
the same non-vacuity test that Avenue C failed for `Xi_C -> delta_LC`.

## 2. The Scale Crux

### 2.1 Dimensional Accounting

A topological invariant is dimensionless:

```text
n in Z,  c_1, Euler number, winding, anomaly index, ...
```

A cosmological constant energy density has dimension four:

```text
rho_Lambda ~ Omega_Lambda rho_crit
            ~ 10^-120 M_Pl^4
            ~ (2--3 meV)^4.
```

Thus every topological-CC proposal needs a scale:

```text
rho_top = n * mu^4
or
rho_top = (1/2) sum_i n_i^2 q_i^2
or
Lambda_top = n / L^2
```

The integer can be `O(1)` without solving the problem. The problem is `mu`,
`q_i`, or `L`.

### 2.2 Four-Form Flux Precedent

The four-form mechanism is the closest real precedent. In four dimensions a
four-form field strength has no local propagating degrees of freedom and acts
as an integration constant contributing to the effective cosmological
constant:

```text
lambda = lambda_bare + (1/2) c^2
```

or, with quantized fluxes,

```text
lambda = lambda_bare + (1/2) sum_i n_i^2 q_i^2.
```

Historical result:

- Hawking and Aurilia--Nicolai--Townsend type constructions show that a
  four-form/integration constant can contribute to `Lambda`, but the constant
  or charge scale is not predicted by topology alone.
- Brown--Teitelboim membrane nucleation can step the cosmological constant,
  but a single charge must be extraordinarily tiny to land in the observed
  window.
- Bousso--Polchinski make the spectrum dense by many quantized four-form
  fluxes. Their own numbers are the important warning: the observational
  window is about `10^-120 M_Pl^4`; a single flux step is too coarse; with
  Planck-scale bare `lambda`, one needs many fluxes, order `100` in ordinary
  compactifications, or special charge/extra-dimension assumptions. The
  residual value is then selected from a discretuum, with anthropic reasoning
  doing the final explanatory work.

This is not an F4 derivation. It is a separate quantum-gravity flux sector.
If imported into Six Birds, it would be a physics bridge:

```text
B_flux : F4 obstruction -> four-form charge lattice and membrane dynamics.
```

No such bridge is supplied. Without it, invoking four-forms merely relabels
the established four-form landscape problem.

### 2.3 Topological Susceptibility and Theta Terms

QCD topological susceptibility is the clean analogy for "topological charge
fluctuations produce vacuum energy":

```text
chi_top = d^2 E(theta) / d theta^2 |_{theta=0}
```

But `chi_top` is dimensionful because QCD has a dynamical strong scale and
quark masses. In chiral perturbation theory,

```text
chi_top ~ f_pi^2 m_pi^2 / (2 N_f)
```

up to higher-order terms, while pure-gauge estimates are typically of order
`(100 MeV)^4`. Either way, the scale is the QCD scale, not topology alone.
Compared with `(2--3 meV)^4`, QCD-scale susceptibilities are about
`10^42--10^44` times too large. They illustrate the rule:

```text
topology supplies the integer/sector;
dynamics supplies the energy scale.
```

F4 currently supplies only the first kind of data, and even that only after a
topological structure is added.

### 2.4 Chern--Simons, Pontryagin, Euler, and Nieh--Yan

Four-dimensional gravitational actions can include topological densities such
as Euler, Pontryagin, and Nieh--Yan terms. The cited gravity literature treats
their coefficients as additional topological or Immirzi-like parameters. These
terms can affect canonical variables, parity/torsion couplings, or anomaly
structures, depending on the theory and matter content.

They do not fix `rho_Lambda`:

- the coefficients are couplings or superselection parameters;
- Nieh--Yan-type terms involve torsion and often vanish in torsion-free
  sectors;
- adding such a term is adding a new gravitational action term, not extracting
  an energy scale from F4;
- when a cosmological constant appears in the same low-energy action, it
  remains an independent dimensionful coupling.

Thus Chern--Simons/Nieh--Yan topology does not evade the scale problem. It
replaces it with a choice of coupling.

### 2.5 Candidate F4 Scales

| candidate scale | result |
|---|---|
| `M_Pl^4` | Natural for quantum gravity but overshoots by about `10^120`. |
| QCD `chi_top` | Topological-vacuum analogy but overshoots by about `10^42--10^44`. |
| `H_0^4` | Horizon scale alone undershoots by about `10^120` relative to `rho_Lambda`; wrong dimensioned combination. |
| `M_Pl^2 H_0^2` | Gives the critical-density scale, but `H_0` is an observed late-time readout; using it fixes the answer by normalization unless F4 predicts `H_0` and onset independently. |
| structure-formation scale | Not fixed by F4; any conversion to `rho_crit` needs a model of growth, voids, clocks, or beams already rejected as non-SBT-selected in LT2/Avenue C. |
| topology volume `1/L^2` or `1/L^4` | Requires a specified compact/global length. Choosing the present horizon is an input, not a topological consequence of F4. |

Scale verdict. F4 does not supply a non-Planckian, non-tuned scale. The
integer may be quantized, but the multiplier is free.

## 3. Small plus Topological Split

The Calugareanu analogy is:

```text
Lk = Tw + Wr
```

where the topological linking number is the sum of non-topological smooth
twist and writhe terms. This shows that a global integer can coexist with
smooth local contributions that vary under deformation.

For cosmological F4, an analogous theorem would need:

```text
Q_total = Q_smooth + Q_global
```

with:

1. a declared conserved global charge `Q_total`;
2. a local smooth contribution `Q_smooth` that corresponds to the perturbative
   FLRW/backreaction residue;
3. a global/topological term `Q_global`;
4. a physical energy functional coupling `Q_total` to `rho_Lambda`;
5. a theorem that local averaging sees only `Q_smooth ~ 10^-5--10^-3`, while
   the global sum contains `Q_global = O(1)`.

No such cosmological theorem exists in the Six Birds apparatus. F4 can
distinguish local-compatible/non-global status; F48 can identify readouts that
descend through a gluing quotient. Neither supplies a conserved topological
charge with a local/global decomposition or a stress-energy map.

Therefore the split is presently an evocative analogy, not a carried theorem.
If one introduces a real topological defect network, a four-form flux, or a
torsion/Chern--Simons sector, then a small+topological split may exist inside
that added physics. But the magnitude would then come from defect tension,
flux charge, torsion coupling, or susceptibility scale, not from F4 itself.

## 4. Decision

No fixed prediction follows. There is no F4-derived integer, no F4-fixed scale,
no computed `Omega_Lambda`, no onset prediction, no `w(z)`, and no discrete
cosmological signature.

The exact failures are:

1. **Invariant failure / under-specification.** The natural F4-to-topology
   candidate is a Cech obstruction of a local-FLRW-fit sheaf/stack. For the
   actual real-valued fit data, this is not naturally a nonzero integer
   invariant. Integer classes require extra bundle/order-parameter/gauge
   structure.
2. **Scale failure.** Even if an integer invariant is supplied, F4 does not
   fix the dimensionful scale converting it into energy density.
3. **Precedent failure.** Four-form and topological-vacuum precedents already
   demonstrate the pattern: topology can quantize sectors, but observed
   `rho_Lambda` requires a tiny step, many fluxes/discretuum, a dynamical scale,
   or anthropic/selection input.
4. **R14 failure if forced.** Choosing `M_Pl^2 H_0^2` or a horizon length to
   obtain `Omega_Lambda ~ 0.68` is a normalizer unless F4 first predicts that
   scale and coefficient. It does not.

Banking statement:

```text
Topological F4 is a possible future audit/status refinement.
It is not a dark-energy magnitude derivation.
Outcome C/B remains banked.
```

## References

- Six Birds Foundations IV catalog:
  F4 Local--Global Obstruction Normal Form; F48 Topology as Global Gluing
  Invariant; F27 Conservation as Orbit Descent; F40 Anomaly / Symmetry
  Obstruction.
- S. W. Hawking, "The cosmological constant is probably zero", Phys. Lett. B
  134 (1984) 403.
- A. Aurilia, H. Nicolai, P. K. Townsend, "Hidden constants: the theta
  parameter of QCD and the cosmological constant of N=8 supergravity", Nucl.
  Phys. B176 (1980) 509.
- J. D. Brown and C. Teitelboim, "Dynamical neutralization of the cosmological
  constant", Phys. Lett. B195 (1987) 177; "Neutralization of the cosmological
  constant by membrane creation", Nucl. Phys. B297 (1988) 787.
- R. Bousso and J. Polchinski, "Quantization of Four-form Fluxes and Dynamical
  Neutralization of the Cosmological Constant", arXiv:hep-th/0004134.
- N. Turok and S. W. Hawking, "Open Inflation, the Four Form and the
  Cosmological Constant", arXiv:hep-th/9803156.
- UKQCD Collaboration, "The topological susceptibility and f_pi from lattice
  QCD", arXiv:hep-lat/0108006.
- S. Mercuri, "Fermions in the Ashtekar-Barbero connection formalism for
  arbitrary values of the Immirzi parameter", arXiv:hep-th/0507253.
- A. Date, R. K. Kaul, S. Sengupta, "SU(2) gauge theory of gravity with
  topological invariants", arXiv:1110.4185.
- M. Montesinos and D. Gonzalez, "Generalizations of the Nieh-Yan topological
  invariant", arXiv:2110.07644.
