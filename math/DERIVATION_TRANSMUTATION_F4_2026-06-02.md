# Transmutation F4 Memo: Running Closure Defect Across the P4 Ladder

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
- `math/DERIVATION_CRITICALITY_F4_2026-06-02.md`.
- The Six Birds corpus listed in Packet WP-TRANSMUTE-F4.

## 0. Verdict

**PARTIAL, not YES.** The SBT corpus does support a native
dimensionless-running form:

```text
stage-local closure defect  ->  per-stage log change  ->  cumulative ratio.
```

For the dark-energy derivation target, the most defensible defect is the
Schur adequacy residual

```text
Xi_j = Xi_{C_j}(D_j | L_j),
```

because Claim S prices this exact residual and the adequacy-residual calculus
already supplies chain-rule, data-processing, bridge, and staged-recursion
forms. Under genuine stage refinement, `Xi_j` can run nontrivially; this is
not vacuous.

But the running rate is not fixed by the six primitives. The coefficient is
carried by stage/profile/substrate data:

```text
alpha_j, epsilon_j, E_j, A_j, C_j, W_j, N_j-K_j, C_0, budget Omega_j,
birth threshold theta.
```

The six primitives fix the **type** of the interaction and several lawful
forms: Schur monotonicity, quotient descent, finite-forcing exponentials,
pressure-as-per-stage-log-growth, and budget-to-price duality. They do not
fix the numerical beta coefficient or the terminal rung `j*`.

Therefore the native dimensional-transmutation route is a real structural
form, but not a dark-energy magnitude derivation. To get

```text
rho_Lambda / rho_Planck ~ 10^-120
```

one must still choose a cumulative hidden volume, contraction product,
threshold, or budget. Choosing, for example, `N-K ~= 399` because
`2^-399 ~= 10^-120` is a fit, not a theorem. The banked C/B result stands.

What is fixed:

- the admissible running-defect shape;
- the Schur residual as a canonical closure currency;
- the fact that genuine refinements can shrink or transport the residual
  lawfully;
- the distinction between exponent/order and coefficient;
- the one-anchor rule: a single substrate unit can dimensionalize a computed
  pure ratio.

What remains free:

- the beta coefficient;
- the bounded-interface constant `C_0`;
- the stage transport/contraction data;
- the residual budgets and audit weights;
- the birth threshold `theta`;
- the terminal stage `j*`.

Decision:

```text
PARTIAL: native form, free coefficient and free termination.
Reopen condition unmet.
```

## 1. Running Defect and Beta Construction

### 1.1 Candidate Defects

Several SBT defects have a staging-running interpretation.

| candidate | strength | weakness |
|---|---|---|
| Idempotence defect `delta_{tau,f}` | Canonical P5/P4 defect; explicit TV formula in Foundations I. | Can be identically zero for trivial constant maps; small defect is only saturation, not nontrivial emergence. |
| Route mismatch `RM(j)` | Direct P3 obstruction; used in To Count and To Chart. | Diagnostic, not itself a currency or budget without P6 audit. |
| Cantor Fekete pressure `P(s)` | Literally a per-stage log-growth rate `lim_n (1/n) log Phi_n(s)`. | Value is closed only on an audited shell; witness dimensions/support constants are host-bound. |
| Adequacy residual `Xi_C(D|L)` | Same Schur residual priced by Claim S; PSD currency, chain rule, data processing, bridge laws. | Stage-to-stage rate coefficients are not fixed by the residual definition. |

The best target for this packet is therefore the adequacy residual.

### 1.2 Stage-Local Schur Defect

Let `j` index an accepted P4 stage. At stage `j`, write

```text
Xi_j = Xi_{C_j}(D_j | L_j),
```

where the native family `L_j`, dissolving family `D_j`, and audit energy
`C_j` live on the stage's legal energy quotient. In the adequacy-residual
paper,

```text
Xi_C(D|L) = K_DD - K_DL K_LL^dagger K_LD
```

is the Schur-complement leftover that the native family cannot explain. It is
positive, budgetable, and Loewner-minimal among native explanations.

To compare stages, one must choose an audited bridge to a common response
space or expose the transport map. This is not optional: Foundations II
requires cross-level comparisons to carry explicit translation/lift records.

Define a scalar stage defect only after such a bridge has been declared. One
safe form is

```text
rho_j = tr(W_j Xi_j) / b_j,
```

where `W_j >= 0` is an audit readout and `b_j > 0` is the declared residual
budget in the same units. Then define the per-stage running rate

```text
beta_j = log rho_{j+1} - log rho_j
```

whenever both defects are positive. Equivalently, under a common transport
space one can use a Loewner/norm ratio.

This is a genuine beta-function analogue: it is a per-stage log change of a
dimensionless closure defect.

### 1.3 Anti-Vacuity: The Schur Defect Can Run

The running is not automatically zero. The adequacy-residual chain rule says
that extending the native family by a genuine new probe can only shrink the
residual:

```text
Xi_C(D | L^+) <= Xi_C(D | L).
```

More explicitly, the iterated Schur-complement identity subtracts a
conditional Schur block. If the added native probe sees a component of the
dissolving family that `L` did not see, then this conditional Schur term is
nonzero, and

```text
Xi_{j+1} = Xi_j - S_j,   S_j >= 0,   S_j != 0.
```

For any audit readout `W` with `tr(W S_j) > 0`,

```text
rho_{j+1} < rho_j,
beta_j < 0.
```

A concrete limiting example is immediate: at stage `j`, take a native family
that cannot represent a dissolving probe, so `Xi_j > 0`; at stage `j+1`, add
that dissolving direction itself as a native probe. Exact adequacy holds at
the later stage, so `Xi_{j+1}=0`. The defect has run.

Thus the transmutation proposal passes the first anti-vacuity gate:

```text
there are real closure systems in which the Schur/F4 defect runs.
```

But the amount of running is the conditional Schur term. That term depends on
the stage's probe geometry, audit energy, bridge, and budget readout. It is
not a primitive-label constant.

### 1.4 Staged Recurrence Form

The adequacy-residual appendix already records the natural staged recurrence:

```text
Xi_{j+1} <= (1 + epsilon_j) A_j Xi_j A_j^* + E_j,
```

or, in a strict-collapse regime,

```text
Xi_{j+1} <= (1 - alpha_j) Xi_j + E_j.
```

In the defect-free scalarized case, this gives

```text
rho_{j+1} / rho_j ~= 1 - alpha_j,
log rho_j ~= log rho_0 + sum_{i<j} log(1 - alpha_i).
```

This is exactly the desired running form. The obstruction is that
`alpha_j`, `epsilon_j`, `A_j`, and `E_j` enter as hypotheses/data. The corpus
does not derive them from P1--P6 alone.

## 2. Structural Rate Versus Free Coefficient

### 2.1 The `C_0` Bounded-Interface Knob

Foundations I defines bounded interface by assuming a constant `C_0 >= 1`
such that

```text
|P / ~_j| <= C_0 (j+1).
```

The paper is explicit: this is a modeling assumption encoding bounded
observable signature; it is not derived from refinement alone. Refinement
alone permits exponential growth.

Therefore `C_0` is a genuine knob. It can control how many distinctions,
modes, sectors, or hidden degrees become visible by stage `j`. Any formula of
the shape

```text
hidden volume H(j) ~= N_j - K_j
ratio ~= 2^{-H(j)}
```

inherits the numerical content of `H(j)`, and hence of the lens/interface
growth data. The finite-forcing lemma gives the real native exponential

```text
P(h definable from f) = 2^{-(N-K)}.
```

It does not fix `N-K`.

This is the clearest coefficient-versus-form separation:

```text
form fixed: exponential in hidden volume;
coefficient/exponent input: hidden volume N-K, governed by host/lens data.
```

### 2.2 BirdInt Cell Classification

The beta-function belongs naturally to the BirdInt interaction zone:

```text
P4 staging/refinement
interacting with P1 operator rewrite
and P6 audit/accounting.
```

More concretely:

- `P1 <- P4`: stage information informs operator rewrite or
  sector-boundary targeting.
- `P6 <- P4`: audit records are stage-indexed and compare closure cost across
  rungs.
- `P2 <- P6`: budget/audit information gates feasibility.
- `P4 <- P6` or `P4 <- P1`: the next stage can be selected after a defect or
  rewrite changes what is maintainable.

But Foundations III blocks the overread that would make this a universal beta
constant. BirdInt's primitive labels are role names, not elements of a total
interaction algebra. A directed cell `P_i <- P_j` is admissible only with
witness, update, profile, level, visibility, threshold, audit, and defect
data. The same primitive pair can have different statuses in different
profiles, and PICA itself is only a scoped model realization, not the
canonical universal algebra.

Therefore the running-rate cell is:

```text
typed, admissible, profile-relative, host-bound.
```

It is not:

```text
beta = beta(P4 x P1 x P6)
```

as a primitive constant.

### 2.3 Foundations II and Cross-Level Self-Consistency

Foundations II gives the exact-six architecture over `FATCD`, but it also
records the relevant nonclaims:

- selected lifts are not unique;
- lower-level data do not determine higher-level structure;
- cross-level comparison is inadmissible without a translation record;
- every active projection requires threshold, witness, level, and audit data.

This blocks a tempting argument:

```text
because the six roles are exact, the cross-level rate is fixed.
```

The scoped exact-six theorem says every admissible description receives a
six-channel bookkeeping/exhaustion record. It does not say the stage-to-stage
transport coefficient is unique or determined by role architecture.

### 2.4 To Count: Exponent/Order Versus Coefficient

To Count is the cleanest local analogy. The difference quotient uses the
operator rewrite

```text
delta_h f = (f(x+h)-f(x)) / h,
```

an `h^{-1}` rescaling that keeps the update comparable across stages. The
finite-difference Leibniz identity has an exact ledger term

```text
h * delta_h f * delta_h g.
```

When the difference quotients remain bounded, the ledger term vanishes as
`h -> 0`. This fixes an order: the defect is proportional to `h` under the
stated feasibility bounds.

But the same paper distinguishes order from coefficient. In the stencil
experiment, the order label `k` is chosen after renormalization `h^{-k}`;
within the first-order class, a moment-normalization step imposes
constraints such as

```text
sum_j c_j = 0,
sum_j j c_j = 1.
```

Likewise, the route mismatch obeys a fitted power law

```text
RM(h) ~= C h^p.
```

The scaling form is meaningful; the coefficient `C`, the tested exponent
`p`, and the normalization class are supplied by the analytic/protocol
setting. This is exactly the distinction needed here:

```text
SBT can fix scaling order under a declared ledger.
It does not automatically fix the numerical coefficient.
```

### 2.5 Cantor Shell Pressure

The Cantor Shell paper defines the pressure

```text
P_T0(s) = lim_n (1/n) log Phi_n(s)
```

on an audited shell. This is the native beta-object closest to the packet's
proposal.

But its scope is explicitly shell-bound:

- it is not a broad pressure theorem beyond the audited shell;
- the support table uses frozen base/shell witnesses with dimensions `16`
  and `20`;
- the pressure-gap consequence is not itself the strictness witness;
- BirdInt records the Cantor strict-bridge as model-grade, host-bound
  realization.

Thus Cantor proves that SBT can close a pressure object on a lawful shell. It
does not prove a universal pressure value from P1--P6.

### 2.6 Crux Result

The running rate is structural in **form** and free in **coefficient**:

```text
structural:
  Schur residual, quotient descent, exponential hidden-volume form,
  pressure/log-growth form, budget-to-price dual shape.

free / inherited:
  C_0, N-K, alpha_j, epsilon_j, stage bridge A_j, defect E_j,
  audit weights, residual budget, birth threshold.
```

## 3. Termination Stage `j*`

A dark-energy ratio needs a definite endpoint:

```text
ratio = exp(sum_{j<j*} beta_j)
```

or a definite hidden volume:

```text
ratio = 2^{-H(j*)}.
```

The corpus does not currently fix `j*`.

### 3.1 No-Go Theorems and Bounded-Interface Saturation

The no-go paper gives two relevant fronts.

First, idempotent packaging stabilizes after one step:

```text
e^2 = e  =>  e^n = e for n >= 1.
```

This does not create a running ladder. It kills one: iterating a fixed
idempotent adds no structure.

Second, with a fixed finite interface `f`, the set of definable predicates has
size

```text
|Def(f)| = 2^{|im(f)|}.
```

Therefore no infinite strictly increasing ladder of definable predicates
exists inside that fixed interface. But the theorem's own escape route is to
change the interface: add coordinates, refine the lens, or change the
package. That is precisely layer birth.

So the no-go proves:

```text
no unbounded laddering inside a fixed finite interface.
```

It does not compute:

```text
the universal maximal depth j_max,
the cosmological birth stage j*,
or the hidden volume H(j*).
```

At most, for a fixed declared interface one gets a finite bound depending on
`|im(f)|`. That cardinality is substrate/lens data.

### 3.2 To Notch Enablement Threshold

To Notch implements enablement-time by monitoring a predictive closure gap:

```text
gap = max(NLL_1 - NLL_2, 0).
```

When the gap exceeds a threshold, the theory is rewritten from a coarse lens
`f_0` to a richer lens `f_1`. This is exactly the desired birth mechanism.

But the threshold is part of the laboratory/audit design. The reported
example has a birth step and a pre-birth gap, but it is a controlled finite
Markov witness, not a theorem that fixes a universal `theta`.

Therefore:

```text
defect-triggered birth is native;
the firing threshold is not currently structural.
```

### 3.3 To Spend and Budget Self-Consistency

To Spend gives the currency-constraint morphism:

```text
lower-layer currency -> higher-layer budget constraint -> shadow price.
```

If a higher layer optimizes a potential under a budget `b`, the multiplier

```text
lambda = d Phi* / d b
```

is the higher-layer shadow price. When the budget binds, the price becomes a
coordinate; when slack, it collapses.

This is structurally important, but it does not fix the budget magnitude.
The paper explicitly separates the existence of a currency direction from the
magnitude currently expressed along it. It also treats currency as
layer-relative: what counts as the spending coordinate depends on the layer's
objects, protocols, and audits.

Thus budget self-consistency does not pin `j*` without an additional theorem
that the budget-to-price-to-budget map has a unique fixed point and that its
fixed point is selected without fitted thresholds.

### 3.4 Adequacy Ladder Coefficients

The adequacy-residual staged appendix records the exact missing data. The
strict-collapse ladder has coefficients

```text
alpha_j > 0
```

and accumulated defects. The multiplicative-additive ladder has

```text
epsilon_j, A_j, E_j.
```

The products and sums decide whether residual memory disappears or remains
bounded. Those products and sums are not derived from the six primitives in
the body of the paper; they are stated as stage-recurrence hypotheses.

Consequently `j*` is not locked.

## 4. Anchor Honesty

The packet's reframe is correct in one important respect:

```text
pure SBT structure is dimensionless;
one substrate unit may be used as the dimensional anchor.
```

If the theory computed a pure ratio

```text
r_SBT = 10^-120,
```

then converting it by one substrate unit, e.g. a Planck-density anchor, would
be honest in the same sense that QCD uses one dimensional scale plus
dimensionless ratios.

But this packet does not compute `r_SBT`. It supplies only lawful forms:

```text
r = 2^{-(N-K)}
r = exp(sum_j beta_j)
r = product_j (1 - alpha_j)
r = pressure-gap consequence on a shell.
```

To match the observed ratio one would have to set, for example,

```text
N-K ~= log_2(10^120) ~= 399,
```

or choose a contraction product with the same value. Nothing in the six
primitives selects `399`, the product, or the endpoint. The Planck anchor is
not the problem; the uncomputed pure number is.

Therefore:

```text
one anchor would be legitimate;
the required pure ratio is still not derived.
```

## 5. Distinctness From Excluded Engines

This route is genuinely distinct from the two previous engines.

It is not topological:

- no integer invariant is required;
- no characteristic class or flux quantization is used;
- the topological-F4 failure on invariant/scale does not directly apply.

It is not critical:

- no divergent susceptibility is required;
- no critical surface or SOC attractor is assumed;
- the criticality-F4 failure on tuning to a phase boundary does not directly
  apply.

The transmutation route is instead a scale-descent/running route:

```text
dimensionless defect runs across P4 stages until a birth/termination event.
```

However, after analysis it folds into the ordinary RG/scale-descent boundary
at the coefficient level. F35 says scale descent is quotient descent iterated
along a tower, and exact renormalization exists when the descended law is
constant on coarsening fibers. It does not determine the beta coefficient.

So the route is distinct in form, but it is not a new magnitude derivation
until the coefficient and endpoint are fixed.

## 6. Decision and Closing Theorem Target

Final classification:

```text
PARTIAL.
```

The native SBT corpus fixes the running **form**:

1. Schur residuals are canonical closure currencies.
2. Chain rules and bridges describe lawful stage-to-stage transport.
3. Finite forcing and Cantor pressure show native exponential/log-growth
   structures.
4. Budget duality explains why a binding residual produces a shadow price.
5. F35 records scale descent as quotient descent through a tower.

But the dark-energy ratio needs more:

```text
structural beta + structural j* = computed pure ratio.
```

Neither side is currently supplied.

The irreducible knobs are:

- `C_0`: bounded-interface constant, explicitly assumed;
- `N-K`: hidden volume in the finite-forcing exponential;
- `alpha_j`, `epsilon_j`: per-stage contraction/inflation coefficients;
- `A_j`, `E_j`: stage transport and paid defect;
- `Omega_j`, `W_j`, `C_j`: budget/audit/readout choices;
- `theta`: enablement/birth threshold;
- `j*`: terminal stage or layer-birth rung.

The theorem that would close the gap is:

```text
Structural Transmutation Theorem.

Given only P1--P6 records plus one substrate unit, the accepted cosmological
closure ladder has a canonical Schur defect Xi_j, a canonical audit readout,
a beta sequence beta_j fixed by BirdInt/F35 data, and a birth stage j* fixed
by a no-go or fixed-point condition. The cumulative pure ratio

  r_SBT = exp(sum_{j<j*} beta_j)

is independent of host presentation and equals the dark-energy ratio without
using Omega_Lambda, H_0, or a fitted threshold.
```

Current status of that theorem:

```text
not proved;
not presently supported by the corpus;
blocked by explicit nonclaims about C_0, selected lifts, host-bound model
realizations, and declared budgets.
```

Banking statement:

```text
The dimensional-transmutation posture is the best native reframe so far.
It makes the target a pure-number theorem, not a meV-scale miracle.
But the corpus currently fixes the algebraic shape, not the coefficient.
Outcome C/B remains banked.
```

## References

- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_of_Emergence_Calculus.tex`:
  idempotence defect `D-IC-02`, finite forcing `2^{-(N-K)}`, bounded-interface
  hypothesis `D-META-BND-01`, self-generated primitives.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_II_Admissibility_Meta_Theory_and_the_Exact_Six_Program.tex`:
  selected lifts, level-profile architecture, scoped exact-six over `FATCD`.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_III_A_Finite_Audited_Interaction_Calculus_for_SBT.tex`:
  BirdInt finite typed interaction calculus, no total six-symbol algebra,
  host-bound model realizations, Cantor/PICA nonclaims.
- `docs/papers/Tsiokos_2026_Six_Birds_No_Go_Theorems_for_Audited_Emergence.tex`:
  idempotent no-ladder, bounded-interface no-ladder, variational closure
  deficit.
- `docs/papers/Tsiokos_2026_Strict_Theory_Extension_on_a_Lawful_Continuous_Cantor_Shell.tex`:
  Fekete pressure `lim_n (1/n) log Phi_n`, audited-shell closure, conditional
  pressure disintegration.
- `docs/papers/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex`:
  enablement-time, defect-triggered theory birth, thresholded prediction gap.
- `docs/papers/Tsiokos_2026_To_Count_a_Stone_with_Six_Birds_A_Mathematics_is_A_Theory.tex`:
  renormalization as P1 operator rewrite, `h^{-k}` order, finite-difference
  ledger term, route-mismatch scaling.
- `docs/papers/Tsiokos_2026_To_Spend_a_Stone_with_Six_Birds_Currency_Constraint_Duality_and_Shadow_Prices_Across_Closure_Layers.tex`:
  currency-constraint duality, shadow prices, budget-relative magnitude.
- `docs/papers/Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex`:
  Schur adequacy residual, chain rule, bridge laws, residual budgets, staged
  residual recurrences.
- `docs/papers/Tsiokos_2026_To_Create_a_Stone_with_Six_Birds_Emergent_Geometric_and_Thermodynamic_Regimes_from_a_Minimal_Stochastic_Substrate.tex`
  and `docs/papers/Tsiokos_2026_To_Chart_a_Stone_with_Six_Birds_Emergence_Phase_Diagrams_for_Effective_Theories_in_Control_Space.tex`:
  PICA mechanism-space/rate controls, timescale policy, phase-diagram
  threshold discipline.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex`:
  F35 Scale Descent/Renormalization, F4 Local-Global, F36 Singular Limit,
  F44 Criticality.
- `lean/SbtCosmo/Derivation/ClosurePrice.lean`: finite Claim S capstone;
  Schur-energy Lagrangian pairing only, no dark-energy magnitude claim.
