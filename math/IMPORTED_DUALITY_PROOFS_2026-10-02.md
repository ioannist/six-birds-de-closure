# Imported duality review and constructive repair, 2026-10-02

Baseline: `903d007`. This packet leaves the paper and frozen experiment outputs
unchanged. It contains mathematical construction and adversarial self-review by
one reviewer; kernel checking and separately implemented graph arithmetic do not
constitute independent human review.

## Original target and import correction

The unchanged paper, sections 2.4 and 4.4, says that min-cut area is the optimal
*dual variable* of boundary entanglement flow, that Born and area share one
composition law, and that area and the closure price are one-number duals which
both vanish when their constraint is slack and are set by budget rather than
local detail. These are substantive parts of the central recognition claim.

The current imported corpus source is
`../six-birds-papers/Tsiokos_2026_To_Kill_Three_Stones_with_Six_Birds_A_Common_Grammar_for_the_SM_QM_and_GR.tex`,
section 5.4, backed by
`../six-birds-sm-qm-gr/review_2026/repairs/q5_lp_duality/`.
It now explicitly distinguishes

```
area(c) = optimal dual objective = sum_e c_e y_e
edge capacity shadow prices = y_e = partial F*/partial c_e
```

in a unique-cut chamber. Its independently contracted entropies show only a
sampled approach toward cuts, not exact saturation or a convergence theorem.
Its four gluing probes satisfy area min-plus composition but fail the proposed
Born entropy rule. Thus the old import does not justify the unchanged wording.

This packet supplies a useful finite repair. It does **not** establish an
intrinsic equality between the dual objective and a multiplier, restore a
universal Born/area composition law, or identify the constructed price with
physical Lambda. The universal composition claim is false and is parked.

## 1. Construct the finite objective and its ledger law

Let K be a nonempty finite cut family, E a finite edge set, and w(k,e) its
incidence weights. Set C_k(c)=sum_e c_e w(k,e). Define A(c) as the minimum of the
actual finite set of these costs. An attained minimizer is constructed with
Finset.min'; it is not a field containing a supplied optimality assertion.
Nonnegative c and w imply A(c)>=0. Every minimizing k gives the supergradient

```
A(d) <= A(c) + sum_e w(k,e)(d_e-c_e).
```

The scalar A(c)=sum_e c_e w(k,e) is distinct from that incidence vector.
For the one-edge graph A(c)=c; at c=3, area is 3 but its derivative with respect
to edge capacity is 1. Both the graph objective and derivative are proved in
Lean (`single_edge_area`, `area_not_individual_price`).

For arbitrary finite vertices and oriented stored edges, define balance(n) as
outgoing minus incoming signed flow. Finite summation by parts proves

```
sum_n p_n balance(n) = sum_e (p_tail(e)-p_head(e)) f_e.
```

Interior conservation, p_source=1 and p_sink=0 return the source flow. If
|f_e|<=c_e and |p_tail-p_head|<=w_e, each summand is <=c_e w_e. This proves weak
duality, source flow <= cut cost, and hence source flow <= A(c) for a family of
lawful potentials. A tight *feasible* flow certificate therefore supplies a
real global optimizer. These are local Lean theorems, including the feasibility
return. Existence of tight flows on arbitrary graphs is **not** assumed to be
proved by this certificate theorem; actual witnesses for the imported carrier
are constructed separately below.

The imported y_e are the incidence values at the unique cut. The general
supergradient theorem does not by itself prove differentiability in a unique-cut
chamber. For this source, exact positive margins and coordinate perturbations
check chamber stability and y_e sensitivities. These finite checks are Python
Fraction computations, not a kernel reification of the 254 graph instances.

## 2. Common scaling supplies an explicitly normalized scalar price

Fix a capacity shape c0 and choose B>=0 as its common dimensionless multiplier.
Finite minimization and nonnegative scalar multiplication give exactly

```
A(B c0) = B A(c0).
```

This holds even at B=0 or when there are tied cuts. At B>0 the scale derivative
is A(c0). Thus the scalar area **is** a marginal price for this declared common
scale coordinate. At the unit scale B=1 it equals the graph's current area.
At a general B, current area is B times this price.

This is a P1 reparameterization / P6 ledger construction: the independently
proved law is finite-minimum homogeneity; applicability fixes the capacity shape
and scale coordinate; the return is the scale derivative. It does not supply a
physical scale, a special spacetime theory, or entanglement equality.

If the scale coordinate is b=unit*B with unit>0, then

```
d A((b/unit)c0)/db = A(c0)/unit.
```

Area at the same physical capacities is unchanged while the coordinate price
changes. In particular the controller examples (A,B)=(3,1) and (3/2,2) have
throughput 3 and prices 3 and 3/2 respectively. The original unqualified area /
price identity cannot survive coordinate changes. Fixed shape is also essential:
a change in local capacities generally changes A(c0) and hence this scale price.
The previous `AllocationPrice` packet already gives a same-budget example where
local objective coefficients change the closure price.

## 3. Add a declared ceiling to construct the slack regime

Original max-flow with all capacities multiplied by B has value B A; it does
not acquire a finite unconstrained saturation level by this coordinate change.
To construct the requested active/slack pattern, explicitly add a throughput
ceiling Q>=0 and a scale-allocation variable x:

```
maximize r, subject to 0<=x<=B, 0<=r<=A x, r<=Q.
```

For A>0, the selected x=min(B,Q/A), r=min(A B,Q) is feasible and globally
optimal; for A=0 the optimum r=0 is also constructed. The negative-throughput
minimization Lagrangian has nonnegative budget, coupling and ceiling multipliers
(lambda,eta,gamma). With the lower-bound multipliers chosen zero, stationarity
and complementarity are

```
lambda=eta A, eta+gamma=1,
lambda(B-x)=eta(Ax-r)=gamma(Q-r)=0.
```

These form a sufficient KKT certificate, not a characterization of every KKT
multiplier tuple at boundary points. A weighted sum of the three constraint
slacks proves global optimality, with no value derivative assumed in the record.
Constructed certificates are

```
A B <= Q: x=B, r=A B, (lambda,eta,gamma)=(A,1,0),
Q <= A B: x=Q/A, r=Q, (lambda,eta,gamma)=(0,0,1).
```

`area_scale_controller_active` explicitly returns the constructed scaled cut
area into the active controller certificate, rather than leaving this bridge
only as a prose identification.

In strict regimes the derivative of min(A B,Q) is A or 0 respectively. These
are derivatives of the explicit real function; as two-sided budget sensitivity
statements they apply at interior budgets B>0. At the
kink A B=Q with A>0 every lambda in [0,A] is certified using eta=lambda/A,
gamma=1-eta. Consequently a binding budget can have zero price, and the
value's derivative is not asserted at that kink. The added ceiling is a new
constraint, not something inherited from the original max-flow problem.

For the imported 14-edge/13-vertex graph, `de_imported_duality_checks.py` declares
Q=10 and scale test values 0,1/2,1,3/2 **before** computing any cuts. The graph
has eight boundary labels and five interior vertices. Independently enumerating
all 32 interior placements for each of 254 nontrivial boundary masks constructs
the cut objectives. A separate depth-first residual-flow implementation
constructs signed rational flow witnesses, then verifies capacities, conservation,
all 8,128 cut-flow bounds, tightness and cut-edge saturation. No source solver is
imported or called. All minima, margins and 3,556 coordinate prices match the
source tables. The 1,016 scale tests check both cut and actual flow homogeneity.
All base areas lie in (0,10), so the unit-scale controller is strictly active;
Q/A+1 supplies a strict slack budget with actual graph flow Q. Boundary prices
0,A/2,A are checked. Forged capacity and conservation witnesses are rejected.
These checks are exact on the declared rational graph and supplied tables.
They do not reproduce the source's random-tensor simulations.

## 4. Exact entropy-contraction obstruction

Use real nonnegative amplitudes as a valid subset of complex qubit amplitudes.
The bipartite pure state

```
psi = sqrt(3/4)|00> + sqrt(1/4)|11>
```

has norm one. Its coefficient matrix is diagonal; its reduced Gram matrix is
exactly diag(3/4,1/4), so its Schmidt entropy is H(3/4), with H the binary entropy
in natural logarithms. Contract one boundary index between two copies:

```
M_psi M_psi = diag(3/4,1/4).
```

This is actual matrix multiplication, summing over the common index. The
resulting unnormalized state has squared norm 5/8, hence it is nonzero and
normalization is legal. Its normalized reduced Gram matrix is diag(9/10,1/10),
with entropy H(9/10). Mathlib's proved strict decrease of H on [1/2,1] gives
H(9/10)<H(3/4), without a floating-point tolerance.

For the one external output label, the two interface placements give the
proposed min-plus candidate

```
min(H(3/4)+0, 0+H(3/4)) = H(3/4).
```

Whole/empty input subsystems have zero entropy because the input is pure.
The output entropy is strictly smaller, so this composition law fails on a
realizable finite tensor contraction. In contrast, the two cuts of a two-edge
path have area min(a,b), proved as `series_path_area`. Equal capacities give
min(a,a)=a. Tied path cuts cause no ambiguity in this value/composition example;
no differentiability or unique-cut claim is needed. The source's four numerical
unique-base probes are separate corroboration, not the basis of this exact proof.

`TensorComposition` mechanizes the coefficient contraction, Gram and trace
bridges, positive normalization, weights and strict binary-entropy inequality.
It uses an explicit Schmidt-diagonal carrier, not a general quantum entropy API,
and asserts no unrelated physical stability, holography or continuum theorem.

## 5. Return to the original claim and options

There are two mathematically defensible directions for the later paper phase:

1. Retain the comparison at the level of finite optimization duality: area is
   a dual *value*, edge incidence gives capacity prices, and the closure budget
   has its scalar multiplier. Their roles are related but not identical.
2. Use the new fixed-shape/common-scale construction for a genuine scalar-price
   comparison, naming its normalization and the added ceiling needed for a slack
   regime. This gives an exact finite illustration under additional premises.

Neither option restores universal shared Born/area composition, a canonical
area-as-multiplier assertion, or a physical Lambda derivation. The imported
physical wording cannot be retained solely on the current finite evidence.
The original scalar closure-price construction remains valid with its explicit
optimization and sensitivity hypotheses. No paper claim has silently been
rewritten here.

## Adversarial self-review and verification scope

- The minimum is constructed; no optimizer existence or derivative is hidden in
  a theorem input. Tight graph flows are actual checked witnesses; the general
  tight-certificate theorem does not construct them for all graphs.
- Graph incidence/potential constraints and signed-flow orientations are checked.
  The Python instances are not presented as Lean-reified graph certificates.
- Scale positivity, zero scale, zero area, ceiling boundary, tied cuts and changed
  units are covered. The sufficient KKT record does not exclude other boundary
  multipliers. A kink price is not called a value derivative.
- The output tensor is actually contracted, is nonzero, and is normalized before
  entropy evaluation. The obstruction applies to the stated min-plus gluing rule,
  not every imaginable composition rule or every entropy inequality.
- New exact checks add evidence without changing frozen experiment results.
  Imported tensor trend/response reports remain imported numerical evidence.
- Reproduce with `lake build`, `lake env lean manifests/check_axioms.lean` in
  `lean/`, and `python scripts/de_imported_duality_checks.py` at the repo root.
  Raw audits and source-hashed evidence live in
  `results/imported_duality_2026-10-02/` and
  `lean/manifests/axiom_audit_imported_duality_2026-10-02.txt`.
