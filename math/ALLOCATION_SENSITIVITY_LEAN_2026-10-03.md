# Derived original allocation value regularity, 2026-10-03

Baseline: `b01df36`. The original paper, runtime, earlier proof modules and
receipts are unchanged. Review is adversarial self-review, with no independent
reviewer. This advances the original budget-dual carrier in section 4.2; it
does not identify its price with physical Lambda or replace the general
Schur-energy convex program in section 4.1 with a sum-allocation budget.

## Target and exact result

Use the original objective, for any finite patch set, positive weights w_i
and curvatures c_i, arbitrary real offsets b_i, and a positive budget B:

```
U(x) = sum_i [w_i log(1+x_i) - c_i*x_i^2/2 + b_i*x_i],
x_i>=0, sum_i x_i<=B,
V(B) = -U(selectedAllocation(B)).
```

The common offset b_i=b used in `scripts/de_dual_carrier.py` is included.
The same previously constructed KKT price and allocation functions are used.
The new theorem derives, without a differentiability hypothesis,

```
V'(B) = -selectedPrice(B)   for every B>0.
```

It strengthens the earlier `AllocationPrice.cost_value_derivative`, which
correctly identified a supplied derivative but did not construct one.
`AllocationSensitivity` proves that the price is Lipschitz on all positive
budgets, and V is C1 there with Lipschitz derivative. All patch active-set
switches and the active/slack transition are covered. No fixed active-set,
interior-patch or optimizer-regularity hypothesis is introduced.

Put `K=sum_i(w_i+c_i)`. The explicit bounds are, for every B,C>0,

```
abs(p(B)-p(C)) <= K*abs(B-C),
0 <= V(C)-V(B)+p(B)*(C-B) <= K*abs(C-B)^2.
```

For every 0<h<B, the exact central finite-difference return satisfies

```
abs((V(B+h)-V(B-h))/(2*h)+p(B)) <= K*h/2.
```

Thus the original two price readouts have a rigorous exact-real error bound,
including switch points. The original Python `finite_diff_dual` negates that
central difference, so this bounds its mathematical error relative to p(B).
This does not certify floating value evaluation, root-finding tolerances or the
reported numerical agreement. No new floating solve was run in this packet.

The actual negative-derivative criterion is also derived:

```
V'(B)<0 iff 0<B<S(0),  S(0)=sum_i demand_i(0).
```

Here B>0 is the exported theorem's domain guard. At and above S(0)>0 the
actual derivative is zero, including an active constraint at equality.
Binding alone still does not imply a positive multiplier or strict sensitivity.

## Independent laws and constructive return

For x,y>=0, exact subtraction in the original marginal gives

```
g(x)-g(y) = w*(y-x)/[(1+x)(1+y)] + c*(y-x).
```

For x<=y and w>=0, the denominator is at least one, so this difference lies
between `c*(y-x)` and `(w+c)*(y-x)`. The two-sided bound does not need a sign
assumption on c; strict antitonicity uses c>0. Previous demand stationarity
and lower-bound complementarity, combined with this strict marginal order,
prove that the original clipped-root demand is antitone in price, including
its zero branch. No demand or price ordering is supplied as a premise.

Now take 0<B<C. The existing support theorem gives p(C)<=p(B). If the prices
are equal, the difference estimate is immediate. Otherwise p(B)>0; actual
budget complementarity gives `mass(x(B))=B>0`. Finiteness supplies a positive
patch i. Demand ordering gives x_i(C)>=x_i(B)>0, so both actual patch
stationarity equations read g_i(x_i(B))=p(B) and g_i(x_i(C))=p(C).
The marginal bound yields

```
p(B)-p(C) <= (w_i+c_i)*(x_i(C)-x_i(B)).
```

All component increases are nonnegative, so this component increase is at
most total increase, which is at most C-B by actual feasibility at C.
Since w_i+c_i<=K, the uniform price estimate follows. This still works if
the larger budget is slack. Empty patch sets cause no gap: the unequal-price
branch would require a positive mass and thus a patch, so only the equal-price
zero branch is possible. The theorem covers empty finite families.

The previous actual cost-value support inequality is applied at both B and C.
It traps the Taylor remainder between zero and
`(p(B)-p(C))*(C-B)`, which the new price estimate bounds by K*abs(C-B)^2.
At a positive B, nearby C are positive. The squared increment is little-o of
the increment, so this explicit remainder constructs `HasDerivAt V (-p(B)) B`.
Price continuity then gives C1 and the Lipschitz derivative. The original
selected optimizer, objective, price and cost value remain unchanged; no
smooth surrogate is substituted for them.

Applying the same quadratic remainder at B+h and B-h cancels the common
first-order contribution. The difference of two remainders in [0,K*h^2]
is in [-K*h^2,K*h^2], proving the central error bound K*h/2.

## Exact controls and evidence

Three concrete exact returns check the sign and boundary:

- The existing heterogeneous two-patch demo at B=3 has its unchanged KKT
  price 1, and the new actual `HasDerivAt` certificate has derivative -1.
- The existing changed-weight demo has the same allocation and B=3, price 2,
  and actual derivative -2. Uniformity does not make the price value or value
  derivative invariant to objective parameters.
- One patch with w=2,c=1,b=0 at B=1 has x=1, an active budget, price zero and
  a constructed zero derivative. This rejects an active-implies-positive
  price or active-implies-strict-sensitivity target inside the original family.

The full default build passes 8104 jobs with warnings treated as errors. All
21 new theorem statements and transitive axiom closures are freshly checked.
The standard-only cumulative audit has 895 ordered declarations: the exact
immutable earlier 874 prefix plus fresh 21 suffix, with old proof/toolchain
identity checked. The full cumulative audit command was not rerun in this
packet. Allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.
Raw suffix, combined audit, statement and self-review receipts are preserved.

`python3 scripts/de_allocation_sensitivity_verify.py` checks the ordered audit,
exported statement domains, no supplied derivative/regularity inputs, protected
previous proof/receipt paths, actual pinned Lean version and mathlib source
identity, and cumulative checkout/canonical Git fingerprints. From `lean/`,
recompute with `lake build`,
`lake env lean -DwarningAsError=true manifests/check_allocation_sensitivity_statements.lean`,
and `lake env lean -DwarningAsError=true manifests/check_allocation_sensitivity_axioms.lean`.
The optional entire cumulative audit remains
`lake env lean manifests/check_axioms.lean`. Saved raw receipts must be refreshed
if recomputing the full packet. See `results/allocation_sensitivity_2026-10-03/`.

The price selector can be nonunique at B=0; this packet neither regularizes its
choice there nor claims a zero-budget derivative. Price differentiability or
C2 regularity of the value is not asserted. No Schur-budget equivalence, general
convex-duality mechanization or physical Lambda identification is inferred.
The paper's broader unresolved and contradicted claims remain as documented.
This packet strengthens the original carrier calculus and removes a supplied
differentiability premise, without a new downgrade.
