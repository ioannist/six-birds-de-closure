# Original allocation carrier: exact optimization and price proofs

Baseline: `7544d54`. This packet strengthens the mathematics of the **original**
`scripts/de_dual_carrier.py` carrier. It does not alter the paper, introduce an
adequacy constraint into that carrier, or identify its price with a physical
cosmological constant. Review is adversarial self-review by one reviewer.

## Frozen target and exact statement

For any finite patch set, positive real weights w_i and curvatures c_i, finite
offsets b_i, and budget B>=0, maximize

```
U(x) = sum_i [w_i log(1+x_i) - c_i x_i^2/2 + b_i x_i],
x_i >= 0, sum_i x_i <= B.
```

The original script uses a common b_i=b. Allowing heterogeneous b_i strengthens
the mathematical theorem and includes the original objective directly.
`AllocationPrice.lean` constructs a KKT solution for every such input, proves
global optimality and uniqueness, and derives the budget-price supporting
inequality. It includes zero and slack budgets and does not assume Slater or
optimizer existence. Its cost-value derivative theorem **assumes**
differentiability at B>0, exactly as the paper-level sensitivity theorem does.

The general convex program with a Schur-energy budget remains a distinct,
conditional theorem in `math/DERIVATION_LT1_2026-06-02.md`. In particular,
`sum_i x_i` is not silently equated to `tr(W Xi)`.

## Independent law: the actual utility's tangent bound

For x,y>=0, apply log(t)<=t-1 to t=(1+y)/(1+x). This gives

```
log(1+y) <= log(1+x) + (y-x)/(1+x).
```

Multiplying by w>=0 and expanding the quadratic exactly gives

```
u(y) <= u(x) + g(x)(y-x) - c(y-x)^2/2,
g(x) = w/(1+x) - cx+b = u'(x).
```

Both the derivative and the tangent bound are proved in Lean. No optimality
conclusion is included as a hypothesis of this law.

A KKT certificate contains x>=0, sum(x)<=B, p>=0, g_i(x_i)<=p,
`(p-g_i(x_i))*x_i=0`, and `p*(B-sum(x))=0`. These imply, for every y>=0,

```
U(y) <= U(x) + p*(sum(y)-B) - sum_i c_i*(y_i-x_i)^2/2.
```

If sum(y)<=B, the middle term is nonpositive. Thus x is globally optimal.
For c_i>0, the penalty vanishes exactly when y=x, proving uniqueness. This
is an independently proved return from stationarity to an optimizer, not a
certificate structure that assumes the desired conclusion.

## Constructing the certificate

Put t=p-b. The exact patch response is

```
a(p) = max(0, [sqrt((c-t)^2+4cw) - (c+t)]/(2c)).
```

For p>=w+b it is zero and g(0)<=p. For p<w+b it is positive; squaring the
root identity proves `ca^2+(c+t)a+t-w=0`, hence g(a)=p. Therefore a(p)
satisfies both lower-bound stationarity and complementarity. It is continuous
in p. Lean also proves the algebraic identity with the Python solver's
rationalized expression

```
a(p) = 2*(w-t)/[sqrt((c-t)^2+4cw)+(c+t)]   when p<w+b.
```

The denominator is strictly positive on this branch. The negative-effective-
price branch in Python uses the direct root instead to improve conditioning.
These identities prove the exact real-arithmetic bridge; they do not establish
a bound on floating root-finding error.

Let S(p)=sum_i a_i(p). If S(0)<=B, p=0 supplies a certificate. Otherwise set
`M=1+sum_i max(0,w_i+b_i)`. Every a_i(M)=0, so S(M)=0<=B<S(0).
The checked intermediate-value theorem on [0,M] produces p with S(p)=B.
This constructs feasibility and all complementarity equations. It works also
at B=0 and for an empty patch set; the latter always uses the p=0 branch.

`selectedPrice` chooses from this **proved existence theorem**, and
`selectedAllocation` is its constructed response. At B>0, any KKT certificates
have the same allocation and price. If total allocation is positive, a
positive patch fixes the price by g_i=p. Otherwise B>0 makes the budget slack
and complementarity fixes p=0. Thus classical choice introduces no extra
value-selection premise for positive budgets. At B=0 the optimizer is still
unique, but the price can be nonunique.

## Price signatures and their boundaries

For B<S(0), the constructed price is positive: price zero would return a(0)
and violate feasibility. Complementarity then forces sum(x)=B. For B>=S(0)
and B>0, the zero-price certificate and uniqueness prove price zero. In
particular, at B=S(0)>0 the budget is active and price is zero. Binding alone
does not imply a strictly positive multiplier.

Comparing the global support inequalities at two budgets B<C proves
`p(C)<=p(B)`. At a positive allocation, g_i=p; at a zero allocation only
g_i<=p follows. Uniformity of the constraint multiplier does not require
every patch to be interior.

Define the actual constructed optimal cost V(B)=-U(x(B)). Feasibility of
x(T), the support inequality and its nonnegative penalty imply

```
V(T) >= V(B) - p(B)*(T-B)     for B,T>=0.
```

Consequently `V(T)+p(B)*T` has a local minimum at every B>0. If V has
derivative d there, the checked derivative-at-local-minimum theorem yields
`d+p(B)=0`. Thus p=-V', and V'<0 implies p>0. Differentiability is visible
in the exported theorem; a finite-difference agreement is not substituted
for it. No unrestricted convex-duality theorem is asserted to be locally
mechanized by this finite-family proof.

For a common offset s and an active allocation, g_i shifts by s. If p+s>=0,
the unchanged allocation and rebased price p+s satisfy all KKT equations,
so the global optimum is unchanged. A sufficiently negative shift violates
this admissibility condition and can make the budget slack. The original
small-offset numerical observation is preserved; unconditional screening is
not established.

## Exact controls and semantic review

The module constructs x=(1,2), c=(1,1), b=0, B=3 with w=(4,9) and p=1.
With w=(6,12), the same x and B have p=2. Both satisfy the actual KKT
conditions and therefore are globally optimal, uniquely so. This refutes
the sentence that a dual's value is set by the budget **and not local detail**
if it means independence from objective parameters. Spatial uniformity and
dependence on local weights are compatible.

With w=(4,9), b=-10, B=3, the exact optimum is x=0, p=0; the budget is
slack. At B=0, w=(4,9), b=0, both p=9 and p=10 are KKT prices. These
controls test the offset domain and zero-budget price uniqueness directly.

The adversarial pass checks the clipped-root branches, positive denominators,
zero/empty/slack cases, summation and cost signs, uniqueness, and the exact
source objective. These proofs strengthen the paper's valid finite price
signatures. They cannot restore background blindness in unchanged Step26,
contradicted measure conclusions, universal tag irrelevance, or a physical
Lambda/stress-energy bridge. The original paper remains incomplete in those
respects; see `math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md`.

The default Lean target includes this module. Fresh build and all-declaration
axiom evidence, source hashes, and the historical Python-test boundary are
recorded in `results/allocation_price_2026-10-02/verification.json`. Earlier
dated receipts remain historical snapshots.
