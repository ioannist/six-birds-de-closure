# Exact extended-objective scalar closure price, 2026-10-03

Baseline: `accb5e8`. Paper, original runtime, prior proofs and evidence are
unchanged. Review is adversarial self-review, not independent review.

This packet closes the extended-real objective-domain reduction left open by
the previous scalar convex-price construction. It does not claim the separate
subdifferential/normal-cone sum rule or the matrix/Loewner dual construction in
`math/DERIVATION_LT1_2026-06-02.md`.

## Exact theorem and actual infimum

Let A be the original admissible set in a real module, J an EReal-valued
objective that never equals minus infinity on A, and energy a real-valued
convex function on A. Assume the ordinary real epigraph

```
{(x,r) : x in A and J(x)<=r, r real}
```

is convex. This is the usual extended-objective convexity condition. Define
the actual original value by the complete-lattice extended-real infimum

```
V(B) = inf {J(x) : x in A, energy(x)<=B}.
```

Suppose an ordinary finite primal optimizer star exists, V(T) is neither
plus nor minus infinity on some open interval containing B, and the actual
finite value has derivative d<0 at B. The formal derivative is of
`T -> (value A J energy T).toReal`, with those finite-neighborhood guards.
It is not the derivative of an arbitrary supplied value or dual field.

Then `ExtendedClosurePrice.positive_price_certificate` constructs

```
price=-d>0,
energy(star)=B,
price*(energy(star)-B)=0,
J(star)<=J(x)+price*(energy(x)-B)  for every x in A,
actual extended dual infimum = actual extended primal infimum.
```

The Lagrangian objective comparison and both infima use EReal, including the
original plus-infinity objective values. The constructed dual is finite:
its value equals the finite attained primal objective. Nonnegative competing
prices obey weak duality without a real lower-bound guard, since their actual
complete-lattice dual infimum may safely be minus infinity. This does not
interpret a real default value for an unbounded infimum as a finite dual price.

No dual, constraint activity, convex finite-domain record, value-support law,
or equality between original and reduced infima is supplied as an input.
Original optimizer existence, actual local finiteness and differentiability
remain explicit premises. The theorem needs neither closedness, finite
dimension nor Slater after these premises are given; it does not assert that
Slater alone establishes them. The usual proper closed convex objective with
the original conditions satisfies the needed epigraph/no-bottom conditions.

## Earned reduction and return

The finite objective domain is

```
F = A intersect {x : J(x) is not plus infinity}.
```

Under the no-minus-infinity premise this is exactly the ordinary effective
domain in A. Mixing the finite epigraph points `(x,J(x).toReal)` proves both
convexity of F and convexity of the real objective on F. The reduced objective
is `realObjective J x = (J x).toReal`, used only on this earned domain.

If the actual V(B) is finite, its feasible set contains a finite-cost point:
otherwise all original costs are plus infinity and their complete infimum is
plus infinity. The real feasible costs are bounded below by V(B).toReal.
Thus both real-infimum guards follow from actual original value finiteness.

`value_domain_return` proves the exact equality

```
V(B) = coe (inf {J(x).toReal : x in F, energy(x)<=B}).
```

The forward inequality uses an actual finite feasible point and the real
greatest-lower-bound property; the reverse treats plus-infinity candidates
separately and compares only finite values with real coercions. The equality
is not a definition or an assumed bridge. Its local version transfers the
actual original derivative to the reduced real infimum. Ordinary optimizer
optimality also returns to F. The previous constructed scalar theorem then
supplies the price and certificate.

Finally every original candidate is restored. At finite-objective points,
the real Lagrangian inequality converts exactly to EReal. At excluded points,
plus infinity plus a finite scalar remains plus infinity, so the original
global inequality holds. Complementarity makes the Lagrangian value at star
equal J(star), earning actual extended primal/dual equality and dual finiteness.

## Actual Schur family and inhabited control

`ExtendedSchurClosurePrice.positive_schur_price` returns the theorem to

```
energy(x)=trace(W*Support.residual L (D(x))),
```

where W is PSD, native L is fixed, and D is affine. Convexity is independently
earned by the previous weighted blind-Gram theorem, including singular native
Gram ranks. The actual constructed generalized inverse is retained. The
positive-definite compatibility with the unchanged original residual and
Lagrangian is already proved in `SchurClosurePrice`. No allocation-sum budget
or physical stress-energy object is substituted.

`ExtendedClosurePriceExamples` uses the same actual singular-native Schur
energy x^2, with a genuinely extended objective

```
J(x)=(x-2)^2 if x>=0, and +infinity otherwise.
```

Its effective domain is exactly `[0,infinity)`, and its real epigraph is proved
convex. For 0<B<4 the optimizer sqrt(B), the actual value `(sqrt(B)-2)^2`,
local finiteness and derivative -1 at B=1 are all proved. The final zero-premise
example applies the generic extended Schur theorem to construct price1 and
actual finite primal/dual equality at value1. Its optimizer/value/derivative
are not assumed fields.

The false-target control deliberately omits the effective-domain restriction.
On the whole original domain, J.toReal admits x=-1 as a feasible zero-cost
point at B=1, since EReal.toReal maps plus infinity to zero. Lean proves the
unrestricted converted real infimum is zero while the actual original value
is one and J(-1) is plus infinity. This verifies why a blind conversion would
change the optimization problem. The new theorem proves the required bridge
and restriction rather than using that conversion.

## Evidence and remaining work

Full default build: 8110 jobs. All 24 new declarations have fresh statement and
transitive axiom checks with warnings treated as errors. Cumulative audit953
is the exact immutable earlier929 prefix plus fresh24 suffix, with prior
proof/toolchain identity checked. The entire cumulative command was not rerun.
Only propext, Classical.choice and Quot.sound occur; no proof holes or
native_decide. Raw suffix, combined audit, statement output and self-review
are retained. The verifier checks pinned Lean/mathlib proof bytes, all previous
protected artifacts, semantic declaration domains and cumulative fingerprints.

From `lean/` run `lake build`, then
`lake env lean -DwarningAsError=true manifests/check_extended_closure_price_statements.lean`
and `lake env lean -DwarningAsError=true manifests/check_extended_closure_price_axioms.lean`.
Run `python3 scripts/de_extended_closure_price_verify.py` from the repo root.
Receipts are in `results/extended_closure_price_2026-10-03/`.

No original carrier, solver, RNG reification or Python test suite was rerun.
The general scalar extended-objective price and global Lagrangian statement
are now mechanized. Separate qualified subdifferential/normal-cone splitting,
matrix/Loewner pricing and physical Lambda identification are not supplied by
this packet. The broader paper remains incomplete at its recorded boundaries.
This is a constructive extension of the scalar theorem, with no new downgrade.
