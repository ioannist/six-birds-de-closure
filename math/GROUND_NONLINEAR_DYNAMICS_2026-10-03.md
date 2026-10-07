# Actual nonlinear ground-map dynamics, 2026-10-03

Baseline `ac420e8`. Adversarial self-review, not independent review. The original
paper, runtime, data, earlier proofs and certificate receipts are unchanged.
This packet closes an analytical nonlinear-return obligation and adds a direct
all-background global control. Concrete original-sample numerical bounds retain
their exact Python computational foundation; they are not Lean proof terms.

## From an actual derivative bound to actual nonlinear convergence

`GroundLocalDynamics` proves a general C1 local-attraction theorem. If f(u)=u
and ||Df(u)||<1, choose q strictly between the derivative norm and1. C1 regularity
earns q-Lipschitz continuity in a neighborhood; a positive-radius closed ball
inside that neighborhood is invariant because its center is fixed. For every
initial point y in that ball, the ACTUAL iterates satisfy

```
distance(f^n(y),u) <= q^n * distance(y,u)
```

and converge to u. The theorem constructs the neighborhood, derives invariance,
and proves convergence by the geometric bound. It does not merely assume local
convergence or convert a numerical stability label into a proof.

The original source-ground map is already C-infinity. The new module earns
C-infinity normalization away from zero, and hence earns the actual normalized
map's regularity at every unit fixed point, for every real mixing fraction.
This uses that its unnormalized mixture equals the nonzero unit field there;
smoothness of the linear selector alone is not substituted for smoothness of
normalization.

For any FIXED continuous linear equivalence S, define

```
f_S(x) = S^-1 N(S x),
A_S = S^-1 DN(u) S.
```

The actual derivative and C-infinity regularity of f_S are derived. The exact
identity `S f_S^n(x)=N^n(Sx)` is proved for every natural n. Thus ||A_S||<1 earns
local convergence of the original normalized iteration, in all eight real
directions, with geometric error in the S coordinates. The coordinate change
does not alter the update rule, its coupling, or its mixing fraction. No new
iteration or invariant alternating slice is substituted for the original map.

The finite-field norm is the sup norm. An additional theorem proves from first
principles that the maximum absolute matrix row sum bounds a continuous linear
map's operator norm. The local-attraction theorem therefore accepts the exact
row-sum bounds produced by the interval certificate checker, with every norm
bound retained as an explicit hypothesis.

Two semantic return lemmas cover the nonlinear root itself. A positive root's
ENTIRE pair (field,energy) equals the actual `groundPair` at its sourced potential;
the energy coordinate is not an unrelated numerical eigenvalue. Every solution
of its sourced bordered derivative equation returns to the actual ground-map
Jacobian. The interval computation can therefore supply a matrix enclosure of
the existing derivative, including source feedback and normalization.

## Return at the original sampled stable points

The original exact interval certificates are replayed read-only. At28 of the30
sample arrays they establish a positive self-consistent ground root, an invertible
fixed rational basis S, and an induced row-sum norm bound on S^-1 DN(u) S
strictly below1. Combining these earned inputs with the new analytical theorem
establishes existence of a nonlinear local convergence neighborhood at each of
these28 positive real fixed points. This mathematical return uses two foundations:
Lean for the analytical implication, and the exact Python checker for concrete
root/basis/row-sum inputs. None of those28 concrete Lean theorem instantiations
is claimed to exist yet.

All18 original background offsets at k=.3 and all coupling samples through15
have this local return, for original half mixing. At coupling15 the induced norm
bound is <0.911617. The paper's historical60-step tolerance failure remains a
different observation. The two certified unstable real modes at20/30 remain
linear instability certificates; no nonlinear global escape theorem follows
automatically from this local-attraction construction.

The neighborhoods are existential, not explicit numerical basin radii. There
is no claim that a frozen initialization lies inside one, that the roots form
one globally continued branch, or that a precise crossing parameter is known.
The mathematical map selects the positive real representative. For positive
convex mixing the new all-parameter invariant proves that every nonnegative
real field maps to a strictly positive unit field and that every nonnegative
unit orbit stays nonnegative and unit. This supports the real-representative
scope; it does not certify the frozen complex phase rule or its initialization.

## Direct global zero-coupling control

`GroundZeroCouplingOrbit` constructs convergence for the unchanged source at
k=0, for EVERY real background, including the original nonconstant template.
The earlier source-deletion theorem earns `groundMap(b,0,u)=positiveGround(b)`.
Let g be that positive unit ground field, let u0 be any nonnegative real unit
field, and let 0<m<=1. The actual update is

```
u_(n+1) = ((1-m)u_n + m g) / sqrt(normSq((1-m)u_n + m g)).
```

The mixture is strictly positive, so normalization is defined. Exact convex
algebra gives its squared norm

```
1-m(1-m)*normSq(u_n-g) <= 1.
```

Its overlap numerator with g is nonnegative, so division by a positive number
at most1 increases that overlap. The correlation gap delta_n=1-dot(g,u_n)
therefore satisfies

```
0 <= delta_(n+1) <= (1-m) delta_n,
normSq(u_n-g) = 2 delta_n.
```

This earns, for every n,

```
||u_n-g||_sup <= sqrt(2 * (1-m)^n * (1-dot(g,u0))).
```

The right side tends to zero. Global convergence and this explicit rate are
proved in Lean. No supplied fixed point, spectral bound, differentiability,
numerical solver, iteration budget or constant-background surrogate is used.
The endpoint m=1 is included and reaches g after one step; m=0 is excluded,
since it would preserve an arbitrary starting field. Initial normalization and
nonnegativity are explicit legitimate guards. The result is global on the
nonnegative real unit sphere, not on arbitrary signed or complex inputs.

## Verification and remaining obligations

Two new roots add40 theorems. Full `lake build` passes8190 jobs with warnings
as errors. All40 statements and transitive standard-only axiom closures are
freshly checked. Cumulative1695 preserves the exact immutable1655 raw prefix
and appends40 fresh closures; the full cumulative command is not rerun.
Original exact certificates are freshly replayed without overwriting their
immutable receipts. Earlier proof/toolchain identity and545 fingerprints are
checked by `scripts/de_ground_dynamics_verify.py`. Only trailing build/audit
receipt whitespace is normalized; diagnostic text is retained. The full Python
suite and original solver are not rerun.

Concrete kernel root/basis/norm certificates remain outstanding. So do any
desired continuous nonlinear branch or crossing certificate and a return to
the original frozen complex trajectory. No physical Lambda bridge, background
blindness, existential coupling boundary or unrestricted selector impossibility
is inferred. No newly supported claim is downgraded; full original-target
completion remains false.
