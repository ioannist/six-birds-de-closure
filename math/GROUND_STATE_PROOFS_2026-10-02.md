# Native ground-state existence and solver-budget demarcation, 2026-10-02

Baseline: `5b228e9`. The paper and frozen experiment artifacts are unchanged.
This is mathematical construction and adversarial self-review by one reviewer,
with local Lean kernel checking and independent floating calculations. It is
not independent human review or a derivation of a physical cosmological value.

## 1. Exact target and source bridge

The original paper section 6 calls the Step54 background family blind and the
coupling sweep a genuine admissibility boundary: convergence at kappa<=10,
runaway at kappa>=15. The imported algorithm does not establish these stronger
claims. Its four residuals are checked only after 60 damped iterations.

The actual eight-site Step26 Hamiltonian is

```
(K u)_i = u_i - (u_{i-1}+u_{i+1})/2,   indices modulo 8,
(G u)_i = (u_{i+1}-u_{i-1})/2,
v_i(u;b,k) = b_i + k [ |(G u)_i|^2 + b_i |u_i|^2 ],
H(u;b,k) = K + diag(v(u;b,k)).
```

The pinned source is the vendored
`step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py`,
SHA256 `391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd`.
Both its kinetic matrix and gradient are independently reconstructed in
`scripts/de_ground_state_checks.py`. The gradient and sourcing bridge is tested
on 24 complex fields at three couplings. The written theorem concerns this
exact finite model over real/complex numbers, not rounded machine arithmetic.

Each source iteration diagonalizes H, finds its lowest unit eigenvector phi,
then normalizes `(1-m)u+m phi` after its declared phase adjustment. The unitary
step is computed for a norm audit but is not used in this update. The sourcing
residual subtracts the same expression from itself; it is identically zero in
exact arithmetic and is not an independent self-consistency condition.

## 2. Positive ground selector: existence, simplicity and continuity

For every finite real vector v, write H_v=K+diag(v). For real u,

```
u^T H_v u = (1/2) sum_i (u_{i+1}-u_i)^2 + sum_i v_i u_i^2.       (1)
```

The identity includes the wrap edge. It is directly proved for all real v,u
in Lean as `GroundState.energy_identity`.

The continuous Rayleigh energy has a minimum on the compact real unit sphere.
The finite-dimensional spectral theorem (or constrained differentiation)
identifies its minimizers with unit vectors in the lowest eigenspace. Replacing
u by |u| preserves its norm and diagonal energy, and cannot increase the kinetic
energy because `||a|-|b||<=|a-b|`. A nonnegative unit ground vector therefore
exists, with no sign assumption on v.

Such a ground vector is strictly positive. If u_i=0, its eigen-equation gives
`u_{i-1}+u_{i+1}=0`. Both neighbors are nonnegative, so both vanish. Repeating
around the connected cycle gives u=0, contradicting unit norm. In fact this
argument proves positivity for any nonnegative normalized eigenvector of this
matrix. Its exact eight-site version is mechanized in
`normalized_nonnegative_eigen_positive`.

The lowest eigenspace is one-dimensional. Otherwise a nonzero linear
combination w of two ground eigenvectors can be chosen with one coordinate
zero. Normalize w. Its coordinatewise absolute value is still a Rayleigh
minimizer by the preceding inequality, so is a nonnegative ground eigenvector
with a zero coordinate. That contradicts strict positivity. Consequently there
is a unique positive unit ground vector g(v).

This selector is continuous on all of R^8. If v_n->v, the vectors g(v_n) lie in
the compact nonnegative unit sphere. Every convergent subsequence has a unit
nonnegative limit u. The minimizing inequality

```
g(v_n)^T H_{v_n} g(v_n) <= w^T H_{v_n} w
```

for each fixed unit w passes to the limit, since matrix entries and the finite
quadratic form are continuous. Hence u is the unique positive unit ground
vector g(v). All cluster points are g(v); compactness then gives convergence
of the whole sequence. Sequential continuity implies continuity here. No
uniform spectral gap is assumed in this argument.

## 3. All-background, all-coupling existence

**Theorem (mathematical proof, not a local Lean declaration).** For every
`b in R^8` and every `k in R`, there is a strictly positive real unit vector u
which is a lowest eigenvector of its own H(u;b,k).

Let Delta be the closed probability simplex
`{p_i>=0, sum_i p_i=1}`. It is nonempty, compact and convex. The coordinate map
`s(p)_i=sqrt(p_i)` is continuous, including at the boundary, and takes Delta
to nonnegative unit fields. Construct

```
F(p)_i = g(v(s(p);b,k))_i^2.
```

Sourcing is a finite polynomial on real fields and g is continuous by section 2.
Thus F is continuous. It takes Delta into its interior, since g is strictly
positive and normalized. Brouwer's compact-convex fixed-point theorem yields
p*=F(p*). Because the ground representative is positive,

```
u*=sqrt(p*)=g(v(sqrt(p*);b,k)).
```

This is the required self-consistent ground state. There is no smallness,
positivity, convergence-rate, uniqueness-of-solution, or stability premise on b
or k. In particular the original nonconstant background template plus every
finite scalar offset is covered, not only a different constant template.

The imported endpoint is the standard finite-dimensional compact-convex
Brouwer theorem. Its hypotheses and full proof are available in the primary
[Isabelle/HOL `Brouwer_Fixpoint` theory](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/HOL/HOL-Analysis/Brouwer_Fixpoint.html#Brouwer_Fixpoint.brouwer).
The simplex is lower-dimensional in R^8; the theorem used requires nonemptiness,
not nonempty ambient interior. This is a mathematical import, not a transfer
of an Isabelle proof into this repository's Lean trust base. The pinned mathlib
does not expose a Brouwer theorem in the searched source; this packet adds no
axiom or proof-carrying substitute for it. A separately published Lean proof was
located during review but has not been imported or transitively audited here.

The real solution also is a complex ground state. Write w=a+ib. Since H is
real symmetric, `w* H w=a^T H a+b^T H b`, and each summand is bounded below
by the lowest real eigenvalue times its squared norm. Thus no complex vector
has lower Rayleigh energy. Simplicity gives the same ground ray over C.

At the positive representative u*, the source's phase adjustment returns u*
from either real sign of its eigenvector. Every normalized damped update fixes
u*, and its update, ground-map, eigen and sourcing residuals are all exactly
zero. The norm check on its unitary step also passes. This proves existence of
an exact admissible fixed-point witness at every finite parameter if
admissibility means existence with these residuals zero. It does not prove that
the frozen solver finds that witness from its fixed initial field and budget.

This endpoint removes an existential value selector from the stated audit;
it does not forbid a new selector, identify indistinguishable full dynamical
records, or prove that the equations ignore b. The equations depend on b, as
already shown by `BackgroundSelection.background_shift_not_scalar`. Both the
background and the coupling possess solutions. The original background-versus-
coupling distinction cannot be restored as an existence/nonexistence boundary.

## 4. Exact constructed sector in Lean

The constant-background specialization is fully constructed locally. For
`b_i=B` set `u_i=sqrt(1/8)`. Its norm squared is one, G u=0, and

```
v_i = B+k B/8 = c,
H_v u = c u,
w^T H_v w = kineticEnergy(w) + c ||w||^2 >= c ||w||^2.
```

The last inequality proves ground minimality for every real test field, not
only the eigen equation. Lean constructs this witness for every B,k in R,
including negative and zero parameters. `constant_background_no_forced_value`
returns this construction to the existing `ForcesValue` predicate: existence
alone cannot force one constant background. No assumed ground witness is
smuggled into that theorem. This local sector does not replace the original
nonconstant template; the latter is covered by the distinct written proof.

`relaxed_fixed_iff` concerns affine relaxation before normalization.
`normalizedRelaxed_fixes` separately proves that a unit fixed point survives
the actual normalization. It asserts no converse for an arbitrary normalized
map. No global convergence or all-background Lean existence is claimed.

## 5. Native phase-sign error and constructive correction

The source computes `z=vdot(candidate,reference)` and multiplies candidate by
`exp(-i arg z)`. Numpy conjugates the first argument. To minimize the distance
to reference the multiplier must instead be `z/|z|`, or `exp(+i arg z)`.
Indeed for candidate a and reference b,

```
||alpha a-b||^2 = ||a||^2+||b||^2 - 2 Re(conj(alpha) <a,b>),
```

which is minimized over |alpha|=1 at alpha=z/|z| when z is nonzero. At zero
overlap all phases have equal distance.

Take the uniform positive unit ground vector a and b=i a. They are the same
ray, but the native helper returns -i a and a gap of 2. The corrected helper
`align_ray` returns i a and zero gap. Thus the native `fixed_point_gap` is not
a generally valid phase-invariant ray distance. Its damped update is also not
globally equivariant under changing the input's phase, away from fixed rays.
The undamped map still induces the correct map of rays: its output phase does
not change its output ray. The existence proof returns a positive real witness
where the phase-sign issue does not invalidate the fixed-point conclusion.

The pinned native source and legacy CSVs remain historical artifacts. The
corrected helper is implemented and tested locally, including distance
minimality, candidate/reference phase covariance and the zero-overlap control.
Its use is not retroactively attributed to any frozen run.
Future `math_review_recompute.py` source checks now also use the corrected
helper for their explicitly phase-aligned state distance and disclose its source.

## 6. Budget reruns and analytic stability diagnostic

Fresh execution of the pinned source reproduces background passes 15/18 at
60 steps and 18/18 at 120, at the same mixing 1/2. The former fails at offsets
-5,-3,10. Failed budgets therefore are not nonexistence certificates. Future
`step54_rederive` output labels the coupling separation as a finite-budget
pass/fail separation and explicitly declines nonexistence, runaway and
linear-stability conclusions from those rows alone.

An independently implemented real positive continuation with mixing 1/5
finds approximate solutions at all 18 offsets and all 12 coupling samples.
The 30 witnesses are stored with their fields and residuals. These computations
are not interval certificates or a substitute for the mathematical theorem.
The continuation initialization is declared as uniform; no uniqueness of the
branch is asserted. The source repair Q7 reports multiple branches at offset -8.

There is also an independent analytic check of the numerical stability map.
At a real positive solution u=g(v(u)), let H have orthonormal eigenvectors
g,u_1,...,u_7 and eigenvalues e0<e1<=...<=e7. Define

```
R = sum_{j=1}^7 u_j u_j^T/(ej-e0),
dv[h]_i = 2k [ (G u)_i (G h)_i + b_i u_i h_i ],
Dg[h] = -R diag(g) dv[h].                                  (2)
```

Equation (2) follows by differentiating H g=e0 g, projecting onto each excited
eigenvector, and using g^T Dg=0 from normalization. The excited eigenvalues
may coincide; only the ground eigenvalue must be simple, as section 2 proves.
At a real field imaginary tangent perturbations have zero first-order sourcing.
Removing radial and global-phase directions therefore gives a seven-dimensional
real block and seven zero imaginary modes for the ground-ray map.

For the locally normalized relaxed map at that positive representative,
its projective tangent derivative is `(1-m)I+m Dg`: normalization removes the
radial derivative, which is zero on these tangent directions at the fixed
point. A mode t consequently becomes `1-m+m t`. For real t and m>0, Lean
proves its exact stability inequality `1-2/m<t<1`. The t=-2 control is unstable
undamped but stable at m=1/2. This scalar law is separate from construction of
the Jacobian and its numerical eigenvalues; it supplies no universal damping
guarantee for every parameter. For the source's phase-sign bug, the discarded
global-phase direction is not a true symmetry direction of its relaxed map;
these diagnostics describe the local positive representative/projective slice.

The analytic block agrees with centered differences at epsilon=1e-6 within
3.4e-9 across all 30 points. The sampled undamped-map unstable backgrounds are
5,8,10; sampled unstable couplings are 10,15,20,30, even though the frozen
60-step solver passes coupling 10. Stability is branch- and map-dependent.
These are floating spectral diagnostics, not rigorously located crossings.
Both parameters can affect stability. A physical criterion selecting this map
and stability notion remains an additional model obligation.

## 7. Self-review and continuation boundary

The positive-ground proof checks actual cycle connectivity; its return checks
the original sourcing and complex ground domain. The compact-convex law is
applied to a constructed continuous map, not to an assumed self-consistent
ground selector. Ground selection for a supplied linear H is proved before
applying it to nonlinear sourcing. No variational energy for the nonlinear
model is assumed: its sourcing need not be a gradient of such an energy.

The local Lean coverage is 20 theorems: exact cycle energy and positivity,
constant-sector ground construction and nonselection, and relaxation controls.
The all-background theorem's topology/spectral continuity construction remains
outside local Lean. The original existential coupling-boundary wording is
false under the existence interpretation; its finite-budget observation and a
scoped stability alternative survive. The all-computations background-blindness
claim, unrestricted no-selector claim and physical Lambda bridge remain
unproved or false as previously documented.

The user requested a pause at this clean checkpoint. After the verification
and commit, resume from this packet rather than restarting the review. Useful
next work is to assess a rigorously certified, explicitly chosen stability
criterion and audit the located external Lean Brouwer dependency before any
formal import. A phase-corrected computation would be a new run, with distinct
provenance, and cannot be substituted for the frozen source output. Paper
revision, physical identification and replacement of false main statements
remain deferred to the user-authorized later phase.
