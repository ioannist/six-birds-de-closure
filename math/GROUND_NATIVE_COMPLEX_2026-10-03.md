# Original complex ground update: local convergence and source controls

The unchanged Step26 phase rule now has an exact mathematical representation
and a Lean proof of local convergence in all sixteen real coordinates, with
its phase and normalization guards maintained at every iterate. The phase
sign bug is retained. Combining the analytic theorem with exact computational
certificates earns complex local attraction at all 28 previously stable
original samples, including coupling 15. The two real unstable modes at 20
and 30 persist in the complex derivative. This does not establish the frozen
complex initialization's basin or a continuous nonlinear branch.

## Source, domain and guards

The frozen source is
`external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py`.
Its SHA-256 remains
`391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd`.
The source uses the eight-site periodic central gradient and the real potential

```
v_i(z) = b_i + κ (|Gz_i|² + b_i |z_i|²).
```

The real symmetric Hamiltonian is diagonalized with `np.linalg.eigh`; the
real lowest eigenvector is then cast to complex. `GroundNativeControls`
derives that any real unit lowest eigenvector is the selected positive ground
or its negative. On the active overlap branch both signs give the same
native aligned result. Arbitrary complex eigensolver phase choices are not
assumed equivalent.

The source computes `c = vdot(candidate, reference)` and multiplies the
candidate by `exp(-i arg(c))`. `GroundNativePhase.native_factor` proves that
this factor is `conj(c)/|c|` when c is nonzero. This is the source's existing
sign error. The corrected `align_ray` helper from a prior packet is not used
or attributed to the frozen source here.

`nativePhase` retains the threshold branch; `nativeUpdate` mixes and
normalizes exactly as the mathematical version of the source does.
`ActivePhase` requires overlap modulus above the threshold, while
`NativeLegal` requires the actual mixed field's Euclidean norm above it.
The original binary64 threshold `1e-10` is reified as

```
7737125245533627 / 77371252455336267181195264.
```

Lean proves this is in [0,1). The analytic theorems work for every threshold
in that interval. At every positive unit actual fixed point, overlap and
mixed-field norm are both one. Continuity earns both guards on a neighborhood.
No field obtained by totalizing division at zero is attributed to source
execution; the source raises there.

The state space is `Field × Field`, real and imaginary parts, with a proved
real continuous linear equivalence to `Fin 8 → ℂ`. This equivalence is not
claimed isometric: the product sup norm differs from the complex sup norm.
The normalization uses the sum of squared real and imaginary coordinates,
proved equal to the complex Euclidean norm squared. The convergence theorem
returns through the equivalence to the original complex field topology.
All derivatives here are real Fréchet derivatives, not holomorphic derivatives.

## Earned full derivative and nonlinear return

For a positive unit actual ground-map fixed point u, let J be the actual
ground-map derivative earned in the previous source/Jacobian construction.
For perturbation `(a,c)`, complex sourcing has derivative depending only on a.
The original aligned candidate has derivative

```
(J a, -u dot(u,c)).
```

Normalization removes the real radial component but preserves the imaginary
phase component. The actual native normalized derivative is

```
(normalizedJacobian b κ m u a, (1-m)c - m u dot(u,c)).
```

These are derivatives of the actual original threshold/exp phase map because
an eventual equality with its smooth ratio representation is proved locally,
including the guard conditions. Imaginary tangent modes have multiplier
1-m; the imaginary phase mode has multiplier 1-2m. At half mixing the
imaginary block is exactly `(I-u uᵀ)/2`. Every real eigenmode embeds into
the full derivative by `(h,0)`, so real unstable modes remain unstable.

`GroundNativeLocal.native_complex_local_attraction_of_rows` takes fixed real
and imaginary continuous linear coordinate equivalences and strict row bounds
on the earned blocks. It proves an actual invariant neighborhood, convergence
of every complex initial field in that neighborhood, and both guards at every
native iterate. The generic construction also gives geometric coordinate
distance bounds. No convergence or invariant-basin premise is supplied.
Exact conjugacy is proved for every iteration count.

The all-background/all-coupling Brouwer existence theorem now returns to legal
fixed points of the original complex update for every real mixing value and
every threshold in [0,1). Stability is a separate question.

## Exact original-sample certificates

`scripts/de_ground_native_certificate.py` freshly replays the previous exact
root and real-spectrum certificates without modifying them. For each of the
30 original root boxes it proposes a fixed dyadic imaginary coordinate basis
using pinned NumPy 1.26.4. Replay uses integer intervals at scale 2^80 and
exact Fraction inversion of the fixed basis. It encloses `(I-u uᵀ)/2` on
the entire certified root box and bounds the transformed row norm.
Generation is a proposal, not evidence until exact replay succeeds.

Every imaginary bound is below 0.500000003. The product norm is bounded by
the maximum of the real and imaginary transformed norms. Therefore all
18 original background offsets at coupling .3 and all coupling samples
through 15 have strict full derivative bounds and mathematical complex local
attraction. At 15 the full bound is below 0.911617. At 20 and 30 the previously
certified real modes below -1 remain modes of the full complex derivative.
Four false-certificate controls reject singular or wrong-size bases, wrong
root identity, and destructive enlargement of the root box.

This is a Lean-checked analytic bridge plus exact Python certificates.
The concrete sampled root, basis and interval inequalities are **not yet
instantiated as Lean kernel proof terms**. Reified original IEEE coefficients
define the mathematical model; the certificate does not emulate rounding at
every operation of the floating runtime. No numerical basin radius or
finite-60-step success bound is inferred.

## Boundary control and remaining claims

For any positive unit fixed u, the unit field `i*u` has the same sourced
Hamiltonian. Native alignment sends its real candidate to `-i*u`. At half
mixing the field cancels exactly to zero. Lean proves that overlap alignment
is active but normalization is illegal. This is an explicit boundary of
global complex convergence under the already known sign bug, not a new
local-attraction failure. No totalized next iterate is claimed as execution.

The main original claims remain incomplete or contradicted as recorded in
the cumulative claim ledger. In particular, neither the phase rule nor this
local theorem restores background blindness, an existential coupling boundary,
physical Lambda identification, or the paper's κ≥15 runaway interpretation.
Local attraction at 15 also strengthens the existing reason to distinguish a
finite-budget failure from instability of its positive fixed point.

The next concrete obligations are kernel instantiation of sampled certificates,
an original-initialization basin or finite-run certificate where feasible,
and a continuous nonlinear branch/crossing construction if needed. The paper,
frozen runtime and original data are unchanged. Review is adversarial
self-review, not independent review. The overall goal remains incomplete.
