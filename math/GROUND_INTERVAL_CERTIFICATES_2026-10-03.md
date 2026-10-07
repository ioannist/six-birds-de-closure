# Original Step26 positive-root and spectral certificates

Baseline `653ab69`. Adversarial self-review by one reviewer, not independent
review. The paper, original runtime, historical results and previous proofs are
unchanged. The new certificates address all 30 parameter arrays used in the
previous original-template positive-real audit. They do not identify a continuous
nonlinear branch between sample points or reproduce the frozen complex run.

## Carrier and analytical return

The background is the original eight-entry `potential` array loaded from the
pinned Step24 JSON by Step26. Each original background offset is applied using
the original IEEE double addition, then the resulting array is reified as exact
dyadic real numbers. Couplings are similarly reified: e.g. the original double
`.3`, rather than a silently substituted exact 3/10. The data/source hashes and
all ordered sample parameters are checked. This input bridge is computational;
it is not a Lean proof of JSON parsing or IEEE execution.

For x=(u,e), use the actual nine polynomial equations

```
F_b,k(x)=((H_(b+k*((G*u)^2+b*u^2))-eI)u, (sum_i u_i^2-1)/2).
```

The new `GroundRootCertificate` Lean module constructs this residual, its actual
C-infinity regularity and full derivative. Its derivative is the ground border
plus the source feedback term `diag(u)*Dv(u)`. A positive normalized eigenvector
is a lowest eigenvector: its overlap with the already constructed positive
ground is strictly positive, and symmetry forces equal eigenvalues. Existing
positive-ground uniqueness therefore returns a positive root of F to the actual
ground selector. Neither ground status nor a supplied numerical fixed point is
assumed by this return.

The general Lean a posteriori theorem takes an injective linear correction C,
a closed ball Q around a center x0 with radius r, q<1, and the explicit bounds

```
sup_(x in Q) ||I-C*DF(x)|| <= q,
||C*F(x0)||+q*r <= r,
all eight field coordinates positive throughout Q.
```

The actual derivative and mean-value theorem give q-Lipschitz continuity of
T(x)=x-CF(x); the displayed residual inequality earns invariance of Q. Banach's
theorem constructs its unique fixed point. Injectivity of C earns F(x)=0.
This is uniqueness of the full nine equations INSIDE Q, not global uniqueness
or uniqueness of all self-consistent ground states. The certificate bounds are
explicit hypotheses of this Lean theorem, not manufactured proof fields.

## Exact computational checks

`de_ground_interval_certificate.py --generate` uses pinned NumPy 1.26.4 to
propose centers, inverse matrices and spectral bases. Generation carries no
proof authority. Replay uses Python integers and Fraction; intervals have
endpoints at multiples of 2^-80. Addition/subtraction are exact, and products,
quotients and rational embeddings round outward using integer floor/ceiling.
Every division interval is checked to exclude zero.

Each proposed root ball has radius 2^-32. Exact interval evaluation checks
positivity, injectivity of C by exact Fraction elimination, and both root bounds.
Across all 30 points, the correction residual is <5.587e-16 and the correction
Lipschitz bound is <3.188e-8. These decimal inequalities are outward summaries
of the integer bounds recorded in `certificates.json`; every center and full
bound is retained there. The program therefore supplies checked mathematical
inputs to the written/Lean root criterion. The concrete 30 instantiations are
NOT Lean kernel proofs: correctness of the Python checker and its arithmetic
implementation remains part of their foundation.

For every root box, the original ground border B is interval-evaluated. A
proposed inverse C_B earns a Neumann bound from E=I-C_B B and ||E||_infinity<1.
Thus B^-1=(I-E)^-1 C_B and

```
||B^-1-C_B||_infinity <= ||E||*||C_B||/(1-||E||).
```

An entrywise enclosure follows from this operator bound. The actual selector
derivative is obtained by solving the earned bordered equation. Composing with
the original source derivative earns J, the full real ground-map derivative.
At a positive unit fixed point the actual half-mixing ambient derivative is

```
A = (I-u*u^T+J)/2.
```

This formula is also proved in Lean. It uses tangency of J. A has tangent range;
the induced radial quotient is zero. The vector u itself need not be a zero
eigenvector: source feedback can couple a radial input to a tangent output.
The checker retains these full matrix entries rather than projecting an
approximate root onto an approximate seven-dimensional tangent basis.

For stable points, a fixed rational invertible basis S is checked by exact
elimination. Interval arithmetic bounds the infinity norm of S^-1 A S strictly
below one. This bounds every complex eigenvalue of the real ambient matrix,
hence all its actual real tangent modes. Candidate complex-conjugate eigenvectors
are converted to a real two-column basis during proposal generation; no real
diagonalizability or computed eigenvalue is assumed by replay.

For the two unstable points, interval Gaussian elimination proves opposite
strict signs of det(A-tI) at rational endpoints below -1. Determinant continuity
and the intermediate-value theorem give an actual real eigenvalue in the
bracket. Since A has tangent range and this eigenvalue is nonzero, a corresponding
nonzero real eigenvector is tangent. This is an earned unstable mode, not an
inference from an approximate eigensolver. It does not prove nonlinear global
escape, runaway, lack of fixed points or failure of every starting orbit.

## Results and limits

All 18 original background offsets at coupling `.3` have a spectrally stable
positive root for half mixing. All 12 original coupling samples have a certified
positive root; couplings through 15 have a stable real tangent spectrum, while
20 and 30 have an unstable real tangent mode.

| Original sample | Certified result for the positive real half-mixing map |
| --- | --- |
| All background offsets, -8 through 10, k=.3 | Spectrum strictly inside the unit disk |
| k=0,.1,.3,.5,1,2,3,5,10 | Spectrum strictly inside the unit disk |
| k=15 | Spectral radius <0.911617 |
| k=20 | A real tangent eigenvalue in (-1.44,-1.42) |
| k=30 | A real tangent eigenvalue in (-2.49,-2.47) |

These are certificates for isolated roots close to the historically proposed
positive solutions. Closeness and uniqueness in small boxes do not certify that
all points lie on a single continuously followed nonlinear branch. No precise
crossing parameter or interval between 15 and20 is certified.

The original 60-step tolerance failure at15 remains a historical finite-budget
fact; it cannot be promoted to instability of this positive root. This confirms
the previously identified limitation of the paper's k>=15 runaway reading;
no newly supported claim is downgraded. The earlier all-parameter existence
theorem still rules out an existential coupling boundary.

For a C1 map, a strict derivative norm bound in a suitable fixed coordinate
norm also yields local attraction by continuity and a smaller invariant ball.
The present packet records the spectral certificates and the exact derivative
bridge. It does not mechanize that nonlinear local-orbit argument or establish
a basin containing the original frozen complex initialization. There are no
certificates for imaginary/projective modes, the erroneous frozen phase rule,
physical Lambda, background blindness or unrestricted selector impossibility.

## Verification

Full `lake build` passes8188 jobs with warnings as errors; 11 new statements
and their transitive standard-only axiom closures are freshly checked.
Cumulative1655 consists of the immutable1644-declaration raw prefix and these
11 fresh closures. The full cumulative command is not rerun.

`de_ground_interval_verify.py` independently differentiates all nine polynomials
at each of the30 centers by exact forward automatic differentiation (2430
derivative coefficients). It checks445 exact arithmetic containments, including
wide signed intervals, and rejects six false certificates: displaced center,
inadequate radius, singular Newton inverse, unstable relabelled stable, stable15
relabelled unstable, and changed original coupling. These are adversarial
self-review controls, not independent human review. Source/toolchain provenance
and532 fingerprints are checked. Only trailing receipt whitespace is normalized;
all diagnostic text is retained. The full Python suite is not rerun.

The original-target goal remains incomplete. Concrete kernel interval proofs,
nonlinear local dynamical return and, if needed, continuous branch/crossing
certification are constructive next steps; previously false or project-sized
universal claims remain separately identified.
