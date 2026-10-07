# Nonlinear escape for the unchanged native complex update

Baseline7cc37e1. This construction supplies the previously missing nonlinear
bridge from an actual expanding real eigenmode to local instability. It concerns
arbitrarily close unit complex starting states and the unchanged native update,
including its original phase convention. It does not identify the frozen seed's
basin or its finite60-step outcome. Paper and runtime remain unchanged.

## Earned quadratic error and finite tracking

For a C2 map f at a fixed point, the derivative is C1 and locally Lipschitz.
The mean-value inequality on convex balls therefore earns
||f(x)-f(0)-Df(0)x||<=K||x||^2. `c2_quadratic_remainder` constructs an actual
positive radius and nonnegative K; this is not a supplied remainder hypothesis
of the final C2 or native theorem.

Translate the fixed point to0. Suppose L=Df(0), Lh=l*h, ||h||=1, R=|l|>1,
and ||L||<=M<R^2. Choose A>0 with4K+MA<=AR^2 and a small s>0 with
As<=1/2. For initial x0=d*h, let yk=d*l^k*h. If d*R^N<=s, finite induction gives

    ||f^[k](x0)-yk|| <= A*(d*R^k)^2,
    ||f^[k](x0)|| <= 2*d*R^k                 (0<=k<=N).

The one-step bound uses the actual linear norm: error_next<=M*error+K||x||^2.
The inequality4K+MA<=AR^2 closes the induction, since ||x||<=2*d*R^k.
Choose d=s/R^N. At the final step, ||f^[N](x0)||>=s-As^2>=s/2, while d tends
to0 as N increases. The radius s is fixed before the arbitrarily small initial
neighborhood is chosen. This is the correct local-instability quantifier order.
`c2_eigenmode_escape_within` also keeps every finite iterate within any prescribed
positive radius B by choosing2s<=B.

The gap ||L||<R^2 is stronger than the usual spectral-instability criterion.
It is explicit and sufficient here; no Jordan form, diagonalizability or
unearned invariant splitting is used. The construction is not asserted for
every map having an eigenvalue outside the unit disk.

## Unit inputs, actual native derivative, and legal execution

The first linear perturbation need not be normalized. `c2_eigenmode_output_escape`
starts the returned orbit at z=f(x0) instead. Continuity at the fixed point makes
z arbitrarily close, and f^[N-1](z)=f^[N](x0) gives the same escape. Any property
of legal outputs can then hold at the initial returned state.

The native normalization helpers prove that a legal native update has complex
norm square1, using the actual normalization formula and the nonzero denominator
earned from the tolerance guard. Zero denominators are not treated as executions.

`displacementMap` is the actual native update expressed in an arbitrary fixed
continuous linear coordinate equivalence and translated to the actual fixed
point. Its fixedness, C-infinity smoothness, actual derivative and exact iteration
conjugacy are derived from the existing native return theorems. Smoothness uses
the earned local phase and normalization guards, retaining the source's
conjugate-first phase convention.

`native_complex_local_escape` explicitly assumes an actual unit ground fixed
field, tolerance in[0,1), a unit real eigenvector of the actual coordinate
derivative with R>1, and the actual coordinate derivative norm<R^2. It then
constructs a fixed s>0 such that every initial neighborhood contains a unit
complex z whose finite native orbit reaches coordinate distance>=s/2. Every
iterate up to and including escape has active phase and legal normalization.
The neighborhood is stated in the explicit coordinate norm, which is equivalent
to the original norm because the coordinate map is a continuous linear
equivalence. The complex packing is not incorrectly called an isometry.

No nonlinear remainder, escape conclusion, normal-form hypothesis or assumed
native derivative is supplied in this final theorem. The root/fixedness and two
linear spectral inputs remain visible, meaningful premises of this general
analytical bridge; their concrete numerical kernel instantiations are separate.

## Return to the original couplings and remaining scope

The immutable exact sample certificates have actual transformed real derivative
row norms below1.430535 at20 and2.484326 at30. Their real eigenvalue brackets
are(-1.44,-1.42) and(-2.49,-2.47). The imaginary block norms are below0.500000003.
The proved product operator-norm return therefore permits M=3/2 at20 and M=3
at30, with M<R^2 in both cases. Normalize the nonzero real eigenmode and extend
it by zero in the imaginary block; the actual native derivative mode return
supplies the full mode. Combining these exact historical certificates with this
analytical bridge establishes mathematical local nonlinear instability at20/30.
The old Python numeric replay is not represented as fresh in this packet.

The concrete sample thin-box identities, row bounds and bracket determinant
signs are still not all instantiated in the Lean kernel. There is no closed
no-spectral-premise theorem at20 or30 in this packet. The[0,30] positive ground
branch itself already has complete kernel tube/anchor/coverage instantiation.

Local instability means some arbitrarily close unit inputs leave one fixed
neighborhood in finitely many legal steps. It does not mean all inputs leave,
unbounded amplitudes, a frozen-seed outcome, a first/simple/transverse crossing
or all-interval instability. The branch fixed point itself persists, and15 has
prior local attraction. The literal kappa>=15 runaway interpretation remains
false; no new claim is made about the separate physical Lambda bridge.

18 fresh statement/axiom checks and full build8783 are required. Cumulative2477
preserves2459 immutable closures and adds18 fresh standard-only closures. A
distinct adversarial self-review and exact provenance/commit gates accompany
the construction. The original-paper goal remains incomplete.
