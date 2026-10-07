# Global native zero-coupling convergence and the original seed

Baseline: `72946bc`. This packet preserves the paper, runtime, data and previous
proof/evidence sources. Review is adversarial self-review, not independent review.

## Target and exact geometry

The previous positive-real zero-coupling theorem did not cover the original
complex initialization. This packet proves global convergence for the actual
unchanged native complex half-mixing update, for every real background, provided
the unit initial field's signed real ground overlap exceeds the source threshold.
It then populates this condition for the original seed at coupling0. It does not
replace the original phase rule with the corrected alignment helper.

At coupling0 the selected positive real ground g is independent of the current
field. Write x=(u,v) for real/imaginary parts, with sum-of-squares norm1, and put

    a = dot(g,u), h = dot(g,v), r = sqrt(a²+h²).

Orthogonal decomposition against the unit g earns r<=1. On the active source
branch the original conjugate phase sends g to `(a/r*g, -h/r*g)`. Its half-mixed
field therefore has squared norm

    d = (1-r+2a²/r)/2,

and the next normalized real ground overlap is

    a' = a(r+1)/(2r sqrt(d)).

For a>0 the exact scalar estimates prove

    a <= r <= 1,
    0 < d,  a <= sqrt(d) <= 1,  a' >= a,
    1-(a')² <= (1-a²/4)(1-a²).

All divisions are justified by earned positive r and d. The squared overlap
defect is nonnegative by the same unit-vector geometry. A useful algebraic hinge
for the contraction is

    1-a² <= (r+1)² - 2r(r-r²+2a²).

Its proof separates r>=1/4 from r<=1/4 and uses nonnegative polynomial products;
no approximate eigenvalue, smoothness, supplied Lipschitz constant or assumed
convergent orbit appears.

If a0>threshold>=0, every later a_n>=a0. Thus every overlap radius and every
mixed normalization norm stay above the same threshold. The rate
q=1-a0²/4 lies in[0,1), and induction gives

    0 <= 1-a_n² <= q^n (1-a0²).

The full real/imaginary squared distance to `(g,0)` is2(1-a_n), at most twice this
defect. The coordinate sup norm is bounded by its Euclidean sum-of-squares norm;
no isometry between those norms is assumed. This earns a geometric distance bound
and actual convergence. Exact iteration conjugacy returns through the proved
real continuous linear packing equivalence to the original complex field.

For negative signed real overlap, reflection of the earned active orbit proves
convergence to `realEmbed(-g)`, maintaining both guards throughout. The threshold
fallback remains in the native formula. There is no assertion that all unit
complex fields converge: the known pure-imaginary cancellation example is an
explicit excluded boundary, and inactive inputs can break reflection.

## Original coefficient and branch return

`GroundOriginalSeed` reifies all16 real/imaginary binary64 input coefficients
from the first original Step24 field as exact rationals. The generator checks
these against the immutable JSON source; JSON parsing itself is not proved in
Lean. The initial state explicitly includes **both** initialization
normalizations from `load_initial_field` and `run_case`. In the exact mathematical
model the first normalization is unit and the second is the same state. This
identity does not claim the two floating normalizations are bitwise identical.

Three closed rational kernel checks establish raw squared norm above1/2, an
upper bound `(101/100)²`, and the negative overlap enclosure upper endpoint below
`-101/500`. The overlap expression retains every signed seed coefficient. Its
box is the previously kernel-certified whole thin nine-coordinate root box at
original coupling0. Both actual initialization inputs are proved above the
original normalization threshold. The actual selected ground equals that identified original
branch root, by the actual zero-coupling ground-map identity; no midpoint root is
substituted.

Expression enclosure soundness therefore bounds the actual raw real overlap.
The raw norm upper bound controls its positive square-root denominator, returning
an actual normalized signed real overlap **below-1/5**. The original threshold is
below1/5. `actual_seed_zero_convergence`, with no hypotheses, proves that the
mathematical original-seed native orbit at original background/coupling0 and
half mixing converges to the **negative actual branch ground**, and that every
iterate is phase-active and legally normalized.

`positive_overlap_rejected` is a substantive false-target control: the actual
original seed does not belong to the positive-overlap halfspace used by the
positive-representative theorem. The negative return is essential, not merely
an unproved change of phase representative.

## Verification and coverage boundary

Four new modules contain44 theorems:16 geometry/actual-map returns, five scalar
estimates, ten orbit/global-native returns and thirteen seed returns/control.
A fresh full default build has8851 jobs. Fresh44 signatures and transitive axiom
closures are required, using only `Classical.choice`, `Quot.sound` and `propext`.
The cumulative2747-declaration audit retains the immutable2703 raw prefix after
source/toolchain identity checks and appends the fresh44 suffix. No full cumulative
audit command is claimed. The verifier checks exact seed regeneration, current
statements, manifests, build, pinned toolchain/mathlib and preserved sources.

This establishes the first exact original-seed basin return at a sampled
coupling, substantially beyond fixed-point existence or local attraction alone.
It concerns the mathematical model with reified original coefficients and exact
real/complex operations. It does **not** emulate IEEE arithmetic per operation,
certify the source's60-step floating convergence verdict, or derive those finite
residual thresholds from this conservative geometric bound. No Python test-suite,
old numeric-certificate replay or floating scout rerun is claimed in this packet.

The other original coupling and background-offset frozen-seed basins remain
pending, as do18 offset kernel sample instances. Further quantitative work could
sharpen the zero-coupling finite-step bound and construct a certified positive-
coupling orbit prefix or explicit attracting neighborhood. The physical Lambda
bridge and previously parked false or project-sized targets remain separate.
The overall original-paper goal is incomplete.
