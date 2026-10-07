# Finite zero-coupling distance of the original native seed

Baseline: `f9d17d2`. Paper, runtime, data and all earlier proof/evidence sources
are preserved. Review is adversarial self-review, not independent review.

## Exact target and scalar construction

For the unchanged original native complex half-mixing map at coupling0, this
packet proves that the exact mathematical original-seed field after60 updates
has squared Euclidean distance less than `(1/500000000)^2` to the negative actual
branch ground. After59 updates it is less than `(3/1000000000)^2`. These are full
complex-field distances, not projected readouts or coordinate sup-norm claims.
The coefficients, both exact initialization normalizations, threshold branches
and all iteration guards are the ones earned in the preceding packet.

Write a,h,r,d,c for the real overlap, imaginary overlap, overlap radius, mixed
squared norm and next normalized real overlap from that packet. Under

    1/2 <= a <= r <= 1,
    d = (1-r+2a²/r)/2,
    c = a(r+1)/(2r sqrt(d)),

the sharper estimate is `1-c² <= (1/2)(1-a²)`. The algebraic hinge is

    E(A) = r³-r²+A(1+r³)-2rA² >= 0,   1/4 <= A=a² <= r².

At A=1/4 the value is

    (3/16)(1-r)+(7/8)(r-1/2)²+(5/4)(r-1/2)³ >= 0.

At A=r² it is `r³(1-r²) >= 0`. For r>1/2 the exact identity

    (r²-1/4)E(A) = (r²-A)E(1/4)+(A-1/4)E(r²)
                    +2r(r²-1/4)(A-1/4)(r²-A)

returns nonnegativity without dividing at an endpoint. The r=1/2 case is checked
separately. Positive overlap earns positive r and d before any cancellation.
The preceding exact coefficient-square identity then yields the half contraction.

Monotonicity retains overlap>=1/2 at every later step. Induction gives defect
at most `(1/2)^n` after n more steps. The exact unit-vector distance identity
returns full squared Euclidean distance at most `2(1/2)^n`.

## Earned original-seed entry

The imaginary overlap expression retains all eight signed original imaginary
coefficients, alongside the already earned real overlap expression. Their
sum of squares is enclosed on the **whole** original coupling0 certified
nine-coordinate root box. Two closed rational kernel comparisons establish

    raw squared norm > (99/100)²,
    raw overlap-radius squared enclosure upper endpoint < (207/1000)².

Expression soundness and the actual branch-to-selected-ground identity return
these bounds to the actual ground. A normalization identity earns normalized
radius<21/100. Reflection preserves this radius and gives real overlap>1/5.
For that reflected state, the first step has real overlap>1/2: the mixed norm
is at most1, while `a(r+1)/(2r)` already exceeds1/2 under these bounds.

The actual original reflected initial state is also proved **outside** the
half-overlap region. Thus the one-step entry is a substantive construction;
the fast-regime assumption is not silently supplied by the seed.

Every-n native iteration conjugacy and activity-dependent reflection earned in
the preceding packet return the estimates to the actual original native orbit.
The squared complex Euclidean norm is exactly the real/imaginary sum of squares;
packing is not assumed to be an isometry for the coordinate sup norm. After the
first step,59 further steps give the60 bound and58 give the59 bound. Both final
rational power comparisons are reduced by kernel-checkable `norm_num` proofs.

## Audit and scope boundary

Two new modules contain17 declarations: seven scalar/geometry/orbit estimates
and ten concrete seed returns/control. A full default build has8853 jobs.
All17 fresh signatures and transitive axiom closures are checked. The cumulative
2764-declaration audit preserves the immutable2747 raw prefix, with source and
toolchain identity checks, and appends the fresh17 suffix. Only `Classical.choice`,
`Quot.sound` and `propext` are allowed. No full cumulative audit rerun, Python test
suite, old numeric replay or new floating scout is claimed.

This is a sharp finite distance theorem in the exact real/complex mathematical
model. The four residuals used by the original source's convergence Boolean
remain to be explicitly bounded. In particular, the source phase-aligns the
final eigenvector and then phase-aligns it again inside `fixed_point_gap`; that
actual double alignment must be retained. IEEE eigensolver and per-operation
rounding are not formalized. Other couplings and18 offset kernel instances are
still pending. The whole original-paper goal remains incomplete.
