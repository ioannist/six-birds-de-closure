# Adversarial self-review of original complex local return

This is a distinct adversarial self-review after implementation, not an
independent review. All six new source modules and the exact certificate
generation/replay were inspected against the unchanged Step26 source.

1. **Phase orientation.** Conjugate-first overlap plus exp(-i arg) is retained,
   not silently replaced by exp(+i arg). The ratio proof conjugates the
   Mathlib polar identity. The negative imaginary derivative and exact i*u
   cancellation would both fail for a substituted corrected rule.
2. **Candidate sign.** The source Hamiltonian is real symmetric and its
   eigenvector is cast from a real array. Ground simplicity and unit norm earn
   the two real signs, with active-branch sign invariance. No arbitrary complex
   candidate-phase invariance or floating eigensolver accuracy is assumed.
3. **Sourcing.** Packing proves the exact modulus-square source. Real and
   imaginary quadratic terms both contribute; the imaginary source derivative
   vanishes only at a real field, not at arbitrary complex fields.
4. **Norms and topology.** The real product and complex sup norms are not
   identified. A real continuous linear equivalence transports convergence.
   Actual normalization uses Euclidean squared norm, proved by coordinate split.
   The full derivative is a real derivative, not a complex holomorphic one.
5. **Guard bridge.** Threshold/argument calculus is returned by eventual equality
   on a neighborhood with overlap and mixed norm above threshold. The invariant
   basin is placed inside the earned guard region; every actual iterate has both
   guards. Totalized division at zero has no execution meaning.
6. **Dynamics.** The C1 theorem earns a Lipschitz constant below one and an
   invariant closed ball; it does not assume orbit convergence. The fixed
   coordinate equivalence conjugates all finite iterates. Product operator norm
   is bounded by the max of both block norms, not by either block alone.
7. **Phase boundary.** i*u is a legal unit initial field with active alignment,
   but native half mixing gives exactly zero and illegal normalization. This
   explicitly prevents extension to all complex initial fields. All-parameter
   legal fixed-point existence does not imply stability or global convergence.
8. **Sample evidence.** The original root/real-Jacobian certificate packet is
   immutable and freshly replayed. Fixed dyadic imaginary bases are exactly
   invertible; outward interval matrix products enclose the full imaginary
   derivative over the root boxes. Singular/wrong-size/wrong-identity bases and
   destructive box enlargement are rejected. Approximate proposal generation
   has no evidentiary role until exact replay succeeds.
9. **Coverage boundary.** The analytic theorem is Lean-checked, but the concrete
   roots, fixed coordinate bases and numerical bounds are Python exact
   computations, not Lean proof terms. No explicit basin radius, frozen-init
   membership, 60-step success, continuous branch, nonlinear escape at20/30,
   physical Lambda, background blindness, or unrestricted selector prohibition
   is inferred. κ15 remains locally stable, which does not restore κ>=15 runaway.
10. **Trust and provenance.** Fresh exported statements and standard axiom
    closures are checked by the packet verifier. The cumulative receipt preserves
    the exact1695-declaration baseline prefix and appends87 fresh closures; its
    full1782-declaration command is not claimed rerun. Frozen source, original
    data, paper, previous proof sources and prior receipts are hash protected.

No remaining correctness defect was identified in this packet. Original-target
completion is still open for the explicitly listed obligations. No new downgrade
of previously supported claims is needed; known false global/physical claims
remain parked in the original-claim coverage ledger.
