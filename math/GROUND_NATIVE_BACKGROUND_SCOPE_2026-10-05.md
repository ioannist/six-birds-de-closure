# Background shifts and the scope of the input hulls

Three new exact source-shift lemmas compiled and passed fresh printed statement
and transitive axiom checks. Their source and receipts are preserved in
`results/native_background_scope_2026-10-05/`. Repository registration is
pending the existing source-freezing campaign gates. The immutable campaign
plans and their proof sources remain unchanged.

The original sourced potential is
\(V_i(b,\kappa,z)=b_i+\kappa(q_i(z)+b_i|z_i|^2)\).
For a uniform scalar shift \(s\), the exact change is

\[
 V_i(b+s,\kappa,z)-V_i(b,\kappa,z)
   =s(1+\kappa|z_i|^2).
\]

Between sites \(i\) and \(j\), the difference of these changes is
\(s\kappa(|z_i|^2-|z_j|^2)\). Thus nonzero coupling, a nonzero shift, and
unequal site densities imply a nonconstant change of the sourced potential.
These are the explicit premises of `source_shift_nonconstant`; the identity
lemmas require no normalization or guard hypothesis. The statements concern
the sourced potential. They do not assert that every nonconstant potential
change necessarily changes every later dynamical observable.

The background sweep fixes coupling at the original binary value of 0.3,
`5404319552844595/18014398509481984`. Therefore the ordinary constant-diagonal
Hamiltonian-shift shortcut cannot establish invariance for general source
fields in this sweep. Its additional density-dependent term must be retained.
This makes precise the background dependence already established by the
separated actual roots and density limits. No new downgrade of those root or
seed-return theorems is needed.

The geometry review also checked all eighteen background boxes against their
exact rational witness data and the actual Lean `B` definitions. Each coordinate
interval is the minimal hull of the exact shifted input and the saved rounded
input. The maximum coordinate width is
`13/36028797018963968`, approximately `3.608224830031759e-16`.
Every hull has at least one fixed coordinate, so every hull has empty interior
in the eight-dimensional background space. Hulls 6, 7, and 8, at offsets -0.2,
-0.1, and zero, are single points.

For each hull, the saved review identifies a fixed coordinate at its exact
shifted-background value. Consequently its intersection with the one-dimensional
family of exact uniform offsets is exactly its one recorded offset: membership
at that coordinate forces the alternative offset to equal the recorded one.
This geometric inference follows by cancellation of the unchanged base
coordinate. It is a separate exact arithmetic review, not an additional Lean
theorem or a newly widened parameter certificate.

The queued whole-box return statement correctly covers every fixed background
inside each such hull, including both exact and rounded models and their
per-coordinate interpolation. It does not supply an open perturbation
neighborhood or a continuous interval of scalar offsets. Its proof statement
already keeps hull membership explicit. Wider robustness would require new
parameter certificates or a parameter-continuity and uniform-basin argument;
the exact shift identity does not provide that extension by itself.

The three new names are `source_uniform_shift`,
`source_shift_site_difference`, and `source_shift_nonconstant`, in
`SbtCosmo.Derivation.GroundNativeBackgroundShift`. Their printed axiom closures
contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no holes,
local axioms, or `native_decide`; eight existing repository source/object
dependencies are pinned. The source semantics and geometric coverage received
an adversarial self-review. No independent review is claimed.

The whole-box production builds, broader native campaign integration, and
original-paper completion remain pending. This supplement proves no IEEE
execution, uniform offset-window convergence, or physical Lambda bridge. The
paper and original runtime remain untouched.
