# Global bounds along guarded native orbits

Seven new theorems have compiled and passed fresh printed-statement and transitive
axiom checks. Their qualified source is preserved in
`results/native_guarded_bounds_2026-10-05/lean/SbtCosmo/Derivation/GroundNativeGuardedBounds.lean`.
It is a separate, currently unregistered supplement. The live main and native
campaign input freezes and registration plans have not been changed.

For a complex field on the original eight sites, write

\[
 \rho_i(z)=|z_i|^2,\qquad
 q_i(z)=\left|\frac{z_{i+1}-z_{i-1}}{2}\right|^2,
 \qquad V_i(z)=b_i+\kappa(q_i(z)+b_i\rho_i(z)).
\]

These are the existing `GroundState.complexGradient`, `complexNormSq` and
`complexSourcePotential` definitions, including the background multiplying the
density term. If the total squared norm is one, then
\(0\leq\rho_i\leq1\), \(|z_i|\leq1\), and \(0\leq q_i\leq1\).
The gradient estimate follows from the triangle inequality and the factor of
two in the centered difference. It suffices for the bound

\[
 |V_i(z)|\leq |b_i|+|\kappa|(1+|b_i|).
\]

This holds for arbitrary real background components and signed real coupling.
It is uniform in the field on the unit sphere; along an orbit it is uniform in
time when the background and coupling are fixed.

The existing `GroundNativeEscape.nativeUpdate_unit` theorem supplies unit norm
after any native update with a nonnegative normalization threshold and a legal
mixed-state normalization. It requires neither an initially unit field nor an
active-phase premise. The new `legal_update_potential_bound` composes that
earned result with the bound above. The all-iterate theorem
`guarded_orbit_unit_and_potential` has the following explicit premises:

- the threshold is nonnegative;
- the initial field has total squared norm one;
- `NativeLegal` holds at every iterate of the actual mathematical native map.

Its conclusion is unit norm and the displayed potential bound at every natural
time. For positive time, only the legality of the preceding normalization is
needed in the proof; the initial norm covers time zero. No entry certificate,
convergence, contraction, sampled-coupling restriction, eigenphase change, or
replacement initialization is used. The theorem does not establish legality
for arbitrary parameters. The total extension of normalization at zero is not
used to attribute a failed normalization to successful source execution.

Consequently, amplitude or sourced-potential blowup cannot describe an infinite
guarded trajectory of this fixed finite-dimensional exact model. Bounded
oscillation, escape from a local fixed-point neighborhood, and failure of a
finite convergence diagnostic remain possible. This reinforces the already
identified limitation of a literal universal high-coupling runaway claim; it
does not prove convergence or a coupling boundary. The attracting two-cycle
constructions at couplings 20 and 30 are consistent with these bounds.
No IEEE execution, continuum limit, spacetime, or physical Lambda result follows
from this finite-dimensional estimate.

The seven new names are `density_le_one`, `component_norm_le_one`,
`gradient_norm_le_one`, `gradient_energy_le_one`, `source_potential_bound`,
`legal_update_potential_bound`, and `guarded_orbit_unit_and_potential`, in
`SbtCosmo.Derivation.GroundNativeGuardedBounds`. Every printed axiom closure
contains only `propext`, `Classical.choice`, and `Quot.sound`. The source contains
no holes, local axioms, or `native_decide`. The proof and its connection to the
existing source definitions received an adversarial self-review. There has
been no independent reviewer for this supplement.

The receipt packet preserves the successful compile and qualified overlay audit,
the first source and two elaboration repairs, and both failed import-path audit
attempts. The failures involved a Lake-qualified module lookup and an incomplete
object overlay; the final audit uses a complete isolated overlay and exited zero.
The packet also records hashes of the 633 existing repository source/object
dependencies used by the compiled imports. Four previously registered
normalization helpers have separately printed standard-only axiom closures;
they are not counted as new declarations.

Repository registration is pending completion of the existing source-frozen
campaign gates. `registration-plan.json` adds one module and seven names in a
separate supplement, without changing the immutable 1734-module campaign or
its four-module real-return supplement. Neither the cumulative campaign build
nor the original-paper completion is claimed by this packet. The paper and
original experiment runtime remain untouched.
