# Native all-parameter ground existence in Lean, 2026-10-03

Baseline: `7ff720b`. This packet mechanizes the all-background theorem written
in `GROUND_STATE_PROOFS_2026-10-02.md`, constructs the linear selector used by
that proof, and proves simplicity and the return to complex fields. The paper
and the frozen experiment source/results are unchanged. This is an adversarial
self-review with kernel checking, not an independent review.

## Exact target

For every `b : Fin 8 → ℝ` and every `κ : ℝ`, there is a strictly positive
unit real field `u` that is a lowest eigenvector of

```
(H_v u)_i = (1 + v_i) u_i - (u_(i-1) + u_(i+1))/2,
v_i = b_i + κ [ ((u_(i+1)-u_(i-1))/2)^2 + b_i u_i^2 ].
```

Indices are modulo eight. No sign, smallness, convergence or fixed-point
witness is a premise. These are the original Step26 kinetic matrix and
central-difference sourcing with `N=8`, `DX=1`. The frozen source SHA256 is
`391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd`;
the earlier Python reconstruction and complex sourcing tests remain the source
bridge. The theorem concerns exact real/complex arithmetic, not machine rounding.

`GroundFixedPoint.exists_selfConsistent_ground` is the file-level endpoint;
all declarations use namespace `SbtCosmo.Derivation.GroundState`. It concludes
`∃ u, (∀ i, 0 < u i) ∧ IsSelfConsistentGround b κ u`. The definition expands to
unit normalization, an eigen equation, and a lower energy bound against **every**
real field. It is not merely an eigenvector or a small numerical residual.

## Construction and substantive dependencies

1. `GroundSelector` proves compactness and nonemptiness of the real unit fields
   and constructs a Rayleigh minimizer for every supplied potential. Taking
   coordinatewise absolute values preserves norm and decreases the actual cycle
   energy. The explicit symmetric matrix is identified with the original
   Hamiltonian. Mathlib's self-adjoint Rayleigh extremum theorem yields the
   eigen equation; homogeneity extends minimality to every field, including zero.
2. The actual cycle's zero-propagation lemma gives strict positivity. A minimum
   positive coordinate ratio gives uniqueness of the positive unit ground
   vector. `positiveGround` uses classical choice only after existence is
   proved; it does not assume a nonlinear self-consistent ground selector.
3. The nonnegative unit fields form a compact range. The graph of minimizing
   pairs is closed because every comparison inequality is closed. Its
   intersection with a closed range subset has a closed projection. Uniqueness
   identifies that projection with the selector's preimage, proving continuity
   on **all** real potentials. No uniform spectral gap is supplied or needed.
4. `GroundFixedPoint` constructs the simplex map
   `p ↦ positiveGround(v(sqrt(p)))²`, proves its continuity and its return to
   the probability simplex, and applies the audited Brouwer theorem at size
   eight. Square roots are continuous at the boundary. Positivity gives
   `sqrt(g_i²)=g_i`, so the resulting probability fixed point returns to the
   original normalized ground field.
5. `GroundSimple` proves that the absolute value of any signed unit ground
   vector is again ground and strictly positive. A lowest eigenvector with a
   zero coordinate must therefore vanish, after normalization if necessary.
   Subtracting a suitable multiple of a ground vector proves that every real
   lowest eigenvector lies in its span. This is simplicity of the linear lowest
   eigenspace, not uniqueness of the nonlinear self-consistent solution.
6. `GroundComplex` constructs the original complex Hamiltonian, source potential,
   norm and Hermitian energy. Real and imaginary energies split exactly. The
   real ground lower bound therefore controls every complex competitor. The
   real fixed point embeds as an exact complex ground state of its own source
   potential, as stated in `exists_native_complex_ground`. Splitting the complex
   eigen equation proves that the complex lowest eigenspace is a single line.

The return is to the finite model with the original nonconstant template too:
`every_background_offset_admitted` allows any template and any offset.
`background_offset_no_forced_value` and `coupling_no_forced_value` derive
nonselection by **existence alone** using explicitly constructed witnesses at
zero and one. They neither forbid an additional selector nor claim that the
actual background-dependent dynamics is blind.

## Brouwer proof import and provenance

The proof is vendored from
[LionSR/Brouwer at ec93e4d](https://github.com/LionSR/Brouwer/tree/ec93e4daed4ad8b4784a9d760e492832e7711433).
Only `Gametheory/Scarf.lean` and `Gametheory/Brouwer.lean` are imported, with
their original MIT license. `lean/Gametheory/PROVENANCE.json` pins the original
raw source and license hashes; `port.patch` records every local difference.
The port keeps Lean/mathlib 4.28.0. It changes renamed API fields/lemmas, makes
one natural-number inequality explicit, adds provenance headers, and removes
only commented-out unfinished drafts. No active proof or theorem is omitted.

The imported endpoint's elaborated statement is exactly

```
Brouwer {n : ℕ+}
  (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))
  (hf : Continuous f) : ∃ x, f x = x
```

It contains no additional existence, compactness, coloring or supplied proof
record premise. The Scarf combinatorial argument, fine-grid diameter bound,
compact subsequence and coordinate inequalities are proved upstream and checked
transitively here. The ambient dimension and lower-dimensional simplex pose no
interior assumption. The small local port does not change the conclusion.

The two upstream modules retain automatic implicit-variable elaboration enabled
explicitly in those files; local construction modules retain the package's
`autoImplicit=false`, `relaxedAutoImplicit=false`, `warningAsError=true` settings.
The imported statement and transitive axiom closure are audited rather than
inferred from those settings. This is a proof import, not a Brouwer axiom or an
unchecked transfer from Isabelle or a different Lean toolchain.

## Adversarial self-review and remaining scope

The first hard child, ground existence for a supplied linear potential, is
constructed before nonlinear sourcing. Selector continuity has no hidden
continuity premise. The Brouwer map is defined on the whole compact simplex,
including boundary points. The norm uses a finite sum of squares even though
`Field`'s topology carries a sup norm; the explicit Euclidean-space bridge
justifies the Rayleigh theorem. Matrix identities and connectivity include the
wrap edge. Complex minimality tests all complex competitors, including zero,
and uses the same real source after embedding. Ground-space simplicity covers
arbitrary signed/complex eigenvectors, not only a chosen positive vector.

No nonlinear variational principle is assumed: the original sourcing need not
be the derivative of a nonlinear energy. Classical choice selects the proved
unique positive unit representative; it does not claim an efficient numerical
procedure. The imported theorem's transitive audit includes its dependencies,
so commented drafts or a textual absence of local axioms are not the authority.

This closes a local mechanization gap; it does **not** restore an existential
coupling boundary. Exact existence holds at every real coupling. A finite-budget
convergence distinction or a declared branch/map stability criterion is separate.
There is no guarantee that the source iteration converges, no rigorously located
spectral stability crossing, and no uniqueness theorem for nonlinear solutions.
The frozen source's phase-sign error persists in the historical source. At the
positive representative, real lowest eigenvector selection and phase alignment
can return that representative; a globally phase-covariant damped algorithm is
not thereby proved. No continuum or physical cosmological identification is
constructed. The original paper remains incomplete for the reasons in the
claim-coverage record.

## Verification

The fresh default `lake build` passes all 8059 jobs with warnings as errors.
The new local modules contain 52 theorems (30 selector, 4 simplicity, 8 nonlinear
fixed-point, 10 complex bridge). The expanded `check_axioms.lean` audits 380
declarations: the previous 327, all 52 new local theorems and imported `Brouwer`.
The raw receipt is
`lean/manifests/axiom_audit_ground_existence_2026-10-03.txt`; the verification
record is `results/ground_existence_2026-10-03/verification.json`.
The existing four ground-state Python tests pass freshly. No Python algorithm
was changed and no new native sweep or interval certificate is claimed.
Historical receipts retain their original dates and coverage.
