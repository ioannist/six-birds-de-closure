# Four original source diagnostics at coupling 0.3

The original reified seed's unchanged native mathematical orbit passes all four
original source convergence tests after sixty updates at original coupling 0.3.
`GroundOriginalPositiveResiduals.actual_seed_positive_sixty_convergence_tests`
has no supplied numerical, candidate, basin or convergence hypothesis. It also
returns active phase and legal normalization for every original iterate.

The coupling is the original binary64 input, mixing is `1/2`, and the exact
original convergence tolerance is
`3022314549036573/302231454903657293676544`. Both initialization normalizations
and the source's conjugated phase rule remain represented. The earlier explicit
basin theorem supplies an actual geometric tail for the original seed.

## Actual source return

The final selected candidate is evaluated at the actual sourced potential of
the sixtieth iterate. Its sign is chosen negative for the distance estimate;
the first active native phase is proved invariant under this real sign choice.
The candidate is not replaced by the continuation-branch ground.

The proof earns complex Euclidean distance at most `1/10000000000` for iterates
59 and60 to the negative branch ground and for iterate60 to the negative actual
sourced candidate. The bounds give:

- last-update gap at most `2e-10`, strictly below the source tolerance;
- the actual twice-aligned fixed gap at most `4e-10`, with both phase guards;
- the actual sourced Rayleigh eigen residual at most
  `(5/2)*(1e-10 + (1e-10)^2)`, strictly below the tolerance;
- sourcing comparison exactly zero, because the source repeats the same
  expression. This is not an independent self-consistency test.

No first stopping index or per-operation IEEE execution is inferred.

## Mathematical bridges

`GroundComplexNormBridge` proves `l2(pack x) ≤ 4*‖x‖` from all sixteen real
coordinates. State uses the product sup norm, while `l2` uses the full complex
Euclidean norm. `pack` is not assumed isometric.

`GroundOriginalBasinEstimates` uses both sets of eight kernel-certified actual
selector-response columns on the whole basin. The resulting selector in basin
coordinates is Lipschitz with constant1, established by the actual derivative
and a convex mean-value theorem. Its center value is the actual fixed branch
ground. Combining this estimate with the native geometric tail bounds the
actual sourced candidate, rather than an arbitrary ground representative.

The actual sixtieth sourced potential lies in `[0,1/2]` at every site. The
positive-ground specification and the uniform comparison state give its ground
energy in the same interval. `GroundComplexResidualBudget` proves a general
shifted cycle-Hamiltonian budget `2+B` for potentials and eigenvalues in `[0,B]`.
Taking `B=1/2` gives `5/2`. Symmetry and the actual ground eigen equation then
bound the Rayleigh energy error quadratically and the eigen residual by
`M*δ + M*δ^2`. The reported residual uses the source's actual Rayleigh energy.

The phase estimate retains both native phase-align calls. A sign change of the
candidate is used only with its earned active guard. The unchanged phase bug
is neither silently corrected nor replaced with a single phase diagnostic.

## Self-review and evidence

This is an adversarial self-review, not independent review. Fresh statement and
axiom checks cover28 theorems. The cumulative2994-declaration audit preserves
the earlier2966 raw evidence with proof-source identity; it does not rerun the
entire cumulative command. The full default build has8892 jobs. Only the
standard `propext`, `Classical.choice` and `Quot.sound` axioms are allowed.
Exact Fraction replay checks the finite powers and all source diagnostic caps;
Lean earns the actual orbit and selector bridges. No new floating solver is run.

The previously proved pure-imaginary control has double phase gap0 but single
gap2 and an illegal half update. It remains immutable evidence that the two
diagnostics cannot be interchanged or treated as sufficient for update legality.
The source-expression audit and previous bad reciprocal/preconditioner controls
also remain unchanged.

Other positive-coupling seed returns, eighteen background-offset kernel instances
and IEEE execution remain separate targets. No paper, original runtime source,
original data or previous proof module is changed. The overall goal is incomplete.
