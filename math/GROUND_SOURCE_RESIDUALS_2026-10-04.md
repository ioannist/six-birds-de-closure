# The four original source convergence tests at zero coupling

Baseline: `c307cf7`. This packet preserves the paper, runtime, seed data and all
previous proof/evidence sources. Review is adversarial self-review, not independent.

## Target and source formula return

`actual_seed_zero_sixty_convergence_tests` has no hypotheses. It proves that
the exact mathematical original-seed native orbit at original background,
coupling0 and half mixing passes **all four** source convergence comparisons
after60 updates. It also returns active phase and legal normalization at every
iterate. The seed coefficients, two initialization normalizations and both
source thresholds are exact reifications of the original binary64 inputs.

The four compared values are:

- the Euclidean norm of the last update, from iterate59 to60;
- the final fixed-point gap, with the **two** source `phase_align` calls;
- the final eigen residual, using the actual Rayleigh energy of iterate60;
- the sourcing comparison, in which the source repeats the same expression.

`GroundSourceDiagnostics` keeps each of these formulas explicit. The frozen
source first aligns `final_phi`, then `fixed_point_gap` aligns it again. We
retain that call graph and its unchanged conjugate phase rule. The source's
real symmetric eigensolver returns a normalized real ground vector up to a real
sign; the earned active-branch sign invariance permits the actual positive
selector representative. Arbitrary complex eigenvector phase is not assumed
sign-invariant. At coupling0 the actual selected ground is exactly the previously
identified branch ground; no frozen midpoint or approximate eigenvector enters.

The convergence threshold is the exact binary64 rational

    3022314549036573 / 302231454903657293676544,

strictly above1/100000000. The normalization threshold is the original exact
reification already proved. The source diagnostic AST, constants and call graph
are checked read-only by the verifier; source parsing is not a Lean proof.

## Full Euclidean norm and phase estimate

The earlier calculus uses coordinate sup norms. Here `l2 z` is the norm of the
same finite complex field in `EuclideanSpace ℂ (Fin8)`; its square equals the
actual `complexNormSq z`. Inner products equal the actual conjugated overlap,
and norm triangle, scalar homogeneity and Cauchy-Schwarz are returned explicitly.

For unit g,z, write c=overlap(g,z), r=|c|, with nonnegative real part of c.
Cauchy-Schwarz gives r<=1. On the earned active branch, the native phase is
`t*g`, with t=conj(c)/r and |t|=1. The exact identities

    l2(t*g-g)² = 2-2 Re(c)/r,
    l2(z-g)² = 2-2 Re(c)

show that the **movement of the candidate** is bounded by l2(z-g). This does not
assert that conjugate alignment reduces its distance to the reference. Indeed
it can increase that distance, and the proof retains that behavior.

If l2(z-g)<=d and the threshold is below1-2d², both successive phase branches
are active. The first candidate stays within d of g, hence within2d of z.
The second candidate moves by at most2d from the first. Its final gap to z is
therefore at most4d. Positive real overlap for both applications is earned from
the unit-vector distance identity and2d²<=1; it is not an extra concrete premise.

For the actual negative target and iterate60, d=1/500000000. Actual real-sign
invariance returns the two-alignment bound to the original positive selected
candidate. The final fixed gap is at most8e-9, and the second diagnostic phase
branch is proved active as well as the already earned first branch.

The last update is bounded by the distances of iterates59 and60 to the same
actual target, respectively below3e-9 and2e-9. It is therefore below5e-9.

## Eigen residual and sourcing comparison

The actual periodic cycle Hamiltonian is symmetric for the finite complex
overlap. Both cyclic shifts preserve the full Euclidean norm. Pointwise
potential bounds derive the Euclidean diagonal operator bound, rather than
supplying an assumed matrix norm. Closed rational kernel arithmetic earns
0<=b_i<=2/5 for every original background entry.

Ground minimality and the actual energy identity earn0<=lambda<=2/5 for the
actual ground energy. Thus the diagonal entries1+b_i-lambda have absolute value
at most7/5, and the two neighboring half shifts add at most1. For the actual
shifted operator K=H-lambda I,

    l2(Kw) <= (12/5) l2(w)     for every full complex field w.

If g is the exact target eigenfield, K g=0. Symmetry kills the cross term,
returning the actual Rayleigh energy error as

    E(z)-lambda = Re overlap(z-g, K(z-g)).

For the genuinely unit iterate z, Cauchy-Schwarz gives absolute energy error at
most `(12/5) l2(z-g)²`. The actual eigen residual therefore satisfies

    l2((H-E(z)I)z) <= (12/5)l2(z-g)+(12/5)l2(z-g)².

At iterate60 this is below the exact convergence threshold (indeed below4.81e-9).
No approximate energy, assumed operator norm or energy quotient at a nonunit
field is substituted. The target eigen equation and energy interval are earned
from the actual selected ground specification.

The source's final sourcing residual compares `final_potential` against the
same `background+kappa*stress_energy_density(psi,background)` expression that
defined it. Its exact mathematical value is0. This repeated-expression
diagnostic does **not** independently certify self-consistent field convergence;
that interpretation is not made here.

## Substantive control and audit boundary

For background0/coupling0 and the unit field `i*realEmbed(uniform)`, the actual
first alignment returns the negative input. The second returns the input.
Thus the actual double fixed gap is0 while the single gap is2. The native half
update at that input cancels to0 and is illegal, as also proved. This rejects
both substituting the single gap for the source's double gap and inferring
legal flow from the double gap alone. It does not undermine the original-seed
endpoint, whose global legality is separately earned.

Five modules contain51 theorems:15 Euclidean/phase,15 Hamiltonian/residual,
three source diagnostic returns,13 concrete original-seed endpoints, and five
controls. Full default build8858 and51 fresh signatures/standard-only transitive
closures are checked. The cumulative2815-declaration audit preserves the immutable
2764 raw prefix after source/toolchain checks and appends the fresh51 suffix.
Only `Classical.choice`, `Quot.sound` and `propext` are allowed. A full cumulative
audit rerun, Python test suite, old numeric replay or new floating scout is not
claimed. Newly used direct Euclidean/complex mathlib sources are checked against
the pinned revision as well as fingerprinted.

This completes all four source convergence tests at coupling0 **in the exact
mathematical model**. The NumPy eigensolver and IEEE per-operation trajectory
remain outside this proof. Positive-coupling original-seed basins,18 offset kernel
instances and the previously parked false/project-sized targets remain pending.
The original-paper goal remains incomplete.
