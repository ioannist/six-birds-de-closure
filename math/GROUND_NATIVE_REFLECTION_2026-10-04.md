# Signed representatives of the original native ground branch

Baseline: `b012aa1`. This packet leaves the paper, original runtime, data and all
previous proof/evidence sources unchanged. Review is adversarial self-review,
not independent review.

## Why the negative representative matters

The original complex initial field has mostly negative overlap with the positive
real ground. A new read-only floating scout calls the unchanged Step26 source's
actual state update, retaining its real eigensolver sign, erroneous phase rule,
fallback and normalization threshold. It matches the two initialization
normalizations in `load_initial_field` and `run_case`. The unused unitary
calculation is a diagnostic and does not enter the state update.

At the scouted couplings 0,0.3 and15 the iterates approach the **negative** real
representative. At15 the 60-step residual remains visible while the 1000-step
state is near that representative. These are numerical observations, not exact
orbit, finite-budget or basin certificates. Distances in the scout compare the
updated state with the preceding candidate, not with a kernel-identified exact
branch root. The scout informs the choice of the next target only.

The existing theorem `GroundOriginalCoordinates.actual_native_attraction`
returns convergence to the positive real representative. To apply local basin
estimates to the frozen seed, a negative target must also be available. Merely
calling both states the same ground ray would not prove convergence to either
state under the source's phase-dependent map.

## Exact reflection construction

Complex sourcing is even: `complexSourcePotential b κ (-z)` equals the source
at z. The selected positive real candidate is therefore the same. The candidate-
first overlap changes sign when the reference changes sign. On the **active**
phase branch the original factor is `conj(c)/|c|`; this factor changes sign.
Thus the mixed field, normalized native update and their actual orbit prefixes
reflect exactly. Complex squared norm is unchanged, and the active phase and
normalization guards transfer to the reflected prefix.

`native_iterate_neg` requires activity only at steps j<N to return the iterate
at N. It does not assume global oddness of the total threshold map. The local
attraction and finite escape bridges use the activity already earned by the
positive-representative theorems. For escape, guards at N are also retained in
returning the complete legal segment.

Reflection is an isometry of the same coordinate norm. The coordinate basis
itself is still not assumed isometric or an eigenbasis. The reflected center is
`T.symm (-u,0)`; the state returned by convergence is `realEmbed (-u)`.

## Concrete kernel returns

`GroundOriginalReflection.actual_negative_native_fixed` proves legal, active
negative native fixed points for every coupling in[0,30] and every real mixing
value, on the actual constructed original branch. Its only mathematical input
is the displayed coupling-range membership.

`actual_negative_native_attraction` proves actual native complex local attraction
at all ten original coupling samples through15, around the negative branch
representative. It takes only a finite sample index. Every iterate is active and
legal. Both signed representatives now have earned local neighborhoods, without
claiming the frozen initial field belongs to either one.

`actual_negative_twenty_native_escape` and `actual_negative_thirty_native_escape`
prove finite guarded escape from arbitrarily close unit complex starts around
the negative representatives at20 and30. They populate all spectral and escape
inputs from the prior kernel mode and operator-norm theorems. Together with the
previous packet, escape is proved around both signs. There is no claim that the
original frozen orbit escapes, every orbit escapes or amplitudes become unbounded.

## Substantive inactive-phase counterexample

The active guard cannot be omitted. Let the candidate be the real unit uniform
ground of the zero potential. Let the real unit reference have four coordinates
plus the uniform value and four minus it. Its overlap with the candidate is zero.
Both the reference and its negative therefore enter the unchanged fallback
branch. With coupling0, background0 and mixing1, both legally normalized updates
return the **same** positive uniform field.

`GroundReflectionControls.unconditional_unit_reflection_rejected` rejects a
universal reflection assertion even on **unit, legally normalized** input fields.
The witness has an actual selected ground candidate, not an arbitrary phase
record or an illegal totalized normalization. Six control theorems establish
unit norm, zero overlap, actual candidate identity, both outputs, legal/inactive
status and the final rejection.

## Verification and remaining work

Three new modules contain25 theorems:15 generic reflection/transfer results,
four concrete original-branch returns and six counterexample results. A fresh
full default build has8847 jobs. Fresh25 exported statements and transitive
closures are required; only the standard axioms `Classical.choice`, `Quot.sound`
and `propext` are admitted. The cumulative2703-declaration audit preserves the
immutable2678 prefix after proof/toolchain identity checks, plus the fresh25
suffix; the full cumulative command is not rerun. The verifier checks exact
manifests, signatures, scope, toolchain and pinned mathlib sources, prior source
identity, and reproducible read-only floating scout output under NumPy1.26.4.
Neither IEEE per-operation emulation nor JSON parsing is proved in Lean.

The exact frozen-seed basin and finite-step source outcomes remain pending, as
do18 background-offset kernel sample instances. A promising next construction
is a global half-mixing native theorem at coupling0, with a nonzero real overlap
condition and explicit phase/normalization margins; this could return the original
seed to the correct signed ground without needing a quantified local radius.
Positive-coupling frozen-seed returns still require additional nonlinear basin or
certified orbit estimates. This packet supplies the missing negative local
endpoint, rather than presuming such estimates. The overall original-paper goal
is incomplete; no previously parked false or project-sized claim is restored.
