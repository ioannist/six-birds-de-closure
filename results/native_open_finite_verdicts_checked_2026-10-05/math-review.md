# Open robustness of the finite convergence verdict at coupling 30

## Verified gain

Four new qualified private Lean modules and fifteen declarations compiled and
passed fresh printed statement / transitive axiom checks. Every closure uses
only `propext`, `Classical.choice` and `Quot.sound`. The concrete finite theorem
constructs a positive joint neighborhood in all eight background coordinates
and coupling around the original coupling-30 input. Every exact mathematical
run truncated after any number of updates from 1 through 60 has a failed
original four-test convergence verdict. Both source update guards hold at
every preceding step and all states through update 60 have norm one.

A combined concrete theorem takes a positive common neighborhood on which
these finite verdicts hold alongside the original seed's infinite attraction
to the same exactly real two-cycle, density separation greater than `9/20`,
all infinite guards/unit norms, state/density nonconvergence and a genuine
full complex attraction neighborhood around the cycle's first phase. Thus
finite failure and asymptotic cycling are established by their own arguments
and returned for the same inputs.

The compiled sources are under
`/tmp/de_native_finite_parameter_verdict/lean/SbtCosmo/Derivation/` and are
copied into the durable packet
`results/native_open_finite_verdicts_checked_2026-10-05/`. Registration, a
fresh build against the final upstream native module names and commit remain
pending the older source-frozen campaigns. The paper and original runtime are
unchanged. This is adversarial self-review, not independent review.

## Runtime semantics and indexing

The original Step26 program at
`external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py`
runs a fixed `range(steps)` loop and computes its Boolean `converged` flag
**after** the loop. Its default is 60 updates. There is no early-exit branch.
The flag compares the final last-update length, final doubly aligned fixed-point
gap, final current-Rayleigh eigen residual and final sourcing self-comparison
against the original convergence tolerance. The Lean `MeetsConvergence`
predicate is the mathematical reification of this post-run conjunction.

Earlier work used the shorthand “stopping verdicts”; the precise claim here is
about the reported convergence verdict for every finite truncation, not an
implemented early-stop mechanism. The theorem's `n < 60` uses the previous
state at iteration `n` and its actual next state at iteration `n+1`, so it
covers runs of lengths `N = n+1` in `1..60`. It does not describe a zero-update
run. At each such truncation, the first of the four comparisons already fails
strictly. Continuity of the other three diagnostics is not needed for this
negative verdict, and failure of any other diagnostic is not assumed.

Both original initialization normalization calls, original half mixing,
original binary64 values reified as exact real constants, original candidate
selection and original conjugated phase convention remain in the map. This
is an exact mathematical-source result; it makes no assertion about a full
IEEE trace or arbitrary floating-point perturbations.

## Strict finite defects and continuity

`GroundOriginalCycle30FiniteVerdicts.strict_stepLength_baseline` proves
`epsilon < l2(psi[n+1]-psi[n])` for every `n < 60` at the original input.
For `n < 59`, it uses the earlier populated prefix's actual two-endpoint
complex enclosure boxes and their kernel-checked rational coordinate gaps.
Both endpoint radii enter the gap bound; the selected coordinate and sign are
kept for each step. The exact binary convergence tolerance is compared with
that gap. The gap is then bounded above by the actual Euclidean update length.

For update 59 to update 60, the previously checked endpoint boxes give update
length strictly greater than `1/4`, which is strictly above the original
convergence tolerance. The final boxes are tied to the actual doubly normalized
original seed by all thirty populated transport pairs. No final-state or
finite-prefix enclosure is an incoming hypothesis in the concrete theorem.

`GroundFiniteParameterContinuity` proves finite parameter-iterate continuity
with regularity required only along the finite baseline prefix. This is a
pure topological theorem. The concrete application supplies it with joint
smoothness of the literal source update at the guarded original states from
the populated first-sixty prefix. No infinite orbit convergence, attractor,
or infinite-guard premise is used in the finite proof. Shared imports also
contain cycle constructions, but the actual finite argument calls the finite
prefix/box results and the guarded local source regularity results.

`GroundNativeSourceParameterSmooth` returns the previous real/imaginary pair
calculus to the original complex source carrier using the exact continuous
linear encode/decode equivalence. Joint smoothness is earned on the active
phase and nonzero mixed-normalization branch. Both literal guards form a joint
open neighborhood. The conversion is exact on the totalized native map before
restricting to the proved legal neighborhood. No unproved global oddness or
fallback-branch smoothness is assumed.

The update Euclidean norm is continuous in the original complex coordinate
topology. Its proof uses the exact identity
`l2(z) = sqrt(complexNormSq(z))`; continuity of the sum of squared complex
components and global continuity of square root are sufficient, including at
zero. For each of the sixty updates, continuity retains the strict length gap
on a parameter neighborhood, while joint source regularity retains both
update guards. A finite intersection of these sixty neighborhoods supplies
one positive radius. Unit initialization and legal normalization at each
successor then give all iterate norms through 60.

The first compile of the concrete finite theorem exited one because the
successor iterate was not definitionally the one-step image in the orientation
used by `change`. The repaired proof uses the exact `iterate_succ_apply'`
identity. That source/log/terminal history is preserved. Two successful
sources were subsequently clarified to state the fixed-length post-run
semantics, and both were recompiled before the fresh full audit. This was a
semantic-comment clarification, not a change to the mathematical statements.
The initial and clarified source versions and their successful receipts are
preserved separately.

## Joined finite and asymptotic return

`GroundOriginalCycle30FiniteAttractorLanding.open_finite_and_real_cycle`
uses the earlier independently constructed open exactly real attracting-cycle
result and the new finite result. The two parameter centres are definitionally
the same original background and coupling. The finite module writes the source
threshold as its original exact binary value; the cycle module writes it as the
stored rational threshold cast to reals. The existing exact threshold identity
proves these functions equal, and exact iteration preserves that equality.

Taking the minimum of the two strictly positive radii produces a single
positive neighborhood. The original seed's even and odd limits are the same
cycle witnesses as the full complex basin's limits. Their strict density gap
excludes equality and hence excludes whole-state and density limits. Every
finite truncation in `1..60` has a failed source convergence flag on those same
inputs. Neither the finite verdict nor the asymptotic claim is inferred from
the other.

## Adversarial self-review and limits

The positive finite radius is a conclusion rather than supplied evidence. The
whole finite defect family is tied to actual seed iterates; separate scalar
budgets over unrelated endpoint boxes would not suffice. The finite continuity
proof uses only the required finite guard prefix. Its intersection is finite,
so no unwarranted radius uniform over an uncontrolled infinite prefix is
introduced. The equality of finite and infinite source definitions is proved,
including the exact threshold identity, before combining their returns.

A merely nonstrict update-length lower bound would not justify this argument. The needed strict inequalities are derived from
the populated certificates. Likewise a failed length at a single finite time
would not establish an infinite cyclic regime; the latter still uses its
separate full-state contraction, actual cycle construction and original-seed
entry. Eventual failure alone would not establish every first-sixty verdict,
which is why the new finite prefix construction is necessary.

The background/coupling radius is positive but not numerically bounded here.
It need not connect sampled couplings, and it proves no universal failed flag
or runaway statement above 15. The source program's `converged` Boolean after
60 updates is a finite diagnostic, not a definition of infinite convergence.
The pending coupling-15 packet distinguishes a failed finite sixty-update flag
from an eventual stable return; each has its own proof obligations. The combined
coupling-30 result has unit orbits and a bounded cycle, so it supports neither
amplitude blowup nor a physical Lambda interpretation. No first bifurcation,
whole coupling classification, IEEE execution or whole-paper completion is
claimed. No new material downgrade was needed.
