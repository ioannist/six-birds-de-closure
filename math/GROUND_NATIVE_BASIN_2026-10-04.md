# Explicit native basin at original coupling 0.3

This packet constructs a quantified attraction basin and returns the unchanged
original seed to it after sixteen native updates. The coupling is the exact
binary64 input `5404319552844595/18014398509481984`; mixing is `1/2` and the
original phase threshold is retained. This is the exact mathematical model of
the source, including its conjugated phase rule and both initialization
normalizations. It is not per-operation IEEE execution.

## Exact return

`GroundOriginalBasin.original_seed_converges_negative_ground` proves genuine
`Tendsto` convergence of the original native orbit to the negative actual
continuation-branch ground. It has no supplied basin or numerical hypothesis.
`original_seed_all_guards` and `original_seed_all_unit` prove active phase,
legal normalization and unit norm at every original orbit state.

The already certified real and imaginary changes of coordinates are assembled
as `T`. In the resulting State product sup norm, the closed ball about
`T.symm (u,0)` has radius `1/40000`. Over that entire ball the actual derivative
of the thresholded native map has operator norm at most `3/5`; both threshold
guards hold. The reflected original sixteenth iterate is within `1/48000` of
this center. For every natural `n`, its reflected tail distance is at most
`(3/5)^n / 48000`. These are explicit constants, not a comparison with an
unspecified local attracting radius. State sup norms and complex Euclidean
norms are not identified.

## Mathematical chain

1. A uniform potential-box Newton certificate encloses the actual positive
   selected ground and its energy for every sourced potential in the state
   box. Positivity and normalization identify the Newton root with the actual
   ground selector; a midpoint root is not substituted.
2. The same actual bordered derivative has a preconditioned defect at most
   `1/2500`. For each of sixteen transformed directions, the actual selector
   derivative equation gives the response error `q*y/(1-q)`, retained in the
   enclosing interval. No approximate matrix is treated as an exact inverse.
3. The phase derivative, mixing derivative and final normalization derivative
   are evaluated throughout the state box. All real and imaginary blocks,
   including both cross blocks, enter the sixteen-column row sums. The actual
   reciprocal square roots and threshold margins are earned.
4. Outward dyadic response and physical-derivative caches reduce repeated
   rational evaluation. Each cache is separately checked by kernel interval
   inclusion before the soundness proof uses it. The Python replay checks the
   same inclusions with exact Fractions. The proposed maximum native row bound
   is about `0.56263`, below `3/5`; the proof uses the rational comparison.
5. The coordinate ball lies inside the uniform state box because the actual
   basis operator norm is at most `177/50`. A convex mean-value theorem yields
   the actual native map's Lipschitz bound on this ball. The actual unit ground
   is a fixed point, so iteration stays in the ball and converges geometrically.
6. The separately certified sixteen-step original prefix supplies the endpoint;
   its reflected coordinate error is bounded against the actual branch ground.
   Reflection is applied only after earning every active-phase guard. Finite
   prefix guards and the infinite tail guards cover all natural indices.

`GroundNativeGeneralDerivative`, `GroundBackgroundResponse`,
`GroundNativeQuantitativeBall`, `GroundNativeDerivativeBox` and `GroundStateRows`
contain the reusable calculus and norm bridges. `GroundBasin.Point002Data`
contains proposals only; `Point002Arithmetic` supplies every closed numerical
budget. `Point002Bridge` keeps its numerical inputs explicit in namespace
`GroundOriginalBasin`; `GroundOriginalBasin.lean` discharges them all.

## Adversarial self-review and evidence

This is a self-review, not independent review. The review checks the actual
selector, exact source phase sign, all sixteen derivative columns, coordinate
norm conventions, cache inclusions, mean-value domain, fixed-point return,
endpoint entry and active-only reflection. The zero-contraction control rejects
a zero derivative budget on an actual populated row. Earlier zero reciprocal
and zero selector preconditioner controls remain intact.

The packet records the pinned toolchain, fresh theorem statements, a fresh
86-declaration axiom suffix, full build and exact rational replay. The cumulative
2966-declaration audit preserves the earlier 2880-declaration raw evidence with
proof-source identity; the entire cumulative command is not rerun. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. The source verifier
checks prior evidence, generated-source identity and checkout/Git fingerprints.

## Remaining work

The four original source convergence diagnostics at sixty updates are not yet
returned for coupling 0.3. Their source expressions, including the twice-aligned
phase gap and Rayleigh energy, must be bounded separately. Other positive-coupling
seed basins, eighteen offset sample instances and per-operation IEEE execution
remain separate targets. No paper or original runtime source is edited. The
overall mathematics-review goal remains incomplete.
