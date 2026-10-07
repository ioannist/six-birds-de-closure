# Exact native-source transport replay checkpoint

The paper and original runtime remain unchanged. This is adversarial self-review
and exact rational replay, not independent review or an IEEE execution proof.
The original-paper goal remains incomplete.

## Target and semantic bridge

The represented map uses the original eight-site periodic kinetic operator,
the background and coupling literals lifted from their stored binary floating
values, the original complex seed, both exact initialization normalizations,
half mixing, and the original phase/normalization threshold. The phase multiplier
retains the source's negative phase angle. Neither a corrected phase convention
nor a different seed is substituted.

The source `run_case` always executes `range(steps)`, then evaluates its four
final diagnostics. Its computed unitary step contributes a norm diagnostic;
the state recurrence assigns the normalized mixed ground candidate to `psi`.
The final fixed-point diagnostic applies phase alignment twice. Its eigen
diagnostic uses the current sourced Hamiltonian and current Rayleigh energy.
The sourcing diagnostic subtracts two copies of the same sourced expression.
These facts match the existing `GroundNativeIteration`, `GroundOriginalSeed`
and `GroundSourceDiagnostics` definitions. The mathematical lowest eigenvector
is the canonical positive real selector. The original real Hamiltonian's real
sign ambiguity is handled by the proved active-phase sign invariance, with
the actual active guards supplied separately. No invariance under arbitrary
complex eigenvector phases is asserted.

The literal 0.1 coupling is `3602879701896397/36028797018963968`; replacing it
with exactly `1/10` would change the represented input. The tolerances are
likewise the exact stored binary values. Every scope statement here concerns
the mathematical lift of those literals. Library eigensolver and floating
arithmetic error, including the two floating initialization operations, remain
outside this replay.

## Replay obligations

`scripts/de_native_sample_transport_replay.py` checks the ten pending transport
families at sample indices1,3,4,5,6,7,8,9,10,11. These comprise598 stable steps
and472 cycle steps, with299 and236 paired certificates respectively. Its checks
use `Fraction` interval arithmetic and invoke no numerical root solver.

For each family the replay matches the actual source background, exact coupling,
literal frame matrices and their two-sided inverses. It verifies the raw seed
coefficients against the source data and their Lean representation, and checks
an independent640-bit enclosure of the exact normalized seed against the
initial physical box. The second mathematical normalization returns the same
unit state by the previously proved `GroundOriginalSeed.double_normalization`.

At every step it verifies the positive selected-ground root certificate,
both inverse-square-root bounds, both strict native guards, a narrow reference
step enclosure and center defect, every one of the sixteen selector-response
and full-update derivative columns, and the coordinate matrix cache. All
derivatives range over the whole stated input box, including imaginary inputs.
The single-step rate may exceed one.

For a pair starting at update2j, the independently recomputed matrix product is
the second whole-box derivative cache times the first cache. The intermediate
transport and center-defect bounds place the required arguments in the second
box. Its row bound and defect budget earn

    delta_(2j+2) <= pairRate * delta_(2j)
                   + (secondRate * firstDefect + secondDefect).

The endpoint comparison retains the actual-root uncertainty for stable samples
and the actual local cycle reference center for20/30. The final propagated
radius plus this center distance must be strictly below the proved basin radius.
Each of the1,070 leaf files is freshly rendered in memory and compared byte for
byte with its frozen Lean source; no Lean source is rewritten.

Input fingerprints are captured before the full run and checked again after
it. Exact arithmetic replay remains distinct from fresh kernel checking of the
populated certificates and their unconditional original-seed return bindings.
The queued full qualified Lean build is a separate gate.

## Observed checks and pending gate

The original stable001 pilot passed60 steps and30 pairs. The cycle30 pilot
passed152 steps and76 pairs. Their prototype source, terminal receipts and
normalized logs are retained; the expanded full checker additionally verifies
the raw seed and captures its input freeze. These two pilot results do not
establish completion of the whole replay campaign.

Four corrupted stable001 inputs were independently rejected by the arithmetic
checker: replacing the exact coupling with1/10, setting the phase inverse to
zero, zeroing an actual response component in the last imaginary input column,
and setting the paired-step rate to zero. None of the original proposal or
Lean source files was changed. These controls exercise mathematical inputs,
not deletion of an unused record or a conjunct in a result label.

The full run returned terminal0 under session18295: all ten families, all1,070
steps, all535 paired certificates and all frozen hashes passed. Its normalized
log is `results/native_sample_transport_2026-10-04/replay_driver.txt`. Its durable input freeze is
`results/native_sample_transport_2026-10-04/replay-freeze.json`. Its final
`replay.json` records the complete checked scope and the input fingerprints.
The four rejected controls and both historical pilots are preserved alongside
it. The arithmetic replay supplies no new claim of completed Lean seed returns, repository
registration, continuum dynamics, a physical Lambda bridge, or whole-paper
completion.


## Durable generated-source backup

`results/native_campaign_candidate_2026-10-04/sources.tar.gz` now saves the full
1734-module private candidate and1734-module qualified source preview, fresh
manifests, all ten transport payloads and construction tools. All3563 archived
files passed source-SHA comparisons in a single sequential extraction pass.
The first random-access gzip verification was intentionally stopped after the
replacement pass returned terminal0; its143 receipt is preserved. This source
backup is not a completed Lean build or an integration/commit gate.


## Observed original numerical comparison

The unchanged original `load_initial_field` and `run_case` functions were freshly
executed with NumPy1.26.4 at all twelve literal couplings, half mixing and60
updates. Every verdict agrees with the mathematical classification candidate:
indices0..8 (through coupling10) pass, and15/20/30 fail. The wrapper preserves
both original initialization normalizations, the unitary diagnostic, current
Rayleigh residual and both final phase calls; it does not replace any source
function. No paper, source routine or original experiment output was written.

`results/native_sample_transport_2026-10-04/original_numeric_compare.json` records
the observed summaries, source/data/wrapper hashes and explicit scope. Its
terminal receipt is0. This comparison supplies empirical execution evidence,
not an IEEE-operation proof, original-seed infinite return or earliest-success
index. The full Lean final classification remains under checking.
