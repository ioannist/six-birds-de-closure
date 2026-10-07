"""Prepare documentation bytes; publish only after actual registered success."""
from pathlib import Path
import hashlib, json

ROOT=Path('/home/repos/six-birds-de-closure')
OUT=ROOT/'results/native_postregistered_documentation_candidate_2026-10-06'
assert not OUT.exists();OUT.mkdir()
sha=lambda b:hashlib.sha256(b).hexdigest()
readme='''

## Original-input mathematical returns (2026-10-06)

Dark energy remains the motivating inference problem. The results concern the
specified mathematical models and readouts; they do not derive physical dark
energy or transfer the model's interpretation to spacetime. The paper is
unchanged and still needs the agreed narrowing. See the
[interpretation scope](math/PHYSICAL_INTERPRETATION_SCOPE_2026-10-05.md).

The exact original twelve-coupling iteration now has a combined Lean theorem.
The ten sampled couplings through15 converge with legal normalization and unit
states at every update. Coupling15 fails the original four-test conjunction at
every update1..60, yet converges after certified basin entry by update178 and
eventually passes those tests. Couplings20 and30 approach genuine attracting
two-cycles; their states remain unit and bounded, while the declared site density
does not converge. The sixty-update diagnostic and infinite-time behavior
therefore distinguish different properties. These statements classify the
twelve supplied samples, not every intervening coupling or IEEE execution.

The eighteen original background controls have infinite limiting orbits at
coupling0.3; fifteen pass the sixty-update diagnostic. Neither Boolean readout
recovers all eighteen inputs. Certified seed returns also cover all backgrounds
in eighteen specified input boxes. This is not a whole continuous interval of
offsets, nor a universal impossibility of parameter identification from richer
observations. Guarded Option execution is proved separately; supplied unit
phase-related starts can split successful execution from normalization failure.

The adopted mediator theorem requires recovery of all four coordinates whenever
a deterministic mediator determines both declared readouts. It is an information
recovery result, with no lower bound of four literal storage fields or four
encoding dimensions. Optimization prices and growth/record windows retain their
explicit mathematical assumptions. They do not select a physically realized
cosmological parameter.

The registered integration adds1772 modules and20798 declarations to the
11776-declaration earlier cumulative audit. Its actual native build, all20798
statement queries and one full32574-query cumulative transitive-axiom command
pass with only `propext`, `Classical.choice` and `Quot.sound`. The preceding
whole-offset integration also passes its registered10003-job build,6909
statement/axiom checks,421-step replay and440-source regeneration. See
`results/native_registered_integration_run_2026-10-06` for actual command
receipts. These are kernel checks and adversarial self-review, not independent
human review or a proof of the paper's unrevised physical claims.
'''
lean='''

## Registered original-input integration (2026-10-06)

The dated reports above retain their historical coverage. The final integration
uses the repaired whole-offset namespaces, a valid import header for the default
axiom manifest, and a repaired proof body for
`SbtCosmo.Derivation.NativeOriginalSampleResults`; its eleven theorem headers,
definitions and imports are unchanged. The aggregate proves unit/guarded
iteration for all twelve samples, convergence exactly for indices below10,
sixty-update success exactly for indices below9, and eventual test success
exactly for indices below10. Index9 is coupling15: finite diagnostic failure
coexists with eventual convergence. The coupling20/30 samples instead approach
unit two-cycles with nonconvergent density at the declared site.

`GroundOriginalAuditNonidentifiability` proves that the original sixty-update
Boolean readout and the Boolean limit-existence readout do not recover all
eighteen original background controls. It does not exclude richer readouts.
`GroundSourceNormalization`, `GroundSourceExecutionReturn`, and
`GroundOriginalCycleExecution` connect legal mathematical normalization to
finite Option execution. `GroundSourceNormalizationFailure` constructs supplied
unit starts with an actual phase-related execution split. These execution
results do not emulate floating-point arithmetic or classify first stopping
indices. Background boxes and open neighborhoods have their declared scopes.

The registered native integration has1772 modules and20798 new declarations;
the default cumulative manifest contains32574 ordered, distinct theorem queries.
All20798 statement queries and the single fresh32574-query axiom command pass.
Only the standard kernel axioms `propext`, `Classical.choice`, and `Quot.sound`
occur. No compiled proof object was copied into the registered source tree.
Command receipts explicitly set `LEAN_NUM_THREADS=4`. The registered integration
run and prior checked packets retain failed histories and distinguish retained
private compiler checks from fresh qualified and registered commands.

To rerun the full registered build and cumulative axiom disclosure:

```bash
LEAN_NUM_THREADS=4 lake build
LEAN_NUM_THREADS=4 lake env lean manifests/check_axioms.lean
```

The physical-frame bridge is outside the user-authorized revised scope. The
paper and original runtime remain unchanged. Interpretive analogies are separate
from the represented model theorems. See
`../math/PHYSICAL_INTERPRETATION_SCOPE_2026-10-05.md` and
`../results/native_registered_integration_run_2026-10-06`.
'''
coverage='''

## Registered native integration, 2026-10-06

The exact original twelve-sample aggregate and original eighteen-control
readout theorem supersede the corresponding historical pending statuses above.
All targets remain scoped to the declared mathematical source models.

| Registered group | Modules | New declarations | Exact scope |
|---|---:|---:|---|
| Native source campaign | 1734 | 20628 | Original12 finite/infinite returns; no classification of all intervening couplings. |
| Real seed returns | 4 | 6 | Supplied real initializations under declared guards. |
| Additional constructions | 29 | 132 | Specified background/coupling neighborhoods and cycle basins. |
| Mathematical execution | 3 | 18 | Guarded finite Option iteration, without IEEE emulation. |
| Normalization failure | 1 | 5 | Supplied unit starts and phase-related execution split. |
| Original-readout nonidentifiability | 1 | 9 | Two Boolean readouts fail to recover all18 original controls; richer readouts remain available. |
| Total | 1772 | 20798 | Full fresh registered statement audit and32574-query cumulative transitive-axiom audit. |

The repaired aggregate retains all eleven theorem headers. The exact mediator
strengthening recovers all four coordinates when both declared readouts factor
through a deterministic mediator; it does not prove an encoding-dimension lower
bound. Physical Lambda/spacetime transfer is outside the revised scope. The
unrevised paper is unchanged; the model results do not validate its unsupported
universal or physical claims. The actual registered receipts are in
`results/native_registered_integration_run_2026-10-06`.
'''
payload={'README.md':readme,'lean/README.md':lean,'lean/manifests/coverage_table.md':coverage}
targets=[]
for name,suffix in payload.items():
 before=(ROOT/name).read_bytes();after=before+suffix.encode();p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(after)
 targets.append(dict(path=name,before_sha256=sha(before),after_sha256=sha(after),candidate_path=str(p)))
plan=dict(status='Unapplied postregistered documentation draft; its success assertions must not be published before genuine registered success',targets=targets,required_controller_terminal=str(ROOT/'results/native_registered_integration_run_2026-10-06/terminal.json'),requires_registered_native_modules=1772,requires_registered_statement_queries=20798,requires_fresh_cumulative_axiom_queries=32574,registered_sources_changed=False,paper_changed=False)
(OUT/'documentation-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
(OUT/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(OUT/'README-candidate-status.txt').write_text('UNAPPLIED DRAFT. Proposed completion assertions depend on the actual registered controller success and completion review. Current success remains pending. No authoritative README, Lean documentation or paper was modified.\n')
(OUT/'file-manifest.json').write_text(json.dumps({str(p.relative_to(OUT)):sha(p.read_bytes()) for p in OUT.rglob('*') if p.is_file()},indent=2)+'\n')
print(json.dumps(dict(prepared_documentation_files=3,published=False,registered_success=False,paper_changed=False)))
