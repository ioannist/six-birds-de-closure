from pathlib import Path
import hashlib,json
ROOT=Path('/home/repos/six-birds-de-closure')
OLD=ROOT/'results/native_postregistered_documentation_candidate_2026-10-06'
OUT=ROOT/'results/native_postinstall_documentation_candidate_2026-10-06'
sha=lambda b:hashlib.sha256(b).hexdigest()
plan=json.loads((OLD/'documentation-plan.json').read_text())
assert not OUT.exists()
snapshot=json.loads(Path('/tmp/de_native_registered_original_audit_receipts/source-snapshot.json').read_text())
old_reference='results/native_registered_stack_integration_run_2026-10-06'
new_reference='results/native_registered_final_verification_2026-10-06'
targets=[]
for row in plan['targets']:
 path=row['path'];original=(ROOT/path).read_bytes();prior=(OLD/path).read_bytes()
 assert sha(original)==row['before_sha256'],path
 assert sha(prior)==row['after_sha256'],path
 assert str(ROOT/path) not in snapshot,path
 text=prior.decode();assert old_reference in text,path
 revised=text.replace(old_reference,new_reference)
 # Record both genuine producers, rather than attributing success to the stopped controller.
 revised=revised.replace('for actual command\nreceipts.', 'for the final native command\nreceipts; the preceding whole-offset results are in\n`results/ground_offset_transport_2026-10-04/verification.json`.')
 targets.append(dict(path=path,before_sha256=sha(original),prior_candidate_sha256=sha(prior),after_sha256=sha(revised.encode()),candidate_path=str(OUT/path),raw=revised.encode()))
OUT.mkdir()
for row in targets:
 target=OUT/row['path'];target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(row.pop('raw'))
new_plan=dict(status='UNAPPLIED DRAFT: completion assertions remain conditional on successful final registered commands and completion review',targets=targets,prior_plan_sha256=sha((OLD/'documentation-plan.json').read_bytes()),required_native_live_terminal='/tmp/de_native_registered_original_audit_receipts/terminal.json',required_native_archived_terminal=str(ROOT/new_reference/'terminal.json'),required_offset_verification=str(ROOT/'results/ground_offset_transport_2026-10-04/verification.json'),requires_registered_native_modules=1772,requires_registered_statement_queries=20798,requires_fresh_cumulative_axiom_queries=32574,requires_current_source_and_object_snapshots=True,requires_actual_build_and_both_audit_exit_codes_zero=True,requires_standard_axioms_only=True,requires_completion_review=True,registered_sources_changed=False,paper_changed=False,authoritative_documentation_changed=False)
(OUT/'documentation-plan.json').write_text(json.dumps(new_plan,indent=2)+'\n')
(OUT/'README-candidate-status.txt').write_text('UNAPPLIED DRAFT. Actual final native success is pending. No completion assertions have been published. The stopped integration controller is historical failure evidence, not the completion producer. Require fresh build, full cumulative axioms, all native statements, current snapshots, durable receipt readback and completion review before applying. Paper and authoritative documentation unchanged.\n')
(OUT/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in OUT.rglob('*') if p.is_file()}
(OUT/'file-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert all(sha((OUT/p).read_bytes())==h for p,h in manifest.items())
assert all(sha((ROOT/r['path']).read_bytes())==r['before_sha256'] for r in targets)
print(json.dumps(dict(prepared_documentation_files=len(targets),readback=True,published=False,registered_success_asserted=False,paper_changed=False)))
