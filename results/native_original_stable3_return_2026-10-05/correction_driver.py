from pathlib import Path
import datetime,hashlib,json,re
repo=Path('/home/repos/six-birds-de-closure');packet=repo/'results/native_original_stable3_return_2026-10-05';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=packet/'file-manifest.json';old=json.loads(manifest.read_text());assert all(sha(packet/f)==h for f,h in old.items())
summary_path=packet/'audit-summary.json';d=json.loads(summary_path.read_text());assert d['coupling']=='3' and d['original_sample_index']==5 and d['checked_declarations']==15 and d['standard_only']
assert all(n.startswith('SbtCosmo.Derivation.NativeStableSeed006.') for n in d['names'])
frame=Path('/tmp/de_native_cycle_lean/NativeStableFrame006.lean');sample=repo/'lean/SbtCosmo/Derivation/GroundSamples/Point006.lean';collector=Path('/tmp/de_checkpoint_stable3_return.py')
assert 'def κ : ℚ := GroundSamples.Point006.a' in frame.read_text();assert re.search(r'^def a : ℚ := 3\s*$',sample.read_text(),re.M)
assert 'index=6;' in collector.read_text() and 'original_sample_index=5' in collector.read_text()
hist=packet/'history'/'initial-copied-index';hist.mkdir(parents=True,exist_ok=False)
(hist/'audit-summary.json').write_bytes(summary_path.read_bytes());(hist/'file-manifest.json').write_bytes(manifest.read_bytes());(hist/'executed_collector.py').write_bytes(collector.read_bytes())
record=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),field='original_sample_index',previous=5,corrected=6,reason='Literal metadata field copied from preceding coupling2 packet; executed collector index and all checked sources/names are006/coupling3',frame_sha256=sha(frame),sample_sha256=sha(sample),executed_collector_sha256=sha(collector),archive_unchanged=True,proof_sources_unchanged=True,compiled_objects_unchanged=True,audit_logs_unchanged=True,review='adversarial self-review',goal_complete=False)
d['original_sample_index']=6;d['metadata_correction']=dict(field=record['field'],previous=5,corrected=6,proofs_changed=False)
summary_path.write_text(json.dumps(d,indent=2)+'\n');(packet/'metadata-correction.json').write_text(json.dumps(record,indent=2)+'\n');(packet/'correction_driver.py').write_bytes(Path(__file__).read_bytes())
readme=packet/'README.md';readme.write_text(readme.read_text()+'\nCheckpoint metadata correction: the initial collector executed index6 and checked coupling3/sample6 sources and declarations, but copied a literal sample-index5 summary field. The initial summary/manifest/executed collector are preserved in history/initial-copied-index. The corrected summary records6; the original checked archive, proof objects and audit logs are unchanged.\n')
for f,h in old.items():
 if f not in {'audit-summary.json','README.md'}:assert sha(packet/f)==h,f
new={str(p.relative_to(packet)):sha(p) for p in sorted(packet.rglob('*')) if p.is_file() and p!=manifest};manifest.write_text(json.dumps(new,indent=2)+'\n');assert all(sha(packet/f)==h for f,h in new.items())
print(json.dumps(dict(coupling='3',original_sample_index=6,checked_declarations=15,initial_metadata_preserved=True,proofs_changed=False,archive_unchanged=True)))
