from pathlib import Path
import json,hashlib,subprocess,datetime,re
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';snapshot=out/'snapshot-file-manifest.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in freezes:
    for f,h in json.loads(p.read_text()).items():assert f not in protected or protected[f]==h;protected[f]=h
assert len(protected)==6262 and all(sha(p)==h for p,h in protected.items())
additional=json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text());assert len(additional)==3936 and all(sha(p)==h for p,h in additional.items())
packet=repo/'results/native_original_stable10_checkpoint_candidate_2026-10-05';assert all(sha(packet/f)==h for f,h in json.loads((packet/'file-manifest.json').read_text()).items())
d=json.loads((packet/'checks.json').read_text());assert d['coupling']=='10' and d['original_sample_index']==8 and d['entry_updates']==60 and d['paired_entry']==30
assert not d['checkpoint_created'] and not d['math_proof_success_claimed']
live=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_native_live_poll_v2.py'],text=True));assert not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
ready=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_checkpoint_stable10_return.py','--mode','preflight'],text=True));assert not ready['checkpoint_created'] and not ready['proof_success_claimed']
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
s=re.sub(r'Latest live observation:stable leaves\d+/597,\nqualified modules\d+/1734,',f'Latest live observation:stable leaves{live["progress"]["stable"]["passed"]}/597,\nqualified modules{live["progress"]["qualified"]["passed"]}/1734,',s)
marker='## Required registered integration order';assert s.count(marker)==1
new='''## Prepared next stable-sample checkpoint

The original coupling10/sample8 collector is prepared at
`/tmp/de_checkpoint_stable10_return.py`;
evidence:`results/native_original_stable10_checkpoint_candidate_2026-10-05`.
It was matched to the collector source actually archived in the completed
coupling5 packet; its dependency collection/archive logic is unchanged. Actual
source guards check Point008.a=10, Frame008's same coupling and Transport.N=30
paired steps, corresponding to60 updates. Preflight exits0 and reports readiness
without mathematical success. Checkpoint mode currently exits2 for missing
actual family/sixty terminal0 audits before creating a packet. This is a
prepared collector, not a completed coupling10 proof or registered build.

After both `NativeStableSeed008Audit terminal 0` and
`NativeStableSeed008SixtyAudit terminal 0` (and their underlying module markers)
appear in the actual drivers, run
`/usr/bin/python3 /tmp/de_checkpoint_stable10_return.py --mode checkpoint`.
It will validate the fifteen exact declarations/standard axioms, every required
leaf/pair marker and all frozen inputs before preserving the completed private
source/object/log checkpoint. No new Lean command is supplied by this collector.
The current leaf/pair compiler processes were observed actively using CPU;
regular10/15, parent qualification and final registered integration are pending.

'''
s=s.replace(marker,new+marker)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,stable10_preflight=ready,candidate_manifest_sha256=sha(packet/'file-manifest.json'),frozen_inputs_revalidated=len(protected),completed_private_audit_freeze_revalidated=len(additional),registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items())
print(json.dumps(dict(utc=stamp,live_jobs=live['live_jobs'],progress=live['progress'],stable10_collector_ready=ready['ready_for_checkpoint'],handover_sha256=sha(note))),flush=True)
