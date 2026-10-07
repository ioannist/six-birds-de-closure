from pathlib import Path
import datetime,hashlib,json,re
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';handover=out/'handover.md';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
fps=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in fps:
 for f,h in json.loads(p.read_text()).items():assert f not in protected or protected[f]==h;protected[f]=h
assert all(sha(p)==h for p,h in protected.items())
jobs={662901:'de_native_campaign_qualified_stream_build.py',760297:'de_native_seed_real_returns_qualified_stream_build.py',853725:'de_native_campaign_verification_stream_finish.py',853723:'de_native_additional_constructions_stream_qualified_build.py',853738:'de_source_execution_supplement_stream_qualified_build.py',4049651:'de_native_stable15_priority_recovery/build_recovery.py',2558747:'de_native_stable_seed_leaves_private_build.py',2637955:'de_native_stable_seed_pairs_private_build.py',2854622:'de_native_stable_seed_families_private_build.py',3948875:'de_native_stable_seed_sixty_private_build.py',940127:'de_native_stable_prefix_failures_private_build.py',2056100:'de_native_original_sample_results_private_build.py'}
for pid,p in jobs.items():assert Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()=='/usr/bin/python3 /tmp/'+p,pid
counts={}
for key,p,denom in [('stable','/tmp/de-native-stable-seed-leaves-driver.log',597),('priority','/tmp/de-native-stable15-priority-recovery-driver.log',289),('qualified','/tmp/de-native-campaign-qualified-stream-driver.log',1734)]:
 text=Path(p).read_text();assert not re.search(r'terminal [1-9]|Traceback',text),p
 ms=re.findall(r'completed (\d+) /'+str(denom),text);assert ms;counts[key]=int(ms[-1])
p=repo/'results/native_registered_resource_candidate_2026-10-05';mf=p/'file-manifest.json';assert all(sha(p/f)==h for f,h in json.loads(mf.read_text()).items())
checks=json.loads((p/'checks.json').read_text());assert checks['actual_registered_commands_run']==0 and not checks['full_registered_success_path_tested'] and len(checks['rejected_environment_receipt_controls'])==4
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {counts["stable"]}/597 scheduled',s);s=re.sub(r'\d+/289 total terminal-zero',f'{counts["priority"]}/289 total terminal-zero',s);s=re.sub(r'with \d+/1734 terminal-zero',f'with {counts["qualified"]}/1734 terminal-zero',s)
s=s.replace('''The registered verifier/runner extension
and review, actual source installation, builds and fresh audits remain pending.''','''Separate extended verifier/runner candidates now pass their extension self-review
and eight corrupted-input controls:
`results/native_registered_resource_candidate_2026-10-05`;
`math/GROUND_NATIVE_REGISTERED_FAILURE_EXTENSION_2026-10-05.md`.
The full inherited registered success path remains untested. Publication/path
adjustments, actual installation, builds and fresh audits remain pending.''')
s=s.replace('''   Explicitly extend both candidates' exact source/object inventories, declaration
   lists and proof gates for the new checked1/5 supplement. Final native statement
   and cumulative axiom commands must then cover20789 and32565 respectively.''','''   The separate extended candidates now cover the new checked1/5 supplement and
   retain all inherited proof gates. Their extension passed adversarial self-review;
   full registered execution and success-path review remain pending. Final native
   statement and cumulative axiom commands must cover20789 and32565 respectively.''')
marker='## Required registered integration order'
assert s.count(marker)==1
resource='''## Explicit registered-command runtime setting

The latest prepared runner/verifier candidates are in
`results/native_registered_resource_candidate_2026-10-05` and documented in
`math/GROUND_REGISTERED_BUILD_RESOURCE_CONTROL_2026-10-05.md`.
Actual future commands explicitly receiveLEAN_NUM_THREADS=4; their receipts
must record that override. All proof gates, commands and1771/20789/32565
inventories are preserved. Two isolated twelve-module default Lake builds
passed with observed compiler peaks2/4 for their corresponding settings.
Four wrong/missing environment receipt controls are rejected. Dedicated and
blocked-task replacement workers mean no universal process or memory bound
is asserted. All235 fixture archive members were verified. Actual registered
commands remain0; both entry points refuse the missing final qualified summary.
The full registered success path remains untested. Apply and record the same
explicit setting at the earlier whole-offset registered gate. Earlier candidates
are immutable historical artifacts; use the latest reviewed candidate for final
publication/path adjustment after its proof prerequisites finish.

'''
s=s.replace(marker,resource+marker)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());snapshot=out/'snapshot-file-manifest.json';(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes());note.write_text(s);handover.write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live_jobs=jobs,progress=counts,frozen_inputs_revalidated=len(protected),extended_checker_manifest_sha256=sha(mf),registered_commands_started=0,registered_inputs_changed=False,goal_complete=False),indent=2)+'\n');manifest={str(f.relative_to(out)):sha(f) for f in sorted(out.rglob('*')) if f.is_file() and f!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/f)==h for f,h in manifest.items());print(json.dumps(dict(utc=stamp,progress=counts,live_jobs=len(jobs),frozen_inputs_revalidated=len(protected),handover_sha256=sha(handover))))
