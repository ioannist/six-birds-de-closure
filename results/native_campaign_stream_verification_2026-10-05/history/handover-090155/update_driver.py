from pathlib import Path
import datetime,hashlib,json,re
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05'
note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';handover=out/'handover.md'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
fps=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]
fps += [Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in fps:
 for f,h in json.loads(p.read_text()).items():
  assert f not in protected or protected[f]==h
  protected[f]=h
assert not set(map(str,[note,handover])).intersection(protected)
assert all(sha(p)==h for p,h in protected.items())
jobs={662901:'de_native_campaign_qualified_stream_build.py',760297:'de_native_seed_real_returns_qualified_stream_build.py',853725:'de_native_campaign_verification_stream_finish.py',853723:'de_native_additional_constructions_stream_qualified_build.py',853738:'de_source_execution_supplement_stream_qualified_build.py',4049651:'de_native_stable15_priority_recovery/build_recovery.py',2558747:'de_native_stable_seed_leaves_private_build.py',2637955:'de_native_stable_seed_pairs_private_build.py',2854622:'de_native_stable_seed_families_private_build.py',3948875:'de_native_stable_seed_sixty_private_build.py',940127:'de_native_stable_prefix_failures_private_build.py',2056100:'de_native_original_sample_results_private_build.py'}
for pid,p in jobs.items():assert Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()=='/usr/bin/python3 /tmp/'+p,pid
counts={}
for key,p,denom in [('stable','/tmp/de-native-stable-seed-leaves-driver.log',597),('priority','/tmp/de-native-stable15-priority-recovery-driver.log',289),('qualified','/tmp/de-native-campaign-qualified-stream-driver.log',1734)]:
 text=Path(p).read_text();assert not re.search(r'terminal [1-9]|Traceback',text),p
 ms=re.findall(r'completed (\d+) /'+str(denom),text);assert ms;counts[key]=int(ms[-1])
packet=repo/'results/native_registered_verification_candidate_2026-10-05'
manifest=json.loads((packet/'file-manifest.json').read_text());assert all(sha(packet/p)==h for p,h in manifest.items())
checks=json.loads((packet/'checks.json').read_text());assert checks['actual_registered_commands_run']==0 and not checks['full_registered_mode_tested']
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text()
s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {counts["stable"]}/597 scheduled',s)
s=re.sub(r'\d+/289 total terminal-zero',f'{counts["priority"]}/289 total terminal-zero',s)
s=re.sub(r'with \d+/1734 terminal-zero',f'with {counts["qualified"]}/1734 terminal-zero',s)
old='5. Update mathematical coverage and repository documentation to checked scopes,'
new='''   Prepared registered verifier/runner candidates are in
   `results/native_registered_verification_candidate_2026-10-05` and documented
   by `math/GROUND_NATIVE_REGISTERED_VERIFICATION_CANDIDATE_2026-10-05.md`.
   Candidate-source checking passes; both registered entry points reject the
   currently missing final qualified summary before any registered command.
   They require actual registered build receipts, 20,784 fresh registered
   statement checks and a fresh full 32,560-declaration standard-only axiom
   command. Full registered execution, adversarial review and publication/path
   adjustments remain pending; these preflights do not certify that success path.
5. Update mathematical coverage and repository documentation to checked scopes,'''
assert s.count(old)==1;s=s.replace(old,new)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir()
(hist/note.name).write_bytes(note.read_bytes());mf=out/'snapshot-file-manifest.json'
(hist/'preceding-snapshot-file-manifest.json').write_bytes(mf.read_bytes())
note.write_text(s);handover.write_text(s)
(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
(hist/'update-verification.json').write_text(json.dumps(dict(utc=stamp,live_jobs=jobs,progress=counts,source_freeze_inputs_revalidated=len(protected),registered_checker_preflights_sha256=sha(packet/'checks.json'),old_handover_preserved=True,registered_inputs_unchanged=True,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=mf}
mf.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items())
print(json.dumps(dict(utc=stamp,progress=counts,live_jobs=len(jobs),source_freeze_inputs_revalidated=len(protected),handover_sha256=sha(handover))))
