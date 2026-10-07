from pathlib import Path
import datetime,hashlib,json,re

repo=Path('/home/repos/six-birds-de-closure')
out=repo/'results/native_campaign_stream_verification_2026-10-05'
note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md'
handover=out/'handover.md'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze_paths=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]
freeze_paths += [Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in freeze_paths:
 for f,h in json.loads(p.read_text()).items():
  assert f not in protected or protected[f]==h
  protected[f]=h
assert not set(map(str,[note,handover])).intersection(protected)
assert all(sha(p)==h for p,h in protected.items())
jobs={662901:'de_native_campaign_qualified_stream_build.py',760297:'de_native_seed_real_returns_qualified_stream_build.py',853725:'de_native_campaign_verification_stream_finish.py',853723:'de_native_additional_constructions_stream_qualified_build.py',853738:'de_source_execution_supplement_stream_qualified_build.py',1255480:'de_native_stable15_priority/build_priority.py',2558747:'de_native_stable_seed_leaves_private_build.py',2637955:'de_native_stable_seed_pairs_private_build.py',2854622:'de_native_stable_seed_families_private_build.py',3948875:'de_native_stable_seed_sixty_private_build.py',940127:'de_native_stable_prefix_failures_private_build.py',2056100:'de_native_original_sample_results_private_build.py'}
for pid,path in jobs.items():assert Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()=='/usr/bin/python3 /tmp/'+path,pid
counts={}
for key,p,denom in [('stable','/tmp/de-native-stable-seed-leaves-driver.log',597),('priority','/tmp/de-native-stable15-priority-driver.log',289),('qualified','/tmp/de-native-campaign-qualified-stream-driver.log',1734)]:
 ms=re.findall(r'completed (\d+) /'+str(denom),Path(p).read_text());assert ms;counts[key]=int(ms[-1])
review=repo/'results/ground_offset_namespace_verifier_review_2026-10-05'
for part in [review,review/'evidence']:
 manifest=json.loads((part/'file-manifest.json').read_text())
 assert all(sha(part/p)==h for p,h in manifest.items())
 assert json.loads((part/'review.json').read_text())['terminal_exit_code']==0
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
s=note.read_text()
s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {counts["stable"]}/597 scheduled',s)
s=re.sub(r'has \d+/289 fresh module',f'has {counts["priority"]}/289 fresh module',s)
s=re.sub(r'with \d+/1734 terminal-zero',f'with {counts["qualified"]}/1734 terminal-zero',s)
old='''   isolated proposed verifier extension must be reviewed before use. It permits
   only those 18 original archived family texts and the original renderer to
'''
new='''   isolated proposed verifier extension passed adversarial self-review: the
   exact 19 changes were accepted, seven controls were rejected, and all other
   verifier gates were confirmed unchanged by AST comparison. The checked repair
   packet's 100 archive members, 1,166 bindings and 6,909 statement/axiom receipts
   were revalidated. Evidence: `results/ground_offset_namespace_verifier_review_2026-10-05`;
   note: `math/GROUND_OFFSET_NAMESPACE_VERIFIER_REVIEW_2026-10-05.md`.
   This review does not complete registered integration. The extension permits
   only those 18 original archived family texts and the original renderer to
'''
assert old in s;s=s.replace(old,new)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'))
hist.mkdir()
(hist/note.name).write_bytes(note.read_bytes())
mf=out/'snapshot-file-manifest.json'
(hist/'preceding-snapshot-file-manifest.json').write_bytes(mf.read_bytes())
note.write_text(s);handover.write_text(s)
(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
(hist/'update-verification.json').write_text(json.dumps(dict(utc=stamp,live_jobs=jobs,progress=counts,source_freeze_inputs_revalidated=len(protected),verifier_review_sha256=sha(review/'review.json'),evidence_review_sha256=sha(review/'evidence/review.json'),old_handover_preserved=True,registered_inputs_unchanged=True,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=mf}
mf.write_text(json.dumps(manifest,indent=2)+'\n')
assert all(sha(out/p)==h for p,h in manifest.items())
print(json.dumps(dict(utc=stamp,progress=counts,live_jobs=len(jobs),source_freeze_inputs_revalidated=len(protected),handover_sha256=sha(handover))))
