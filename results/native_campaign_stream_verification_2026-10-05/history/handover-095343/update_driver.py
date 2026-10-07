from pathlib import Path
import datetime,hashlib,json
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';handover=out/'handover.md';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
fps=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in fps:
 for f,h in json.loads(p.read_text()).items():assert f not in protected or protected[f]==h;protected[f]=h
assert all(sha(p)==h for p,h in protected.items())
p=repo/'results/native_registered_installation_with_failure_candidate_2026-10-05';mf=p/'file-manifest.json';assert all(sha(p/f)==h for f,h in json.loads(mf.read_text()).items())
s=note.read_text();marker='## Required registered integration order';assert s.count(marker)==1
paragraph='''The exact extended installation bytes are now prepared separately in
`results/native_registered_installation_with_failure_candidate_2026-10-05`:
1771 native modules/20789 native declarations/32565 prospective cumulative
names and1783 verified archived target files. The prior1780-file candidate and
all original plans remain unchanged. The registered verifier/runner extension
and review, actual source installation, builds and fresh audits remain pending.
An initial pre-output preparer assertion mistook a registered transitive parent
for an old direct external import; its exact failed driver is preserved in
`results/native_installation_failure_extension_history_2026-10-05`. The
corrected preparer checked the actual parent and succeeded, with no proof or
registered-source changes.

'''
s=s.replace(marker,paragraph+marker)
s=s.replace('''   Extend this archived installation candidate explicitly for the separate
   one-module/five-declaration execution-failure supplement before installing it;
   do not count that module under the old20784/32560 audit lists.''','''   The separate extended1783-file candidate now includes the new1/5 supplement.
   Use its exact bytes after extending/reviewing the registered checker/runner;
   do not count that module under the old20784/32560 audit lists.''')
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());snapshot=out/'snapshot-file-manifest.json';(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);handover.write_text(s);(hist/'verification.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),frozen_inputs_revalidated=len(protected),extended_candidate_manifest_sha256=sha(mf),registered_inputs_changed=False,goal_complete=False),indent=2)+'\n');manifest={str(f.relative_to(out)):sha(f) for f in sorted(out.rglob('*')) if f.is_file() and f!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/f)==h for f,h in manifest.items());print('Extended installation recorded;6262 frozen inputs unchanged; history and snapshot hashes verified.')
