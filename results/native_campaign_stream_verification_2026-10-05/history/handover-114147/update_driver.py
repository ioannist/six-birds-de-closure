from pathlib import Path
import datetime,hashlib,json,re,subprocess
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';snapshot=out/'snapshot-file-manifest.json';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in freezes:
 for f,h in json.loads(p.read_text()).items():assert f not in protected or protected[f]==h;protected[f]=h
assert len(protected)==6262 and all(sha(p)==h for p,h in protected.items())
additional=json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text());assert len(additional)==3936 and all(sha(p)==h for p,h in additional.items())
live=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_native_live_poll.py'],text=True));assert live['live_jobs']==12 and not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
assert Path('/proc/1509758/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()=='/usr/bin/python3 /tmp/de_run_repaired_cumulative_audit.py'
assert not Path('/tmp/de_audit_manifest_header_repair/cumulative-terminal.json').exists()
packet=repo/'results/ground_offset_binary_fingerprint_candidate_2026-10-05';assert all(sha(packet/p)==h for p,h in json.loads((packet/'file-manifest.json').read_text()).items())
archive='results/ground_offset_namespace_recovery_checked_2026-10-05/checked_artifacts.tar.gz';raw=(repo/archive).read_bytes();a=subprocess.check_output(['git','hash-object','--stdin'],cwd=repo,input=raw).decode().strip();b=subprocess.check_output(['git','hash-object','--stdin','--path='+archive],cwd=repo,input=raw).decode().strip();assert a==b
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {live["progress"]["stable"]["passed"]}/597 scheduled',s);s=re.sub(r'\d+/289 total terminal-zero',f'{live["progress"]["priority15"]["passed"]}/289 total terminal-zero',s);s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
old='`/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_repaired.py`';new='`/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_binary_repaired.py`';assert s.count(old)==1;s=s.replace(old,new)
addition='''A subsequent actual artifact test found that the inherited canonical text
fingerprint helper rejects the binary compressed proof archive when it contains
CRLF and NUL. The latest proposal above hashes binary bytes unchanged and
retains the canonical text comparison. Actual archive bytes pass; all2858
prior file comparisons are identical, and AST comparison preserves every
verification gate except the final fingerprint call. Actual Git path-filtered
and raw object hashes agree for that archive. Evidence:
`results/ground_offset_binary_fingerprint_candidate_2026-10-05`.
No registered success path was run; the prior header exception review remains
applicable because its entire tested block is unchanged.

'''
anchor='At the earlier11776 phase, install that exact header repair after freeze release\n';assert s.count(anchor)==1;s=s.replace(anchor,addition+anchor)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,additional_private_cumulative_driver_pid=1509758,frozen_inputs_revalidated=len(protected),additional_freeze_inputs_revalidated=len(additional),binary_candidate_file_manifest_sha256=sha(packet/'file-manifest.json'),actual_git_binary_object_equals_raw=a,registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items());print(json.dumps(dict(utc=stamp,live_jobs=live['live_jobs'],frozen_inputs_revalidated=len(protected),additional_inputs_revalidated=len(additional),handover_sha256=sha(note))))
