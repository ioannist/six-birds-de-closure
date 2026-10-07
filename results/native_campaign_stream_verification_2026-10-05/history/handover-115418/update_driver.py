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
assert Path('/proc/1509758/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()=='/usr/bin/python3 /tmp/de_run_repaired_cumulative_audit.py';assert not Path('/tmp/de_audit_manifest_header_repair/cumulative-terminal.json').exists()
packets=[repo/'results'/n for n in ['ground_offset_header_installation_candidate_2026-10-05','ground_offset_header_installer_candidate_2026-10-05']]
for packet in packets:assert all(sha(packet/p)==h for p,h in json.loads((packet/'file-manifest.json').read_text()).items())
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {live["progress"]["stable"]["passed"]}/597 scheduled',s);s=re.sub(r'\d+/289 total terminal-zero',f'{live["progress"]["priority15"]["passed"]}/289 total terminal-zero',s);s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
addition='''The exact pre-native source installation and guarded installer are now prepared:
`results/ground_offset_header_installation_candidate_2026-10-05` and
`results/ground_offset_header_installer_candidate_2026-10-05`.
They cover21 files:18 namespace repairs, renderer,11776-query header and latest
whole-offset verifier. Original/repaired archives were read back and hashed;
exactly20 targets belong to the historical leaf freeze, whose verifier script
was not frozen. No compiled proof object is copied. Source preflight succeeds;
actual apply preflight exits2 before writes for the live source-freeze owner.
Full apply success path is untested. `/tmp/de_offset_header_install_candidate.py`
defaults to candidate mode; its apply mode additionally requires all private
native proof gates, the actual completed11776 isolated audit, unchanged release
freeze inputs, exact target preimages and recorded per-file installation.
An initial preparer expected a renderer repaired-file path that its plan does
not define. Its pre-output failure is preserved in
`results/ground_offset_header_installation_preparation_history_2026-10-05`;
the corrected preparer applies and verifies the plan's exact renderer replacement.
Before fresh registered family commands, preserve the two old failed family
receipts and driver log under history; the existing stage driver rejects old
receipt paths. Actual builds, fresh audits and whole-offset semantics remain
mandatory after source installation.

'''
anchor='At the earlier11776 phase, install that exact header repair after freeze release\n';assert s.count(anchor)==1;s=s.replace(anchor,addition+anchor)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,additional_private_cumulative_driver_pid=1509758,frozen_inputs_revalidated=len(protected),additional_freeze_inputs_revalidated=len(additional),candidate_manifests={str(p/'file-manifest.json'):sha(p/'file-manifest.json') for p in packets},registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items());print(json.dumps(dict(utc=stamp,progress=live['progress'],frozen_inputs_revalidated=len(protected),additional_inputs_revalidated=len(additional),handover_sha256=sha(note))))
