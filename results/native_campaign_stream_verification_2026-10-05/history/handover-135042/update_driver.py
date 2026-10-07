from pathlib import Path
import json,hashlib,subprocess,datetime,re
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';snapshot=out/'snapshot-file-manifest.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in freezes:
    for f,h in json.loads(p.read_text()).items():
        assert f not in protected or protected[f]==h
        protected[f]=h
assert len(protected)==6262 and all(sha(p)==h for p,h in protected.items())
additional=json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text());assert len(additional)==3936 and all(sha(p)==h for p,h in additional.items())
packets=[repo/'results'/n for n in ['native_installer_postreplace_failure_history_2026-10-05','native_registered_original_audit_journal_installer_candidate_2026-10-05','ground_offset_header_journal_installer_candidate_2026-10-05','offset_header_journal_review_preparation_history_2026-10-05']]
for p in packets:assert all(sha(p/f)==h for f,h in json.loads((p/'file-manifest.json').read_text()).items())
for p in packets[1:3]:
    d=json.loads((p/'checks.json').read_text());assert len(d['actual_file_operation_cases'])==5 and all(r['journal_correct'] for r in d['actual_file_operation_cases'])
    assert not d['registered_sources_changed'] and not d['full_apply_success_path_tested']
    assert [r['actual_exit_code'] for r in d['preflights']]==[0,2]
live=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_native_live_poll_v2.py'],text=True));assert not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=s.replace('/tmp/de_native_registered_install_original_audit_candidate.py','/tmp/de_native_registered_install_original_audit_journal_candidate.py')
s=s.replace('/tmp/de_offset_header_install_candidate.py','/tmp/de_offset_header_install_journal_candidate.py')
s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
s=re.sub(r'Latest live observation:stable leaves\d+/597,\nqualified modules\d+/1734,',f'Latest live observation:stable leaves{live["progress"]["stable"]["passed"]}/597,\nqualified modules{live["progress"]["qualified"]["passed"]}/1734,',s)
marker='## Required registered integration order';assert s.count(marker)==1
new='''## Source installer journal boundary repair

An actual isolated post-replacement directory-flush fault showed that the
historical native writer could replace a target before the caller added it to
the completed list. Exact executed source and before/observed-after bytes are
preserved in `results/native_installer_postreplace_failure_history_2026-10-05`.
This is a reporting repair, not a mathematics downgrade or registered mutation.

Use these corrected source installers:
`/tmp/de_offset_header_install_journal_candidate.py` for the preceding21 files;
`/tmp/de_native_registered_install_original_audit_journal_candidate.py` for1786
native source targets. Their durable packets are
`results/ground_offset_header_journal_installer_candidate_2026-10-05` and
`results/native_registered_original_audit_journal_installer_candidate_2026-10-05`.
Both record attempted targets before writing and, on failure, pending targets
and observed original/proposed hashes. Three actual pre/post-replacement fault
cases and two actual normal file-operation cases pass for each stage. The
native inherited guards/atomic writer are unchanged; the21-file source/private
11776/release gates are unchanged and its proof dependency uses the reviewed
original-audit-extended verifier. Shared writer/journal functions have equal
ASTs. Candidate preflights exit0 and apply preflights exit2 for the live freeze
owner, before registered mutation or receipt directories. Full apply success
paths and ensuing registered builds/audits remain pending.

A first21-file-stage review collector expected a native-only pending-response
field and exited1 after its file-operation cases. The actual failed collector,
fixtures and tool-observed exit/error are preserved in
`results/offset_header_journal_review_preparation_history_2026-10-05`; missing
captured subprocess stdout is not fabricated. The corrected collector passed
the actual stage schema. Old packets/plan/source candidates remain immutable.
See `math/GROUND_SOURCE_INSTALLATION_JOURNAL_REVIEW_2026-10-05.md`.

'''
s=s.replace(marker,new+marker)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,new_packet_manifests={str(p/'file-manifest.json'):sha(p/'file-manifest.json') for p in packets},frozen_inputs_revalidated=len(protected),completed_private_audit_freeze_revalidated=len(additional),registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items())
print(json.dumps(dict(utc=stamp,live_jobs=live['live_jobs'],progress=live['progress'],corrected_installer_stages=2,actual_file_operation_cases=10,handover_sha256=sha(note))),flush=True)
