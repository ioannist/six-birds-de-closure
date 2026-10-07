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
additional=json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text())
assert len(additional)==3936 and all(sha(p)==h for p,h in additional.items())
names=['original_audit_nonidentifiability_dependency_checkpoint_2026-10-05','native_registered_original_audit_installation_candidate_2026-10-05','native_registered_original_audit_verification_candidate_2026-10-05','native_registered_original_audit_installer_candidate_2026-10-05']
packets=[repo/'results'/n for n in names]
for p in packets:assert all(sha(p/f)==h for f,h in json.loads((p/'file-manifest.json').read_text()).items())
archive=json.loads((packets[0]/'checkpoint-verification.json').read_text());assert archive['archive_members_verified']==2674 and archive['checked_declarations']==9
verify=json.loads((packets[2]/'checks.json').read_text());assert len(verify['rejected_controls'])==9 and verify['registered_commands_started']==0
install=json.loads((packets[3]/'checks.json').read_text());assert len(install['rejected_preimage_controls'])==4 and not install['registered_sources_changed']
live=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_native_live_poll_v2.py'],text=True));assert not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
start=s.index('Use the new header-aware source candidate in');end=s.index('\nPrevious installation/runtime candidates below',start)
s=s[:start]+'''Use the latest original-audit extended source candidate in
`results/native_registered_original_audit_installation_candidate_2026-10-05`
(1786 targets,1772 modules,20798 native declarations,32574 cumulative queries),
together with
`results/native_registered_original_audit_verification_candidate_2026-10-05`
and the source-only installer candidate noted below. The prior valid1771/20789/
32565 header candidate remains its immutable base. Source preflight and both
private supplement gates pass; actual registered build/audits remain pending.
'''+s[end:]
start=s.index('Separate canonical1-module/9-declaration candidate:');end=s.index('## Required registered integration order',start)
s=s[:start]+'''The separate canonical1/9 candidate and every earlier plan remain immutable.
Its complete historical dependencies are now separately archived in
`results/original_audit_nonidentifiability_dependency_checkpoint_2026-10-05`:
2674 members were read back and hashed, including all2660 prior bindings,
1327 project dependency objects and the original registration file. This
preserves historical proof bytes before legitimate registered rebuilding;
it is not another compilation or a registered command.

The combined native source candidate, verifier/runner and source installer
are now prepared for1772 modules,20798 native declarations,32574 cumulative
queries and1786 source targets. Durable packets:
`results/native_registered_original_audit_installation_candidate_2026-10-05`,
`results/native_registered_original_audit_verification_candidate_2026-10-05`,
`results/native_registered_original_audit_installer_candidate_2026-10-05`.
Latest entry points:
`/tmp/de_native_registered_verify_original_audit_candidate.py`,
`/tmp/de_native_registered_build_original_audit_candidate.py`,
`/tmp/de_native_registered_install_original_audit_candidate.py`.

The checker preserves the inherited parent candidate/proof/release/whole-offset
gates and adds the exact9-declaration historical proof/archive gate. The current
original source equations/configuration must agree; exactly the historical or
proposed native registration is allowed. Fresh registered theorem scopes and
all32574 standard-only cumulative queries remain mandatory. Nine altered-source/
receipt/type controls are rejected, with four explicit virtual metadata reads.
Actual registered checker/runner preflights exit2 for missing qualified evidence,
before commands or receipts. Their full success path remains untested.

The native source installer requires released freezes, all private gates and
the completed genuine10003/11776 whole-offset phase. It verifies every target
preimage, archives originals, records source/object snapshots and intent/journal,
then atomically installs only source files. Objects/non-target equations must
remain unchanged. An isolated helper fixture exercises actual replacement/new
file operations and rejects four preimage/path controls. Actual apply preflight
exits2 for live owner662901 before registered mutation/receipt creation; full
apply success is untested. It follows the earlier21-file source stage, not a
replacement for that stage or its audits. No registered integration, paper
edit or goal completion is claimed. See
`math/GROUND_NATIVE_ORIGINAL_AUDIT_INTEGRATION_2026-10-05.md`.

Latest live observation:stable leaves'''+str(live['progress']['stable']['passed'])+'''/597,
qualified modules'''+str(live['progress']['qualified']['passed'])+'''/1734,'''+str(live['live_jobs'])+''' confirmed live jobs, priority15
verified terminal0/289 modules, no recorded new failures. Earlier1771/20789/
32565 instructions below are historical base scopes; use the latest32574
candidate/checker/installer for the final native phase. The preceding11776/
10003 phase and all parent proof/freeze gates remain unchanged. This scoped
value-selection return does not restore unrestricted no-value-law language
or physical identification.

'''+s[end:]
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir()
(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes());(hist/'live_poll_v2.py').write_bytes(Path('/tmp/de_native_live_poll_v2.py').read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,new_packet_manifests={str(p/'file-manifest.json'):sha(p/'file-manifest.json') for p in packets},frozen_inputs_revalidated=len(protected),completed_private_audit_freeze_revalidated=len(additional),registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n')
assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items())
print(json.dumps(dict(utc=stamp,live_jobs=live['live_jobs'],progress=live['progress'],native_candidate_modules=1772,native_candidate_declarations=20798,native_candidate_cumulative_queries=32574,handover_sha256=sha(note))),flush=True)
