from pathlib import Path
import datetime,hashlib,json,re
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';snapshot=out/'snapshot-file-manifest.json';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in freezes:
 for f,h in json.loads(p.read_text()).items():assert f not in protected or protected[f]==h;protected[f]=h
assert len(protected)==6262 and all(sha(p)==h for p,h in protected.items())
audit_root=Path('/tmp/de_audit_manifest_header_repair');additional=json.loads((audit_root/'cumulative-source-freeze.json').read_text());assert all(sha(p)==h for p,h in additional.items())
jobs=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode().strip()
 except (FileNotFoundError,ProcessLookupError,PermissionError):continue
 if cmd=='/usr/bin/python3 /tmp/de_run_repaired_cumulative_audit.py':jobs.append(int(p.name))
assert len(jobs)==1 and not (audit_root/'cumulative-terminal.json').exists()
counts={}
for key,p,total in [('stable','/tmp/de-native-stable-seed-leaves-driver.log',597),('priority','/tmp/de-native-stable15-priority-recovery-driver.log',289),('qualified','/tmp/de-native-campaign-qualified-stream-driver.log',1734)]:
 raw=Path(p).read_text();assert not re.search(r'terminal [1-9]|Traceback',raw);counts[key]=int(re.findall(r'completed (\d+) /'+str(total),raw)[-1])
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {counts["stable"]}/597 scheduled',s);s=re.sub(r'\d+/289 total terminal-zero',f'{counts["priority"]}/289 total terminal-zero',s);s=re.sub(r'with \d+/1734 terminal-zero',f'with {counts["qualified"]}/1734 terminal-zero',s)
addition=f'''## Critical current audit-layout correction

Actual Lean4.28 controls establish that imports after queries are invalid. This
affects the committed4867, frozen current11776 and historical prepared32565
default manifests. Dedicated valid-layout audits and compiled theorem modules
retain their stated scopes; none certifies those invalid layouts. The exact
repair moves every import to the header, preserving import order, every
nonimport byte and all ordered queries. Raw byte-prefix preservation is
explicitly superseded. Historical files remain archived; no frozen registered
source changed. See `math/GROUND_AUDIT_MANIFEST_HEADER_REPAIR_2026-10-05.md`.

A fresh isolated11776 cumulative audit is live at PID{jobs[0]}, tool session68289:
`/tmp/de_run_repaired_cumulative_audit.py`; root
`/tmp/de_audit_manifest_header_repair`. Its actual terminal, log and summary are
authoritative; no terminal exists at recording. Its additional{len(additional)}
source/object/helper bindings were revalidated. It is not registered execution.

Use the new header-aware source candidate in
`results/native_registered_header_installation_candidate_2026-10-05` (1783
files,1771 modules,20789 declarations,32565 cumulative queries), together with
`results/native_registered_header_verification_candidate_2026-10-05`.
Previous installation/runtime candidates below are historical and their
default manifest layouts must not be installed. Source preflight passes;
registered runner correctly refuses missing qualified evidence before commands.

The new whole-offset verifier proposal is
`/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_repaired.py`:
existing19 namespace/renderer changes plus the exact manifest hoist are the
only20 allowed historical-freeze changes. The actual extracted exception
accepts those20 and rejects11 corrupted views; fresh registered receipt logic
remains untested. Evidence:
`results/ground_offset_header_verifier_candidate_2026-10-05`;
`results/ground_offset_header_exception_review_2026-10-05`.

At the earlier11776 phase, install that exact header repair after freeze release
and require a fresh actual registered11776 cumulative audit, in addition to the
10003-job build and every inherited semantic/provenance gate. Prepared runner:
`/tmp/de_offset_registered_cumulative_audit_candidate.py`; evidence:
`results/ground_offset_registered_cumulative_runner_candidate_2026-10-05`.
It refuses live freeze owners before writes. Fresh32565/20789 registered audits
remain mandatory afterward. Preserve historical audit logs and distinguish
their combined evidence from either fresh cumulative command. No full success
path, registered integration, paper revision or goal completion is claimed.

'''
assert '## Critical current audit-layout correction' not in s
s=s.replace('## Completed mathematical checks\n',addition+'## Completed mathematical checks\n',1)
s=s.replace('The existing default manifest is an exact\n   byte prefix.','The historical source candidate preserved an exact\n   byte prefix; that layout is invalid and is superseded by the header repair above.')
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,progress=counts,frozen_inputs_revalidated=len(protected),additional_audit_freeze_inputs_revalidated=len(additional),private_audit_driver_pid=jobs[0],private_audit_terminal_pending=True,registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items());print(json.dumps(dict(progress=counts,frozen_inputs_revalidated=len(protected),additional_audit_inputs_revalidated=len(additional),private_audit_pid=jobs[0],handover_sha256=sha(note))))
