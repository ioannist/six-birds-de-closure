from pathlib import Path
import datetime,hashlib,json,re,subprocess
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05';note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';snapshot=out/'snapshot-file-manifest.json';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in freezes:
 for f,h in json.loads(p.read_text()).items():assert f not in protected or protected[f]==h;protected[f]=h
assert len(protected)==6262 and all(sha(p)==h for p,h in protected.items())
additional=json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text());assert len(additional)==3936 and all(sha(p)==h for p,h in additional.items())
live=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_native_live_poll_v2.py'],text=True));assert live['live_jobs']==11 and len(live['verified_terminal_jobs'])==1 and not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
assert not Path('/proc/4049651/cmdline').exists() and not Path('/proc/1509758/cmdline').exists()
folders=['native_stable15_full_return_checked_2026-10-05','audit_manifest_header_repair_checked_2026-10-05','native_original_stable5_return_2026-10-05'];packets=[repo/'results'/n for n in folders]
for packet in packets:assert all(sha(packet/p)==h for p,h in json.loads((packet/'file-manifest.json').read_text()).items())
a=json.loads((packets[0]/'checkpoint-verification.json').read_text());assert a['standard_only'] and a['checked_declarations']==27 and a['archive_members_verified']==1175 and a['bound_modules']==965
a=json.loads((packets[1]/'checkpoint-verification.json').read_text());assert a['standard_only'] and a['checked_declarations']==11776 and a['archive_members_verified']==1997 and not a['registered_command']
a=json.loads((packets[2]/'audit-summary.json').read_text());assert a['standard_only'] and a['checked_declarations']==15 and a['coupling']=='5' and a['original_sample_index']==7 and a['archive_members']==311
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {live["progress"]["stable"]["passed"]}/597 scheduled',s);s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
start=s.index('A fresh isolated11776 cumulative audit is live at PID');end=s.index('\nUse the new header-aware source candidate',start)
s=s[:start]+'''The fresh isolated11776 cumulative audit completed with actual compiler and
driver exit0 (session68289); PID1509758 has exited. All ordered declarations
use only standard axioms. The durable packet is
`results/audit_manifest_header_repair_checked_2026-10-05`:1997 verified archive
members,1965 direct source/object bindings and3936 revalidated inputs. Every
direct source and all19 private namespace objects are archived;1946 registered
objects are historical hash bindings, not archived copies. Actual command,
source, environment, terminal and log are preserved. No registered source was
changed and this is not the mandatory registered11776 audit. The preparation
candidate remains immutable with its historical pending flag.
'''+s[end:]
start=s.index('A separate recovery is live at PID4049651');end=s.index('## Recovery and qualification chain',start)
s=s[:start]+'''The separate priority15 recovery PID4049651 completed and exited with actual
terminal0. Its289 modules comprise73 retained and216 fresh ones, with178
single-step leaves,89 pairs,18 prerequisites and4 aggregates. Its combined27
printed declaration/standard-only axiom audit passed. The exact original seed
enters at178 updates and converges to the actual negative coupled ground, with
all iterates guarded/unit and all-site density limits. Every source diagnostic
conjunction at updates1..60 still fails, witnessed by its last-update component.
Thus finite-budget failure is compatible with eventual convergence at15.
No earliest successful update or IEEE theorem is claimed. The earlier finite18
packet remains unchanged. The full packet has1175 verified archived members
and965 source/object bindings:
`results/native_stable15_full_return_checked_2026-10-05`;
`math/GROUND_NATIVE_STABLE15_FULL_RETURN_2026-10-05.md`.
The original regular15 campaign and twelve-sample aggregate remain mandatory;
production plans and paths are unchanged. Its2777 historical frozen inputs were
revalidated, along with the other still-live freezes. Use the new read-only
`/tmp/de_native_live_poll_v2.py`, which distinguishes this verified terminal0
job from missing/unexplained handles; the original helper remains unchanged.

'''+s[end:]
old='''  Earlier checked zero/0.1/0.3/0.5/1 returns and evidence remain. Couplings5,10,15
  remain pending in the regular stable campaign. No production plan count changes.'''
new='''  Original coupling5/sample7 is now checked: its15 infinite-return/sixty
  declaration audits passed, with all four source tests passing at60 and all
  iterates guarded/unit. The durable packet has311 verified members,109 private
  and675 repository bindings:
  `results/native_original_stable5_return_2026-10-05`;
  `math/GROUND_NATIVE_ORIGINAL_STABLE5_RETURN_2026-10-05.md`.
  Its sample-index metadata is derived from the checked index variable.
  Earlier checked zero/0.1/0.3/0.5/1 returns and evidence remain. Couplings10,15
  remain pending in the original regular campaign; priority15 is checked
  separately. No production plan count changes.'''
assert s.count(old)==1;s=s.replace(old,new)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir();(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes());(hist/'live_poll_v2.py').write_bytes(Path('/tmp/de_native_live_poll_v2.py').read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,priority15_driver_completed=True,private_cumulative_driver_completed=True,frozen_inputs_revalidated=len(protected),completed_audit_freeze_inputs_revalidated=len(additional),checked_packet_manifests={str(p/'file-manifest.json'):sha(p/'file-manifest.json') for p in packets},registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items());print(json.dumps(dict(utc=stamp,live_jobs=live['live_jobs'],progress=live['progress'],checked_packets=folders,handover_sha256=sha(note))))
