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
packets=[repo/'results'/n for n in ['original_audit_nonidentifiability_checked_2026-10-05','original_audit_nonidentifiability_production_candidate_2026-10-05']]
for p in packets:assert all(sha(p/f)==h for f,h in json.loads((p/'file-manifest.json').read_text()).items())
checked=json.loads((packets[0]/'checkpoint-verification.json').read_text());assert checked['standard_only'] and checked['checked_declarations']==9 and checked['compile_terminal_exit_code']==checked['audit_terminal_exit_code']==0
live=json.loads(subprocess.check_output(['/usr/bin/python3','/tmp/de_native_live_poll_v2.py'],text=True));assert not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text();s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'with \d+/1734 terminal-zero',f'with {live["progress"]["qualified"]["passed"]}/1734 terminal-zero',s)
s=s.replace('All twelve listed parents were confirmed live\nfor this update; no agents were spawned.',f'{live["live_jobs"]} listed parents are live at this update; priority15 is a verified\nterminal-zero completed job. No agents were spawned.')
marker='## Required registered integration order'
assert s.count(marker)==1
new='''## New original-audit value nonidentifiability construction

A fresh isolated module and all nine exact printed-statement/transitive-axiom
queries passed, with standard axioms only. Its finite interface is defined
from the actual original sixty-update four-test proposition and bridged through
the earned original verdict theorem:15 distinct offsets pass. Original -8/-2
are an admitted equal-verdict/different-offset split pair. Its infinite interface
is existence of a limit for the actual original seed orbit, earned from the
unconditional original eighteen-case theorem:all18 distinct offsets pass.
Neither Boolean interface admits a decoder recovering every actual control.
The infinite Boolean definition is explicitly classical/noncomputable.
The scalar is the offset input control, not energy, closure price or physical
Lambda; fuller traces/source information and extra value-selection criteria
are outside this no-decoder statement. No added ledger or altered dynamics.

Checked packet:
`results/original_audit_nonidentifiability_checked_2026-10-05`;
note:`math/GROUND_ORIGINAL_AUDIT_NONIDENTIFIABILITY_2026-10-05.md`.
1327 project dependency modules and2660 inputs are hash-bound unchanged;
dependencies are historical object bindings, not archived copies. Actual own
source/object, commands, logs, terminal receipts and freezes are preserved.
Both earlier actual terminal1 attempts are explicitly preserved as failures.

Separate canonical1-module/9-declaration candidate:
`results/original_audit_nonidentifiability_production_candidate_2026-10-05`.
It has not been installed. All earlier plans/candidates remain unchanged.
The combined native installation/checker/runner must now be explicitly extended
to1772 modules,20798 native declarations,32574 cumulative queries and1786 target
files. The1771/20789/32565 candidates above remain historical prepared bases;
they do not cover this add-on. Existing earlier11776/10003 phase and parent
proof/freeze gates remain unchanged. This direct scoped value-selection return
does not restore unrestricted no-value-law language or physical identification.

'''
s=s.replace(marker,new+marker)
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir()
(hist/note.name).write_bytes(note.read_bytes());(hist/'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes());(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s);(out/'handover.md').write_text(s)
(hist/'verification.json').write_text(json.dumps(dict(utc=stamp,live=live,new_packet_manifests={str(p/'file-manifest.json'):sha(p/'file-manifest.json') for p in packets},frozen_inputs_revalidated=len(protected),completed_private_audit_freeze_revalidated=len(additional),registered_sources_changed=False,goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=snapshot};snapshot.write_text(json.dumps(manifest,indent=2)+'\n')
assert all(sha(out/p)==h for p,h in manifest.items());assert all(sha(p)==h for p,h in protected.items());assert all(sha(p)==h for p,h in additional.items())
print(json.dumps(dict(utc=stamp,live_jobs=live['live_jobs'],progress=live['progress'],checked_addon_declarations=9,handover_sha256=sha(note))),flush=True)
