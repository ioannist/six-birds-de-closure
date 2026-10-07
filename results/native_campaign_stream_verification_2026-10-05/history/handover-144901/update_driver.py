from pathlib import Path
import datetime, hashlib, json, re, subprocess

repo = Path('/home/repos/six-birds-de-closure')
out = repo / 'results/native_campaign_stream_verification_2026-10-05'
note = repo / 'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md'
snapshot = out / 'snapshot-file-manifest.json'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

freezes = [Path('/tmp') / name for name in (
    'de-native-campaign-qualified-stream-freeze.json',
    'de-native-seed-real-returns-qualified-stream-freeze.json',
    'de-native-campaign-verification-stream-finish-freeze.json')]
freezes += [Path('/tmp') / name / 'source-freeze.json' for name in (
    'de_native_stable15_priority_recovery',
    'de_native_additional_constructions_stream_qualified',
    'de_source_execution_supplement_stream_qualified')]
bound = {}
for freeze in freezes:
    for p, h in json.loads(freeze.read_text()).items():
        assert p not in bound or bound[p] == h
        bound[p] = h
assert len(bound) == 6262
extra = json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text())
assert len(extra) == 3936
assert all(sha(p) == h for p, h in (bound | extra).items())
live = json.loads(subprocess.check_output(
    ['/usr/bin/python3', '/tmp/de_native_live_poll_v2.py'], text=True))
assert not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
ready = json.loads(subprocess.check_output(
    ['/usr/bin/python3', '/tmp/de_checkpoint_stable10_return.py', '--mode', 'preflight'], text=True))
assert not ready['proof_success_claimed'] and not ready['checkpoint_created']
stamp = datetime.datetime.now(datetime.timezone.utc)
s = note.read_text()
assert (out / 'handover.md').read_bytes() == note.read_bytes()
assert s.count('## Prepared next stable-sample checkpoint') == 1
s, n = re.subn(r'Recorded [^\n]+',
    f'Recorded {stamp.isoformat()}. This is a recovery pointer; current sources, terminal', s, count=1)
assert n == 1
s, n = re.subn(r'(The original stable leaf driver PID2558747 has )\d+(/597 scheduled)',
    lambda m: m[1] + str(live['progress']['stable']['passed']) + m[2], s)
assert n == 1
s, n = re.subn(r'with \d+/1734 terminal-zero',
    f"with {live['progress']['qualified']['passed']}/1734 terminal-zero", s)
assert n == 1
s, n = re.subn(r'Latest live observation:stable leaves\d+/597,\nqualified modules\d+/1734,',
    f"Latest live observation:stable leaves{live['progress']['stable']['passed']}/597,\nqualified modules{live['progress']['qualified']['passed']}/1734,", s)
assert n == 1
hist = out / 'history' / ('handover-' + stamp.strftime('%H%M%S'))
hist.mkdir()
(hist / note.name).write_bytes(note.read_bytes())
(hist / 'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes())
(hist / 'update_driver.py').write_bytes(Path(__file__).read_bytes())
note.write_text(s)
(out / 'handover.md').write_text(s)
(hist / 'verification.json').write_text(json.dumps({
    'utc': stamp.isoformat(), 'live': live, 'stable10_preflight': ready,
    'frozen_inputs_revalidated': len(bound),
    'completed_private_audit_freeze_revalidated': len(extra),
    'registered_sources_changed': False, 'goal_complete': False,
}, indent=2) + '\n')
manifest = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
    if p.is_file() and p != snapshot}
snapshot.write_text(json.dumps(manifest, indent=2) + '\n')
assert all(sha(out / p) == h for p, h in manifest.items())
assert all(sha(p) == h for p, h in (bound | extra).items())
assert note.read_bytes() == (out / 'handover.md').read_bytes()
print(json.dumps({'utc': stamp.isoformat(), 'progress': live['progress'],
    'stable10_collector_ready': ready['ready_for_checkpoint'],
    'handover_sha256': sha(note), 'registered_sources_changed': False}))
