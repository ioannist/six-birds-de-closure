from pathlib import Path
import datetime, hashlib, json, re, subprocess

repo = Path('/home/repos/six-birds-de-closure')
out = repo / 'results/native_campaign_stream_verification_2026-10-05'
note = repo / 'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md'
snapshot = out / 'snapshot-file-manifest.json'
packet = repo / 'results/native_original_stable10_return_2026-10-05'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

for p, h in json.loads((packet / 'file-manifest.json').read_text()).items():
    assert sha(packet / p) == h, p
d = json.loads((packet / 'audit-summary.json').read_text())
assert d['terminal_exit_code'] == 0 and d['standard_only']
assert (d['coupling'], d['original_sample_index'], d['actual_entry_update']) == ('10', 8, 60)
assert (d['checked_declarations'], d['leaf_certificates'], d['paired_certificates']) == (15, 60, 30)
assert (d['archive_members'], d['private_modules'], d['repository_modules']) == (311, 109, 675)
assert d['original_seed_infinite_return_checked'] and d['sixty_four_tests_pass']
assert not d['repository_registered'] and not d['goal_complete']
bound = {}
freezes = [Path('/tmp') / n for n in (
    'de-native-campaign-qualified-stream-freeze.json',
    'de-native-seed-real-returns-qualified-stream-freeze.json',
    'de-native-campaign-verification-stream-finish-freeze.json')]
freezes += [Path('/tmp') / n / 'source-freeze.json' for n in (
    'de_native_stable15_priority_recovery',
    'de_native_additional_constructions_stream_qualified',
    'de_source_execution_supplement_stream_qualified')]
for f in freezes:
    for p, h in json.loads(f.read_text()).items():
        assert p not in bound or bound[p] == h
        bound[p] = h
extra = json.loads(Path('/tmp/de_audit_manifest_header_repair/cumulative-source-freeze.json').read_text())
assert len(bound) == 6262 and len(extra) == 3936
assert all(sha(p) == h for p, h in (bound | extra).items())
live = json.loads(subprocess.check_output(['/usr/bin/python3', '/tmp/de_native_live_poll_v2.py'], text=True))
assert not live['missing_or_changed_processes'] and not live['recorded_failure_logs']
assert 8 in live['regular_stable_sample_indices_with_both_audits']
s = note.read_text()
assert note.read_bytes() == (out / 'handover.md').read_bytes()
stamp = datetime.datetime.now(datetime.timezone.utc)
s = re.sub(r'Recorded [^\n]+', f'Recorded {stamp.isoformat()}. This is a recovery pointer; current sources, terminal', s, count=1)
s, n = re.subn(r'(The original stable leaf driver PID2558747 has )\d+(/597 scheduled)',
    lambda m: m[1] + str(live['progress']['stable']['passed']) + m[2], s)
assert n == 1
s, n = re.subn(r'with \d+/1734 terminal-zero', f"with {live['progress']['qualified']['passed']}/1734 terminal-zero", s)
assert n == 1
s, n = re.subn(r'Latest live observation:stable leaves\d+/597,\nqualified modules\d+/1734,',
    f"Latest live observation:stable leaves{live['progress']['stable']['passed']}/597,\nqualified modules{live['progress']['qualified']['passed']}/1734,", s)
assert n == 1
old = 'Earlier checked zero/0.1/0.3/0.5/1 returns and evidence remain. Couplings10,15\n  remain pending in the original regular campaign; priority15 is checked\n  separately. No production plan count changes.'
new = '''Original coupling10/sample8 is now checked as well:60 single-step and30
  paired certificates,15 actual statement/standard-axiom checks and311 verified
  archive members. Its original seed enters after60 updates and converges to
  the actual negative ground with all guards/unit norms and all-site density
  limits; all four source diagnostics pass at60. Packet:
  `results/native_original_stable10_return_2026-10-05`;
  note:`math/GROUND_NATIVE_ORIGINAL_STABLE10_RETURN_2026-10-05.md`.
  Earlier checked zero/0.1/0.3/0.5/1 returns and evidence remain. Coupling15
  remains pending in the original regular campaign; priority15 is checked
  separately. No production plan count changes.'''
assert s.count(old) == 1
s = s.replace(old, new)
start = s.index('## Prepared next stable-sample checkpoint')
end = s.index('## Required registered integration order', start)
s = s[:start] + '''## Completed original coupling10 checkpoint

Both actual family and sixty-update compiler/audit exit0 markers are present.
`/usr/bin/python3 /tmp/de_checkpoint_stable10_return.py --mode checkpoint`
completed with actual exit0 and preserved
`results/native_original_stable10_return_2026-10-05`.
Its15 exact declarations use standard axioms only. All60 leaves,30 pairs,
311 archive members,109 private and675 repository module bindings were checked;
6262 frozen inputs stayed unchanged. Archive readback/hash verification passed.
This collector ran no new Lean command, and driver snapshots do not certify
completion of their full campaigns. The preparation candidate's earlier
pending flags remain historical. Do not rerun checkpoint mode into its already
existing packet. Regular15, the original twelve-sample aggregate, qualification
and registered integration still require actual completed evidence.

''' + s[end:]
hist = out / 'history' / ('handover-' + stamp.strftime('%H%M%S'))
hist.mkdir()
(hist / note.name).write_bytes(note.read_bytes())
(hist / 'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes())
(hist / 'update_driver.py').write_bytes(Path(__file__).read_bytes())
(hist / 'verification.json').write_text(json.dumps({
    'utc': stamp.isoformat(), 'live': live,
    'stable10_packet_manifest_sha256': sha(packet / 'file-manifest.json'),
    'stable10_summary_sha256': sha(packet / 'audit-summary.json'),
    'stable10_math_note_sha256': sha(repo / 'math/GROUND_NATIVE_ORIGINAL_STABLE10_RETURN_2026-10-05.md'),
    'frozen_inputs_revalidated': len(bound),
    'completed_private_audit_freeze_revalidated': len(extra),
    'registered_sources_changed': False, 'goal_complete': False,
}, indent=2) + '\n')
note.write_text(s)
(out / 'handover.md').write_text(s)
manifest = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p != snapshot}
snapshot.write_text(json.dumps(manifest, indent=2) + '\n')
assert all(sha(out / p) == h for p, h in manifest.items())
assert all(sha(p) == h for p, h in (bound | extra).items())
assert note.read_bytes() == (out / 'handover.md').read_bytes()
print(json.dumps({'utc': stamp.isoformat(), 'progress': live['progress'],
    'handover_sha256': sha(note), 'stable10_checkpoint_complete': True,
    'registered_sources_changed': False, 'goal_complete': False}))
