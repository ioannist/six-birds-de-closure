from pathlib import Path
import datetime, hashlib, json, re, subprocess

repo = Path('/home/repos/six-birds-de-closure')
out = repo / 'results/native_campaign_stream_verification_2026-10-05'
note = repo / 'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md'
snapshot = out / 'snapshot-file-manifest.json'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

offset = repo / 'results/ground_offset_header_installation_candidate_2026-10-05'
native = repo / 'results/native_registered_original_audit_installation_candidate_2026-10-05'
for packet in [offset, native]:
    assert all(sha(packet / p) == h for p, h in json.loads((packet / 'file-manifest.json').read_text()).items())
op = json.loads((offset / 'installation-plan.json').read_text())
np = json.loads((native / 'installation-plan.json').read_text())
assert (op['registered_file_changes'], op['historical_leaf_freeze_changes']) == (21, 20)
assert (np['native_modules'], np['native_fresh_declarations'], np['prospective_default_declarations'], np['source_archive_members']) == (1772, 20798, 32574, 1786)
assert not op['new_proof_object_installations'] and not np['qualified_objects_copied']
entrypoints = [Path('/tmp') / n for n in (
    'de_offset_header_install_journal_candidate.py',
    'de_native_registered_install_original_audit_journal_candidate.py',
    'de_native_registered_verify_original_audit_candidate.py',
    'de_native_registered_build_original_audit_candidate.py',
    'de_offset_registered_cumulative_audit_candidate.py')]
assert all(p.is_file() for p in entrypoints)
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
start = s.index('## Required registered integration order')
end = s.index('Known false/project-sized claims remain parked', start)
s = s[:start] + '''## Required registered integration order

These are the current actions. Earlier preparation inventories above are
historical evidence and must not replace these reviewed candidates or gates.

1. Finish the regular coupling15 entries, sixty verdicts, prefix failures and
   original twelve-sample aggregate. Finish Q/S/F and both supplemental
   qualified campaigns. Release every active source freeze only on authoritative
   terminal completion; preserve its protected inputs while its owner is live.
2. Preserve the old failed family receipts and driver log before fresh commands.
   Apply `/tmp/de_offset_header_install_journal_candidate.py --mode apply`
   only after its existing release/private-proof gates pass. Its exact reviewed
   21-file source plan installs18 namespace repairs, the renderer repair, the
   11776-query import-header hoist and the latest whole-offset verifier. Exactly
   20 targets intersect the historical leaf freeze; all other inputs remain
   unchanged. Preserve originals and per-file attempted/completed journals.
   No compiled proof objects are installed. Candidate/helper controls do not
   establish full apply success.
3. Run genuine registered family/aggregate commands and the default10003-job
   Lake build with explicitLEAN_NUM_THREADS=4. Require6909 exact statement/axiom
   checks,421-step replay,440-source regeneration and every inherited semantic
   and provenance gate. Run the fresh actual registered11776-query cumulative
   audit using `/tmp/de_offset_registered_cumulative_audit_candidate.py` and
   close the whole-offset verifier gate before changing native registration.
   The isolated completed11776 audit is prerequisite evidence, not this fresh
   registered command; concatenated historical receipts are not a substitute.
4. Apply `/tmp/de_native_registered_install_original_audit_journal_candidate.py`
   in apply mode only after its release/private/whole-offset gates pass. The
   exact source plan in
   `results/native_registered_original_audit_installation_candidate_2026-10-05`
   covers1772 native modules,20798 fresh declarations,32574 cumulative queries
   and1786 source targets. Preserve the1771/32565 and earlier candidates as
   history. Use the extended checker/runner
   `/tmp/de_native_registered_verify_original_audit_candidate.py` and
   `/tmp/de_native_registered_build_original_audit_candidate.py`; require fresh
   actual registered builds,20798 printed statement checks and one complete
   32574-query standard-only cumulative axiom command. Commands and receipts
   must recordLEAN_NUM_THREADS=4 and the exact sources, configurations, objects
   and logs. Retain every inherited proof, replay, semantic and provenance gate,
   including the new original-audit nine-declaration supplement. Exact source
   installation copies no compiled proof object. Full apply/build success paths
   still need actual execution and review; preparation does not certify them.
5. Update mathematical coverage and repository documentation to checked scopes,
   finish source/object/provenance verification, commit the completed changes
   and check the resulting worktree. Leave paper and original runtime unchanged.

''' + s[end:]
hist = out / 'history' / ('handover-' + stamp.strftime('%H%M%S'))
hist.mkdir()
(hist / note.name).write_bytes(note.read_bytes())
(hist / 'preceding-snapshot-file-manifest.json').write_bytes(snapshot.read_bytes())
(hist / 'update_driver.py').write_bytes(Path(__file__).read_bytes())
(hist / 'verification.json').write_text(json.dumps({
    'utc': stamp.isoformat(), 'live': live,
    'offset_plan_sha256': sha(offset / 'installation-plan.json'),
    'native_plan_sha256': sha(native / 'installation-plan.json'),
    'entrypoint_sha256': {str(p): sha(p) for p in entrypoints},
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
    'handover_sha256': sha(note), 'integration_instruction_counts': [21,1772,20798,32574,1786],
    'registered_sources_changed': False, 'goal_complete': False}))
