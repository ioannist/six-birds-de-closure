"""Read back the completed auxiliary packet; requires observed API success."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path('/home/repos/six-birds-de-closure')
LEAN = ROOT / 'lean'
OUT = ROOT / 'results/native_registered_parallel_stable_pairs_2026-10-07'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text())

def main():
    actual = load(OUT / 'actual-exec-result.json')
    assert actual['session_id'] == 12765 and actual['exit_code'] == 0
    intent = load(OUT / 'intent.json')
    terminal = load(OUT / 'terminal.json')
    build = load(OUT / 'build-terminal.json')
    objects = load(OUT / 'objects-snapshot.json')
    selected = intent['planned_unbuilt']
    assert len(selected) == 299 and selected == sorted(set(selected))
    assert all(re.fullmatch(r'SbtCosmo\.Derivation\.NativeStableSeed\d{3}\.Pair\d{3}', n) for n in selected)
    assert intent['command'] == ['lake', 'build'] + ['+' + n for n in selected]
    assert intent['cwd'] == str(LEAN)
    assert intent['environment_overrides'] == {'LEAN_NUM_THREADS': '4'}
    assert intent['unbuilt_overlap_with_main_cycle20_and30'] == []
    assert intent['proof_objects_copied'] == 0
    assert build['terminal_exit_code'] == terminal['terminal_exit_code'] == 0
    for field in ['command', 'cwd', 'environment_overrides']:
        assert build[field] == intent[field]
    assert build['intent_sha256'] == sha(OUT / 'intent.json')
    assert build['log_sha256'] == sha(OUT / 'build.log')
    assert sha(OUT / 'driver.py') == intent['driver_sha256'] == sha('/tmp/de_registered_parallel_stable_pairs_2026-10-07.py')
    assert intent['registered_plan_sha256'] == sha(ROOT / 'results/native_registered_aggregate_installation_candidate_2026-10-06/installation-plan.json')
    assert intent['full_source_snapshot_sha256'] == sha('/tmp/de_native_registered_original_audit_receipts/source-snapshot.json')
    snapshot = load('/tmp/de_native_registered_original_audit_receipts/source-snapshot.json')
    assert intent['local_dependencies'] == len(intent['source_sha256'])
    for path, digest in intent['source_sha256'].items():
        assert sha(path) == digest == snapshot[path], path
    assert set(objects) == set(selected)
    for name, digest in objects.items():
        assert sha(LEAN / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')) == digest, name
    log = (OUT / 'build.log').read_text()
    assert 'Build completed successfully' in log
    assert not re.search(r'error:|warning:|Traceback|build failed', log)
    assert set(selected) <= set(re.findall(r'Built (SbtCosmo\.Derivation\.\S+)', log))
    for field in ['selected_targets', 'selected_objects_checked', 'genuinely_reported_built_selected_modules']:
        assert terminal[field] == 299
    assert terminal['proof_objects_copied'] == 0
    assert terminal['full_registered_build_still_required'] is True
    assert terminal['full_axiom_and_statement_audits_still_required'] is True
    assert terminal['goal_complete'] is False
    assert not (OUT / 'readback-verification.json').exists()
    (OUT / 'readback-driver.py').write_bytes(Path(__file__).read_bytes())
    result = dict(utc=datetime.now(timezone.utc).isoformat(), observed_session_id=12765,
                  observed_exit_code=0, selected_modules=299,
                  current_source_bindings_checked=len(intent['source_sha256']),
                  current_object_bindings_checked=299, command_and_log_bindings_checked=True,
                  readback_driver_sha256=sha(__file__), proof_objects_archived=0,
                  verification_scope='Auxiliary pair compilation only',
                  full_registered_build_and_audits_still_required=True, goal_complete=False)
    (OUT / 'readback-verification.json').write_text(json.dumps(result, indent=2) + '\n')
    manifest = {p.name: sha(p) for p in sorted(OUT.iterdir()) if p.is_file() and p.name != 'file-manifest.json'}
    assert not any(p.endswith(('.olean', '.ilean', '.o')) for p in manifest)
    (OUT / 'file-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert all(sha(OUT / name) == digest for name, digest in load(OUT / 'file-manifest.json').items())
    print(json.dumps(result))

if __name__ == '__main__':
    main()
