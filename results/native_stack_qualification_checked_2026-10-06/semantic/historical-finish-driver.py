"""Run the complete qualified verifier only after both proof campaigns close."""
from pathlib import Path
import hashlib, json, os, re, subprocess, time

repo = Path('/home/repos/six-birds-de-closure')
out = repo / 'results/native_aggregate_semantic_verification_2026-10-06'
verifier = Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/verify_recovery.py')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
source = json.loads(Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/source-verification-anchored.json').read_text())
assert source['source_stage_passed'] and not source['qualified_stage_passed']
assert source['module_count'] == 1738 and source['enumerated_theorem_count'] == 20634
assert source['verifier_sha256'] == sha(verifier)
freeze = {}
for name in ['/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/source-freeze.json']:
    path = Path('/tmp', name)
    for p, h in json.loads(path.read_text()).items():
        assert p not in freeze or freeze[p] == h
        freeze[p] = h
    freeze[str(path)] = sha(path)
replay = repo / 'results/native_sample_transport_2026-10-04'
for p, h in json.loads((replay / 'replay-freeze.json').read_text()).items():
    assert p not in freeze or freeze[p] == h, p
    freeze[p] = h
inputs = [verifier, Path(__file__), Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/source-verification-anchored.json')]
inputs += [replay / p for p in ['replay.json', 'replay-freeze.json', 'status.json', 'replay_driver.txt']]
for root, prefix in [('/tmp/de_native_campaign_production_preview', 'native_campaign'),
                     ('/tmp/de_native_seed_real_returns_preview', 'native_seed_real_returns')]:
    inputs += [Path(root) / 'lean/manifests' / ('check_' + prefix + '_' + stage + '.lean')
               for stage in ['statements', 'axioms']]
for p in inputs:
    h = sha(p)
    assert str(p) not in freeze or freeze[str(p)] == h, p
    freeze[str(p)] = h
freeze_path = Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/finish-source-freeze.json')
assert not freeze_path.exists()
freeze_path.write_text(json.dumps(freeze, indent=2) + '\n')

def check():
    for p, h in freeze.items():
        assert sha(p) == h, p

parents = [
    (3164894, 'python3 /tmp/de_native_campaign_aggregate_recovery_2026-10-05/build_recovery.py',
     '/tmp/de_native_campaign_aggregate_recovery_2026-10-05/driver.log',
     'All1734 qualified modules and20628 fresh statement/axiom checks passed; aggregate proof repaired; supplements, semantic replay and registered integration pending',
     '/tmp/de_native_campaign_aggregate_recovery_2026-10-05/summary.json', 1734, 20628),
    (3241065, 'python3 /tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/build_recovery.py',
     '/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/driver.log',
     'All four supplemental qualified modules and six statement/axiom checks passed; repository integration pending',
     '/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/summary.json', 4, 6),
]

def ready():
    complete = True
    for pid, cmd, log, marker, summary, count, names in parents:
        text = Path(log).read_text()
        assert not re.search(r'terminal [1-9]|Traceback|exception ', text), log
        if marker not in text:
            complete = False
            p = Path('/proc') / str(pid) / 'cmdline'
            assert p.exists(), 'Required proof driver disappeared without terminal success: ' + log
            assert p.read_bytes().replace(b'\0', b' ').decode().strip() == cmd, pid
        else:
            d = json.loads(Path(summary).read_text())
            assert d['terminal_exit_code'] == 0 and d['standard_only']
            assert d['module_count'] == count
            assert d['fresh_statement_count'] == d['fresh_axiom_count'] == names
    return complete

check()
print('Final verification driver PID', os.getpid(),
      'waiting for both qualified proof campaigns; frozen inputs', len(freeze), flush=True)
while not ready():
    time.sleep(10)
check()
assert out.exists() and not (out / 'qualified_verification.json').exists()
log = out / 'qualified_verification_driver.txt'
assert not log.exists()
with log.open('w') as stream:
    result = subprocess.run(['/usr/bin/python3', str(verifier), '--stage', 'qualified',
                             '--output', str(out / 'qualified_verification.json')],
                            cwd=repo, stdout=stream, stderr=subprocess.STDOUT)
text = log.read_text()
log.write_text('\n'.join(t.rstrip() for t in text.splitlines()).rstrip() + '\n')
check()
terminal = {'terminal_exit_code': result.returncode, 'verifier_sha256': sha(verifier),
            'log_sha256': sha(log), 'freeze_sha256': sha(freeze_path)}
(out / 'qualified_verification_terminal.json').write_text(json.dumps(terminal, indent=2) + '\n')
print('Complete qualified semantic verifier terminal', result.returncode, flush=True)
assert result.returncode == 0 and 'Traceback' not in text and 'error:' not in text and 'warning:' not in text
record = json.loads((out / 'qualified_verification.json').read_text())
assert record['source_stage_passed'] and record['qualified_stage_passed'] and record['standard_only']
assert record['checked_modules'] == 1738
assert record['retained_compile_checks'] == 993 and record['fresh_modules'] == 745
assert record['fresh_statement_checks'] == record['fresh_axiom_checks'] == 20634
summary = {'terminal_exit_code': 0, 'standard_only': True, 'module_count': 1738, 'retained_compile_checks': 993, 'fresh_recovery_compile_checks': 745,
           'fresh_statement_count': 20634, 'fresh_axiom_count': 20634,
           'verification_sha256': sha(out / 'qualified_verification.json'),
           'source_freeze_sha256': sha(freeze_path),
           'scope': 'Exact native campaign source/replay and full fresh qualified semantic/statement/axiom verification passed; repository installation, registration, build, cumulative audit provenance and commit remain pending.'}
Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/finish-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('Native campaign complete qualified semantic verification passed; repository integration and commit pending', flush=True)
