from pathlib import Path
import hashlib, json, os, re, subprocess, time

cwd = Path('/home/repos/six-birds-de-closure/lean')
preview = Path('/tmp/de_native_seed_real_returns_preview')
private = Path('/tmp/de_native_cycle_lean')
objects = Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/objects')
overlay = Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/overlay')
receipts = Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/receipts')
planp = Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/production-plan.json')
parent_planp = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05/production-plan.json')
plan = json.loads(planp.read_text())
assert plan['module_count'] == 4 and plan['fresh_theorem_count'] == 6
assert hashlib.sha256(parent_planp.read_bytes()).hexdigest() == plan['parent_plan_sha256']
rows = {r['production_module']: r for r in plan['modules']}
names = [n for r in plan['modules'] for n in r['declared_theorems']]
assert len(names) == len(set(names)) == 6

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def normalize(s):
    return '\n'.join(t.rstrip() for t in s.splitlines()).rstrip() + '\n'

# Preserve both campaigns' authoritative input sets; never alter their plans.
freeze = {}
for filename in ['/tmp/de_native_campaign_aggregate_recovery_2026-10-05/source-object-freeze.json',
                 'de-native-seed-real-returns-freeze.json']:
    original = json.loads(Path('/tmp', filename).read_text())
    for p, h in original.items():
        assert p not in freeze or freeze[p] == h, p
        freeze[p] = h
    p = Path('/tmp', filename)
    freeze[str(p)] = sha(p)
inputs = [planp, parent_planp, Path(__file__)] + list(preview.rglob('*.lean'))
for r in plan['modules']:
    inputs.append(private / (r['private_module'] + '.lean'))
for p in inputs:
    h = sha(p)
    assert str(p) not in freeze or freeze[str(p)] == h, p
    freeze[str(p)] = h
freeze_path = Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/source-freeze.json')
assert not freeze_path.exists()
freeze_path.write_text(json.dumps(freeze, indent=2) + '\n')

def check():
    for p, h in freeze.items():
        assert sha(p) == h, p

parents = [
    (3325544, 'python3 /tmp/de_native_campaign_stack_adoption_2026-10-06/adopt.py',
     '/tmp/de_native_campaign_stack_adoption_2026-10-06/driver.log',
     'All1734 qualified modules and20628 fresh statement/axiom checks passed; aggregate proof repaired; supplements, semantic replay and registered integration pending',
     '/tmp/de_native_campaign_stack_adoption_2026-10-06/summary.json'),
    (2371188, '/usr/bin/python3 /tmp/de_native_seed_real_returns_private_build.py',
     '/tmp/de-native-seed-real-returns-driver.log',
     'Both original-seed exactly-real cycle returns passed;2 standard-only declarations; supplemental qualified registration pending',
     '/tmp/de-native-seed-real-returns-summary.json'),
]

def ready():
    complete = True
    for pid, cmd, log, marker, summary in parents:
        text = Path(log).read_text()
        assert not re.search(r'terminal [1-9]|Traceback|exception ', text), log
        if marker not in text:
            complete = False
            p = Path('/proc') / str(pid) / 'cmdline'
            assert p.exists(), 'Required parent disappeared without success: ' + log
            assert p.read_bytes().replace(b'\0', b' ').decode().strip() == cmd, pid
        else:
            d = json.loads(Path(summary).read_text())
            assert d['terminal_exit_code'] == 0 and d['standard_only'], summary
            if pid == 3325544:
                assert d['failed_statement_exit_code'] == -6 and not d['compiler_objects_recompiled']
                assert d == json.loads(Path('/tmp/de_native_campaign_stack_adoption_2026-10-06/terminal.json').read_text())
                for path, digest in d['audit_recovery_bindings'].items(): assert sha(path) == digest, path
                assert d['adoption_freeze_sha256'] == sha('/tmp/de_native_campaign_stack_adoption_2026-10-06/adoption-input-freeze.json')
                assert d['module_count'] == 1734
                assert d['fresh_statement_count'] == d['fresh_axiom_count'] == 20628
                assert d['plan_sha256'] == plan['parent_plan_sha256']
                assert d['source_freeze_sha256'] == sha('/tmp/de_native_campaign_aggregate_recovery_2026-10-05/source-object-freeze.json')
            else:
                assert len(d['names']) == 2
                assert d['source_freeze_sha256'] == sha('/tmp/de-native-seed-real-returns-freeze.json')
    return complete

check()
print('Supplemental qualified driver PID', os.getpid(),
      'waiting for checked seed returns and1734-module campaign; frozen inputs',
      len(freeze), flush=True)
while not ready():
    time.sleep(10)
check()

# Check the completed parent's fresh module receipts, not just a status marker.
parent_receipts = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05/receipts')
parent_records = json.loads((parent_receipts / 'modules.json').read_text())
parent_plan = json.loads(parent_planp.read_text())
parent_rows = {r['production_module']: r for r in parent_plan['modules']}
assert len(parent_records) == len(parent_rows) == 1734
assert {r['module'] for r in parent_records} == set(parent_rows)
for record in parent_records:
    row = parent_rows[record['module']]
    assert record['terminal_exit_code'] == 0
    assert record['source_sha256'] == row['production_sha256']
    assert record['log_sha256'] == sha(record['log_path'])
    assert record['olean_sha256'] == sha(record['object_path'])
    actual_source = Path(row['production_source_override']) if 'production_source_override' in row else Path('/tmp/de_native_campaign_production_preview') / row['production_path']
    assert sha(actual_source) == record['source_sha256']
for p in [objects, overlay, receipts]:
    assert not p.exists(), p
    p.mkdir()
parent_overlay = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05/overlay')
assert parent_overlay.exists()
for p in parent_overlay.rglob('*.olean'):
    q = overlay / p.relative_to(parent_overlay)
    q.parent.mkdir(parents=True, exist_ok=True)
    q.symlink_to(p.resolve(strict=True))
lakepath = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=cwd, text=True).strip()
leanbin = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=cwd, text=True).strip()
env = dict(os.environ, LEAN_PATH=str(overlay) + ':' + lakepath, LEAN_NUM_THREADS='4')
done = set()
records = []
while len(done) < 4:
    eligible = [n for n, r in rows.items() if n not in done and
                {d for d in r['qualified_imports'] if d in rows} <= done]
    assert eligible, 'Supplementary import cycle'
    name = eligible[0]
    r = rows[name]
    source = preview / r['production_path']
    check()
    assert sha(source) == r['production_sha256']
    rel = Path(*name.split('.')).with_suffix('.olean')
    output = objects / rel
    output.parent.mkdir(parents=True, exist_ok=True)
    log = receipts / (r['private_module'] + '.log')
    assert not output.exists() and not log.exists()
    with log.open('w') as f:
        result = subprocess.run([leanbin, '-s', '65536', '-R', str(preview / 'lean'), '-o', str(output), str(source)],
                                cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    text = log.read_text()
    log.write_text(normalize(text))
    check()
    record = {'module': name, 'terminal_exit_code': result.returncode,
              'source_sha256': sha(source), 'log_sha256': sha(log)}
    if output.exists():
        record['olean_sha256'] = sha(output)
    (receipts / (r['private_module'] + '-terminal.json')).write_text(json.dumps(record, indent=2) + '\n')
    print(name, 'terminal', result.returncode, flush=True)
    assert result.returncode == 0 and 'error:' not in text and 'warning:' not in text, name
    link = overlay / rel
    link.parent.mkdir(parents=True, exist_ok=True)
    assert not link.exists(), link
    link.symlink_to(output)
    records.append(record)
    done.add(name)
(receipts / 'modules.json').write_text(json.dumps(records, indent=2) + '\n')
for stage in ['statements', 'axioms']:
    source = preview / 'lean/manifests' / ('check_native_seed_real_returns_' + stage + '.lean')
    log = receipts / (stage + '.log')
    check()
    assert not log.exists()
    with log.open('w') as f:
        result = subprocess.run([leanbin, '-s', '65536', '-R', str(preview / 'lean'), str(source)],
                                cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    text = log.read_text()
    log.write_text(normalize(text))
    check()
    print(stage, 'terminal', result.returncode, flush=True)
    assert result.returncode == 0 and 'error:' not in text and 'warning:' not in text, stage
    if stage == 'axioms':
        entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))", text, re.S)
        assert [n for n, _, _ in entries] == names
        assert all(set(a.replace('\n', ' ').replace(',', ' ').split()) <=
                   {'propext', 'Classical.choice', 'Quot.sound'} for _, a, _ in entries)
summary = {'terminal_exit_code': 0, 'standard_only': True, 'module_count': 4,
           'fresh_statement_count': 6, 'fresh_axiom_count': 6, 'names': names,
           'plan_sha256': sha(planp), 'source_freeze_sha256': sha(freeze_path),
           'parent_summary_sha256': sha('/tmp/de_native_campaign_stack_adoption_2026-10-06/summary.json'),
           'seed_summary_sha256': sha('/tmp/de-native-seed-real-returns-summary.json'),
           'parent_module_receipts_sha256': sha(parent_receipts / 'modules.json'),
           'scope': 'Fresh separate supplemental qualified proofs of exactly-real original-seed cycle returns at20/30. Four modules and six checks supplement, without altering, the completed1734-module/20628-check parent. Repository integration and commit still pending.'}
Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('All four supplemental qualified modules and six statement/axiom checks passed; repository integration pending', flush=True)
