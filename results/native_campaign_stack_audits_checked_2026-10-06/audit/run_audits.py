"""Repeat complete, unchanged campaign audits after a preserved stack abort."""
from pathlib import Path
import datetime, hashlib, json, os, re, resource, subprocess, traceback

BASE = Path(__file__).parent
OLD = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
CWD = Path('/home/repos/six-birds-de-closure/lean')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan = json.loads((OLD / 'production-plan.json').read_text())
records = json.loads((OLD / 'receipts/modules.json').read_text())
rows = {r['production_module']: r for r in plan['modules']}
names = [n for r in plan['modules'] for n in r['declared_theorems']]
assert len(records) == len(rows) == 1734
assert len(names) == len(set(names)) == 20628
assert {r['module'] for r in records} == set(rows)
assert sum(r['retained'] for r in records) == 993
old_terminal = json.loads((OLD / 'receipts/statements-terminal.json').read_text())
assert old_terminal['terminal_exit_code'] == -6
assert 'Stack overflow detected. Aborting.' in (OLD / 'receipts/statements.log').read_text()
inputs = json.loads((OLD / 'source-object-freeze.json').read_text())
for r in records:
    assert r['terminal_exit_code'] == 0
    assert r['source_sha256'] == rows[r['module']]['production_sha256']
    for key, digest in [('source_path', 'source_sha256'), ('object_path', 'olean_sha256'), ('log_path', 'log_sha256')]:
        assert sha(r[key]) == r[digest], (r['module'], key)
        assert r[key] not in inputs or inputs[r[key]] == r[digest]
        inputs[r[key]] = r[digest]
    assert not re.search(r'error:|warning:', Path(r['log_path']).read_text())
    if r['retained']:
        assert sha(r['original_terminal_path']) == r['original_terminal_sha256']
        inputs[r['original_terminal_path']] = r['original_terminal_sha256']
for p in [Path(__file__), OLD / 'production-plan.json', OLD / 'integration-review.json',
          OLD / 'source-object-freeze.json', OLD / 'receipts/modules.json',
          OLD / 'receipts/statements-terminal.json', OLD / 'receipts/statements.log',
          OLD / 'terminal.json', OLD / 'driver.log']:
    assert str(p) not in inputs or inputs[str(p)] == sha(p)
    inputs[str(p)] = sha(p)
imports = ''.join('import ' + m + '\n' for m in rows)
expected = imports + 'set_option warningAsError true\n' + ''.join('#check ' + n + '\n' for n in names)
assert (OLD / 'receipts/CampaignStatements.lean').read_text() == expected
for stage, command in [('statements', '#check'), ('axioms', '#print axioms')]:
    p = BASE / ('Campaign' + stage.title() + '.lean')
    assert not p.exists()
    p.write_text(imports + 'set_option warningAsError true\n' + ''.join(command + ' ' + n + '\n' for n in names))
    inputs[str(p)] = sha(p)
assert sha(BASE / 'CampaignStatements.lean') == old_terminal['source_sha256']
freeze_path = BASE / 'source-object-freeze.json'
assert not freeze_path.exists()
freeze_path.write_text(json.dumps(inputs, indent=2) + '\n')
def check():
    for p, h in inputs.items():
        assert sha(p) == h, p

env = dict(os.environ, LEAN_PATH=old_terminal['lean_path'], LEAN_NUM_THREADS='4')
leanbin = old_terminal['command'][0]
stack_kib = 65536
soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
assert hard == resource.RLIM_INFINITY or hard >= stack_kib * 1024
resource.setrlimit(resource.RLIMIT_STACK, (stack_kib * 1024, hard))
terminal = {}
try:
    check()
    print('Stack recovery PID', os.getpid(), '1734 existing module checks validated; unchanged20628 queries per audit; stackKiB', stack_kib, flush=True)
    for stage in ['statements', 'axioms']:
        source = BASE / ('Campaign' + stage.title() + '.lean')
        log = BASE / (stage + '.log')
        assert not log.exists()
        args = [leanbin, '-s', str(stack_kib), '-R', str(BASE), str(source)]
        with log.open('w') as f:
            result = subprocess.run(args, cwd=CWD, env=env, stdout=f, stderr=subprocess.STDOUT)
        text = log.read_text()
        receipt = dict(terminal_exit_code=result.returncode, command=args, cwd=str(CWD),
                       lean_path=env['LEAN_PATH'], lean_num_threads=4, stack_kib=stack_kib,
                       source_sha256=sha(source), log_sha256=sha(log),
                       utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        (BASE / (stage + '-terminal.json')).write_text(json.dumps(receipt, indent=2) + '\n')
        print(stage, 'terminal', result.returncode, flush=True)
        assert result.returncode == 0 and not re.search(r'error:|warning:|Stack overflow', text), stage
        if stage == 'statements':
            declared = set(names)
            heads = [line.split(None, 1)[0].split('.{', 1)[0].rstrip(':')
                     for line in text.splitlines() if line and not line[0].isspace()]
            assert [h for h in heads if h in declared] == names
        else:
            entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))", text, re.S)
            assert [n for n, _, _ in entries] == names
            assert all(set(a.replace('\n', ' ').replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'} for _, a, _ in entries)
        check()
    terminal = dict(terminal_exit_code=0, standard_only=True, module_count=1734,
                    retained_terminal_zero_modules=993, fresh_recovery_modules=741,
                    fresh_statement_count=20628, fresh_axiom_count=20628,
                    preserved_failed_parent=str(OLD), failed_statement_exit_code=-6,
                    module_inventory_sha256=sha(OLD / 'receipts/modules.json'),
                    plan_sha256=sha(OLD / 'production-plan.json'),
                    source_freeze_sha256=sha(freeze_path),
                    unchanged_statement_source=True, proof_sources_changed=False,
                    registered_integration_pending=True)
    (BASE / 'summary.json').write_text(json.dumps(terminal, indent=2) + '\n')
    print('All20628 unchanged statement queries and20628 axiom queries passed; downstream adoption pending', flush=True)
except BaseException as error:
    terminal = dict(terminal_exit_code=1, error=repr(error), traceback=traceback.format_exc())
    traceback.print_exc()
finally:
    (BASE / 'terminal.json').write_text(json.dumps(terminal, indent=2) + '\n')
if terminal.get('terminal_exit_code') != 0:
    raise SystemExit(1)
