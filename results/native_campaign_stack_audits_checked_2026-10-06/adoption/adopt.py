"""Adopt genuine full audit recovery without changing the failed campaign."""
from pathlib import Path
import datetime, hashlib, json, os, re, time, traceback

BASE = Path(__file__).parent
OLD = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
AUDIT = Path('/tmp/de_native_campaign_stack_recovery_2026-10-06')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not (BASE / 'summary.json').exists()
inputs = json.loads((AUDIT / 'source-object-freeze.json').read_text())
for p in [Path(__file__), AUDIT / 'source-object-freeze.json']:
    inputs[str(p)] = sha(p)
freeze = BASE / 'adoption-input-freeze.json'
assert not freeze.exists()
freeze.write_text(json.dumps(inputs, indent=2) + '\n')
def check():
    for p, h in inputs.items():
        assert sha(p) == h, p
terminal = {}
try:
    check()
    print('Audit adoption PID', os.getpid(), 'waiting for genuine20628/20628 audit success; no compiler restart', flush=True)
    while not (AUDIT / 'terminal.json').exists():
        p = Path('/proc/2490922/cmdline')
        assert p.exists(), 'Audit disappeared without a terminal receipt'
        assert p.read_bytes().split(b'\0')[:2] == [b'python3', str(AUDIT / 'run_audits.py').encode()]
        time.sleep(10)
    audit_terminal = json.loads((AUDIT / 'terminal.json').read_text())
    assert audit_terminal['terminal_exit_code'] == 0, audit_terminal
    audit = json.loads((AUDIT / 'summary.json').read_text())
    assert audit == audit_terminal and audit['standard_only']
    assert audit['module_count'] == 1734 and audit['fresh_statement_count'] == audit['fresh_axiom_count'] == 20628
    assert audit['retained_terminal_zero_modules'] == 993 and audit['fresh_recovery_modules'] == 741
    assert audit['unchanged_statement_source'] and not audit['proof_sources_changed']
    assert audit['source_freeze_sha256'] == sha(AUDIT / 'source-object-freeze.json')
    plan = json.loads((OLD / 'production-plan.json').read_text())
    names = [n for r in plan['modules'] for n in r['declared_theorems']]
    assert len(names) == len(set(names)) == 20628
    records = json.loads((OLD / 'receipts/modules.json').read_text())
    assert len(records) == len({r['module'] for r in records}) == 1734
    assert all(r['terminal_exit_code'] == 0 for r in records)
    assert sum(r['retained'] for r in records) == 993
    for stage in ['statements', 'axioms']:
        receipt = json.loads((AUDIT / (stage + '-terminal.json')).read_text())
        assert receipt['terminal_exit_code'] == 0 and receipt['stack_kib'] == 65536 and receipt['lean_num_threads'] == 4
        assert receipt['command'][1:3] == ['-s', '65536']
        assert receipt['source_sha256'] == sha(AUDIT / ('Campaign' + stage.title() + '.lean'))
        assert receipt['log_sha256'] == sha(AUDIT / (stage + '.log'))
        assert not re.search(r'error:|warning:|Stack overflow', (AUDIT / (stage + '.log')).read_text())
    failed = json.loads((OLD / 'receipts/statements-terminal.json').read_text())
    assert failed['terminal_exit_code'] == -6
    assert sha(AUDIT / 'CampaignStatements.lean') == failed['source_sha256']
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))", (AUDIT / 'axioms.log').read_text(), re.S)
    assert [n for n, _, _ in entries] == names
    assert all(set(a.replace('\n', ' ').replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'} for _, a, _ in entries)
    gate = Path(plan['aggregate_proof_repair']['checked_private_gate'])
    d = json.loads(gate.read_text())
    assert d['terminal_exit_code'] == d['compiler_terminal_exit_code'] == d['audit_terminal_exit_code'] == 0
    assert d['standard_only'] and d['checked_declarations'] == d['unchanged_theorem_headers'] == 11
    check()
    completed = {str(p): sha(p) for p in [AUDIT / name for name in ['summary.json', 'terminal.json', 'statements-terminal.json', 'axioms-terminal.json', 'statements.log', 'axioms.log']]}
    terminal = dict(terminal_exit_code=0, standard_only=True, module_count=1734,
        retained_terminal_zero_modules=993, fresh_recovery_modules=741,
        fresh_statement_count=20628, fresh_axiom_count=20628,
        original_private_aggregate_gate_passed=True, original_private_aggregate_summary_sha256=sha(gate),
        source_freeze_sha256=sha(OLD / 'source-object-freeze.json'),
        plan_sha256=sha(OLD / 'production-plan.json'), review_sha256=sha(OLD / 'integration-review.json'),
        module_inventory_sha256=sha(OLD / 'receipts/modules.json'),
        audit_recovery_summary_sha256=sha(AUDIT / 'summary.json'),
        audit_recovery_root=str(AUDIT), audit_recovery_bindings=completed,
        adoption_freeze_sha256=sha(freeze),
        preserved_failed_parent=str(OLD), failed_statement_exit_code=-6,
        compiler_objects_recompiled=False, original_frozen_sources_unchanged=True,
        registered_sources_changed=False, qualification_supplements_and_registered_integration_pending=True,
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (BASE / 'summary.json').write_text(json.dumps(terminal, indent=2) + '\n')
    print('All1734 qualified modules and20628 fresh statement/axiom checks passed; aggregate proof repaired; supplements, semantic replay and registered integration pending', flush=True)
    print('Qualification uses preserved1734 compiler records and actual full stack-recovery audits; original failed terminal remains unchanged', flush=True)
except BaseException as error:
    terminal = dict(terminal_exit_code=1, error=repr(error), traceback=traceback.format_exc())
    traceback.print_exc()
finally:
    (BASE / 'terminal.json').write_text(json.dumps(terminal, indent=2) + '\n')
if terminal.get('terminal_exit_code') != 0:
    raise SystemExit(1)
