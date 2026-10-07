"""Exercise failure handling without installing sources or running Lean builds."""
from pathlib import Path
import ast, hashlib, importlib.util, json, tempfile

ROOT=Path('/home/repos/six-birds-de-closure')
OUT=ROOT/'results/native_registered_integration_controller_candidate_2026-10-06'
source=Path('/tmp/de_registered_integration_after_aggregate_recovery.py')
assert not OUT.exists();OUT.mkdir()
spec=importlib.util.spec_from_file_location('registered_integration_controller',source)
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
assert not c.parent_ready(), 'Private qualification is still live'
with tempfile.TemporaryDirectory(prefix='de_registered_controller_review_') as td:
 t=Path(td);c.OUT=t
 success=c.execute('test-terminal-zero',['python3','-c','print("isolated controller test")'],t)
 assert success['terminal_exit_code']==0
 try:c.execute('test-terminal-seven',['python3','-c','raise SystemExit(7)'],t)
 except AssertionError:pass
 else:raise AssertionError('Nonzero command was incorrectly accepted')
 assert json.loads((t/'test-terminal-seven-terminal.json').read_text())['terminal_exit_code']==7
 try:c.execute('test-warning-zero',['python3','-c','print("warning: isolated diagnostic control")'],t)
 except AssertionError:pass
 else:raise AssertionError('Diagnostic command was incorrectly accepted')
 assert json.loads((t/'test-warning-zero-terminal.json').read_text())['terminal_exit_code']==0
 c.OFFSET=t/'old';c.OFFSET.mkdir()
 bindings={}
 for n in ['families_Point000_build.txt','families_Point001_build.txt','families_driver.txt']:
  p=c.OFFSET/n;p.write_text('isolated historical failure '+n+'\n');bindings[str(p)]=c.sha(p)
 c.preserve_failures(bindings)
 archive=t/'historical-offset-family-failures'
 assert all(c.sha(archive/Path(p).name)==h and not Path(p).exists() for p,h in bindings.items())
 assert json.loads((t/'historical-offset-failure-preservation.json').read_text())['phase']=='preserved'
 copied=t/'verified-test-artifacts';copied.mkdir()
 # Only isolated test outputs are included here, never described as Lean proof
 # or full registered integration receipts.
 for p in t.glob('*.json'):(copied/p.name).write_bytes(p.read_bytes())
 for p in t.glob('*.log'):(copied/p.name).write_bytes(p.read_bytes())
 for p in copied.iterdir():(OUT/p.name).write_bytes(p.read_bytes())
data=dict(review='adversarial self-review',live_parent_wait_verified=True,actual_isolated_terminal_zero=True,actual_terminal_seven_rejected=True,actual_warning_terminal_zero_rejected=True,three_historical_logs_preserved_and_read_back=True,registered_source_mutations=0,actual_lean_commands_started=0,registered_success=False)
(OUT/'self-review.json').write_text(json.dumps(data,indent=2)+'\n')
(OUT/'controller.py').write_bytes(source.read_bytes())
(OUT/'self-review-driver.py').write_bytes(Path(__file__).read_bytes())
(OUT/'README.md').write_text('Candidate for serial authorized registered integration after five actual proof parents succeed and release their freezes. No weakening of installation or mathematical gates. Isolated process/failure-history controls are controller tests, not Lean proof receipts. Actual registered success remains pending. The controller leaves coverage reconciliation, completion review and commit to the main agent.\n')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(data))
