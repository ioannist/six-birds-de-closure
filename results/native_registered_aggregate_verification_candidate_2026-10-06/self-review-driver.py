"""Adversarial self-review of the source-only recovery and historical transport."""
from pathlib import Path
import ast, hashlib, importlib.util, json

ROOT=Path('/home/repos/six-birds-de-closure')
OUT=ROOT/'results/native_registered_aggregate_verification_candidate_2026-10-06'
new=Path('/tmp/de_native_registered_verify_aggregate_recovery.py')
old=Path('/tmp/de_native_registered_verify_original_audit_candidate.py')
def funcs(p):
 return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(p.read_text()).body if isinstance(n,ast.FunctionDef)}
a,b=funcs(old),funcs(new)
unchanged=['failure_proof_gate','registered','original_audit_types','original_audit_proof_gate','_parent_candidate']
assert all(a[n]==b[n] for n in unchanged)
spec=importlib.util.spec_from_file_location('reviewed_registered_guard',new)
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
f=json.loads((ROOT/'results/native_original_sample_aggregate_repair_checked_2026-10-05/source-input-freeze.json').read_text())
plan=json.loads((ROOT/'results/ground_offset_header_installation_candidate_2026-10-05/installation-plan.json').read_text())
rows={str(ROOT/r['path']):r for r in plan['targets']}
allowed=sorted(set(rows)&set(f));assert len(allowed)==18
real=v.sha
simulated={p:rows[p]['after_sha256'] for p in allowed}
v.sha=lambda p:simulated.get(str(p),real(p))
v.check_aggregate_historical_inputs(f)
negative=[]
for label,mutate in [
 ('unapproved_current_source',lambda:simulated.update({allowed[0]:'0'*64})),
 ('false_historical_source_hash',lambda:f.update({allowed[0]:'0'*64})),
 ('unapproved_other_input',lambda:simulated.update({next(p for p in f if p not in allowed):'0'*64}))]:
 original_f=dict(f);original_sim=dict(simulated)
 # Restore the valid post-install state before each individual control.
 simulated.clear();simulated.update({p:rows[p]['after_sha256'] for p in allowed})
 mutate()
 try:v.check_aggregate_historical_inputs(f)
 except AssertionError:negative.append(label)
 else:raise AssertionError('Control incorrectly accepted: '+label)
 f.clear();f.update(original_f);simulated.clear();simulated.update(original_sim)
v.sha=real
v.check_aggregate_historical_inputs(f)
assert negative==['unapproved_current_source','false_historical_source_hash','unapproved_other_input']
try:v.require_freezes_released()
except v.Pending as e:active_gate=str(e)
else:raise AssertionError('Active recovery source freeze was not protected')
for name in ['de_native_registered_install_aggregate_recovery.py','de_offset_header_install_aggregate_recovery.py']:
 historical='de_native_registered_install_original_audit_journal_candidate.py' if name.startswith('de_native') else 'de_offset_header_install_journal_candidate.py'
 before,after=funcs(Path('/tmp')/historical),funcs(Path('/tmp')/name)
 for function in ['atomically_install','install_target','observed_targets','record_installation_failure']:
  assert before[function]==after[function]
data=dict(review='adversarial self-review',unchanged_substantive_gate_functions=unchanged,unchanged_journal_functions_per_installer=4,approved_post_install_source_changes_accepted=18,negative_controls_rejected=negative,active_freeze_gate_rejected=active_gate,registered_sources_changed=False,qualified_success=False,registered_success=False)
(OUT/'self-review.json').write_text(json.dumps(data,indent=2)+'\n')
(OUT/'self-review-driver.py').write_bytes(Path(__file__).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file() and p.name!='file-manifest.json'},indent=2)+'\n')
print(json.dumps(data))
