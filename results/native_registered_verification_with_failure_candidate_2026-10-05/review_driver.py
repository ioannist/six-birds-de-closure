from pathlib import Path
import ast,copy,datetime,hashlib,importlib.util,json,subprocess
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_registered_verification_with_failure_candidate_2026-10-05';out.mkdir(exist_ok=False)
vp=Path('/tmp/de_native_registered_verify_with_failure_candidate.py');bp=Path('/tmp/de_native_registered_build_with_failure_candidate.py');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('extended_registered_verifier_review',vp);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
plan,files,names,full=v.candidate();positive=v.failure_proof_gate(plan)
controls=[]
def reject(label,mutate):
 bad=copy.deepcopy(plan);mutate(bad)
 try:v.failure_proof_gate(bad)
 except (AssertionError,StopIteration):controls.append(dict(control=label,rejected=True))
 else:raise AssertionError('Unexpected acceptance: '+label)
reject('missing new module',lambda p:p['modules'].pop())
reject('changed new declaration list',lambda p:p['modules'][-1]['declared_theorems'].pop())
reject('wrong new source hash',lambda p:p['modules'][-1].update(source_sha256='0'*64))
reject('wrong normalization parent source',lambda p:next(r for r in p['modules'] if r['module']=='SbtCosmo.Derivation.GroundSourceNormalization').update(source_sha256='0'*64))
reject('wrong separate production-plan binding',lambda p:p.update(additional_candidate_plan_sha256='0'*64))
original_load=v.load
for key,value in [('standard_only',False),('terminal_exit_code',1)]:
 def altered(path,key=key,value=value):
  d=original_load(path)
  if Path(path)==repo/'results/source_normalization_failure_checked_2026-10-05/audit-summary.json':d[key]=value
  return d
 v.load=altered
 try:v.failure_proof_gate(plan)
 except AssertionError:controls.append(dict(control='injected audit summary '+key,rejected=True,adapter='in-memory load return only; no files changed'))
 else:raise AssertionError(key)
 finally:v.load=original_load
log=Path('/tmp/de_source_normalization_failure/Audit.log').read_text().replace('[propext,','[propext, added_nonstandard_axiom,',1)
try:v.parser.axiom_entries(log,names[-5:])
except AssertionError:controls.append(dict(control='nonstandard transitive axiom',rejected=True,scope='actual inherited axiom parser on modified log text'))
else:raise AssertionError('Nonstandard axiom accepted')
old=Path('/tmp/de_native_registered_verify_candidate.py').read_text()
for a,b in [('1770','1771'),('20784','20789'),('32560','32565'),('1780','1783')]:old=old.replace(a,b)
old=old.replace('/tmp/de_native_registered_receipts','/tmp/de_native_registered_with_failure_receipts')
base_funcs={n.name:n for n in ast.parse(old).body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))};new_funcs={n.name:n for n in ast.parse(vp.read_text()).body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
preserved=[]
for name in ['sha','rawsha','load','required','require_freezes_released','registered','main']:
 assert ast.dump(base_funcs[name],include_attributes=False)==ast.dump(new_funcs[name],include_attributes=False),name;preserved.append(name)
pg=copy.deepcopy(new_funcs['proof_gates']);assert isinstance(pg.body[0],ast.Expr) and pg.body[0].value.func.id=='failure_proof_gate';pg.body.pop(0)
assert ast.dump(pg,include_attributes=False)==ast.dump(base_funcs['proof_gates'],include_attributes=False);preserved.append('proof_gates after removing only new first call')
expected=Path('/tmp/de_native_registered_build_candidate.py').read_text().replace('/tmp/de_native_registered_verify_candidate.py','/tmp/de_native_registered_verify_with_failure_candidate.py').replace('/tmp/de_native_registered_receipts','/tmp/de_native_registered_with_failure_receipts')
assert bp.read_text()==expected
checks=[]
for name,cmd,expected_code in [('candidate',[str(vp),'--mode','candidate'],0),('registered',[str(vp),'--mode','registered'],2),('runner',[str(bp)],2)]:
 command=['/usr/bin/python3']+cmd;r=subprocess.run(command,text=True,capture_output=True);(out/(name+'-stdout.log')).write_text(r.stdout);(out/(name+'-stderr.log')).write_text(r.stderr)
 assert r.returncode==expected_code and not r.stderr,(name,r.returncode,r.stderr)
 d=json.loads(r.stdout);checks.append(dict(command=command,terminal_exit_code=r.returncode,result=d))
assert not Path('/tmp/de_native_registered_with_failure_receipts').exists()
(out/'verifier_candidate.py').write_bytes(vp.read_bytes());(out/'build_candidate.py').write_bytes(bp.read_bytes());(out/'review_driver.py').write_bytes(Path(__file__).read_bytes());(out/'source_parser_reference.py').write_bytes((repo/'scripts/de_native_campaign_verify.py').read_bytes())
record=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),positive_failure_gate=positive,rejected_controls=controls,inherited_functions_preserved=preserved,runner_unchanged_except_explicit_verifier_and_receipt_paths=True,checks=checks,actual_registered_commands_run=0,full_registered_mode_tested=False,registered_sources_changed=False,old_candidates_unchanged=True,review='adversarial self-review of extension; full inherited registered success path remains pending',goal_complete=False,installation_plan_sha256=sha(v.CANDIDATE/'installation-plan.json'))
(out/'checks.json').write_text(json.dumps(record,indent=2)+'\n');(out/'README.md').write_text('Prepared verifier/runner extension for the separate1771-module/20789-native-declaration/32565-cumulative installation candidate. Candidate-source checking and actual checked failure packet validation pass. Eight controls are rejected:five plan changes,two injected audit-summary fields,and one actual parser test on a modified nonstandard-axiom log. Existing proof gates and registered verification are preserved by AST comparison, with only the declared counts/receipt path and new failure gate added. Both registered entry points refuse the missing final qualified summary before starting commands or creating receipts. No actual registered command was run. Full registered success-path review/testing, publication/path adjustment, source installation, builds and fresh audits remain pending. Review is adversarial self-review, not independent review.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in out.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(dict(candidate_modules=len(plan['modules']),native_declarations=len(names),cumulative_declarations=len(full),failure_gate=positive,rejected_controls=len(controls),actual_registered_commands_run=0,full_registered_success_path_tested=False,output=str(out))))
