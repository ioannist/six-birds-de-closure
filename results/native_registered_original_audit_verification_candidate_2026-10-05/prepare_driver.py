from pathlib import Path
import ast,json,hashlib,importlib.util,subprocess,datetime,copy
REPO=Path('/home/repos/six-birds-de-closure')
OLD=Path('/tmp/de_native_registered_verify_header_candidate.py')
NEW=Path('/tmp/de_native_registered_verify_original_audit_candidate.py')
OLD_RUN=Path('/tmp/de_native_registered_build_header_candidate.py')
NEW_RUN=Path('/tmp/de_native_registered_build_original_audit_candidate.py')
OUT=REPO/'results/native_registered_original_audit_verification_candidate_2026-10-05'
HELPER=Path('/tmp/de_native_original_audit_gate_functions.py')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def funcs(s):return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(s).body if isinstance(n,ast.FunctionDef)}
old=OLD.read_text();text=old
text=text.replace("CANDIDATE=ROOT/'results/native_registered_header_installation_candidate_2026-10-05'", "PARENT=ROOT/'results/native_registered_header_installation_candidate_2026-10-05'\nCANDIDATE=ROOT/'results/native_registered_original_audit_installation_candidate_2026-10-05'")
node=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name=='candidate')
lines=text.splitlines(keepends=True)
parent=''.join(lines[node.lineno-1:node.end_lineno]).replace('def candidate():','def _parent_candidate():',1).replace('CANDIDATE','PARENT')
text=''.join(lines[:node.lineno-1])+parent+'\n'+''.join(lines[node.end_lineno:])
anchor='def proof_gates(plan):\n failure_proof_gate(plan)'
assert text.count(anchor)==1;text=text.replace(anchor,'def proof_gates(plan):\n original_audit_proof_gate(plan)\n failure_proof_gate(plan)')
anchor=" types=parser.statement_entries(logs['statements'],names)\n"
assert text.count(anchor)==1;text=text.replace(anchor,anchor+' original_audit_types(types)\n')
text=text.replace('registered_source_files=1783,registered_native_modules=1771,registered_native_statement_checks=20789','registered_source_files=1786,registered_native_modules=1772,registered_native_statement_checks=20798')
text=text.replace('fresh_registered_cumulative_axiom_checks=32565','fresh_registered_cumulative_axiom_checks=32574')
text=text.replace('candidate_checked=True,modules=1771,declarations=20789,archive_members=1783','candidate_checked=True,modules=1772,declarations=20798,archive_members=1786')
text=text.replace('/tmp/de_native_registered_header_receipts','/tmp/de_native_registered_original_audit_receipts')
assert text.count('def main():')==1;text=text.replace('def main():',HELPER.read_text()+'\n\ndef main():',1)
assert not NEW.exists() and not NEW_RUN.exists() and not OUT.exists()
NEW.write_text(text)
runner=OLD_RUN.read_text().replace(str(OLD),str(NEW)).replace('/tmp/de_native_registered_header_receipts','/tmp/de_native_registered_original_audit_receipts')
NEW_RUN.write_text(runner)
a=funcs(old);b=funcs(text)
unchanged=[n for n in a if n not in {'candidate','proof_gates','registered','main'}]
assert all(a[n]==b[n] for n in unchanged)
assert set(b)==set(a)|{'_parent_candidate','original_audit_types','original_audit_proof_gate'}
recovered_parent=parent.replace('def _parent_candidate():','def candidate():',1).replace('PARENT','CANDIDATE')
assert funcs(recovered_parent)['candidate']==a['candidate']
recovered_proof=text.replace(' original_audit_proof_gate(plan)\n','',1)
assert funcs(recovered_proof)['proof_gates']==a['proof_gates']
assert runner.replace(str(NEW),str(OLD)).replace('/tmp/de_native_registered_original_audit_receipts','/tmp/de_native_registered_header_receipts')==OLD_RUN.read_text()
spec=importlib.util.spec_from_file_location('native_original_audit_verifier',NEW);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
plan,files,names,full=v.candidate()
assert (len(files),len(names),len(full))==(1786,20798,32574)
new_gate=v.original_audit_proof_gate(plan);failure_gate=v.failure_proof_gate(plan)
assert new_gate['declarations']==9 and failure_gate['declarations']==5

controls=[]
def reject(label,run):
 try:run()
 except (AssertionError,ValueError,KeyError):controls.append(label)
 else:raise AssertionError('Control accepted: '+label)
bad=copy.deepcopy(plan);bad['modules'][-1]['declared_theorems']=bad['modules'][-1]['declared_theorems'][:-1]
reject('missing_original_audit_declaration',lambda:v.original_audit_proof_gate(bad))
badsha=copy.deepcopy(plan);badsha['modules'][-1]['source_sha256']='0'*64
reject('changed_original_audit_source_binding',lambda:v.original_audit_proof_gate(badsha))
original_load=v.load
packet=REPO/'results/original_audit_nonidentifiability_checked_2026-10-05'
def virtual_receipt(label,path,edit):
 payload=original_load(path);edit(payload)
 v.load=lambda p:copy.deepcopy(payload) if Path(p)==path else original_load(p)
 try:reject(label,lambda:v.original_audit_proof_gate(plan))
 finally:v.load=original_load
virtual_receipt('failed_compile_receipt',packet/'compile-terminal.json',lambda d:d.update(terminal_exit_code=1))
virtual_receipt('wrong_compile_command',packet/'compile-terminal.json',lambda d:d.update(command=['lean', 'unrelated.lean']))
virtual_receipt('missing_thread_override',packet/'audit-terminal.json',lambda d:d.update(environment_overrides={'LEAN_PATH':d['environment_overrides']['LEAN_PATH']}))
virtual_receipt('wrong_audit_log_binding',packet/'audit-terminal.json',lambda d:d.update(log_sha256='0'*64))
log=(packet/'audit.log').read_text();own_names=plan['modules'][-1]['declared_theorems']
for label,badlog in [('wrong_finite_admitted_count',log.replace('15\n','14\n')),('wrong_infinite_admitted_count',log.replace('18\n','17\n')),('wrong_passing_split_case',log.replace('GroundOriginalOffsetSixty.Tests 3','GroundOriginalOffsetSixty.Tests 4'))]:
 assert badlog!=log
 reject(label,lambda s=badlog:v.original_audit_types(v.parser.statement_entries(s,own_names)))

# Real entry points must refuse absent qualification evidence before creating
# any registered receipt directory or starting an actual registered command.
receipts=Path('/tmp/de_native_registered_original_audit_receipts');assert not receipts.exists()
preflights=[]
for label,cmd in [('candidate',[str(NEW),'--mode','candidate']),('registered',[str(NEW),'--mode','registered']),('runner',[str(NEW_RUN)])]:
 r=subprocess.run(['/usr/bin/python3']+cmd,cwd=REPO,capture_output=True,text=True)
 expected=0 if label=='candidate' else 2
 assert r.returncode==expected,(label,r.returncode,r.stdout,r.stderr)
 assert not receipts.exists()
 if label!='candidate':assert 'Required evidence is absent' in r.stdout and 'goal_complete' in r.stdout
 preflights.append(dict(label=label,actual_exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
OUT.mkdir()
for name,p in [('verifier_candidate.py',NEW),('runner_candidate.py',NEW_RUN),('gate_functions.py',HELPER),('prepare_driver.py',Path(__file__))]:(OUT/name).write_bytes(p.read_bytes())
checks=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),candidate_source_targets=len(files),native_modules=1772,native_declarations=len(names),cumulative_queries=len(full),original_audit_proof_gate=new_gate,execution_failure_proof_gate=failure_gate,unchanged_inherited_functions=unchanged,inherited_parent_candidate_ast_unchanged=True,inherited_proof_gates_ast_unchanged=True,runner_change_only_verifier_and_receipt_paths=True,rejected_controls=controls,virtual_receipt_read_substitutions=4,preflights=preflights,registered_commands_started=0,full_registered_success_path_tested=False,review='Adversarial self-review; no independent review',goal_complete=False)
(OUT/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'README.md').write_text('Prepared extended native verifier/runner. The unchanged parent candidate comparison remains as an embedded function. The new1/9 gate binds actual source/object/command/environment/log/terminal receipts, exact declarations/standard axioms and all2674 preserved archive members. Historical objects/configuration remain archived; current original source equations and pinned configuration must agree, with exactly the original or proposed native lake registration accepted. Existing mathematical proof/release/whole-offset gates remain. Fresh registered statements additionally validate the new theorem scopes. Nine corrupted controls are rejected; four receipt substitutions are explicitly virtual reads. Actual candidate preflight succeeds, while registered verifier/runner each exit2 for missing parent qualification before any registered command or receipt directory. Full success path remains untested.\n')
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
assert all(sha(OUT/p)==h for p,h in json.loads((OUT/'file-manifest.json').read_text()).items())
print(json.dumps(checks),flush=True)
