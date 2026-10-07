from pathlib import Path
import ast,datetime,hashlib,importlib.util,json,subprocess
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_registered_header_verification_candidate_2026-10-05'
old=Path('/tmp/de_native_registered_verify_resource_candidate.py');new=Path('/tmp/de_native_registered_verify_header_candidate.py')
runner_old=Path('/tmp/de_native_registered_build_resource_candidate.py');runner_new=Path('/tmp/de_native_registered_build_header_candidate.py')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
text=old.read_text().replace("CANDIDATE=ROOT/'results/native_registered_installation_with_failure_candidate_2026-10-05'","CANDIDATE=ROOT/'results/native_registered_header_installation_candidate_2026-10-05'")
before=""" assert files['lean/manifests/check_axioms.lean'].endswith(suffix)
 old=files['lean/manifests/check_axioms.lean'][:-len(suffix)]
 assert rawsha(old)==plan['input_sha256'][str(ROOT/'lean/manifests/check_axioms.lean')]
"""
after=""" header=ROOT/'results/audit_manifest_header_repair_candidate_2026-10-05'
 assert all(sha(header/p)==h for p,h in load(header/'file-manifest.json').items())
 repair=plan['header_repair']
 assert repair['plan_sha256']==sha(header/'repair-plan.json')
 assert repair['file_manifest_sha256']==sha(header/'file-manifest.json')
 old=(header/'current_manifest.repaired.lean').read_bytes()
 assert rawsha(old)==repair['pre_native_repaired_sha256']==plan['input_sha256'][str(ROOT/'lean/manifests/check_axioms.lean')]
 assert old==hoist((header/'current_manifest.before.lean').read_bytes())
 assert files['lean/manifests/check_axioms.lean']==hoist(old+suffix)
 assert files['lean/manifests/check_axioms.lean']==(header/'native_manifest.repaired.lean').read_bytes()
 assert full[:11776]==re.findall(r'^#print axioms (\\S+)',old.decode(),re.M)
 assert not plan['preserved_default_manifest_byte_prefix']
"""
assert text.count(before)==1;text=text.replace(before,after)
text=text.replace('\ndef candidate():','\ndef hoist(raw):\n lines=raw.splitlines(keepends=True)\n return b\'\'.join(l for l in lines if l.startswith(b\'import \'))+b\'\'.join(l for l in lines if not l.startswith(b\'import \'))\n\ndef candidate():',1)
gate=" assert offset['namespace_recovery']['verified']\n"
newgate=gate+" assert offset['manifest_header_repair']['verified']\n assert offset['axiom_audit']['full_cumulative_command_rerun']\n"
assert text.count(gate)==1;text=text.replace(gate,newgate)
text=text.replace('/tmp/de_native_registered_resource_receipts','/tmp/de_native_registered_header_receipts')
new.write_text(text)
runner=runner_old.read_text().replace(str(old),str(new)).replace('/tmp/de_native_registered_resource_receipts','/tmp/de_native_registered_header_receipts')
rgate=" assert offset['lean_build']['success'] and offset['lean_build']['jobs']==10003 and offset['namespace_recovery']['verified']\n"
assert runner.count(rgate)==1;runner=runner.replace(rgate,rgate+" assert offset['manifest_header_repair']['verified'] and offset['axiom_audit']['full_cumulative_command_rerun']\n")
runner_new.write_text(runner)
def functions(raw):return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
a=functions(old.read_text());b=functions(text)
assert set(b)==set(a)|{'hoist'}
unchanged=[n for n in a if n not in {'candidate','registered','main'}]
assert all(a[n]==b[n] for n in unchanged)
assert a['main']!=b['main'] # Only the default receipt path changed in main.
spec=importlib.util.spec_from_file_location('header_candidate_verifier',new);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
plan,files,names,full=v.candidate();assert (len(files),len(names),len(full))==(1783,20789,32565)
v.failure_proof_gate(plan)
oldraw=(repo/'results/audit_manifest_header_repair_candidate_2026-10-05/current_manifest.repaired.lean').read_bytes()
expected=v.hoist(oldraw);assert expected==oldraw
lines=oldraw.splitlines(keepends=True);i=next(i for i,l in enumerate(lines) if l.startswith(b'#print axioms '));j=next(j for j,l in enumerate(lines) if l.startswith(b'import '))
mutations={'dropped_query':b''.join(lines[:i]+lines[i+1:]),'duplicated_query':oldraw+lines[i],'changed_body':oldraw+b'\n','dropped_import':b''.join(lines[:j]+lines[j+1:]),'late_import':b''.join(lines[:j]+lines[j+1:])+lines[j]}
query_indices=[k for k,l in enumerate(lines) if l.startswith(b'#print axioms ')];x,y=query_indices[:2];swapped=list(lines);swapped[x],swapped[y]=swapped[y],swapped[x];mutations['reordered_queries']=b''.join(swapped)
rejected=[]
for name,raw in mutations.items():
 try:assert raw==expected
 except AssertionError:rejected.append(name)
 else:raise AssertionError(name)
# Hoisting a valid file is idempotent; hoisting a late import repairs layout
# but does not authorize its changed position in the import vector.
assert v.hoist(expected)==expected
out.mkdir(exist_ok=False)
checks=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_archive_files=len(files),native_declarations=len(names),cumulative_declarations=len(full),unchanged_inherited_functions=unchanged,rejected_controls=rejected,registered_commands_started=0,full_success_path_tested=False,goal_complete=False)
for target,source in [('verifier_candidate.py',new),('runner_candidate.py',runner_new),('prepare_driver.py',Path(__file__))]:(out/target).write_bytes(source.read_bytes())
(out/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(out/'README.md').write_text('Prepared header-aware native verifier and runner. All inherited mathematical proof gates remain. Candidate comparison validates exact import hoisting and11776 ordered-query preservation; registered execution additionally requires the verified header repair and an actual fresh11776 whole-offset cumulative audit. Final actual32565/20789 commands, thread override receipts and full source/object bindings remain required. Source preflight and six corrupted-file controls pass; full registered success path remains untested. No registered command started.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in out.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(checks))
