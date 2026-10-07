"""Run actual registered build/audits only after installed bytes and gates agree."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json,os,re,subprocess,traceback

ROOT=Path('/home/repos/six-birds-de-closure')
VERIFIER=Path('/tmp/de_native_registered_verify_resource_candidate.py')
spec=importlib.util.spec_from_file_location('native_registered_verifier',VERIFIER)
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,data):Path(p).write_text(json.dumps(data,indent=2)+'\n')

def main():
 try:
  plan,files,names,full=verify.candidate()
  verify.proof_gates(plan)
  verify.require_freezes_released()
 except verify.Pending as e:
  print(json.dumps(dict(status='pending',reason=str(e),registered_commands_started=False,goal_complete=False)),flush=True)
  return 2
 offset=verify.required(ROOT/'results/ground_offset_transport_2026-10-04/verification.json')
 assert offset['axiom_audit']['success'] and offset['axiom_audit']['declarations_cumulative']==11776
 assert offset['lean_build']['success'] and offset['lean_build']['jobs']==10003 and offset['namespace_recovery']['verified']
 for p,raw in files.items():assert (ROOT/p).read_bytes()==raw,('Install exact checked candidate first',p)
 out=Path('/tmp/de_native_registered_resource_receipts');assert not out.exists(),out
 out.mkdir()
 snapshot={str(p):sha(p) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
 for name in ('lean-toolchain','lake-manifest.json'):snapshot[str(ROOT/'lean'/name)]=sha(ROOT/'lean'/name)
 write(out/'source-snapshot.json',snapshot)
 helpers={str(Path(__file__)):sha(__file__),str(VERIFIER):sha(VERIFIER),str(ROOT/'scripts/de_native_campaign_verify.py'):sha(ROOT/'scripts/de_native_campaign_verify.py')}
 source=out/'statements.lean'
 source.write_text(''.join('import '+r['module']+'\n' for r in plan['modules'])+'set_option warningAsError true\n'+''.join('#check '+n+'\n' for n in names))
 helpers[str(source)]=sha(source)
 runtime_env=dict(os.environ,**verify.REQUIRED_ENV)
 def check():
  assert all(sha(p)==h for p,h in snapshot.items())
  assert all(sha(p)==h for p,h in helpers.items())
 commands={'build':['lake','build'],'axioms':['lake','env','lean','manifests/check_axioms.lean'],
           'statements':['lake','env','lean',str(source)]}
 try:
  for stage,command in commands.items():
   check();log=out/(stage+'.log')
   print('Actual registered',stage,'command starting:',command,flush=True)
   with log.open('w') as f:r=subprocess.run(command,cwd=ROOT/'lean',env=runtime_env,stdout=f,stderr=subprocess.STDOUT)
   d=dict(utc=datetime.now(timezone.utc).isoformat(),terminal_exit_code=r.returncode,command=command,cwd=str(ROOT/'lean'),
          installation_plan_sha256=sha(verify.CANDIDATE/'installation-plan.json'),source_snapshot_sha256=sha(out/'source-snapshot.json'),log_sha256=sha(log),environment_overrides=verify.REQUIRED_ENV)
   if stage!='build':d['objects_snapshot_sha256']=sha(out/'objects-snapshot.json')
   write(out/(stage+'-terminal.json'),d);check()
   assert r.returncode==0 and not re.search(r'error:|warning:|Traceback|build failed',log.read_text()),stage
   if stage=='build':
    assert 'Build completed successfully' in log.read_text()
    objects={row['module']:sha(ROOT/'lean/.lake/build/lib/lean'/Path(*row['module'].split('.')).with_suffix('.olean')) for row in plan['modules']}
    write(out/'objects-snapshot.json',objects)
   elif stage=='axioms':verify.parser.axiom_entries(log.read_text(),full)
   else:verify.parser.statement_entries(log.read_text(),names)
   print('Actual registered',stage,'terminal0',flush=True)
  check();verify.proof_gates(plan);verify.require_freezes_released()
  result=verify.registered(plan,files,names,full,out)
  write(out/'verification.json',result)
  write(out/'terminal.json',dict(terminal_exit_code=0,registered_native_verified=True,verification_sha256=sha(out/'verification.json'),goal_complete=False))
  print(json.dumps(result),flush=True);return 0
 except BaseException as e:
  write(out/'terminal.json',dict(terminal_exit_code=1,error=repr(e),traceback=traceback.format_exc(),goal_complete=False))
  raise
if __name__=='__main__':raise SystemExit(main())
