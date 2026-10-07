"""Run the authorized registered integration after every private recovery closes."""
from pathlib import Path
import resource, datetime, hashlib, importlib.util, json, os, re, subprocess, time, traceback

ROOT=Path('/home/repos/six-birds-de-closure')
OUT=ROOT/'results/native_registered_stack_integration_run_2026-10-06'
NATIVE=ROOT/'results/native_registered_aggregate_installation_candidate_2026-10-06'
GATES=ROOT/'results/native_registered_stack_verification_candidate_2026-10-06'
OFFSET=ROOT/'results/ground_offset_transport_2026-10-04'
HELPERS={
 'offset_install':Path('/tmp/de_offset_header_install_stack_recovery.py'),
 'offset_build':ROOT/'scripts/de_ground_offset_transport_build.py',
 'offset_cumulative':Path('/tmp/de_offset_registered_cumulative_audit_stack_recovery.py'),
 'offset_verify':Path('/tmp/de_ground_offset_transport_verify_stack_recovery.py'),
 'native_install':Path('/tmp/de_native_registered_install_stack_recovery.py'),
 'native_build':Path('/tmp/de_native_registered_build_stack_recovery.py'),
 'native_verify':Path('/tmp/de_native_registered_verify_stack_recovery.py'),
 'parser':Path('/tmp/de_native_campaign_parser_stack_recovery.py'),
 'repair_guard':Path('/tmp/de_registered_aggregate_repair_guard.py')}
PARENTS=[
 (3325544,'/tmp/de_native_campaign_stack_adoption_2026-10-06/adopt.py','/tmp/de_native_campaign_stack_adoption_2026-10-06/summary.json',1734,20628),
 (3403554,'/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/build_recovery.py','/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/summary.json',4,6),
 (3769018,'/tmp/de_native_campaign_semantic_stack_recovery_2026-10-06/finish_recovery.py','/tmp/de_native_campaign_semantic_stack_recovery_2026-10-06/finish-summary.json',1738,20634),
 (3825483,'/tmp/de_native_additional_constructions_stack_recovery_2026-10-06/build_recovery.py','/tmp/de_native_additional_constructions_stack_recovery_2026-10-06/summary.json',29,132),
 (3827081,'/tmp/de_source_execution_supplement_stack_recovery_2026-10-06/build_recovery.py','/tmp/de_source_execution_supplement_stack_recovery_2026-10-06/summary.json',3,18)]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
def write(p,d):Path(p).write_text(json.dumps(d,indent=2)+'\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()

def prepare():
 assert not OUT.exists();OUT.mkdir()
 bindings={str(p):sha(p) for p in [Path(__file__),*HELPERS.values()]}
 for packet in [NATIVE,GATES,ROOT/'results/ground_offset_registered_recovery_candidate_2026-10-06',ROOT/'results/ground_offset_header_installation_candidate_2026-10-05']:
  manifest=load(packet/'file-manifest.json')
  assert all(sha(packet/p)==h for p,h in manifest.items())
  for p,h in manifest.items():bindings[str(packet/p)]=h
  bindings[str(packet/'file-manifest.json')]=sha(packet/'file-manifest.json')
 # Bind the exact original offset failure receipts before preserving them.
 for name in ['families_Point000_build.txt','families_Point001_build.txt','families_driver.txt']:
  p=OFFSET/name;assert p.is_file() and re.search(r'error:|Traceback|terminal [1-9]',p.read_text()),name
  bindings[str(p)]=sha(p)
 write(OUT/'initial-helper-bindings.json',bindings)
 return bindings

def parent_ready():
 ready=True
 for pid,script,summary,modules,decls in PARENTS:
  try:argv=(Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0')
  except FileNotFoundError:argv=[]
  active=len(argv)>1 and argv[1].decode()==script
  if not Path(summary).exists():
   assert active,'Parent vanished without success: '+script
   ready=False;continue
  d=load(summary)
  assert d['terminal_exit_code']==0 and d['standard_only'],summary
  assert d['module_count']==modules and d['fresh_statement_count']==d['fresh_axiom_count']==decls,summary
  if active:ready=False
 return ready

def execute(label,command,cwd,log=None):
 log=log or OUT/(label+'.log');assert not log.exists(),log
 print(utc(),label,'starting',flush=True)
 with log.open('w') as stream:
  result=subprocess.run(command,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='4'),stdout=stream,stderr=subprocess.STDOUT)
 raw=log.read_text()
 # Retain diagnostics and normalize only trailing whitespace, as required by
 # the existing receipt verifier. Record the exact resulting log hash.
 log.write_text('\n'.join(line.rstrip() for line in raw.splitlines()).rstrip()+'\n')
 receipt=dict(utc=utc(),terminal_exit_code=result.returncode,command=command,cwd=str(cwd),environment_overrides={'LEAN_NUM_THREADS':'4'},log_path=str(log),log_sha256=sha(log))
 write(OUT/(label+'-terminal.json'),receipt)
 print(utc(),label,'terminal',result.returncode,flush=True)
 assert result.returncode==0 and not re.search(r'error:|warning:|Traceback|build failed',raw),label
 return receipt

def preserve_failures(bindings):
 archive=OUT/'historical-offset-family-failures';archive.mkdir()
 for name in ['families_Point000_build.txt','families_Point001_build.txt','families_driver.txt']:
  p=OFFSET/name;q=archive/name
  assert sha(p)==bindings[str(p)]
  q.write_bytes(p.read_bytes());assert sha(q)==bindings[str(p)]
  # Journal the intended removal before freeing the required fresh-log path.
  write(OUT/'historical-offset-failure-preservation.json',dict(current_source=str(p),archived_target=str(q),sha256=sha(q),phase='before_remove_original_log'))
  p.unlink()
 write(archive/'file-manifest.json',{p.name:sha(p) for p in archive.iterdir()})
 write(OUT/'historical-offset-failure-preservation.json',dict(phase='preserved',archive_manifest_sha256=sha(archive/'file-manifest.json'),preserved_files=3))

def main():
 stack_soft,stack_hard=resource.getrlimit(resource.RLIMIT_STACK)
 assert stack_hard==resource.RLIM_INFINITY or stack_hard>=65536*1024
 resource.setrlimit(resource.RLIMIT_STACK,(65536*1024,stack_hard))
 bindings=prepare()
 print(utc(),'Integration controller PID',os.getpid(),'waiting for five verified proof parents; no source mutation yet',flush=True)
 while not parent_ready():time.sleep(10)
 assert all(sha(p)==h for p,h in bindings.items())
 spec=importlib.util.spec_from_file_location('final_registered_guards',HELPERS['native_verify'])
 v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 v.require_freezes_released();plan,*_=v.candidate();v.proof_gates(plan)
 write(OUT/'completed-parent-bindings.json',{summary:sha(summary) for _,_,summary,_,_ in PARENTS})
 preserve_failures(bindings)
 execute('offset-install',['python3',str(HELPERS['offset_install']),'--mode','apply'],ROOT)
 execute('offset-families',['python3',str(HELPERS['offset_build']),'families','--workers','2'],ROOT,OFFSET/'families_driver.txt')
 execute('offset-return',['python3',str(HELPERS['offset_build']),'return','--workers','1'],ROOT,OFFSET/'return_driver.txt')
 execute('offset-default-build',['lake','build'],ROOT/'lean',OFFSET/'lean_build.txt')
 assert 'Build completed successfully (10003 jobs).' in (OFFSET/'lean_build.txt').read_text()
 execute('offset-new-axioms',['lake','env','lean','-s','65536','manifests/check_ground_offset_transport_axioms.lean'],ROOT/'lean',ROOT/'lean/manifests/axiom_audit_ground_offset_transport_new_2026-10-04.txt')
 execute('offset-statements',['lake','env','lean','-s','65536','manifests/check_ground_offset_transport_statements.lean'],ROOT/'lean',OFFSET/'theorem_statements.txt')
 execute('offset-cumulative',['python3',str(HELPERS['offset_cumulative'])],ROOT)
 execute('offset-verify',['python3',str(HELPERS['offset_verify'])],ROOT)
 offset=load(OFFSET/'verification.json')
 assert offset['axiom_audit']['success'] and offset['axiom_audit']['full_cumulative_command_rerun']
 assert offset['axiom_audit']['declarations_cumulative']==11776 and offset['lean_build']['jobs']==10003
 assert offset['namespace_recovery']['verified'] and offset['manifest_header_repair']['verified']
 execute('native-install',['python3',str(HELPERS['native_install']),'--mode','apply'],ROOT)
 execute('native-build-and-full-audits',['python3',str(HELPERS['native_build'])],ROOT)
 final=load('/tmp/de_native_registered_original_audit_receipts/verification.json')
 assert final['registered_native_modules']==1772 and final['registered_native_statement_checks']==20798
 assert final['fresh_registered_cumulative_axiom_checks']==32574 and final['standard_only'] and final['registered_build_passed']
 write(OUT/'terminal.json',dict(utc=utc(),terminal_exit_code=0,registered_native_verified=True,whole_offset_verification_sha256=sha(OFFSET/'verification.json'),native_verification_sha256=sha('/tmp/de_native_registered_original_audit_receipts/verification.json'),coverage_reconciliation_and_commit_pending=True,goal_complete=False))
 print(utc(),'All actual registered proof gates passed; coverage reconciliation, completion audit and commit remain pending',flush=True)

if __name__=='__main__':
 try:main()
 except BaseException as error:
  if OUT.exists():write(OUT/'controller-failure.json',dict(utc=utc(),error=repr(error),traceback=traceback.format_exc(),goal_complete=False))
  raise
