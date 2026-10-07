"""Run a real registered11776 query only after frozen jobs and repair installation."""
from pathlib import Path
import resource,datetime,hashlib,importlib.util,json,os,re,subprocess,traceback
ROOT=Path('/home/repos/six-birds-de-closure');header=ROOT/'results/audit_manifest_header_repair_candidate_2026-10-05';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
verifier=Path('/tmp/de_native_registered_verify_stack_recovery.py')
spec=importlib.util.spec_from_file_location('native_guards',verifier);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
 try:
  v.require_freezes_released()
  for proc in Path('/proc').iterdir():
   if not proc.name.isdigit():continue
   try:cmd=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode().strip()
   except (FileNotFoundError,ProcessLookupError,PermissionError):continue
   if cmd=='/usr/bin/python3 /tmp/de_run_repaired_cumulative_audit.py':raise v.Pending('Private cumulative audit still owns a source freeze')
  assert all(sha(header/p)==h for p,h in json.loads((header/'file-manifest.json').read_text()).items())
  manifest=ROOT/'lean/manifests/check_axioms.lean'
  if manifest.read_bytes()!=(header/'current_manifest.repaired.lean').read_bytes():raise v.Pending('Install exact repaired11776 manifest after freeze release')
  plan=json.loads(Path('/tmp/de_offset_transport_namespace_recovery/registered-integration-plan.json').read_text())
  if not all(sha(ROOT/p)==r['repaired_sha256'] for p,r in plan['namespace_repairs'].items()):raise v.Pending('Install exact19 namespace/renderer repairs first')
 except v.Pending as e:
  print(json.dumps(dict(status='pending',reason=str(e),registered_commands_started=False,goal_complete=False)));return 2
 out=ROOT/'results/ground_offset_transport_2026-10-04/cumulative-registered-receipts';assert not out.exists();out.mkdir()
 sources={str(p):sha(p) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
 for name in ['lean-toolchain','lake-manifest.json']:p=ROOT/'lean'/name;sources[str(p)]=sha(p)
 imports=re.findall(r'^import (\S+)',manifest.read_text(),re.M);names=re.findall(r'^#print axioms (\S+)',manifest.read_text(),re.M)
 assert len(imports)==len(set(imports))==1965 and len(names)==len(set(names))==11776
 objects={m:sha((ROOT/'lean/.lake/build/lib/lean'/Path(*m.split('.'))).with_suffix('.olean')) for m in imports}
 all_objects={str(p):sha(p) for p in (ROOT/'lean/.lake/build/lib/lean').rglob('*.olean')}
 helpers={str(Path(__file__)):sha(__file__),str(verifier):sha(verifier),str(Path('/tmp/de_native_campaign_parser_stack_recovery.py')):sha('/tmp/de_native_campaign_parser_stack_recovery.py')}
 write(out/'source-snapshot.json',sources);write(out/'objects-snapshot.json',objects);write(out/'all-registered-objects-snapshot.json',all_objects);write(out/'helper-snapshot.json',helpers)
 def check():assert all(sha(p)==h for d in [sources,all_objects,helpers] for p,h in d.items())
 stack_soft,stack_hard=resource.getrlimit(resource.RLIMIT_STACK);assert stack_hard==resource.RLIM_INFINITY or stack_hard>=65536*1024;resource.setrlimit(resource.RLIMIT_STACK,(65536*1024,stack_hard))
 cmd=['lake','env','lean','-s','65536','manifests/check_axioms.lean'];env={'LEAN_NUM_THREADS':'4'};log=out/'axioms.log'
 try:
  check();print('Actual registered11776 cumulative axiom command starting',flush=True)
  with log.open('w') as f:p=subprocess.run(cmd,cwd=ROOT/'lean',env=dict(os.environ,**env),stdout=f,stderr=subprocess.STDOUT)
  terminal=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),terminal_exit_code=p.returncode,command=cmd,cwd=str(ROOT/'lean'),environment_overrides=env,manifest_sha256=sha(manifest),source_snapshot_sha256=sha(out/'source-snapshot.json'),objects_snapshot_sha256=sha(out/'objects-snapshot.json'),all_registered_objects_snapshot_sha256=sha(out/'all-registered-objects-snapshot.json'),helper_snapshot_sha256=sha(out/'helper-snapshot.json'),log_sha256=sha(log))
  write(out/'axioms-terminal.json',terminal);check();assert p.returncode==0 and not re.search(r'error:|warning:',log.read_text())
  v.parser.axiom_entries(log.read_text(),names)
  write(out/'summary.json',dict(terminal_exit_code=0,standard_only=True,checked_declarations=11776,registered_command=True,whole_offset_verification_pending=True,goal_complete=False));return 0
 except BaseException as e:
  write(out/'driver-failure.json',dict(error=repr(e),traceback=traceback.format_exc(),goal_complete=False));raise
if __name__=='__main__':raise SystemExit(main())
