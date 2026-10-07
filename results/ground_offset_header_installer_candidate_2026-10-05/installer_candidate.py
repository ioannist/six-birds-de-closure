"""Install exact reviewed source repairs only after all real private gates finish."""
from pathlib import Path
import argparse,datetime,hashlib,importlib.util,json,os,re,tarfile,traceback,uuid
ROOT=Path('/home/repos/six-birds-de-closure');PACKET=ROOT/'results/ground_offset_header_installation_candidate_2026-10-05';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rawsha=lambda b:hashlib.sha256(b).hexdigest()
verifier=Path('/tmp/de_native_registered_verify_header_candidate.py');spec=importlib.util.spec_from_file_location('native_source_guards',verifier);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
def load(p):return json.loads(Path(p).read_text())
def write(p,d):Path(p).write_text(json.dumps(d,indent=2)+'\n')
def candidate():
 assert all(sha(PACKET/p)==h for p,h in load(PACKET/'file-manifest.json').items())
 plan=load(PACKET/'installation-plan.json');assert plan['registered_file_changes']==21 and plan['historical_leaf_freeze_changes']==20 and plan['new_proof_object_installations']==0
 assert all(sha(p)==h for p,h in plan['input_sha256'].items())
 result={}
 for tag in ['original','repaired']:
  archive=PACKET/(tag+'_files.tar.gz');assert sha(archive)==plan[tag+'_archive_sha256'];result[tag]={}
  with tarfile.open(archive,'r|gz') as tar:
   for m,r in zip(tar,plan['targets'],strict=True):
    assert m.isfile() and m.name==r['path'] and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
    raw=tar.extractfile(m).read();key='before' if tag=='original' else 'after';assert rawsha(raw)==r[key+'_sha256'] and len(raw)==r[key+'_size']
    assert m.name not in result[tag];result[tag][m.name]=raw
  assert len(result[tag])==21
 assert set(result['original'])==set(result['repaired'])
 assert all((ROOT/p).read_bytes()==raw for p,raw in result['original'].items())
 return plan,result
def private_audit_gate():
 root=Path('/tmp/de_audit_manifest_header_repair');summary=v.required(root/'cumulative-summary.json');terminal=v.required(root/'cumulative-terminal.json')
 assert summary['terminal_exit_code']==terminal['terminal_exit_code']==0 and summary['standard_only'] and summary['checked_declarations']==11776
 source=root/'current_manifest.repaired.lean';log=root/'cumulative-axioms.log'
 assert terminal['command']==['/home/ioannis/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean',str(source)] and terminal['cwd']==str(ROOT/'lean')
 assert terminal['environment_overrides']=={'LEAN_NUM_THREADS':'4'} and not terminal['registered_command']
 assert terminal['source_sha256']==sha(source) and terminal['source_freeze_sha256']==sha(root/'cumulative-source-freeze.json') and terminal['log_sha256']==sha(log)
 names=re.findall(r'^#print axioms (\S+)',source.read_text(),re.M);assert len(names)==len(set(names))==11776 and names==summary['names']
 v.parser.axiom_entries(log.read_text(),names)
 return root,summary
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--mode',choices=['candidate','apply'],default='candidate');args=ap.parse_args()
 plan,payload=candidate()
 if args.mode=='candidate':print(json.dumps(dict(prepared_target_files=21,proof_objects_installed=0,registered_sources_changed=False,proof_gates_checked=False,goal_complete=False)));return 0
 try:
  v.require_freezes_released()
  for proc in Path('/proc').iterdir():
   if not proc.name.isdigit():continue
   try:cmd=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode().strip()
   except (FileNotFoundError,ProcessLookupError,PermissionError):continue
   if cmd=='/usr/bin/python3 /tmp/de_run_repaired_cumulative_audit.py':raise v.Pending('Isolated cumulative audit still owns a source freeze')
  native_plan,*_=v.candidate();v.proof_gates(native_plan);audit_root,audit=private_audit_gate()
 except v.Pending as e:print(json.dumps(dict(status='pending',reason=str(e),registered_sources_changed=False,goal_complete=False)));return 2
 freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]+[audit_root/'cumulative-source-freeze.json']
 protected={}
 for p in freezes:
  for f,h in load(p).items():assert f not in protected or protected[f]==h;protected[f]=h
 assert all(sha(p)==h for p,h in protected.items())
 assert all((ROOT/p).read_bytes()==raw for p,raw in payload['original'].items())
 receipt=ROOT/'results/ground_offset_header_installation_receipts_2026-10-05';assert not receipt.exists();receipt.mkdir();write(receipt/'before-source-freeze.json',protected)
 write(receipt/'intent.json',dict(installation_plan_sha256=sha(PACKET/'installation-plan.json'),installer_sha256=sha(__file__),private_cumulative_audit_summary_sha256=sha(audit_root/'cumulative-summary.json'),targets=plan['targets'],registered_build_pending=True,goal_complete=False))
 installed=[]
 def atomically_install(p,raw):
  temp=p.with_name(p.name+'.de-repair-'+uuid.uuid4().hex)
  try:
   with temp.open('xb') as stream:stream.write(raw);stream.flush();os.fsync(stream.fileno())
   os.replace(temp,p)
  finally:temp.unlink(missing_ok=True)
 try:
  for r in plan['targets']:
   p=ROOT/r['path'];assert sha(p)==r['before_sha256'];atomically_install(p,payload['repaired'][r['path']]);installed.append(r['path']);write(receipt/'journal.json',dict(installed=installed,registered_build_pending=True,goal_complete=False))
  assert all((ROOT/p).read_bytes()==raw for p,raw in payload['repaired'].items())
  expected_changed={str(ROOT/p) for p in installed}&set(protected);actual_changed={p for p,h in protected.items() if sha(p)!=h};assert actual_changed==expected_changed
  write(receipt/'terminal.json',dict(terminal_exit_code=0,installed_source_files=21,proof_objects_installed=0,registered_build_pending=True,registered_cumulative_audit_pending=True,whole_offset_verification_pending=True,goal_complete=False));print('Exact21-file source repair installed; actual registered proof gates remain pending');return 0
 except BaseException as e:
  # Preserve partial mutation and its journal rather than rewriting external
  # changes or concealing an installation failure. Original bytes are archived.
  write(receipt/'terminal.json',dict(terminal_exit_code=1,error=repr(e),traceback=traceback.format_exc(),installed_source_files=installed,registered_build_pending=True,goal_complete=False));raise
if __name__=='__main__':raise SystemExit(main())
