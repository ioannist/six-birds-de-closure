"""Install exact reviewed source repairs only after all real private gates finish."""
from pathlib import Path
import argparse,datetime,hashlib,importlib.util,json,os,re,tarfile,traceback,uuid
ROOT=Path('/home/repos/six-birds-de-closure');PACKET=ROOT/'results/ground_offset_header_installation_candidate_2026-10-05';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();rawsha=lambda b:hashlib.sha256(b).hexdigest()
verifier=Path('/tmp/de_native_registered_verify_stack_recovery.py');spec=importlib.util.spec_from_file_location('native_source_guards',verifier);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
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

def current_hash(p):
    assert not p.is_symlink(),('Source target is a symlink',str(p))
    if p.exists():
        assert p.is_file(),('Source target is not a file',str(p))
        return sha(p)
    return None


def atomically_install(p,raw):
    p.parent.mkdir(parents=True,exist_ok=True)
    assert p.parent.resolve().is_relative_to(ROOT.resolve())
    tmp=p.with_name(p.name+'.native-install-'+uuid.uuid4().hex)
    try:
        with tmp.open('xb') as stream:stream.write(raw);stream.flush();os.fsync(stream.fileno())
        os.replace(tmp,p)
        descriptor=os.open(p.parent,os.O_RDONLY|os.O_DIRECTORY)
        try:os.fsync(descriptor)
        finally:os.close(descriptor)
    finally:tmp.unlink(missing_ok=True)


def install_target(row,raw,receipts,installed,attempted):
    p=ROOT/row['path']
    assert current_hash(p)==row['existing_target_sha256'],row['path']
    attempted.append(row['path'])
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_target=row['path'],phase='before_write',fresh_registered_build_pending=True,goal_complete=False))
    atomically_install(p,raw)
    assert sha(p)==row['sha256'],row['path']
    installed.append(row['path'])
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_target=None,phase='write_completed',fresh_registered_build_pending=True,goal_complete=False))


def observed_targets(plan):
    observations={}
    for row in plan['targets']:
        p=ROOT/row['path']
        item=dict(original_sha256=row['existing_target_sha256'],proposed_sha256=row['sha256'])
        try:
            assert p.resolve().is_relative_to(ROOT.resolve()),'Target resolves outside repository'
            value=current_hash(p)
            item.update(observed_sha256=value,matches_original=value==row['existing_target_sha256'],matches_proposed=value==row['sha256'],absent=value is None)
        except BaseException as e:item.update(observation_error=repr(e))
        observations[row['path']]=item
    return observations


def record_installation_failure(receipts,plan,installed,attempted,error):
    observed=observed_targets(plan)
    pending=[p for p in attempted if p not in installed]
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_targets=pending,phase='failed',observed_targets=observed,fresh_registered_build_pending=True,goal_complete=False))
    write(receipts/'terminal.json',dict(terminal_exit_code=1,installed=installed,attempted=attempted,pending_targets=pending,observed_targets=observed,error=repr(error),traceback=traceback.format_exc(),goal_complete=False))



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
 freezes=[Path('/tmp/de_native_campaign_stack_recovery_2026-10-06/source-object-freeze.json'),Path('/tmp/de_native_campaign_stack_adoption_2026-10-06/adoption-input-freeze.json'),Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/source-freeze.json'),Path('/tmp/de_native_campaign_semantic_stack_recovery_2026-10-06/finish-source-freeze.json'),Path('/tmp/de_native_additional_constructions_stack_recovery_2026-10-06/source-freeze.json'),Path('/tmp/de_source_execution_supplement_stack_recovery_2026-10-06/source-freeze.json'),Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05/source-object-freeze.json'),Path('/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/source-freeze.json'),Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/finish-source-freeze.json')]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_aggregate_recovery_2026-10-06','de_source_execution_supplement_aggregate_recovery_2026-10-06']]+[audit_root/'cumulative-source-freeze.json']
 protected={}
 for p in freezes:
  for f,h in load(p).items():assert f not in protected or protected[f]==h;protected[f]=h
 assert all(sha(p)==h for p,h in protected.items())
 assert all((ROOT/p).read_bytes()==raw for p,raw in payload['original'].items())
 receipt=ROOT/'results/ground_offset_header_installation_receipts_2026-10-05';assert not receipt.exists();receipt.mkdir();write(receipt/'before-source-freeze.json',protected)
 write(receipt/'intent.json',dict(installation_plan_sha256=sha(PACKET/'installation-plan.json'),installer_sha256=sha(__file__),private_cumulative_audit_summary_sha256=sha(audit_root/'cumulative-summary.json'),targets=plan['targets'],registered_build_pending=True,goal_complete=False))
 installed=[];attempted=[]
 normalized_plan=dict(targets=[dict(path=r['path'],existing_target_sha256=r['before_sha256'],sha256=r['after_sha256']) for r in plan['targets']])
 try:
  for r in normalized_plan['targets']:
   install_target(r,payload['repaired'][r['path']],receipt,installed,attempted)
  assert all((ROOT/p).read_bytes()==raw for p,raw in payload['repaired'].items())
  expected_changed={str(ROOT/p) for p in installed}&set(protected);actual_changed={p for p,h in protected.items() if sha(p)!=h};assert actual_changed==expected_changed
  write(receipt/'terminal.json',dict(terminal_exit_code=0,installed_source_files=21,proof_objects_installed=0,registered_build_pending=True,registered_cumulative_audit_pending=True,whole_offset_verification_pending=True,goal_complete=False));print('Exact21-file source repair installed; actual registered proof gates remain pending');return 0
 except BaseException as e:
  # Preserve partial mutation and its journal rather than rewriting external
  # changes or concealing an installation failure. Original bytes are archived.
  record_installation_failure(receipt,normalized_plan,installed,attempted,e);raise
if __name__=='__main__':raise SystemExit(main())
