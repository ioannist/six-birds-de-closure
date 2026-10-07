"""Archive genuine final registered results after their actual producer exits zero."""
from pathlib import Path
import hashlib,importlib.util,json,re,shutil
ROOT=Path('/home/repos/six-birds-de-closure')
LIVE=Path('/tmp/de_native_registered_original_audit_receipts')
OUT=ROOT/'results/native_registered_final_verification_2026-10-06'
OBSERVED=Path('/tmp/de_native_registered_actual_exec_result_2026-10-06.json')
VERIFIER=Path('/tmp/de_native_registered_verify_postinstall_recovery.py')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())

def main():
 assert not OUT.exists()
 observed=load(OBSERVED)
 assert observed['session_id']==40823 and observed['exit_code']==0
 terminal=load(LIVE/'terminal.json');result=load(LIVE/'verification.json')
 assert terminal['terminal_exit_code']==0 and terminal['registered_native_verified']
 assert terminal['verification_sha256']==sha(LIVE/'verification.json')
 assert result['registered_source_files']==1786 and result['registered_native_modules']==1772
 assert result['registered_native_statement_checks']==20798 and result['fresh_registered_cumulative_axiom_checks']==32574
 assert result['registered_build_passed'] and result['standard_only']
 assert result['goal_complete'] is False and result['original_paper_restoration_complete'] is False
 candidate=ROOT/'results/native_registered_postinstall_verification_candidate_2026-10-06'
 assert all(sha(candidate/p)==h for p,h in load(candidate/'file-manifest.json').items())
 for name in ('de_native_registered_build_postinstall_recovery.py','de_native_registered_verify_postinstall_recovery.py'):
  assert sha(Path('/tmp')/name)==sha(candidate/name)
 parser=Path('/tmp/de_native_campaign_parser_stack_recovery.py')
 assert sha(parser)==sha(ROOT/'results/native_registered_stack_verification_candidate_2026-10-06'/parser.name)
 snapshot=load(LIVE/'source-snapshot.json')
 current={str(p):sha(p) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
 for name in ('lean-toolchain','lake-manifest.json'):current[str(ROOT/'lean'/name)]=sha(ROOT/'lean'/name)
 assert snapshot==current and result['source_snapshot_sha256']==sha(LIVE/'source-snapshot.json')
 objects=load(LIVE/'objects-snapshot.json');assert len(objects)==1772
 for module,h in objects.items():assert sha(ROOT/'lean/.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean'))==h
 assert result['objects_snapshot_sha256']==sha(LIVE/'objects-snapshot.json')
 plan_path=ROOT/'results/native_registered_aggregate_installation_candidate_2026-10-06/installation-plan.json'
 plan=load(plan_path);names=[name for row in plan['modules'] for name in row['declared_theorems']]
 assert len(names)==len(set(names))==20798
 full=re.findall(r'^#print axioms ([\w.]+)$',(ROOT/'lean/manifests/check_axioms.lean').read_text(),re.M)
 assert len(full)==len(set(full))==32574
 spec=importlib.util.spec_from_file_location('final_receipt_verifier',VERIFIER)
 verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
 commands={'build':['lake','build'],'axioms':['lake','env','lean','-s','65536','manifests/check_axioms.lean'],'statements':['lake','env','lean','-s','65536',str(LIVE/'statements.lean')]}
 for stage,command in commands.items():
  receipt=load(LIVE/(stage+'-terminal.json'));log=LIVE/(stage+'.log')
  assert receipt['terminal_exit_code']==0 and receipt['command']==command and receipt['cwd']==str(ROOT/'lean')
  assert receipt['environment_overrides']==verify.REQUIRED_ENV
  assert receipt['installation_plan_sha256']==sha(plan_path)
  assert receipt['source_snapshot_sha256']==sha(LIVE/'source-snapshot.json') and receipt['log_sha256']==sha(log)
  assert not re.search(r'error:|warning:|Traceback|build failed',log.read_text())
  if stage!='build':assert receipt['objects_snapshot_sha256']==sha(LIVE/'objects-snapshot.json')
 assert 'Build completed successfully' in (LIVE/'build.log').read_text()
 verify.parser.axiom_entries((LIVE/'axioms.log').read_text(),full)
 types=verify.parser.statement_entries((LIVE/'statements.log').read_text(),names)
 verify.original_audit_types(types)
 expected=''.join('import '+r['module']+'\n' for r in plan['modules'])+'set_option warningAsError true\n'+''.join('#check '+n+'\n' for n in names)
 assert (LIVE/'statements.lean').read_text()==expected
 OUT.mkdir()
 originals={}
 for path in LIVE.iterdir():
  assert path.is_file() and path.suffix!='.olean';originals[path.name]=sha(path);shutil.copyfile(path,OUT/path.name)
 shutil.copyfile(OBSERVED,OUT/'actual-exec-result.json')
 for path in (Path('/tmp/de_native_registered_build_postinstall_recovery.py'),VERIFIER,parser,Path(__file__)):
  shutil.copyfile(path,OUT/path.name)
 assert all(sha(OUT/p)==h for p,h in originals.items())
 archive=dict(original_receipt_directory=str(LIVE),original_receipt_sha256=originals,actual_producer_session=40823,actual_producer_exit_code=0,current_source_and_native_object_bindings_checked=True,archived_proof_objects=0,full_cumulative_axiom_queries=32574,native_statement_queries=20798,goal_complete=False)
 (OUT/'archive-readback.json').write_text(json.dumps(archive,indent=2)+'\n')
 manifest={str(p.relative_to(OUT)):sha(p) for p in OUT.rglob('*') if p.is_file()}
 (OUT/'file-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 assert all(sha(OUT/p)==h for p,h in manifest.items())
 print(json.dumps(dict(archived_files=len(manifest),readback=True,actual_producer_exit_code=0,archived_proof_objects=0,goal_complete=False)))
if __name__=='__main__':main()
