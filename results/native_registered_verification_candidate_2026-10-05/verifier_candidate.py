"""Verify exact native installation only after real proof and registered gates."""
import argparse,hashlib,importlib.util,json,re,subprocess,tarfile
from pathlib import Path

ROOT=Path('/home/repos/six-birds-de-closure')
CANDIDATE=ROOT/'results/native_registered_installation_candidate_2026-10-05'
STREAM=ROOT/'results/native_campaign_stream_verification_2026-10-05'
STANDARD={'propext','Classical.choice','Quot.sound'}
MUTABLE_DOCS={'README.md','lean/README.md','lean/manifests/coverage_table.md',
              'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
class Pending(Exception):pass
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rawsha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def required(p):
 p=Path(p)
 if not p.is_file():raise Pending('Required evidence is absent: '+str(p))
 return load(p)
spec=importlib.util.spec_from_file_location('registered_source_parser',ROOT/'scripts/de_native_campaign_verify.py')
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)

def candidate():
 manifest=load(CANDIDATE/'file-manifest.json')
 assert all(sha(CANDIDATE/p)==h for p,h in manifest.items())
 plan=load(CANDIDATE/'installation-plan.json')
 assert (plan['native_modules'],plan['native_fresh_declarations'],plan['prospective_default_declarations'])==(1770,20784,32560)
 archive=CANDIDATE/'proposed_registered_files.tar.gz'
 assert sha(archive)==plan['source_archive_sha256']
 files={}
 with tarfile.open(archive,'r|gz') as tar:
  for member,row in zip(tar,plan['targets'],strict=True):
   assert member.name==row['path'] and member.isfile()
   assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
   raw=tar.extractfile(member).read()
   assert len(raw)==row['size'] and rawsha(raw)==row['sha256']
   assert member.name not in files;files[member.name]=raw
 assert len(files)==1780
 names=[];modules=[]
 for row in plan['modules']:
  raw=files[row['target']];assert rawsha(raw)==row['source_sha256']
  assert parser.declarations(raw.decode())==row['declared_theorems']
  plain=parser.uncomment(raw.decode())
  assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|constant)\s',plain,re.M)
  names+=row['declared_theorems'];modules.append(row['module'])
 assert len(names)==len(set(names))==20784 and len(modules)==len(set(modules))==1770
 full=re.findall(r'^#print axioms (\S+)',files['lean/manifests/check_axioms.lean'].decode(),re.M)
 assert len(full)==len(set(full))==32560 and full[-20784:]==names
 suffix=('\n'+''.join('import '+m+'\n' for m in modules)+'\n'+''.join('#print axioms '+n+'\n' for n in names)).encode()
 assert files['lean/manifests/check_axioms.lean'].endswith(suffix)
 old=files['lean/manifests/check_axioms.lean'][:-len(suffix)]
 assert rawsha(old)==plan['input_sha256'][str(ROOT/'lean/manifests/check_axioms.lean')]
 return plan,files,names,full

def proof_gates(plan):
 summary=required('/tmp/de-native-campaign-verification-stream-finish-summary.json')
 record=required(STREAM/'qualified_verification.json')
 terminal=required(STREAM/'qualified_verification_terminal.json')
 assert summary['terminal_exit_code']==terminal['terminal_exit_code']==0 and summary['standard_only']
 assert summary['module_count']==1738 and summary['fresh_statement_count']==summary['fresh_axiom_count']==20634
 assert summary['verification_sha256']==sha(STREAM/'qualified_verification.json')
 assert terminal['log_sha256']==sha(STREAM/'qualified_verification_driver.txt')
 assert terminal['verifier_sha256']==record['verifier_sha256']==sha('/tmp/de_native_campaign_stream_verify.py')
 assert record['source_stage_passed'] and record['qualified_stage_passed'] and record['standard_only']
 assert record['fresh_modules']==1738 and record['fresh_statement_checks']==record['fresh_axiom_checks']==20634
 parent=required('/tmp/de-native-campaign-qualified-stream-summary.json')
 real=required('/tmp/de-native-seed-real-returns-qualified-stream-summary.json')
 assert record['parent_summary_sha256']==sha('/tmp/de-native-campaign-qualified-stream-summary.json')
 assert record['supplement_summary_sha256']==sha('/tmp/de-native-seed-real-returns-qualified-stream-summary.json')
 for d,m,n in [(parent,1734,20628),(real,4,6)]:
  assert d['terminal_exit_code']==0 and d['standard_only'] and d['module_count']==m
  assert d['fresh_statement_count']==d['fresh_axiom_count']==n
 aggregate=required('/tmp/de-native-original-sample-results-audit-summary.json')
 assert aggregate['terminal_exit_code']==0 and aggregate['standard_only'] and len(aggregate['names'])==11
 assert parent['original_private_aggregate_gate_passed']
 assert parent['original_private_aggregate_summary_sha256']==sha('/tmp/de-native-original-sample-results-audit-summary.json')
 by_module={r['module']:r for r in plan['modules']}
 for dirname,group,count,ns in [('de_native_additional_constructions_stream_qualified','additional',29,132),('de_source_execution_supplement_stream_qualified','execution',3,18)]:
  base=Path('/tmp')/dirname;d=required(base/'summary.json');t=required(base/'terminal.json')
  assert d==t and d['terminal_exit_code']==0 and d['standard_only'] and d['module_count']==count
  assert d['fresh_statement_count']==d['fresh_axiom_count']==ns
  pp=ROOT/'results'/('native_additional_constructions_candidate_2026-10-05' if group=='additional' else 'source_execution_production_candidate_2026-10-05')/'production-plan.json'
  assert d['production_plan_sha256']==sha(pp) and d['source_freeze_sha256']==sha(base/'source-freeze.json')
  assert d['parent_summary_sha256']==sha('/tmp/de-native-seed-real-returns-qualified-stream-summary.json')
  target_modules={m for m,r in by_module.items() if r['group']==group}
  records=load(base/'receipts/modules.json')
  assert len(records)==count and {r['module'] for r in records}==target_modules
  group_names=[n for r in plan['modules'] if r['group']==group for n in r['declared_theorems']]
  for row in records:
   r=by_module[row['module']];p=Path(r['candidate_source'])
   assert row['terminal_exit_code']==0 and row['source_sha256']==r['source_sha256']==sha(p)
   assert sha(base/'objects'/Path(*row['module'].split('.')).with_suffix('.olean'))==row['object_sha256']
   assert sha(base/'receipts'/(p.stem+'.log'))==row['log_sha256']
  for stage in ('statements','axioms'):
   r=load(base/'receipts'/(stage+'-terminal.json'));log=base/'receipts'/(stage+'.log')
   assert r['terminal_exit_code']==0 and r['log_sha256']==sha(log)
   assert not re.search(r'error:|warning:',log.read_text())
   if stage=='axioms':parser.axiom_entries(log.read_text(),group_names)
   else:parser.statement_entries(log.read_text(),group_names)
 priority=required('/tmp/de_native_stable15_priority_recovery/summary.json')
 assert required('/tmp/de_native_stable15_priority_recovery/terminal.json')==priority
 assert priority['terminal_exit_code']==0 and priority['standard_only']
 assert priority['fresh_modules']==216 and priority['retained_terminal_zero_modules']==73 and priority['total_modules']==289
 assert priority['source_freeze_sha256']==sha('/tmp/de_native_stable15_priority_recovery/source-freeze.json')
 for tag,count in [('FiniteVerdictsAudit',18),('CombinedReturnAudit',27)]:
  d=required(Path('/tmp/de_native_stable15_priority_recovery')/(tag+'-summary.json'))
  assert d['terminal_exit_code']==0 and d['standard_only'] and d['checked_declarations']==count
 return record

def require_freezes_released():
 jobs={662901:'de_native_campaign_qualified_stream_build.py',760297:'de_native_seed_real_returns_qualified_stream_build.py',
       853725:'de_native_campaign_verification_stream_finish.py',853723:'de_native_additional_constructions_stream_qualified_build.py',
       853738:'de_source_execution_supplement_stream_qualified_build.py',4049651:'de_native_stable15_priority_recovery/build_recovery.py',
       2558747:'de_native_stable_seed_leaves_private_build.py',2637955:'de_native_stable_seed_pairs_private_build.py',
       2854622:'de_native_stable_seed_families_private_build.py',3948875:'de_native_stable_seed_sixty_private_build.py',
       940127:'de_native_stable_prefix_failures_private_build.py',2056100:'de_native_original_sample_results_private_build.py'}
 for pid,script in jobs.items():
  try:cmd=Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()
  except FileNotFoundError:continue
  if cmd=='/usr/bin/python3 /tmp/'+script:raise Pending(f'Source freeze owner remains active: PID{pid} {script}')

def registered(plan,files,names,full,receipts):
 offset=required(ROOT/'results/ground_offset_transport_2026-10-04/verification.json')
 assert offset['axiom_audit']['success'] and offset['axiom_audit']['declarations_cumulative']==11776
 assert offset['lean_build']['success'] and offset['lean_build']['jobs']==10003
 assert offset['namespace_recovery']['verified']
 for p,h in offset['source_sha256'].items():
  if p not in MUTABLE_DOCS and p not in {'lean/lakefile.lean','lean/manifests/check_axioms.lean'}:assert sha(ROOT/p)==h,p
 for p,raw in files.items():assert (ROOT/p).read_bytes()==raw,('Installed bytes differ',p)
 for p,h in plan['input_sha256'].items():
  if p not in {str(ROOT/'lean/lakefile.lean'),str(ROOT/'lean/manifests/check_axioms.lean')}:assert sha(p)==h,p
 snapshot=required(receipts/'source-snapshot.json')
 expected={str(p):sha(p) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
 for name in ('lean-toolchain','lake-manifest.json'):expected[str(ROOT/'lean'/name)]=sha(ROOT/'lean'/name)
 assert snapshot==expected, 'Registered source snapshot must cover the current full source tree'
 objects=required(receipts/'objects-snapshot.json')
 expected_objects={r['module']:sha(ROOT/'lean/.lake/build/lib/lean'/Path(*r['module'].split('.')).with_suffix('.olean')) for r in plan['modules']}
 assert objects==expected_objects
 statement_source=receipts/'statements.lean'
 expected_statement=''.join('import '+r['module']+'\n' for r in plan['modules'])+'set_option warningAsError true\n'+''.join('#check '+n+'\n' for n in names)
 assert statement_source.read_text()==expected_statement
 commands={'build':['lake','build'],'axioms':['lake','env','lean','manifests/check_axioms.lean'],
           'statements':['lake','env','lean',str(statement_source)]}
 logs={}
 for stage,command in commands.items():
  d=required(receipts/(stage+'-terminal.json'));log=receipts/(stage+'.log')
  assert d['terminal_exit_code']==0 and d['command']==command and d['cwd']==str(ROOT/'lean')
  assert d['installation_plan_sha256']==sha(CANDIDATE/'installation-plan.json')
  assert d['source_snapshot_sha256']==sha(receipts/'source-snapshot.json') and d['log_sha256']==sha(log)
  if stage!='build':assert d['objects_snapshot_sha256']==sha(receipts/'objects-snapshot.json')
  logs[stage]=log.read_text();assert not re.search(r'error:|warning:|Traceback|build failed',logs[stage])
 assert 'Build completed successfully' in logs['build']
 parser.axiom_entries(logs['axioms'],full)
 types=parser.statement_entries(logs['statements'],names)
 prefix='SbtCosmo.Derivation.NativeOriginalSampleResults.'
 for name,parts in {'original_sample_has_limit_iff':['Fin 12','Tendsto','↔','< 10'],
                    'original_sample_sixty_tests_iff':['Fin 12','↔','< 9','59','60'],
                    'original_sample_eventual_tests_iff':['Fin 12','↔','< 10','∀ᶠ'],
                    'original_sample_successful_prefix_iff':['Fin 12','↔','< 9','< 60','∃']}.items():
  parser.require_parts(re.sub(r'\s+',' ',types[prefix+name]),*parts)
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean',text=True).strip()
 assert version==offset['actual_lean_version_checked']
 lib=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=lib,text=True).strip()==offset['mathlib']['revision']
 assert not subprocess.check_output(['git','status','--porcelain'],cwd=lib,text=True).strip()
 return dict(registered_source_files=1780,registered_native_modules=1770,registered_native_statement_checks=20784,
             fresh_registered_cumulative_axiom_checks=32560,standard_only=True,registered_build_passed=True,
             source_snapshot_sha256=sha(receipts/'source-snapshot.json'),objects_snapshot_sha256=sha(receipts/'objects-snapshot.json'),
             original_paper_restoration_complete=False,goal_complete=False)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--mode',choices=['candidate','registered'],required=True)
 ap.add_argument('--receipts',type=Path,default=Path('/tmp/de_native_registered_receipts'))
 args=ap.parse_args()
 try:
  plan,files,names,full=candidate()
  if args.mode=='candidate':
   print(json.dumps(dict(candidate_checked=True,modules=1770,declarations=20784,archive_members=1780,
                        proof_gates_checked=False,repository_integrated=False,goal_complete=False)))
   return 0
  proof_gates(plan)
  require_freezes_released()
  result=registered(plan,files,names,full,args.receipts)
  print(json.dumps(result));return 0
 except Pending as e:
  print(json.dumps(dict(status='pending',reason=str(e),repository_integrated=False,goal_complete=False)));return 2
if __name__=='__main__':raise SystemExit(main())
