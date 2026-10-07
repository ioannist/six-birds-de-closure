"""Verify exact native installation only after real proof and registered gates."""
import argparse,hashlib,importlib.util,json,re,subprocess,tarfile
from pathlib import Path

ROOT=Path('/home/repos/six-birds-de-closure')
PARENT=ROOT/'results/native_registered_header_installation_candidate_2026-10-05'
CANDIDATE=ROOT/'results/native_registered_aggregate_installation_candidate_2026-10-06'
STREAM=ROOT/'results/native_stack_semantic_verification_2026-10-06'
STANDARD={'propext','Classical.choice','Quot.sound'}
REQUIRED_ENV={'LEAN_NUM_THREADS':'4'}
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
spec=importlib.util.spec_from_file_location('registered_source_parser',Path('/tmp/de_native_campaign_parser_stack_recovery.py'))
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)

def hoist(raw):
 lines=raw.splitlines(keepends=True)
 return b''.join(l for l in lines if l.startswith(b'import '))+b''.join(l for l in lines if not l.startswith(b'import '))

def _parent_candidate():
 manifest=load(PARENT/'file-manifest.json')
 assert all(sha(PARENT/p)==h for p,h in manifest.items())
 plan=load(PARENT/'installation-plan.json')
 assert (plan['native_modules'],plan['native_fresh_declarations'],plan['prospective_default_declarations'])==(1771,20789,32565)
 archive=PARENT/'proposed_registered_files.tar.gz'
 assert sha(archive)==plan['source_archive_sha256']
 files={}
 with tarfile.open(archive,'r|gz') as tar:
  for member,row in zip(tar,plan['targets'],strict=True):
   assert member.name==row['path'] and member.isfile()
   assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
   raw=tar.extractfile(member).read()
   assert len(raw)==row['size'] and rawsha(raw)==row['sha256']
   assert member.name not in files;files[member.name]=raw
 assert len(files)==1783
 names=[];modules=[]
 for row in plan['modules']:
  raw=files[row['target']];assert rawsha(raw)==row['source_sha256']
  assert parser.declarations(raw.decode())==row['declared_theorems']
  plain=parser.uncomment(raw.decode())
  assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|constant)\s',plain,re.M)
  names+=row['declared_theorems'];modules.append(row['module'])
 assert len(names)==len(set(names))==20789 and len(modules)==len(set(modules))==1771
 full=re.findall(r'^#print axioms (\S+)',files['lean/manifests/check_axioms.lean'].decode(),re.M)
 assert len(full)==len(set(full))==32565 and full[-20789:]==names
 assert plan['modules'][-1]['group']=='execution_failure'
 assert modules[-1]=='SbtCosmo.Derivation.GroundSourceNormalizationFailure'
 assert len(plan['modules'][-1]['declared_theorems'])==5
 suffix=('\n'+''.join('import '+m+'\n' for m in modules[:-1])+'\n'+''.join('#print axioms '+n+'\n' for n in names[:-5])+
         '\nimport '+modules[-1]+'\n\n'+''.join('#print axioms '+n+'\n' for n in names[-5:])).encode()
 header=ROOT/'results/audit_manifest_header_repair_candidate_2026-10-05'
 assert all(sha(header/p)==h for p,h in load(header/'file-manifest.json').items())
 repair=plan['header_repair']
 assert repair['plan_sha256']==sha(header/'repair-plan.json')
 assert repair['file_manifest_sha256']==sha(header/'file-manifest.json')
 old=(header/'current_manifest.repaired.lean').read_bytes()
 assert rawsha(old)==repair['pre_native_repaired_sha256']==plan['input_sha256'][str(ROOT/'lean/manifests/check_axioms.lean')]
 assert old==hoist((header/'current_manifest.before.lean').read_bytes())
 assert files['lean/manifests/check_axioms.lean']==hoist(old+suffix)
 assert files['lean/manifests/check_axioms.lean']==(header/'native_manifest.repaired.lean').read_bytes()
 assert full[:11776]==re.findall(r'^#print axioms (\S+)',old.decode(),re.M)
 assert not plan['preserved_default_manifest_byte_prefix']
 return plan,files,names,full



def failure_proof_gate(plan):
 packet=ROOT/'results/source_normalization_failure_checked_2026-10-05'
 extra=ROOT/'results/source_normalization_failure_production_candidate_2026-10-05'
 for root in [packet,extra]:
  assert all(sha(root/f)==h for f,h in load(root/'file-manifest.json').items())
 ep=load(extra/'production-plan.json');d=load(packet/'audit-summary.json')
 assert ep['checked_packet_file_manifest_sha256']==sha(packet/'file-manifest.json')
 assert ep['checked_audit_summary_sha256']==sha(packet/'audit-summary.json')
 assert d['terminal_exit_code']==0 and d['standard_only'] and d['checked_declarations']==5
 rows=[r for r in plan['modules'] if r['group']=='execution_failure'];assert len(rows)==1
 row=rows[0];names=row['declared_theorems'];assert d['names']==ep['modules'][0]['declared_theorems']==names
 assert row['source_sha256']==d['source_sha256']==ep['modules'][0]['production_sha256']
 assert sha(Path(row['candidate_source']))==row['source_sha256']
 assert plan['additional_candidate_plan_sha256']==sha(extra/'production-plan.json')
 am=load(packet/'archive-manifest.json');archive=packet/'checked_artifacts.tar.gz'
 assert am['archive_sha256']==sha(archive);entries={}
 with tarfile.open(archive,'r|gz') as tar:
  for member,item in zip(tar,am['entries'],strict=True):
   assert member.isfile() and member.name==item['name']
   raw=tar.extractfile(member).read();assert len(raw)==item['size'] and rawsha(raw)==item['sha256']
   assert member.name not in entries;entries[member.name]=raw
 assert len(entries)==25
 base='de_source_normalization_failure/'
 terminal=json.loads(entries[base+'audit-terminal.json']);compile_terminal=json.loads(entries[base+'compile-terminal.json'])
 assert terminal['terminal_exit_code']==compile_terminal['terminal_exit_code']==0
 lean='/home/ioannis/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean'
 private='/tmp/de_source_normalization_failure'
 assert terminal['command']==[lean,'-R',private,private+'/Audit.lean']
 assert compile_terminal['command']==[lean,'-R',private+'/lean','-o',private+'/GroundSourceNormalizationFailure.olean',private+'/lean/SbtCosmo/Derivation/GroundSourceNormalizationFailure.lean']
 query='import SbtCosmo.Derivation.GroundSourceNormalizationFailure\nset_option warningAsError true\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names)
 assert entries[base+'Audit.lean'].decode()==query
 for tag in ['compile','audit']:
  freeze=json.loads(entries[base+tag+'-source-freeze.json'])
  assert all(sha(p)==h for p,h in freeze.items())
 assert terminal['names']==names and terminal['log_sha256']==d['log_sha256']==rawsha(entries[base+'Audit.log'])
 assert terminal['source_freeze_sha256']==d['source_freeze_sha256']==rawsha(entries[base+'audit-source-freeze.json'])
 assert compile_terminal['source_sha256']==d['source_sha256']==rawsha(entries[base+'lean/SbtCosmo/Derivation/GroundSourceNormalizationFailure.lean'])
 assert compile_terminal['object_sha256']==d['object_sha256']==ep['checked_object_sha256']==rawsha(entries[base+'GroundSourceNormalizationFailure.olean'])
 assert compile_terminal['log_sha256']==rawsha(entries[base+'compile.log'])
 assert compile_terminal['source_freeze_sha256']==rawsha(entries[base+'compile-source-freeze.json'])
 log=entries[base+'Audit.log'].decode();assert not re.search(r'error:|warning:',log)
 parser.axiom_entries(log,names);types=parser.statement_entries(log,names)
 prefix='SbtCosmo.Derivation.GroundSourceNormalizationFailure.'
 for short,parts in {
  'imaginary_ground_execution':['normSq u = 1','groundMap b κ u = u','ActivePhase','some','none'],
  'imaginary_ground_no_continuation':['0 < N','run τ','none'],
  'exists_unit_execution_failure':['(b :','(κ : ℝ)','∃ z','complexNormSq z = 1','some z','∀ (N : ℕ)','0 < N','none'],
  'original_tolerance_unit_execution_failure':['(b :','(κ : ℝ) : ∃ z','originalTolerance','∀ (N : ℕ)','none'],
  'exists_phase_execution_split':['∃ a z','Complex.I','∀ (j : Fin 8)','Complex.normSq','complexSourcePotential','some a','none','∀ (N : ℕ)']}.items():
  value=re.sub(r'\s+',' ',types[prefix+short]);parser.require_parts(value,*parts)
  if short.startswith('exists_') or short.startswith('original_tolerance_'):assert 'groundMap' not in value and '(hf :' not in value
 bindings=load(packet/'source-bindings.json');assert len(bindings['module_bindings'])==25
 for binding in bindings['module_bindings'].values():assert sha(binding['source'])==binding['source_sha256']
 normal='SbtCosmo.Derivation.GroundSourceNormalization'
 parent=next(r for r in plan['modules'] if r['module']==normal)
 assert parent['source_sha256']==ep['normalization_parent_source_sha256']==bindings['module_bindings'][normal]['source_sha256']
 assert rawsha(entries['de_source_normalization_return/overlay/SbtCosmo/Derivation/GroundSourceNormalization.olean'])==bindings['module_bindings'][normal]['object_sha256']
 for root in [packet,extra]:assert all(sha(root/f)==h for f,h in load(root/'file-manifest.json').items())
 return dict(declarations=5,standard_only=True,archive_members=25,source_bindings=25,actual_registered_execution=False)

def stack_audit_gate(parent):
 adoption=Path('/tmp/de_native_campaign_stack_adoption_2026-10-06')
 audit=Path('/tmp/de_native_campaign_stack_recovery_2026-10-06')
 original=Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
 assert parent==required(adoption/'terminal.json')
 assert parent['failed_statement_exit_code']==-6 and not parent['compiler_objects_recompiled']
 assert parent['module_inventory_sha256']==sha(original/'receipts/modules.json')
 assert parent['adoption_freeze_sha256']==sha(adoption/'adoption-input-freeze.json')
 result=required(audit/'summary.json')
 assert result==required(audit/'terminal.json') and result['terminal_exit_code']==0 and result['standard_only']
 assert result['module_count']==1734 and result['fresh_statement_count']==result['fresh_axiom_count']==20628
 assert result['unchanged_statement_source'] and not result['proof_sources_changed']
 assert result['source_freeze_sha256']==sha(audit/'source-object-freeze.json')
 assert parent['audit_recovery_summary_sha256']==sha(audit/'summary.json')
 completed=[audit/n for n in ['summary.json','terminal.json','statements-terminal.json','axioms-terminal.json','statements.log','axioms.log']]
 assert parent['audit_recovery_bindings']=={str(p):sha(p) for p in completed}
 failed=required(original/'receipts/statements-terminal.json');assert failed['terminal_exit_code']==-6
 assert sha(audit/'CampaignStatements.lean')==failed['source_sha256']
 plan=load(original/'production-plan.json');names=[n for r in plan['modules'] for n in r['declared_theorems']]
 assert len(names)==len(set(names))==20628
 for stage in ['statements','axioms']:
  receipt=required(audit/(stage+'-terminal.json'));source=audit/('Campaign'+stage.title()+'.lean');log=audit/(stage+'.log')
  assert receipt['terminal_exit_code']==0 and receipt['lean_num_threads']==4 and receipt['stack_kib']==65536
  assert receipt['command'][1:3]==['-s','65536']
  assert receipt['source_sha256']==sha(source) and receipt['log_sha256']==sha(log)
  assert not re.search(r'error:|warning:|Stack overflow',log.read_text())
  if stage=='axioms':parser.axiom_entries(log.read_text(),names)
  else:parser.statement_entries(log.read_text(),names)
 # The full freezes were checked by successful qualification before installation.
 # Bind those historical records here; registered builds recheck installed sources.

def proof_gates(plan):
 original_audit_proof_gate(plan)
 failure_proof_gate(plan)
 summary=required('/tmp/de_native_campaign_semantic_stack_recovery_2026-10-06/finish-summary.json')
 record=required(STREAM/'qualified_verification.json')
 terminal=required(STREAM/'qualified_verification_terminal.json')
 assert summary['terminal_exit_code']==terminal['terminal_exit_code']==0 and summary['standard_only']
 assert summary['module_count']==1738 and summary['fresh_statement_count']==summary['fresh_axiom_count']==20634
 assert summary['verification_sha256']==sha(STREAM/'qualified_verification.json')
 assert terminal['log_sha256']==sha(STREAM/'qualified_verification_driver.txt')
 assert terminal['verifier_sha256']==record['verifier_sha256']==sha('/tmp/de_native_campaign_semantic_stack_recovery_2026-10-06/verify_recovery.py')
 assert record['source_stage_passed'] and record['qualified_stage_passed'] and record['standard_only']
 assert record['checked_modules']==1738 and record['retained_compile_checks']==993 and record['fresh_modules']==745
 assert record['fresh_statement_checks']==record['fresh_axiom_checks']==20634
 parent=required('/tmp/de_native_campaign_stack_adoption_2026-10-06/summary.json')
 stack_audit_gate(parent)
 real=required('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/summary.json')
 assert record['parent_summary_sha256']==sha('/tmp/de_native_campaign_stack_adoption_2026-10-06/summary.json')
 assert record['supplement_summary_sha256']==sha('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/summary.json')
 for d,m,n in [(parent,1734,20628),(real,4,6)]:
  assert d['terminal_exit_code']==0 and d['standard_only'] and d['module_count']==m
  assert d['fresh_statement_count']==d['fresh_axiom_count']==n
 aggregate=required('/home/repos/six-birds-de-closure/results/native_original_sample_aggregate_repair_checked_2026-10-05/audit-summary.json')
 assert aggregate['terminal_exit_code']==0 and aggregate['standard_only'] and len(aggregate['names'])==11
 assert parent['original_private_aggregate_gate_passed']
 assert parent['original_private_aggregate_summary_sha256']==sha('/home/repos/six-birds-de-closure/results/native_original_sample_aggregate_repair_checked_2026-10-05/audit-summary.json')
 by_module={r['module']:r for r in plan['modules']}
 for dirname,group,count,ns in [('de_native_additional_constructions_stack_recovery_2026-10-06','additional',29,132),('de_source_execution_supplement_stack_recovery_2026-10-06','execution',3,18)]:
  base=Path('/tmp')/dirname;d=required(base/'summary.json');t=required(base/'terminal.json')
  assert d==t and d['terminal_exit_code']==0 and d['standard_only'] and d['module_count']==count
  assert d['fresh_statement_count']==d['fresh_axiom_count']==ns
  pp=ROOT/'results'/('native_additional_constructions_candidate_2026-10-05' if group=='additional' else 'source_execution_production_candidate_2026-10-05')/'production-plan.json'
  assert d['production_plan_sha256']==sha(pp) and d['source_freeze_sha256']==sha(base/'source-freeze.json')
  assert d['parent_summary_sha256']==sha('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/summary.json')
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
 recovery_jobs={2490922:'/tmp/de_native_campaign_stack_recovery_2026-10-06/run_audits.py',3325544:'/tmp/de_native_campaign_stack_adoption_2026-10-06/adopt.py',3403554:'/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/build_recovery.py',3769018:'/tmp/de_native_campaign_semantic_stack_recovery_2026-10-06/finish_recovery.py',3825483:'/tmp/de_native_additional_constructions_stack_recovery_2026-10-06/build_recovery.py',3827081:'/tmp/de_source_execution_supplement_stack_recovery_2026-10-06/build_recovery.py',3164894:'/tmp/de_native_campaign_aggregate_recovery_2026-10-05/build_recovery.py',
  3241065:'/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/build_recovery.py',
  4046958:'/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/finish_recovery.py',
  4054594:'/tmp/de_native_additional_constructions_aggregate_recovery_2026-10-06/build_recovery.py',
  4054600:'/tmp/de_source_execution_supplement_aggregate_recovery_2026-10-06/build_recovery.py'}
 for pid,script in recovery_jobs.items():
  try:argv=Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0')
  except FileNotFoundError:continue
  if len(argv)>1 and argv[1].decode()==script:raise Pending(f'Source freeze owner remains active: PID{pid} {script}')
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
 assert offset['manifest_header_repair']['verified']
 assert offset['axiom_audit']['full_cumulative_command_rerun']
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
 commands={'build':['lake','build'],'axioms':['lake','env','lean','-s','65536','manifests/check_axioms.lean'],
           'statements':['lake','env','lean','-s','65536',str(statement_source)]}
 logs={}
 for stage,command in commands.items():
  d=required(receipts/(stage+'-terminal.json'));log=receipts/(stage+'.log')
  assert d['terminal_exit_code']==0 and d['command']==command and d['cwd']==str(ROOT/'lean')
  assert d['environment_overrides']==REQUIRED_ENV
  assert d['installation_plan_sha256']==sha(CANDIDATE/'installation-plan.json')
  assert d['source_snapshot_sha256']==sha(receipts/'source-snapshot.json') and d['log_sha256']==sha(log)
  if stage!='build':assert d['objects_snapshot_sha256']==sha(receipts/'objects-snapshot.json')
  logs[stage]=log.read_text();assert not re.search(r'error:|warning:|Traceback|build failed',logs[stage])
 assert 'Build completed successfully' in logs['build']
 parser.axiom_entries(logs['axioms'],full)
 types=parser.statement_entries(logs['statements'],names)
 original_audit_types(types)
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
 return dict(registered_source_files=1786,registered_native_modules=1772,registered_native_statement_checks=20798,
             fresh_registered_cumulative_axiom_checks=32574,standard_only=True,registered_build_passed=True,
             source_snapshot_sha256=sha(receipts/'source-snapshot.json'),objects_snapshot_sha256=sha(receipts/'objects-snapshot.json'),
             original_paper_restoration_complete=False,goal_complete=False)

def original_audit_types(types):
 prefix='SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability.'
 required_parts={
  'offsets_injective':['Function.Injective','GroundOriginalOffsets.offsets'],
  'finite_readout_eq_verdict':['Fin 18','finiteReadout i =','GroundOriginalOffsetSixty.verdict i'],
  'actual_passing_split_pair':['GroundOriginalOffsetSixty.Tests 0','GroundOriginalOffsetSixty.Tests 3','finiteReadout 0 =','finiteReadout 3','offsets 0 ≠','offsets 3'],
  'finite_admitted_offset_count':['Finset.image','finiteReadout i = true','card = 15'],
  'no_finite_readout_decoder':['¬∃ decode','∀ (i : Fin 18)','decode (','finiteReadout i','offsets i'],
  'all_original_has_limit':['Fin 18','HasLimit i'],
  'limit_readout_true':['Fin 18','limitReadout i = true'],
  'infinite_admitted_offset_count':['Finset.image','limitReadout i = true','card = 18'],
  'no_limit_readout_decoder':['¬∃ decode','∀ (i : Fin 18)','decode (','limitReadout i','offsets i']}
 for short,parts in required_parts.items():
  parser.require_parts(re.sub(r'\s+',' ',types[prefix+short]),*parts)



def check_aggregate_historical_inputs(frozen):
 packet=ROOT/'results/ground_offset_header_installation_candidate_2026-10-05'
 assert all(sha(packet/p)==h for p,h in load(packet/'file-manifest.json').items())
 transport=load(packet/'installation-plan.json')
 assert transport['registered_file_changes']==21 and transport['historical_leaf_freeze_changes']==20
 targets={str(ROOT/r['path']):r for r in transport['targets']}
 allowed={str(ROOT/'lean/SbtCosmo/Derivation/GroundOffsetTransport'/f'Point{i:03d}.lean') for i in range(18)}
 assert allowed==set(targets)&set(frozen)
 archive=packet/'original_files.tar.gz'
 assert sha(archive)==transport['original_archive_sha256']
 with tarfile.open(archive,'r|gz') as stream:
  for member,row in zip(stream,transport['targets'],strict=True):
   assert member.isfile() and member.name==row['path']
   raw=stream.extractfile(member).read()
   assert len(raw)==row['before_size'] and rawsha(raw)==row['before_sha256']
   path=str(ROOT/row['path'])
   if path in allowed:assert frozen[path]==row['before_sha256']
 lake=str(ROOT/'lean/lakefile.lean')
 assert lake in frozen and lake not in allowed
 native=load(CANDIDATE/'installation-plan.json')
 assert all(sha(CANDIDATE/p)==h for p,h in load(CANDIDATE/'file-manifest.json').items())
 assert (native['native_modules'],native['native_fresh_declarations'],native['prospective_default_declarations'])==(1772,20798,32574)
 row=next(r for r in native['targets'] if r['path']=='lean/lakefile.lean')
 assert frozen[lake]==row['existing_target_sha256']
 if sha(lake)!=frozen[lake]:
  assert sha(lake)==row['sha256']
  receipts=ROOT/'results/native_registered_original_audit_installation_receipts_2026-10-05'
  installed=required(receipts/'terminal.json');intent=required(receipts/'intent.json')
  assert installed['terminal_exit_code']==0 and installed['installed_source_files']==1786 and installed['proof_objects_installed']==0
  assert intent['installation_plan_sha256']==sha(CANDIDATE/'installation-plan.json')
  assert intent['before_source_snapshot_sha256']==sha(receipts/'before-source-snapshot.json')
  assert load(receipts/'before-source-snapshot.json')[lake]==frozen[lake]
  originals=load(receipts/'original-target-archive-manifest.json')
  archive=receipts/'original_target_files.tar.gz';assert sha(archive)==originals['archive_sha256']
  saved=next(r for r in originals['entries'] if r['path']=='lean/lakefile.lean')
  assert saved['sha256']==frozen[lake]
  with tarfile.open(archive,'r:gz') as stream:
   member=stream.getmember('lean/lakefile.lean');assert member.isfile()
   raw=stream.extractfile(member).read();assert len(raw)==saved['size'] and rawsha(raw)==frozen[lake]
  proposal=CANDIDATE/'proposed_registered_files.tar.gz';assert sha(proposal)==native['source_archive_sha256']
  with tarfile.open(proposal,'r:gz') as stream:
   member=stream.getmember('lean/lakefile.lean');assert member.isfile()
   raw=stream.extractfile(member).read();assert len(raw)==row['size'] and rawsha(raw)==row['sha256']
  assert Path(lake).read_bytes()==raw
 for p,h in frozen.items():
  if p in allowed:
   assert h==targets[p]['before_sha256']
   assert sha(p) in {h,targets[p]['after_sha256']},p
  elif p==lake:assert sha(p) in {h,row['sha256']},p
  else:assert sha(p)==h,p

def verify_registered_repair(plan, files, parent_plan):
 recovery=Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
 semantic=Path('/tmp/de_registered_aggregate_repair_guard.py')
 assert sha(semantic)=='c01f9b8cd0d872516fe21bf8b01804a89b07a7c4b69ab506e4e70fe0835fa10b'
 spec=importlib.util.spec_from_file_location('aggregate_repair_guard',semantic)
 guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
 qp=load(recovery/'production-plan.json');guard.verify_aggregate_repair(qp, check_aggregate_historical_inputs)
 assert plan['aggregate_proof_repair']==qp['aggregate_proof_repair']
 assert plan['aggregate_recovery_production_plan_sha256']==sha(recovery/'production-plan.json')
 old=ROOT/'results/native_registered_original_audit_installation_candidate_2026-10-05'
 assert all(sha(old/p)==h for p,h in load(old/'file-manifest.json').items())
 assert plan['historical_original_audit_candidate_plan_sha256']==sha(old/'installation-plan.json')
 original=load(old/'installation-plan.json')
 module='SbtCosmo.Derivation.NativeOriginalSampleResults'
 qr=next(r for r in qp['modules'] if r['production_module']==module)
 rr=next(r for r in plan['modules'] if r['module']==module)
 prior=next(r for r in original['modules'] if r['module']==module)
 assert prior==next(r for r in parent_plan['modules'] if r['module']==module)
 assert rr['candidate_source']==qr['production_source_override']
 assert rr['source_sha256']==qr['production_sha256']==sha(rr['candidate_source'])
 assert rr['declared_theorems']==qr['declared_theorems']==prior['declared_theorems']
 assert files[rr['target']]==Path(rr['candidate_source']).read_bytes()
 assert guard.declaration_types(Path(prior['candidate_source']).read_text())==guard.declaration_types(files[rr['target']].decode())
 assert guard.imports(Path(prior['candidate_source']).read_text())==guard.imports(files[rr['target']].decode())
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|constant)\s',parser.uncomment(files[rr['target']].decode()),re.M)

def candidate():
 parent_plan,parent_files,parent_names,parent_full=_parent_candidate()
 assert all(sha(CANDIDATE/p)==h for p,h in load(CANDIDATE/'file-manifest.json').items())
 plan=load(CANDIDATE/'installation-plan.json')
 assert (plan['native_modules'],plan['native_fresh_declarations'],plan['prospective_default_declarations'])==(1772,20798,32574)
 assert plan['parent_header_candidate_plan_sha256']==sha(PARENT/'installation-plan.json')
 assert sha(CANDIDATE/'proposed_registered_files.tar.gz')==plan['source_archive_sha256']
 files={}
 with tarfile.open(CANDIDATE/'proposed_registered_files.tar.gz','r|gz') as tar:
  for m,row in zip(tar,plan['targets'],strict=True):
   assert m.isfile() and m.name==row['path'] and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
   raw=tar.extractfile(m).read();assert len(raw)==row['size'] and rawsha(raw)==row['sha256']
   assert m.name not in files;files[m.name]=raw
 assert len(files)==plan['source_archive_members']==1786
 verify_registered_repair(plan, files, parent_plan)
 normalized=[dict(r) for r in plan['modules'][:-1]]
 oldrow=next(r for r in parent_plan['modules'] if r['module']=='SbtCosmo.Derivation.NativeOriginalSampleResults')
 for r in normalized:
  if r['module']==oldrow['module']:
   r['candidate_source']=oldrow['candidate_source'];r['source_sha256']=oldrow['source_sha256']
 assert normalized==parent_plan['modules']
 assert plan['topological_order'][:-1]==parent_plan['topological_order']
 addon=ROOT/'results/original_audit_nonidentifiability_production_candidate_2026-10-05'
 assert all(sha(addon/p)==h for p,h in load(addon/'file-manifest.json').items())
 ep=load(addon/'production-plan.json');row=plan['modules'][-1]
 assert row['group']=='original_audit_nonidentifiability' and ep['modules']==1 and ep['declarations']==9
 assert row['module']==ep['module']=='SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability'
 assert row['declared_theorems']==ep['names'] and row['source_sha256']==ep['source_sha256']==sha(row['candidate_source'])
 assert row['target']=='lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean'
 added={str(p.relative_to(addon)):p.read_bytes() for p in (addon/'lean').rglob('*.lean')}
 assert len(added)==3 and set(files)==set(parent_files)|set(added) and not set(parent_files)&set(added)
 assert all(files[p]==raw for p,raw in added.items())
 assert all(files[p]==raw for p,raw in parent_files.items() if p not in {'lean/lakefile.lean','lean/manifests/check_axioms.lean','lean/SbtCosmo/Derivation/NativeOriginalSampleResults.lean'})
 anchor=b'    `SbtCosmo.Derivation.GroundSourceNormalizationFailure]'
 assert parent_files['lean/lakefile.lean'].count(anchor)==1
 assert files['lean/lakefile.lean']==parent_files['lean/lakefile.lean'].replace(anchor,b'    `SbtCosmo.Derivation.GroundSourceNormalizationFailure,\n    `'+row['module'].encode()+b']')
 suffix=('\nimport '+row['module']+'\n\n'+''.join('#print axioms '+n+'\n' for n in ep['names'])).encode()
 assert files['lean/manifests/check_axioms.lean']==hoist(parent_files['lean/manifests/check_axioms.lean']+suffix)
 assert rawsha(files['lean/manifests/check_axioms.lean'])==plan['header_repair']['native_repaired_sha256']
 assert plan['header_repair']['parent_native_repaired_sha256']==parent_plan['header_repair']['native_repaired_sha256']
 assert plan['header_repair']['ordered_parent_native_query_prefix_preserved']==32565
 assert plan['group_counts']==dict(parent_plan['group_counts'],original_audit_nonidentifiability={'modules':1,'declarations':9})
 names=parent_names+ep['names'];full=parent_full+ep['names']
 assert len(set(names))==20798 and len(set(full))==32574
 assert parser.declarations(files[row['target']].decode())==ep['names']
 assert re.findall(r'^#print axioms (\S+)',files['lean/manifests/check_axioms.lean'].decode(),re.M)==full
 modules={r['module']:r for r in plan['modules']};position={m:i for i,m in enumerate(plan['topological_order'])}
 assert len(modules)==len(position)==1772 and set(modules)==set(position)
 for r in plan['modules']:
  for imp in parser.imports(files[r['target']].decode()):
   if imp in position:assert position[imp]<position[r['module']]
   else:assert imp in plan['external_imports']
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|constant)\s',parser.uncomment(files[row['target']].decode()),re.M)
 assert plan['original_audit_addon_plan_sha256']==sha(addon/'production-plan.json')
 return plan,files,names,full

def original_audit_proof_gate(plan):
 packet=ROOT/'results/original_audit_nonidentifiability_checked_2026-10-05'
 addon=ROOT/'results/original_audit_nonidentifiability_production_candidate_2026-10-05'
 checkpoint=ROOT/'results/original_audit_nonidentifiability_dependency_checkpoint_2026-10-05'
 for p in [packet,addon,checkpoint]:assert all(sha(p/f)==h for f,h in load(p/'file-manifest.json').items())
 d=load(packet/'checkpoint-verification.json');ep=load(addon/'production-plan.json');cp=load(checkpoint/'checkpoint-verification.json')
 rows=[r for r in plan['modules'] if r['group']=='original_audit_nonidentifiability'];assert len(rows)==1
 row=rows[0];names=row['declared_theorems']
 assert d['checked_modules']==1 and d['checked_declarations']==9 and d['standard_only']
 assert d['compile_terminal_exit_code']==d['audit_terminal_exit_code']==0
 assert d['names']==ep['names']==names
 assert row['source_sha256']==d['source_sha256']==ep['source_sha256']==sha(row['candidate_source'])
 assert ep['checked_packet_manifest_sha256']==cp['parent_packet_manifest_sha256']==plan['original_audit_checked_manifest_sha256']==sha(packet/'file-manifest.json')
 assert plan['original_audit_addon_plan_sha256']==sha(addon/'production-plan.json')
 assert plan['original_audit_dependency_manifest_sha256']==sha(checkpoint/'file-manifest.json')
 compile_terminal=load(packet/'compile-terminal.json');audit_terminal=load(packet/'audit-terminal.json')
 assert compile_terminal['terminal_exit_code']==audit_terminal['terminal_exit_code']==0
 private='/tmp/de_original_audit_nonidentifiability_v3';src=private+'/lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean';obj=private+'/GroundOriginalAuditNonidentifiability.olean'
 assert compile_terminal['command']==['lake','env','lean','-R',private+'/lean','-o',obj,src]
 assert audit_terminal['command']==['/home/ioannis/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean',private+'/Audit.lean']
 assert compile_terminal['cwd']==audit_terminal['cwd']==str(ROOT/'lean')
 assert compile_terminal['environment_overrides']=={'LEAN_NUM_THREADS':'4'}
 assert audit_terminal['environment_overrides']['LEAN_NUM_THREADS']=='4'
 assert audit_terminal['environment_overrides']['LEAN_PATH'].split(':')[0]==private+'/audit-overlay'
 assert compile_terminal['unchanged_inputs'] and compile_terminal['changed_inputs']==[]
 assert compile_terminal['source_sha256']==d['source_sha256']==sha(packet/'lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean')
 assert compile_terminal['object_sha256']==sha(packet/'GroundOriginalAuditNonidentifiability.olean')
 assert compile_terminal['log_sha256']==sha(packet/'compile.log')
 assert compile_terminal['freeze_sha256']==sha(packet/'compile-source-freeze.json')
 assert audit_terminal['audit_source_sha256']==sha(packet/'Audit.lean') and audit_terminal['log_sha256']==d['audit_log_sha256']==cp['parent_audit_log_sha256']==sha(packet/'audit.log')
 assert audit_terminal['freeze_sha256']==sha(packet/'audit-source-object-freeze.json')
 query='import '+row['module']+'\nset_option warningAsError true\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names)
 assert (packet/'Audit.lean').read_text()==query
 for log in [packet/'compile.log',packet/'audit.log']:assert not re.search(r'error:|warning:',log.read_text())
 parser.axiom_entries((packet/'audit.log').read_text(),names)
 original_audit_types(parser.statement_entries((packet/'audit.log').read_text(),names))
 am=load(checkpoint/'archive-manifest.json');archive=checkpoint/'checked_sources_objects_receipts.tar.gz'
 assert sha(archive)==am['archive_sha256']
 archived={}
 with tarfile.open(archive,'r|gz') as tar:
  for m,e in zip(tar,am['entries'],strict=True):
   assert m.isfile() and m.name==e['name'] and m.size==e['size']
   assert not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
   h=hashlib.sha256()
   with tar.extractfile(m) as stream:
    for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
   assert h.hexdigest()==e['sha256'];assert m.name not in archived;archived[m.name]=e['sha256']
 assert len(archived)==cp['archive_members_verified']==2674 and cp['checked_declarations']==9 and cp['standard_only']
 for p,h in load(packet/'file-manifest.json').items():assert archived['checked_packet/'+p]==h
 assert archived['checked_packet/file-manifest.json']==sha(packet/'file-manifest.json')
 cf=load(packet/'compile-source-freeze.json');af=load(packet/'audit-source-object-freeze.json')
 assert len(cf)==2658 and len(af)==cp['bound_inputs']==d['bound_inputs']==2660
 assert all(af[p]==h for p,h in cf.items())
 for name,h in af.items():
  p=Path(name)
  if p.is_relative_to(ROOT):arc='repo/'+str(p.relative_to(ROOT))
  else:
   assert p.is_relative_to(Path(private));arc='private/'+str(p.relative_to(private))
  assert archived[arc]==h
  # Historical objects are explicitly preserved in the checked archive.
  # Current source equations and pinned configuration must still agree.
  if p.is_relative_to(ROOT) and '/.lake/build/' not in str(p) and p!=ROOT/'lean/lakefile.lean':assert sha(p)==h
 historical_lake=af[str(ROOT/'lean/lakefile.lean')]
 assert cp['preserved_lakefile_sha256']==historical_lake
 installed_lake=next(r['sha256'] for r in plan['targets'] if r['path']=='lean/lakefile.lean')
 assert sha(ROOT/'lean/lakefile.lean') in {historical_lake,installed_lake}
 assert d['project_dependency_modules']==cp['project_dependency_modules']==1327
 return dict(declarations=9,standard_only=True,archived_members=2674,historical_inputs=2660,actual_registered_execution=False)


def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--mode',choices=['candidate','registered'],required=True)
 ap.add_argument('--receipts',type=Path,default=Path('/tmp/de_native_registered_original_audit_receipts'))
 args=ap.parse_args()
 try:
  plan,files,names,full=candidate()
  if args.mode=='candidate':
   print(json.dumps(dict(candidate_checked=True,modules=1772,declarations=20798,archive_members=1786,
                        proof_gates_checked=False,repository_integrated=False,goal_complete=False)))
   return 0
  proof_gates(plan)
  require_freezes_released()
  result=registered(plan,files,names,full,args.receipts)
  print(json.dumps(result));return 0
 except Pending as e:
  print(json.dumps(dict(status='pending',reason=str(e),repository_integrated=False,goal_complete=False)));return 2
if __name__=='__main__':raise SystemExit(main())
