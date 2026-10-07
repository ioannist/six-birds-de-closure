from pathlib import Path
import concurrent.futures,hashlib,json,os,re,subprocess,time,traceback
repo=Path('/home/repos/six-birds-de-closure');cwd=repo/'lean';candidate=repo/'results/source_execution_production_candidate_2026-10-05'
base=Path('/tmp/de_source_execution_supplement_stack_recovery_2026-10-06');assert base.exists() and not (base/'source-freeze.json').exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.loads((candidate/'production-plan.json').read_text());assert plan['module_count']==3 and plan['fresh_theorem_count']==18
rows={r['module']:r for r in plan['modules']};names=[n for r in plan['modules'] for n in r['declared_theorems']]
assert len(rows)==3 and len(names)==len(set(names))==18
inputs=list((cwd/'SbtCosmo').rglob('*.lean'))+[cwd/'lakefile.lean',cwd/'lean-toolchain',cwd/'lake-manifest.json',Path(__file__)]
inputs += [p for p in candidate.rglob('*') if p.is_file()]
for packet,record in plan['prior_packet_bindings'].items():
 root=repo/'results'/packet;p=root/'file-manifest.json';assert sha(p)==record['file_manifest_sha256'];inputs.append(p)
 for rel,h in json.loads(p.read_text()).items():assert sha(root/rel)==h
freeze={str(p):sha(p) for p in inputs};(base/'source-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
def check():
 for p,h in freeze.items():assert sha(p)==h,p
parentlog=Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/driver.log');parent_summary=Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/summary.json')
parentmarker='All four supplemental qualified modules and six statement/axiom checks passed; repository integration pending'
def ready():
 s=parentlog.read_text();assert not re.search(r'terminal [1-9]|Traceback|exception ',s),'Supplemental parent failed'
 if parentmarker in s:
  d=json.loads(parent_summary.read_text());assert d['terminal_exit_code']==0 and d['standard_only'] and d['module_count']==4 and d['fresh_axiom_count']==6
  assert d['parent_summary_sha256']==sha('/tmp/de_native_campaign_stack_adoption_2026-10-06/summary.json')
  return True
 p=Path('/proc/3403554/cmdline');assert p.exists(),'Supplemental parent disappeared before terminal success'
 assert p.read_bytes().replace(b'\0',b' ').decode().strip()=='python3 /tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/build_recovery.py'
 return False
terminal={}
try:
 check();print('Source execution3-module /18-theorem qualified driver PID',os.getpid(),'waiting for checked parent recovery; frozen inputs',len(freeze),flush=True)
 while not ready():time.sleep(10)
 check()
 overlay=base/'overlay';objects=base/'objects';receipts=base/'receipts'
 for p in [overlay,objects,receipts]:p.mkdir()
 parent_overlay=Path('/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/overlay')
 for p in parent_overlay.rglob('*.olean'):
  q=overlay/p.relative_to(parent_overlay);q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve(strict=True))
 for root in ['/tmp/de_native_campaign_aggregate_recovery_2026-10-05/receipts','/tmp/de_native_seed_real_returns_stack_recovery_2026-10-06/receipts']:
  p=Path(root)/'modules.json';records=json.loads(p.read_text())
  for row in records:
   rel=Path(*row['module'].split('.')).with_suffix('.olean');assert row['terminal_exit_code']==0 and sha(overlay/rel)==row['olean_sha256'],row['module']
   if 'object_path' in row:
    assert sha(row['object_path'])==row['olean_sha256'] and sha(row['log_path'])==row['log_sha256']
    assert not re.search(r'error:|warning:',Path(row['log_path']).read_text())
    if row.get('retained',False):
     assert sha(row['original_terminal_path'])==row['original_terminal_sha256']
     original=json.loads(Path(row['original_terminal_path']).read_text());assert all(row[k]==v for k,v in original.items())
 raw=subprocess.check_output(['lake','env','which','lean'],cwd=cwd,text=True).strip();lp=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=cwd,text=True).strip();env=dict(os.environ,LEAN_PATH=str(overlay)+':'+lp,LEAN_NUM_THREADS='4')
 def compile_one(module):
  row=rows[module];src=candidate/row['production_path'];assert sha(src)==row['production_sha256'];rel=Path(*module.split('.')).with_suffix('.olean');obj=objects/rel;obj.parent.mkdir(parents=True,exist_ok=True)
  log=receipts/(src.stem+'.log');receipt=log.with_suffix('.json');assert not log.exists() and not obj.exists()
  cmd=[raw,'-s','65536','-R',str(candidate/'lean'),'-o',str(obj),str(src)]
  with log.open('w') as f:r=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
  d=dict(module=module,terminal_exit_code=r.returncode,source_sha256=sha(src),log_sha256=sha(log),command=cmd)
  if r.returncode==0:d['object_sha256']=sha(obj)
  receipt.write_text(json.dumps(d,indent=2)+'\n');print(module,'terminal',r.returncode,flush=True)
  assert r.returncode==0 and not re.search(r'error:|warning:',log.read_text()),module
  assert d['source_sha256']==row['production_sha256'];link=overlay/rel;assert not link.exists();link.parent.mkdir(parents=True,exist_ok=True);link.symlink_to(obj)
  return d
 pending=set(rows);done=set();running={};records=[]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  while pending or running:
   eligible=[m for m in plan['topological_order'] if m in pending and set(plan['dependencies'][m])<=done]
   for module in eligible[:2-len(running)]:pending.remove(module);running[pool.submit(compile_one,module)]=module
   assert running,'No eligible additional module'
   completed,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in completed:module=running.pop(f);records.append(f.result());done.add(module)
   check()
 (receipts/'modules.json').write_text(json.dumps(records,indent=2)+'\n')
 for stage in ['statements','axioms']:
  src=candidate/'lean/manifests'/('check_source_execution_supplement_'+stage+'.lean');log=receipts/(stage+'.log')
  cmd=[raw,'-s','65536',str(src)]
  with log.open('w') as f:r=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
  (receipts/(stage+'-terminal.json')).write_text(json.dumps(dict(terminal_exit_code=r.returncode,command=cmd,source_sha256=sha(src),log_sha256=sha(log)),indent=2)+'\n')
  print(stage,'terminal',r.returncode,flush=True);assert r.returncode==0 and not re.search(r'error:|warning:',log.read_text()),stage
  if stage=='axioms':
   found=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))",log.read_text(),re.S)
   assert [n for n,_,_ in found]==names
   assert all(set(a.replace('\n',' ').replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'} for _,a,_ in found)
 check();terminal=dict(terminal_exit_code=0,standard_only=True,module_count=3,fresh_statement_count=18,fresh_axiom_count=18,source_freeze_sha256=sha(base/'source-freeze.json'),production_plan_sha256=sha(candidate/'production-plan.json'),parent_summary_sha256=sha(parent_summary),repository_registered=False,goal_complete=False)
 (base/'summary.json').write_text(json.dumps(terminal,indent=2)+'\n')
 print('All3 source execution qualified modules and18 exact statement/standard-only axiom checks passed; repository registration and commit pending',flush=True)
except BaseException as e:
 terminal=dict(terminal_exit_code=1,error=repr(e),traceback=traceback.format_exc());traceback.print_exc()
finally:
 (base/'terminal.json').write_text(json.dumps(terminal,indent=2)+'\n')
raise SystemExit(terminal['terminal_exit_code'])
