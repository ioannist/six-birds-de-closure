from pathlib import Path
import datetime,hashlib,importlib.util,json,re,subprocess,tarfile
import argparse,sys
ap=argparse.ArgumentParser(description='Checkpoint the original coupling10 only after actual family and sixty audits finish')
ap.add_argument('--mode',choices=['preflight','checkpoint'],default='preflight')
args=ap.parse_args()
repo_pre=Path('/home/repos/six-birds-de-closure');base_pre=Path('/tmp/de_native_cycle_lean')
assert 'def κ : ℚ := GroundSamples.Point008.a' in (base_pre/'NativeStableFrame008.lean').read_text()
assert re.search(r'^def a : ℚ := 10\s*$',(repo_pre/'lean/SbtCosmo/Derivation/GroundSamples/Point008.lean').read_text(),re.M)
assert re.search(r'^def N : ℕ := 30\s*$',(base_pre/'NativeStableSeed008Transport.lean').read_text(),re.M)
family_pre=Path('/tmp/de-native-stable-seed-families-driver.log').read_text()
sixty_pre=Path('/tmp/de-native-stable-seed-sixty-driver.log').read_text()
assert not re.search(r'terminal [1-9]|Traceback|^exception',family_pre+sixty_pre,re.M)
required_family=['NativeStableSeed008Transport terminal 0','NativeStableSeed008Audit terminal 0']
required_sixty=['NativeStableSeed008Sixty terminal 0','NativeStableSeed008SixtyAudit terminal 0']
ready=all(m in family_pre for m in required_family) and all(m in sixty_pre for m in required_sixty)
if args.mode=='preflight' or not ready:
 print(json.dumps(dict(mode=args.mode,coupling='10',original_sample_index=8,paired_entry=30,entry_updates=60,ready_for_checkpoint=ready,family_markers_present=[m for m in required_family if m in family_pre],sixty_markers_present=[m for m in required_sixty if m in sixty_pre],proof_success_claimed=False,checkpoint_created=False,goal_complete=False)),flush=True)
 raise SystemExit(0 if args.mode=='preflight' else 2)

repo=Path('/home/repos/six-birds-de-closure');base=Path('/tmp/de_native_cycle_lean');out=repo/'results/native_original_stable10_return_2026-10-05'
assert not out.exists();index=8;tag=f'{index:03d}';family_module='NativeStableSeed'+tag
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
parser_path=repo/'scripts/de_native_campaign_verify.py';spec=importlib.util.spec_from_file_location('stable10_source_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
family_log=Path('/tmp/de-native-stable-seed-families-driver.log');sixty_log=Path('/tmp/de-native-stable-seed-sixty-driver.log')
for suffix in ['Transport','Audit']:assert family_module+suffix+' terminal 0' in family_log.read_text()
for suffix in ['Sixty','SixtyAudit']:assert family_module+suffix+' terminal 0' in sixty_log.read_text()
queries=[family_module+'Audit',family_module+'SixtyAudit'];auditlogs=[Path('/tmp/de-native-stable-seed-family-build-'+queries[0]+'.log'),Path('/tmp/de-native-stable-seed-sixty-build-'+queries[1]+'.log')]
names=[];types={}
for query,log in zip(queries,auditlogs,strict=True):
 raw=(base/(query+'.lean')).read_text();nn=re.findall(r'^#check (\S+)',raw,re.M);assert re.findall(r'^#print axioms (\S+)',raw,re.M)==nn
 s=log.read_text();assert not re.search(r'error:|warning:',s);parser.axiom_entries(s,nn);types.update(parser.statement_entries(s,nn));names+=nn
assert len(names)==len(set(names))==15
prefix='SbtCosmo.Derivation.'+family_module+'.'
parser.require_parts(re.sub(r'\s+',' ',types[prefix+'original_seed_return']),'Tendsto','GroundOriginalSeed.initial','realEmbed (-','∀ (n : ℕ)','ActivePhase','NativeLegal','complexNormSq')
parser.require_parts(re.sub(r'\s+',' ',types[prefix+'original_seed_density_limit']),'(j : Fin 8)','Tendsto','Complex.normSq','GroundOriginalSeed.initial')
parser.require_parts(re.sub(r'\s+',' ',types[prefix+'Sixty.actual_four_source_tests']),'MeetsConvergence','originalTolerance','GroundOriginalResiduals.ε','(1 / 2)','orbit 59','orbit 60')
assert 'def κ : ℚ := GroundSamples.Point008.a' in (base/'NativeStableFrame008.lean').read_text()
assert re.search(r'^def a : ℚ := 10\s*$',(repo/'lean/SbtCosmo/Derivation/GroundSamples/Point008.lean').read_text(),re.M)
assert re.search(r'^def N : ℕ := 30\s*$',(base/(family_module+'Transport.lean')).read_text(),re.M)
private={};registered={};external={};paths=set(auditlogs)|{Path(__file__)}
inventory=json.loads((repo/'results/native_campaign_candidate_2026-10-04/status.json').read_text())['files']
def collect(module):
 if module in private or module in registered or module in external:return
 if (base/(module+'.lean')).exists():
  source=base/(module+'.lean');row=dict(source=str(source),source_sha256=sha(source));key='private/'+source.name
  if key in inventory:assert row['source_sha256']==inventory[key];row['candidate_archive_member']=key
  paths.add(source)
  if module not in queries:
   obj=base/(module+'.olean');assert obj.exists();row.update(object=str(obj),object_sha256=sha(obj));paths.add(obj)
  private[module]=row
 elif module.startswith(('SbtCosmo.','Gametheory.')):
  source=repo/'lean'/Path(*module.split('.')).with_suffix('.lean');obj=repo/'lean/.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
  assert source.exists() and obj.exists(),module;registered[module]=dict(source=str(source),source_sha256=sha(source),object=str(obj),object_sha256=sha(obj))
 else:
  source=repo/'lean/.lake/packages/mathlib'/Path(*module.split('.')).with_suffix('.lean');assert source.exists(),module;external[module]=dict(source=str(source),source_sha256=sha(source));return
 for line in source.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split('--',1)[0].split():collect(dep)
for q in queries:collect(q)
leaflog=Path('/tmp/de-native-stable-seed-leaves-driver.log').read_text();pairlog=Path('/tmp/de-native-stable-seed-pairs-driver.log').read_text()
for suffix,count,progress,logprefix in [('Step',60,leaflog,'de-native-stable-seed-step-build-'),('Pair',30,pairlog,'de-native-stable-seed-pair-build-')]:
 for j in range(count):
  module=family_module+suffix+f'{j:03d}';assert module in private and module+' terminal 0' in progress
  log=Path('/tmp')/(logprefix+module+'.log');assert log.exists() and not log.read_text().strip();paths.add(log)
for suffix,kind in [('Transport','family'),('Audit','family'),('Sixty','sixty'),('SixtyAudit','sixty')]:
 p=Path('/tmp')/('de-native-stable-seed-'+kind+'-build-'+family_module+suffix+'.log');assert p.exists();paths.add(p)
fps=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
frozen={}
for p in fps:
 for f,h in json.loads(p.read_text()).items():assert f not in frozen or frozen[f]==h;frozen[f]=h
assert all(sha(p)==h for p,h in frozen.items())
out.mkdir();archive=out/'completed_artifacts.tar.gz';entries=[]
with tarfile.open(archive,'w:gz',dereference=True) as tar:
 for p in sorted(paths):
  name=str(p.relative_to('/tmp'));h=sha(p);tar.add(p,arcname=name,recursive=False);assert sha(p)==h
  entries.append(dict(name=name,source=str(p),sha256=h,size=p.stat().st_size))
with tarfile.open(archive,'r|gz') as tar:
 for member,row in zip(tar,entries,strict=True):
  assert member.name==row['name'] and member.isfile();raw=tar.extractfile(member).read();assert len(raw)==row['size'] and hashlib.sha256(raw).hexdigest()==row['sha256']
(out/'archive-manifest.json').write_text(json.dumps(dict(archive_sha256=sha(archive),entries=entries),indent=2)+'\n')
(out/'source-bindings.json').write_text(json.dumps(dict(private=private,repository=registered,external_imports=external,frozen_inputs_revalidated=len(frozen)),indent=2)+'\n')
mathlib=repo/'lean/.lake/packages/mathlib';rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip();assert rev=='8f9d9cff6bd728b17a24e163c9402775d9e6a365';assert not subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True).strip()
summary=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),terminal_exit_code=0,terminal_evidence='Actual family/sixty driver exit0 markers and compiler/audit logs; collector runs no new Lean command',standard_only=True,names=names,checked_declarations=15,coupling='10',original_sample_index=index,actual_entry_update=60,leaf_certificates=60,paired_certificates=30,audit_log_sha256={str(p):sha(p) for p in auditlogs},private_modules=len(private),repository_modules=len(registered),archive_members=len(entries),mathlib_revision=rev,source_freeze_inputs_revalidated=len(frozen),original_seed_infinite_return_checked=True,sixty_four_tests_pass=True,repository_registered=False,qualified_verification_pending=True,whole_twelve_sample_campaign_complete=False,ieee_execution=False,paper_edited=False,original_runtime_edited=False,review='adversarial self-review',goal_complete=False)
(out/'audit-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
snap=out/'driver-snapshots';snap.mkdir()
for prefix in ['leaves','pairs','families','sixty']:
 p=Path('/tmp')/('de-native-stable-seed-'+prefix+'-driver.log');(snap/p.name).write_bytes(p.read_bytes())
(out/'README.md').write_text('Original coupling10/sample8: the unchanged reified complex starting state enters its actual negative-ground basin after60 certified updates, converges with active phase/legal normalization/unit norm at every iterate, and has the actual ground densities as all-site limits. All four original mathematical source tests pass at update60. Fifteen actual printed declarations and transitive-axiom closures were checked against completed family/sixty exit0 driver markers. This collector did not rerun Lean and does not claim a fresh registered build. Private dependency sources and objects, compile/audit logs and exact collector are archived with sequential hash readback; registered dependencies are source/object bound. Four parent logs are live snapshots, not terminal receipts for the entire campaign. Fresh qualified compilation, registration, whole-sample classification, actual cumulative audits and commit remain pending. No IEEE or earliest-success-index claim. Paper/runtime unchanged; review is adversarial self-review.\n')
assert all(sha(p)==h for p,h in frozen.items())
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()};(out/'file-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/f)==h for f,h in manifest.items())
print(json.dumps(summary))
