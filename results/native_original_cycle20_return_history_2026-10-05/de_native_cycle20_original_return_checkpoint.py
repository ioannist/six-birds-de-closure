from pathlib import Path
import datetime,hashlib,json,re,subprocess,tarfile
repo=Path('/home/repos/six-birds-de-closure');lean=repo/'lean';private=Path('/tmp/de_native_cycle_lean');out=repo/'results/native_original_cycle20_return_2026-10-05';assert not out.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
fullp=Path('/tmp/de-native-cycle-seed20-full-audit-summary.json');realp=Path('/tmp/de-native-cycle-seed20-real-return-audit-summary.json')
full=json.loads(fullp.read_text());real=json.loads(realp.read_text())
assert full['terminal_exit_code']==real['terminal_exit_code']==0 and full['standard_only'] and real['standard_only'] and len(full['names'])==10 and len(real['names'])==1
fulllog=Path('/tmp/de-native-cycle-seed-full-build-NativeCycleSeed20FullAudit.log');reallog=Path('/tmp/de-native-cycle-seed20-real-return-audit.log')
assert sha(fulllog)==full['log_sha256'] and sha(reallog)==real['log_sha256']
for summary,log in [(full,fulllog),(real,reallog)]:
 found=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))",log.read_text(),re.S)
 assert [n for n,_,_ in found]==summary['names']
 assert all(set(a.replace('\n',' ').replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'} for _,a,_ in found)
parent=json.loads(Path('/tmp/de-native-seed-real-returns-summary.json').read_text());assert parent['terminal_exit_code']==0 and parent['standard_only'] and len(parent['names'])==2
candidate=repo/'results/native_campaign_candidate_2026-10-04';inventory=json.loads((candidate/'status.json').read_text())['files'];archive_sha='b1e0dc26b05d4cbef324823cc0aa4137abc393ea9316e0bf245df4c1a8f3428f';assert sha(candidate/'sources.tar.gz')==archive_sha
bindings={};external={};supplemental=[]
def collect(module):
 if module in bindings or module in external:return
 p=private/(module+'.lean')
 if p.exists():
  obj=p.with_suffix('.olean');kind='private';key='private/'+p.name
  if key in inventory:assert inventory[key]==sha(p),module
  else:
   assert module in ['NativeCycleSeed20RealReturn','NativeCycle20RealOriginalReturn'],module
   supplemental.append(p)
 elif (lean/Path(*module.split('.')).with_suffix('.lean')).exists():
  p=lean/Path(*module.split('.')).with_suffix('.lean');obj=lean/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean');kind='repository'
 else:
  external[module]={}
  if module.startswith('Mathlib.'):
   p=lean/'.lake/packages/mathlib'/Path(*module.split('.')).with_suffix('.lean');assert p.exists();external[module]=dict(source=str(p),source_sha256=sha(p))
  else:assert module.startswith(('Mathlib','Lean','Std','Batteries','Aesop','Qq','Plausible','ProofWidgets','ImportGraph')),module
  return
 assert obj.exists(),module
 bindings[module]=dict(kind=kind,source=str(p),source_sha256=sha(p),object=str(obj),object_sha256=sha(obj),candidate_member=key if kind=='private' and key in inventory else None)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split('--',1)[0].split():collect(dep)
collect('NativeCycleSeed20RealReturn')
private_sources={n:r['source_sha256'] for n,r in bindings.items() if r['kind']=='private'}
for n in ['NativeCycleSeed20Step'+f'{i:03d}' for i in range(320)]+['NativeCycleSeed20Pair'+f'{i:03d}' for i in range(160)]:assert n in bindings,n
for module,h in real.get('private_source_sha256',{}).items():assert sha(private/(module+'.lean'))==h,module
frozenp=Path('/tmp/de-native-seed-real-returns-freeze.json');freeze=json.loads(frozenp.read_text());assert parent['source_freeze_sha256']==sha(frozenp);assert all(sha(Path(p))==h for p,h in freeze.items())
mathlib=lean/'.lake/packages/mathlib';head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip();assert head=='8f9d9cff6bd728b17a24e163c9402775d9e6a365' and not subprocess.check_output(['git','status','--porcelain'],cwd=mathlib,text=True).strip()
runtime=repo/'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py';assert sha(runtime)=='391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd'
review=repo/'math/GROUND_NATIVE_ORIGINAL_CYCLE20_RETURN_2026-10-05.md'
paths=[fullp,realp,fulllog,reallog,Path('/tmp/de-native-seed-real-returns-summary.json'),frozenp,Path(__file__),review]
paths += [private/(n+'.lean') for n in ['NativeCycleSeed20Transport','NativeCycleSeed20Return','NativeCycleSeed20RealReturn','NativeCycleSeed20FullAudit','NativeCycleSeed20RealReturnAudit','NativeCycle20RealOriginalReturn']]
paths += [Path('/tmp/de-native-cycle-seed-full-build-NativeCycleSeed20'+n+'.log') for n in ['Transport','Return']]+[Path('/tmp/de-native-cycle-seed20-real-return-build.log')]
paths += [Path('/tmp/'+n+'.log') for n in ['de-native-cycle-seed-leaves-driver','de-native-cycle-seed-pairs-driver','de-native-cycle-seed-families-driver','de-native-seed-real-returns-driver']]
leaflog=Path('/tmp/de-native-cycle-seed-leaves-driver.log').read_text();assert 'All472 original-seed native transport leaves passed; one earlier pilot plus471 fresh' in leaflog
pairlog=Path('/tmp/de-native-cycle-seed-pairs-driver.log').read_text();assert 'All236 paired original-seed certificates passed; two earlier pilots plus234 fresh' in pairlog
for i in range(320):
 p=Path('/tmp/de-native-seed-build-NativeCycleSeed20Step'+f'{i:03d}'+'.log');assert p.exists() and not re.search(r'error:|warning:',p.read_text());paths.append(p)
for i in range(160):
 p=Path('/tmp/de-native-cycle-seed20-pair000.log') if i==0 else Path('/tmp/de-native-seed-pair-build-NativeCycleSeed20Pair'+f'{i:03d}'+'.log')
 assert p.exists() and not re.search(r'error:|warning:',p.read_text());paths.append(p)
# Historical finite verdict checks stay distinct from the newly completed11.
historical_finite=[]
for stem,log in [('de-native-cycle-seed20-sixty','de-native-cycle-seed-sixty-build-NativeCycleSeed20SixtyAudit.log'),('de-native-cycle-seed20-prefix-failures','de-native-cycle-seed20-prefix-failures-audit.log')]:
 summary=Path('/tmp/'+stem+'-audit-summary.json');d=json.loads(summary.read_text());p=Path('/tmp/'+log);assert d['terminal_exit_code']==0 and d['standard_only'] and sha(p)==d['log_sha256'];paths += [summary,p]
 historical_finite.append(dict(summary_sha256=sha(summary),log_sha256=sha(p),names=d['names'],fresh_in_this_packet=False))
paths += [p for p in Path('/tmp/de_native_cycle20_original_return_checkpoint_history').rglob('*') if p.is_file()];paths += supplemental;out.mkdir();entries=[];archive=out/'checked_artifacts.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
 for p in sorted(set(paths)):
  name='workspace/'+str(p.relative_to(repo)) if p.is_relative_to(repo) else str(p.relative_to('/tmp'));h=sha(p);tar.add(p,arcname=name,recursive=False);assert sha(p)==h;entries.append(dict(name=name,source=str(p),sha256=h,size=p.stat().st_size))
with tarfile.open(archive,'r|gz') as tar:
 for member,row in zip(tar,entries,strict=True):
  assert member.name==row['name'];f=tar.extractfile(member);assert f and hashlib.sha256(f.read()).hexdigest()==row['sha256']
(out/'archive-manifest.json').write_text(json.dumps(dict(archive_sha256=sha(archive),entries=entries),indent=2)+'\n')
(out/'source-bindings.json').write_text(json.dumps(dict(module_bindings=bindings,external_imports=external,candidate_archive=str(candidate/'sources.tar.gz'),candidate_archive_sha256=archive_sha,candidate_archive_sequential_verification=json.loads((candidate/'archive_verification.json').read_text()),supplemental_sources={str(p):sha(p) for p in supplemental},seed_real_source_freeze_sha256=sha(frozenp),inputs_revalidated=len(freeze),mathlib_head=head,mathlib_clean=True,lean_version=subprocess.check_output(['lake','env','lean','--version'],cwd=lean,text=True).strip(),lean_toolchain_sha256=sha(lean/'lean-toolchain'),lake_manifest_sha256=sha(lean/'lake-manifest.json'),runtime_sha256=sha(runtime),historical_finite_audits=historical_finite),indent=2)+'\n')
(out/'audit-summary.json').write_text(json.dumps(dict(terminal_exit_code=0,standard_only=True,checked_declarations=11,names=full['names']+real['names'],full_audit=full,real_audit=real,historical_finite_checks_counted_as_fresh=False),indent=2)+'\n')
(out/'README.md').write_text('''# Original coupling20 real two-cycle return

The actual original complex seed has a populated320-update /160-pair entry into the certified source cycle basin. Ten original-seed and one exactly-real return declarations passed their fresh printed statements and standard-only transitive axiom checks. The result supplies exactly real unit source period-two witnesses, site-four density gap greater than9/20, original-seed even/odd limits, all source phase/normalization guards and unit norms, state/density nonconvergence, eventual L2 updates greater than9/40 and failure of the original four-test conjunction. No dynamic hypothesis is supplied by the caller.

The first1..60 finite verdict failures have separate historical checked evidence and a separately checked open finite parameter theorem; eventual failure is not substituted for them. The source uses a fixed iteration count and reports convergence afterward, with no early-exit branch. This is an exact mathematical source result, not an IEEE trace, earliest diagnostic index, amplitude blowup, universal high-coupling claim, continuum statement or physical Lambda bridge.

The archive preserves all320 leaf and160 pair logs, completed compile/audit receipts, sources not present in the original candidate archive, parent-driver terminal histories, finite historical audit evidence, construction script and self-review. Imported sources and objects are pinned; candidate source hashes and its preserved sequential verification are matched. Every new archive member passed sequential SHA256 readback. The coupling20/30 original cycle/real return parents are terminal success. Stable samples and qualified production integration remain pending. Paper and runtime are unchanged. Review is adversarial self-review, not independent review.
''')
verification=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),terminal_exit_code=0,checked_declarations=11,standard_only=True,seed_entry_updates=320,paired_steps=160,archive_members_sequentially_verified=len(entries),private_modules_bound=sum(r['kind']=='private' for r in bindings.values()),repository_modules_bound=sum(r['kind']=='repository' for r in bindings.values()),original_seed_real_initially_assumed=False,production_registration_pending=True,paper_edited=False,original_runtime_edited=False,goal_complete=False)
(out/'checkpoint-verification.json').write_text(json.dumps(verification,indent=2)+'\n');manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()};(out/'file-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items());print(json.dumps(verification),flush=True)
