"""Audit populated rounded-offset original-seed prefixes and basin returns."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='e68dee3'
PRIOR='results/ground_offset_basin_2026-10-04/verification.json'
PACKET='results/ground_offset_prefix_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundCertifiedNativePrefix','GroundOffsetPrefixInitial','GroundCertifiedNativeEntry','GroundOffsetSeedReturn']
W=json.loads((ROOT/PACKET/'witnesses.json').read_text())
MODS += [f'GroundOffsetPrefix.Point{i:03d}.Step{n:03d}' for i,p in enumerate(W['points']) for n in range(len(p['steps']))]
MODS += [f'GroundOffsetPrefix.Point{i:03d}' for i in range(18)]+['GroundOriginalOffsetSeed']
OLD_AUDIT='lean/manifests/axiom_audit_ground_offset_basin_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_offset_prefix_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_offset_prefix_2026-10-04.txt'
MUTABLE={'README.md','lean/README.md','lean/lakefile.lean','lean/manifests/check_axioms.lean','lean/manifests/coverage_table.md','math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
def read(p):return (ROOT/p).read_text()
def sha(b):return hashlib.sha256(b).hexdigest()
def baseline(p):return subprocess.check_output(['git','show',BASE+':'+p],cwd=ROOT)
def sourcepath(m):return 'lean/'+(PREFIX+m).replace('.','/')+'.lean'
def canonical(p):
 b=(ROOT/p).read_bytes()
 if b'\r\n' in b:
  attrs=subprocess.check_output(['git','check-attr','text','eol','--',p],cwd=ROOT).decode()
  assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in b
  b=b.replace(b'\r\n',b'\n')
 return b

def closures(raw,ns):
 es=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
 assert [n for n,a in es]==ns
 assert not re.search(r'error:|warning:|sorryAx',raw)
 for n,a in es:assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},n

def flatten(t):
 t=' '.join(t.replace('(',' ').replace(')',' ').split())
 return re.sub(r'\s+,',',',t).replace('⇑','').replace('↑ ','↑')

def names():
 ns=[]
 for m in MODS:
  s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
  namespace=re.search(r'^namespace (\S+)',s,re.M).group(1)
  if m=='GroundCertifiedNativePrefix':namespace+='.Certificate'
  ns += [namespace+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
 assert len(MODS)==444 and len(ns)==len(set(ns))==956
 return ns

def verify():
 prior=json.loads(read(PRIOR));assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
 assert len(prior['source_sha256'])==1618
 for p,h in prior['source_sha256'].items():
  if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
 new=names();old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
 old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==3488
 imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
 assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
 assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
 for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
  assert read('lean/manifests/check_ground_offset_prefix_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
 oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT);assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
 closures(oldraw,old);closures(newraw,new)
 header=('Cumulative audit: immutable 3488-declaration raw prefix plus freshly audited 956-declaration suffix.\n'
  'Baseline: e68dee3; proof-source/toolchain identity checked by de_ground_offset_prefix_verify.py.\n'
  'Full 4444-declaration command was not rerun in this packet.\n\n')
 combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
 raw=read(PACKET+'theorem_statements.txt')
 assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
 assert not re.search(r'error:|warning:',raw)
 starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
 for i,m in enumerate(starts):decls[m.group().rstrip('.')]=flatten(raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)].replace(PREFIX,''))
 def require(n,*ts):
  for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
 require('GroundCertifiedNativePrefix.Certificate.enclosed','c','hb','GroundCertifiedNativePrefix.Certificate.orbit','GroundNativePhase.unpack')
 require('GroundOffsetSeedReturn.rounded_seed_return','c','hentry','Filter.Tendsto','∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal','GroundState.complexNormSq')
 name='GroundOriginalOffsetSeed.rounded_original_seed_return'
 require(name,'i : Fin 18','GroundOriginalOffsets.rounded_b i','GroundOriginalOffsets.roundedRoot i','GroundOriginalOffsets.certificates i',
  'GroundNativeIteration.nativeUpdate','GroundNativeControls.originalTolerance','1 / 2','GroundOriginalSeed.initial',
  'Filter.Tendsto','GroundState.realEmbed','∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal','GroundState.complexNormSq','= 1')
 assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+name])
 require('GroundOriginalOffsetSeed.rounded_original_geometric_tail','GroundOriginalOffsetSeed.data i','GroundOriginalOffsetBasins.rate i','dist','^ n')
 require('GroundOriginalOffsetSeed.all_original_prefix_enclosed','GroundOffsetSeedReturn.orbit','GroundNativePhase.unpack')
 require('GroundOriginalOffsetSeed.zero_entry_budget_rejected','¬')
 require('GroundOriginalOffsetSeed.rounded_original_density_limit','i : Fin 18','j : Fin 8','Filter.Tendsto','Complex.normSq','GroundOriginalOffsets.roundedRoot i')
 require('GroundOriginalOffsetSeed.eventual_original_density_separation','∀ᶠ','9 / 100','GroundOffsetSeedReturn.orbit 0','GroundOffsetSeedReturn.orbit 17')
 from de_ground_offset_prefix_render import replay_point,render_steps,render_families
 w=json.loads(read(PACKET+'witnesses.json'));assert w==W and len(w['points'])==18
 for p,h in w['source_sha256'].items():assert sha((ROOT/p).read_bytes())==h,p
 rootp='results/ground_offsets_2026-10-04/witnesses.json';basisp='results/ground_offset_stability_2026-10-04/witnesses.json';basinp='results/ground_offset_basin_2026-10-04/witnesses.json'
 roots=json.loads(read(rootp))['points'];bases=json.loads(read(basisp))['points'];basins=json.loads(read(basinp))['points']
 assert len(roots)==len(bases)==len(basins)==18
 assert [len(p['steps']) for p in w['points']]==[37,65,40,23,18,17,16,16,16,15,15,15,15,15,15,15,16,52]
 for i,(p,r,c,b) in enumerate(zip(w['points'],roots,bases,basins)):
  assert p['offset_index']==i and p['entry']['sign']==-1
  replay_point(p,r,c,b)
 generated=render_steps(w)|render_families(w);assert len(generated)==439
 for p,s in generated.items():assert read(p)==s,p
 core=read(sourcepath('GroundCertifiedNativePrefix'))
 for t in ['GroundUncertainNativeBox.arithmetic_native_step','c.seams','c.enclosed','nativeUpdate_unit','GroundOriginalSeed.initial_unit']:
  assert t in core,t
 entry=read(sourcepath('GroundCertifiedNativeEntry'))
 for t in ['coordinateBox_sound','differenceBox_sound','map_sub','tendsto_add_atTop_iff_nat','Function.iterate_add_apply']:
  assert t in entry,t
 bridge=read(sourcepath('GroundOffsetSeedReturn'))
 for t in ['whole_background_box_explicit_negative_native_basin','rounded_inputs_sound','iterate_property_of_tail','iterate_tendsto_of_tail','nativeUpdate_unit','distance_from_boxes']:
  assert t in bridge,t
 initial=read(sourcepath('GroundOffsetPrefixInitial'))
 for t in ['inverse_sqrt_sound','normalizedBox_sound','raw_norm_return','double_normalization']:
  assert t in initial,t
 final=read(sourcepath('GroundOriginalOffsetSeed'))
 for i in range(18):
  for t in ['certificate','entry','distance']:
   assert f'GroundOffsetPrefix.Point{i:03d}.'+t in final
 for t in ['rounded_seed_return','rounded_seed_geometric_tail','zero_entry_budget_rejected']:
  assert t in final,t
 build=read(PACKET+'lean_build.txt');assert 'Build completed successfully (9398 jobs).' in build
 assert not re.search(r'error:|warning:|build failed',build)
 leaves=read(PACKET+'leaf_builds.txt');assert leaves.count('Build completed successfully (8668 jobs).')==421
 for m in ['GroundCertifiedNativePrefix']+MODS[4:-19]:
  p=sourcepath(m);assert 'Frozen source SHA256: '+sha((ROOT/p).read_bytes())+' '+p in leaves,p
 for i,p in enumerate(w['points']):
  for n in range(len(p['steps'])):
   assert f'Fresh leaf command: lake build {PREFIX}GroundOffsetPrefix.Point{i:03d}.Step{n:03d}' in leaves
   r=read(PACKET+f'point{i:03d}_step{n:03d}_build.txt');assert 'Built '+PREFIX+f'GroundOffsetPrefix.Point{i:03d}.Step{n:03d}' in r
   assert not re.search(r'error:|warning:|build failed',r)
 families=read(PACKET+'family_builds.txt')
 for i in range(18):
  p=sourcepath(f'GroundOffsetPrefix.Point{i:03d}')
  assert 'Frozen source SHA256: '+sha((ROOT/p).read_bytes())+' '+p in families,p
  assert f'Fresh family command: lake build {PREFIX}GroundOffsetPrefix.Point{i:03d}' in families
 for p in ['generic_prefix_build.txt','generic_entry_build.txt','initial_build.txt','seed_return_build.txt','pilot_build.txt','family_build.txt']+[f'point{i:03d}_family_build.txt' for i in range(18)]:
  r=read(PACKET+p);assert 'Build completed successfully' in r and not re.search(r'error:|warning:|build failed',r)
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip();assert version==prior['actual_lean_version_checked']
 mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
 assert not subprocess.check_output(['git','status','--porcelain'],cwd=libroot).strip()
 for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
 files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,'lean/manifests/check_ground_offset_prefix_axioms.lean','lean/manifests/check_ground_offset_prefix_statements.lean','math/GROUND_OFFSET_SEED_RETURNS_2026-10-04.md','scripts/de_ground_offset_prefix_render.py','scripts/de_ground_offset_prefix_verify.py'}
 files.update(sourcepath(m) for m in MODS)
 files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
 # Actual receipt count is bound rather than assumed from planned bookkeeping.
 expected=1618+1+444+2+2+1+2+len([p for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json'])
 assert len(files)==expected,(len(files),expected)
 v=dict(baseline_commit=BASE,scope='Guarded infinite actual original-seed convergence at all18 rounded background-offset inputs',
  axiom_audit=dict(declarations_cumulative=4444,declarations_preserved=3488,declarations_fresh=956,new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
  lean_build=dict(command='lake build',jobs=9398,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
  statement_check=dict(declarations=956,success=True),fresh_leaf_compilation=dict(modules=421,receipt=PACKET+'leaf_builds.txt',success=True),mathlib=mathlib,actual_lean_version_checked=version,
  original_return=dict(background_offset_instances=18,rounded_background_inputs=True,exact_uniform_offset_seed_return=False,whole_background_box_seed_return=False,
   mathematical_original_seed_literal=True,both_initial_normalizations_preserved=True,original_phase_rule_unchanged=True,all_finite_seams_earned=True,
   actual_negative_basin_entry=True,entry_times=[len(p['steps']) for p in w['points']],infinite_actual_native_convergence=True,
   all_native_iterate_guards_earned=True,all_native_iterates_unit=True,geometric_coordinate_tail=True,actual_root_distance_not_proposal_center=True,
   all_site_density_limits=True,eventual_endpoint_site0_density_gap="greater than9/100",finite_density_separation_time=False,
   all_offset_sixty_source_tests=False,IEEE_per_operation_emulation=False,first_stopping_index=False,global_nonlinear_uniqueness=False,physical_Lambda_bridge=False,
   control='zero populated entry row budget rejected'),
  Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,no_floating_solver_rerun=True,saved_matrices_proposal_role_only=True,prior_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,python_test_suite_rerun=False,
  paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,next_construction='Offset sixty-update verdicts and exact uniform-offset seed returns; remaining coupling seed returns',
  source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
 (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
 print(f'4444 cumulative standard-only closures;956 fresh statements;all18 rounded-offset original-seed infinite returns;{len(files)} fingerprints')
if __name__=='__main__':verify()
