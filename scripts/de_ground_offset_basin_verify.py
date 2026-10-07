"""Audit explicit whole-background-box basins for eighteen original offsets."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='d60f6f9'
PRIOR='results/ground_offset_stability_2026-10-04/verification.json'
PACKET='results/ground_offset_basin_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundUncertainNativeBox','GroundUncertainNativeBasin','GroundComplexIntervalBudget']+[f'GroundOffsetBasins.Point{i:03d}' for i in range(18)]+['GroundOriginalOffsetBasins']
OLD_AUDIT='lean/manifests/axiom_audit_ground_offset_stability_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_offset_basin_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_offset_basin_2026-10-04.txt'
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
  if m=='GroundUncertainNativeBasin':namespace+='.Certificate'
  ns += [namespace+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
 assert len(MODS)==22 and len(ns)==len(set(ns))==261
 return ns

def verify():
 prior=json.loads(read(PRIOR));assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
 assert len(prior['source_sha256'])==1561
 for p,h in prior['source_sha256'].items():
  if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
 new=names();old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
 old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==3227
 imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
 assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
 assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
 for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
  assert read('lean/manifests/check_ground_offset_basin_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
 oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT);assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
 closures(oldraw,old);closures(newraw,new)
 header=('Cumulative audit: immutable 3227-declaration raw prefix plus freshly audited 261-declaration suffix.\n'
  'Baseline: d60f6f9; proof-source/toolchain identity checked by de_ground_offset_basin_verify.py.\n'
  'Full 3488-declaration command was not rerun in this packet.\n\n')
 combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
 raw=read(PACKET+'theorem_statements.txt')
 assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
 assert not re.search(r'error:|warning:',raw)
 starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
 for i,m in enumerate(starts):decls[m.group().rstrip('.')]=flatten(raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)].replace(PREFIX,''))
 def require(n,*ts):
  for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
 require('GroundUncertainNativeBasin.Certificate.actual_derivative_norm','hR','hD','hJ','hrows','hb','GroundNativeQuantitativeBall.derivative','≤ ↑c.rate')
 require('GroundUncertainNativeBasin.Certificate.actual_ball_convergence','hR','hD','hJ','hrows','hf','hz','Filter.Tendsto','∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal','dist','^ n')
 require('GroundComplexIntervalBudget.shifted_l2_bound','A ≤ b i','b i ≤ B','A ≤ e','e ≤ B','2 + B - A')
 for kind,root,bg in [('exact','root','b'),('rounded','roundedRoot','rounded_b')]:
  for negative in ['', 'negative_']:
   name='GroundOriginalOffsetBasins.actual_'+kind+'_'+negative+'explicit_basin'
   require(name,'i : Fin 18','hz','Metric.closedBall','GroundOriginalOffsetBasins.commonRadius',
    'GroundOriginalOffsets.'+root+' i','GroundOriginalOffsets.'+bg+' i',
    'GroundNativeIteration.nativeUpdate','GroundNativeControls.originalTolerance','1 / 2',
    'Filter.Tendsto','GroundState.realEmbed','∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal','dist','^ n')
   assert not re.search(r'\b(?:h(?!z\b)\w*)\s*:',decls[PREFIX+name])
 require('GroundOriginalOffsetBasins.whole_background_box_explicit_native_basin','hβ','hz','GroundOriginalOffsetStability.wholeRoot','GroundNativeIteration.nativeUpdate','β')
 require('GroundOriginalOffsetBasins.whole_background_box_explicit_negative_native_basin','hβ','hz','GroundOriginalOffsetStability.wholeRoot','GroundNativeIteration.nativeUpdate','β')
 require('GroundOriginalOffsetBasins.zero_native_row_budget_rejected','¬')
 from de_ground_offset_basin_generate import replay_point,render
 w=json.loads(read(PACKET+'witnesses.json'));assert len(w['points'])==18
 rootp='results/ground_offsets_2026-10-04/witnesses.json';basisp='results/ground_offset_stability_2026-10-04/witnesses.json'
 assert w['root_source_sha256']==sha((ROOT/rootp).read_bytes())
 assert w['basis_source_sha256']==sha((ROOT/basisp).read_bytes())
 roots=json.loads(read(rootp))['points'];bases=json.loads(read(basisp))['points']
 assert len(roots)==len(bases)==18
 for d in w['points']:
  assert len(d['z'])==9 and len(d['C'])==9 and all(len(row)==9 for row in d['C'])
  assert len(d['y'])==len(d['error'])==len(d['DG'])==len(d['DF'])==16
  assert all(len(row)==8 for row in d['DG'])
  assert all(len(pair)==2 and all(len(row)==8 for row in pair) for pair in d['DF'])
  assert len(d['K'])==len(d['L'])==2
 bounds=[replay_point(i,r,c,d) for i,(r,c,d) in enumerate(zip(roots,bases,w['points']))]
 generated=render(w);assert len(generated)==18
 for p,s in generated.items():assert read(p)==s,p
 assert all(0<=v<=F(d['rate'])<1 for v,d in zip(bounds,w['points']))
 assert all(F(d['rho'])==F(1,400000 if i==17 else 40000) for i,d in enumerate(w['points']))
 generic=read(sourcepath('GroundUncertainNativeBasin'))
 for t in ['actual_selected_enclosed','selectedDerivative_enclosed','fullDerivativeBox_sound','StateBox.included_sound','operator_norm_le_rows','hrows.real_rows','hrows.imag_rows','explicit_native_ball_convergence','native_iterate_neg','input_box_on_ball']:
  assert t in generic,t
 box=read(sourcepath('GroundUncertainNativeBox'))
 for t in ['sourceBox_sound','sourceDerivativeBox_sound','actual_selected_enclosed','actual_selector_response_enclosed']:
  assert t in box,t
 family=read(sourcepath('GroundOriginalOffsetBasins'))
 for i in range(18):
  for t in ['responses','response_included','derivative_included','rows','basis_rows','radius_pos','basis_nonneg']:
   assert f'GroundOffsetBasins.Point{i:03d}.'+t in family
 for t in ['whole_root_return','actual_ball_convergence','actual_negative_ball_convergence','root_field_box','common_ball_entry','zero_native_row_budget_rejected']:
  assert t in family,t
 build=read(PACKET+'lean_build.txt');assert 'Build completed successfully (8954 jobs).' in build
 assert not re.search(r'error:|warning:|build failed',build)
 leaves=read(PACKET+'leaf_builds.txt');assert leaves.count('Build completed successfully (8688 jobs).')==18
 for m in [m for m in MODS[:-1] if m!='GroundComplexIntervalBudget']:
  p=sourcepath(m);assert 'Frozen source SHA256: '+sha((ROOT/p).read_bytes())+' '+p in leaves,p
 for i in range(18):
  assert f'Fresh leaf command: lake build {PREFIX}GroundOffsetBasins.Point{i:03d}' in leaves
  r=read(PACKET+f'point{i:03d}_build.txt');assert 'Built '+PREFIX+f'GroundOffsetBasins.Point{i:03d}' in r
  assert not re.search(r'error:|warning:|build failed',r)
 for p in ['native_box_build.txt','native_basin_build.txt','signed_budget_build.txt','family_build.txt']:
  r=read(PACKET+p);assert 'Build completed successfully' in r and not re.search(r'error:|warning:|build failed',r)
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip();assert version==prior['actual_lean_version_checked']
 mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
 for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
 files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,'lean/manifests/check_ground_offset_basin_axioms.lean','lean/manifests/check_ground_offset_basin_statements.lean','math/GROUND_OFFSET_EXPLICIT_BASINS_2026-10-04.md','scripts/de_ground_offset_basin_generate.py','scripts/de_ground_offset_basin_verify.py'}
 files.update(sourcepath(m) for m in MODS)
 files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
 assert len(files)==1618,len(files)
 v=dict(baseline_commit=BASE,scope='Explicit sixteen-real-coordinate native basins, all18 original offsets, both signs and exact/rounded input models and whole background boxes',
  axiom_audit=dict(declarations_cumulative=3488,declarations_preserved=3227,declarations_fresh=261,new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
  lean_build=dict(command='lake build',jobs=8954,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
  statement_check=dict(declarations=261,success=True),fresh_leaf_compilation=dict(modules=18,receipt=PACKET+'leaf_builds.txt',success=True),mathlib=mathlib,actual_lean_version_checked=version,
  original_return=dict(background_offset_kernel_instances=18,whole_background_boxes_earned=True,exact_and_rounded_inputs_distinguished=True,selector_border_inverse_distinct_from_Newton_inverse=True,
   quantitative_response_loss_retained=True,actual_native_all_sixteen_columns=True,complex_coordinate_dimension=16,exact_two_sided_basis_inverses_preserved=True,original_phase_rule_unchanged=True,
   max_whole_ball_operator_budget=str(max(F(p['rate']) for p in w['points'])),positive_and_negative_native_explicit_basins=True,
   all_basin_native_iterate_guards_earned=True,geometric_coordinate_error=True,uniform_coordinate_radius='1/400000',larger_radius_first17='1/40000',continuous_scalar_offset_interval_claimed=False,
   all_offset_frozen_seed_entry_earned=False,all_offset_sixty_source_tests=False,signed_linear_sourced_Hamiltonian_budget=True,
   IEEE_per_operation_emulation=False,global_nonlinear_uniqueness=False,physical_Lambda_bridge=False,control='zero actual populated native row budget rejected'),
  Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,no_floating_solver_rerun=True,saved_matrices_proposal_role_only=True,prior_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,python_test_suite_rerun=False,
  paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,next_construction='Offset frozen-seed basin entry and source finite verdicts; remaining coupling seed returns',
  source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
 (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
 print('3488 cumulative standard-only closures;261 fresh statements;all18 explicit complex basins,both signs/input models;1618 fingerprints')
if __name__=='__main__':verify()
