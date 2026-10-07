"""Audit the populated .3 basin and its actual original-seed return."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE='c30b65a'
PRIOR='results/ground_native_prefix_2026-10-04/verification.json'
PACKET='results/ground_basin_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundNativeGeneralDerivative','GroundBackgroundResponse','GroundNativeQuantitativeBall','GroundNativeDerivativeBox','GroundStateRows','GroundBasin.Point002Data','GroundBasin.Point002Arithmetic','GroundBasin.Point002Bridge','GroundOriginalBasin']
OLD_AUDIT='lean/manifests/axiom_audit_ground_native_prefix_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_basin_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_basin_2026-10-04.txt'
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

def names():
 ns=[]
 for m in MODS:
  s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
  namespace=re.search(r'^namespace (\S+)',s,re.M).group(1)
  ns += [namespace+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
 assert len(MODS)==9 and len(ns)==len(set(ns))==86
 return ns

def closures(raw,ns):
 es=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
 assert [n for n,a in es]==ns
 assert not re.search(r'error:|warning:|sorryAx',raw)
 for n,a in es:assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},n

def flatten(t):
 t=' '.join(t.replace('(',' ').replace(')',' ').split())
 return re.sub(r'\s+,',',',t).replace('⇑','').replace('↑ ','↑')

def verify():
 prior=json.loads(read(PRIOR));assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
 assert len(prior['source_sha256'])==1412
 for p,h in prior['source_sha256'].items():
  if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
 new=names()
 old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
 old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==2880
 imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
 assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
 assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
 for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
  assert read('lean/manifests/check_ground_basin_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
 oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
 assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
 closures(oldraw,old);closures(newraw,new)
 header=('Cumulative audit: immutable 2880-declaration raw prefix plus freshly audited 86-declaration suffix.\n'
  'Baseline: c30b65a; proof-source/toolchain identity checked by de_ground_basin_verify.py.\n'
  'Full 2966-declaration command was not rerun in this packet.\n\n')
 combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
 raw=read(PACKET+'theorem_statements.txt')
 assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
 assert not re.search(r'error:|warning:',raw)
 starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
 for i,m in enumerate(starts):
  t=raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)]
  decls[m.group().rstrip('.')]=flatten(t.replace(PREFIX,''))
 def require(n,*ts):
  for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
 require('GroundBackgroundResponse.actual_response_error','GroundSmooth.pairDerivative','GroundBackgroundResponse.ResponseArithmetic')
 require('GroundNativeGeneralDerivative.nativePairMap_hasFDerivAt','HasFDerivAt','GroundNativeJacobian.nativePairMap','GroundNativeGeneralDerivative.fullDerivative')
 require('GroundNativeQuantitativeBall.explicit_native_ball_convergence','Metric.closedBall','hguards','hbound','Filter.Tendsto','GroundNativeIteration.nativeUpdate')
 require('GroundOriginalBasin.whole_ball_derivative','Metric.closedBall','≤ ↑GroundBasin.Point002Data.rate')
 require('GroundOriginalBasin.original_endpoint_entry','GroundOriginalNativePrefix.orbit 16','Metric.closedBall')
 require('GroundOriginalBasin.original_seed_converges_negative_ground','Filter.Tendsto GroundOriginalNativePrefix.orbit','GroundState.realEmbed -GroundOriginalBasin.u')
 require('GroundOriginalBasin.original_seed_all_guards','n : ℕ','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
 require('GroundOriginalBasin.original_seed_all_unit','n : ℕ','= 1')
 require('GroundOriginalBasin.reflected_tail_rate','n : ℕ','≤ 3 / 5 ^ n * 1 / 48000')
 for n in ['original_seed_converges_negative_ground','original_endpoint_entry','positive_future']:
  assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalBasin.'+n])
 from de_ground_basin_generate import replay
 from de_ground_basin_render import render
 w=json.loads(read(PACKET+'witnesses.json'));budgets=replay(w)
 for p,s in render(w).items():assert read(p)==s,p
 general=read(sourcepath('GroundNativeGeneralDerivative'))
 for t in ['nativePairMap_eventual_return','congr_of_eventuallyEq','-imagOverlap b κ x / overlapNorm b κ x','selected_hasFDerivAt']:
  assert t in general,t
 response=read(sourcepath('GroundBackgroundResponse'))
 for t in ['pairDerivative_equation b v','actual_border_defect h hb','q*y ≤ e*(1-q)','actual_response_error h hv hb hV']:
  assert t in response,t
 ball=read(sourcepath('GroundNativeQuantitativeBall'))
 for t in ['Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le','coordinate_fixed T (m := m)','lipschitz_fixed_orbit_converges','coordinate_iterate_return']:
  assert t in ball,t
 bridge=read(sourcepath('GroundBasin.Point002Bridge'))
 for t in ['StateBox.included_sound (hJ j)','GroundNativeBox.included_sound (hD j i)','GroundStateRows.operator_norm_le_rows','core_endpoint_entry','← map_sub']:
  assert t in bridge,t
 family=read(sourcepath('GroundOriginalBasin'))
 for t in ['Point002Arithmetic.real_jet_cache','Point002Arithmetic.imag_jet_cache','Point002Arithmetic.real_rows','Point002Arithmetic.imag_rows','Point002Arithmetic.endpoint_rows','explicit_native_ball_convergence','native_iterate_neg','tendsto_add_atTop_iff_nat','native_prefix_guards','original_seed_all_guards n']:
  assert t in family,t
 build=read(PACKET+'lean_build.txt');assert 'Build completed successfully (8888 jobs).' in build
 assert not re.search(r'error:|warning:|build failed',build)
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
 assert version==prior['actual_lean_version_checked']
 mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
 for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
 files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
  'lean/manifests/check_ground_basin_axioms.lean','lean/manifests/check_ground_basin_statements.lean',
  'math/GROUND_NATIVE_BASIN_2026-10-04.md','scripts/de_ground_basin_generate.py',
  'scripts/de_ground_basin_render.py','scripts/de_ground_basin_verify.py'}
 files.update(sourcepath(m) for m in MODS)
 files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
 v=dict(baseline_commit=BASE,scope='Explicit .3 native basin and exact original-seed infinite convergence',
  axiom_audit=dict(declarations_cumulative=2966,declarations_preserved=2880,declarations_fresh=86,
   new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
   preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
  lean_build=dict(command='lake build',jobs=8888,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
  statement_check=dict(declarations=86,success=True),mathlib=mathlib,actual_lean_version_checked=version,
  original_return=dict(coupling=w['coupling'],mixing='1/2',coordinate_radius='1/40000',contraction_rate='3/5',endpoint_coordinate_distance='at most1/48000',
   exact_native_orbit_original_seed=True,positive_coupling_infinite_convergence=True,target='negative actual continuation branch ground',
   all_original_orbit_states_unit=True,all_original_orbit_inputs_active_and_legal=True,
   original_both_initial_normalizations_preserved=True,whole_sourced_potential_boxes=True,
   all_sixteen_derivative_columns=True,both_cross_blocks_retained=True,near_inverse_response_error_retained=True,
   cache_inclusions_kernel_checked=True,actual_selected_ground_not_midpoint=True,
   both_inverse_square_roots_and_guards_earned=True,source_conjugated_phase_retained=True,
   positive_coupling_sixty_source_tests=False,IEEE_per_operation_emulation=False,background_offset_kernel_instances=0,
   controls=['zero contraction budget rejected','prior zero selector preconditioner and reciprocal controls preserved']),
  exact_Fraction_budgets=list(map(str,budgets)),Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,NumPy_proposal_role_only=True,
  prior_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,floating_scout_rerun=False,python_test_suite_rerun=False,
  paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,
  next_construction='Positive-coupling finite source tests and remaining background instances',
  source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
 (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
 print('2966 cumulative standard-only closures;86 fresh statements;original .3 seed converges;'+str(len(files))+' fingerprints')
if __name__=='__main__':verify()
