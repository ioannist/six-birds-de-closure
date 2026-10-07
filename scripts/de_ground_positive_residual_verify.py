"""Audit actual .3 original-seed sixty-update source diagnostics."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='5885a36'
PRIOR='results/ground_basin_2026-10-04/verification.json'
PACKET='results/ground_positive_residual_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundComplexNormBridge','GroundComplexResidualBudget','GroundOriginalBasinEstimates','GroundOriginalPositiveResiduals']
OLD_AUDIT='lean/manifests/axiom_audit_ground_basin_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_positive_residual_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_positive_residual_2026-10-04.txt'
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
 assert len(MODS)==4 and len(ns)==len(set(ns))==28
 return ns

def closures(raw,ns):
 es=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
 assert [n for n,a in es]==ns
 assert not re.search(r'error:|warning:|sorryAx',raw)
 for n,a in es:assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},n

def flatten(t):
 t=' '.join(t.replace('(',' ').replace(')',' ').split())
 return re.sub(r'\s+,',',',t).replace('⇑','').replace('↑ ','↑')

def budgets():
 s=F(177,50);q=F(3,5);entry=F(1,48000);d=F(1,10000000000);eps=F.from_float(1e-8)
 out=dict(coupling=str(F.from_float(.3)),source_threshold=str(F.from_float(1e-10)),convergence_epsilon=str(eps),coordinate_rate=str(q),coordinate_entry=str(entry),basis_norm_budget=str(s),euclidean_factor='4',selector_coordinate_lipschitz_budget='1',distance_budget=str(d),
  orbit_59_proposed_euclidean_cap=str(4*s*q**43*entry),orbit_60_proposed_euclidean_cap=str(4*s*q**44*entry),actual_candidate_60_proposed_distance_cap=str((4*s+4)*q**44*entry),
  last_update_cap=str(2*d),double_phase_cap=str(4*d),sourced_potential_budget='1/2',sourced_shifted_hamiltonian_budget='5/2',rayleigh_eigen_residual_cap=str(F(5,2)*(d+d*d)),sourcing_cap='0')
 assert all(F(out[k])<=d for k in ['orbit_59_proposed_euclidean_cap','orbit_60_proposed_euclidean_cap','actual_candidate_60_proposed_distance_cap'])
 assert all(F(out[k])<eps for k in ['last_update_cap','double_phase_cap','rayleigh_eigen_residual_cap','sourcing_cap'])
 assert F.from_float(1e-10)<1-2*d*d and 2*d*d<=1
 return out

def verify():
 prior=json.loads(read(PRIOR));assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
 assert len(prior['source_sha256'])==1437
 for p,h in prior['source_sha256'].items():
  if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
 new=names();old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
 old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==2966
 imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
 assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
 assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
 for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
  assert read('lean/manifests/check_ground_positive_residual_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
 oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT);assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
 closures(oldraw,old);closures(newraw,new)
 header=('Cumulative audit: immutable 2966-declaration raw prefix plus freshly audited 28-declaration suffix.\n'
  'Baseline: 5885a36; proof-source/toolchain identity checked by de_ground_positive_residual_verify.py.\n'
  'Full 2994-declaration command was not rerun in this packet.\n\n')
 combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
 raw=read(PACKET+'theorem_statements.txt')
 assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
 assert not re.search(r'error:|warning:',raw)
 starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
 for i,m in enumerate(starts):
  decls[m.group().rstrip('.')]=flatten(raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)].replace(PREFIX,''))
 def require(n,*ts):
  for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
 require('GroundComplexNormBridge.l2_pack_le','GroundComplexEuclidean.l2','≤ 4 * ‖x‖')
 require('GroundComplexResidualBudget.shifted_l2_bound','hb','he','≤ 2 + B * GroundComplexEuclidean.l2 z')
 require('GroundOriginalBasinEstimates.selector_lipschitz','LipschitzOnWith 1','GroundNativePhase.selected','Metric.closedBall')
 require('GroundOriginalBasinEstimates.actual_candidate_distance','n : ℕ','GroundNativeIteration.nativeCandidate','GroundOriginalNativePrefix.orbit')
 require('GroundOriginalPositiveResiduals.actual_candidate_distance_sixty','GroundComplexEuclidean.l2','GroundOriginalPositiveResiduals.orbit 60','≤ GroundOriginalPositiveResiduals.d')
 require('GroundOriginalPositiveResiduals.actual_candidate_ground_data','GroundState.complexHamiltonian','GroundOriginalPositiveResiduals.potential','GroundOriginalPositiveResiduals.eigenvalue')
 require('GroundOriginalPositiveResiduals.final_fixed_gap_threshold','GroundSourceDiagnostics.finalFixedGap','GroundNativePhase.nativePhase','GroundNativeIteration.nativeCandidate')
 require('GroundOriginalPositiveResiduals.actual_seed_positive_sixty_convergence_tests','GroundSourceDiagnostics.MeetsConvergence','GroundOriginalPositiveResiduals.orbit 59','GroundOriginalPositiveResiduals.orbit 60','n : ℕ','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
 for n in ['actual_seed_positive_sixty_convergence_tests','actual_candidate_distance_sixty','final_eigen_threshold','final_fixed_gap_threshold']:
  assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalPositiveResiduals.'+n])
 caps=budgets();assert json.loads(read(PACKET+'exact_budgets.json'))==caps
 estimates=read(sourcepath('GroundOriginalBasinEstimates'))
 for t in ['Point002Arithmetic.real_response_cache','Point002Arithmetic.imag_response_cache','Point002Arithmetic.selector_rows','selected_hasFDerivAt b','Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le','selector_lipschitz.dist_le_mul','sourceBox_sound originalBackground κ hx','complexSourcePotential_neg','Point002Arithmetic.source_bounds']:
  assert t in estimates,t
 final=read(sourcepath('GroundOriginalPositiveResiduals'))
 for t in ['actual_candidate_distance 44','nativePhase_real_sign_invariant tolerance_budget.1 hd.1','double_phase_gap actual_candidate_ground_data.1','energy potential (positiveGround potential)','eigen_residual_bound actual_candidate_ground_data.2.1','sourcing_self_comparison_zero','original_seed_all_guards','Function.iterate_succ_apply\' GroundOriginalNativePrefix.f 59']:
  assert t in final,t
 assert '3022314549036573/302231454903657293676544' in final
 build=read(PACKET+'lean_build.txt');assert 'Build completed successfully (8892 jobs).' in build
 assert not re.search(r'error:|warning:|build failed',build)
 for p in ['generic_build.txt','estimates_build.txt','original_build.txt']:
  r=read(PACKET+p);assert 'Build completed successfully' in r and not re.search(r'error:|warning:|build failed',r)
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip();assert version==prior['actual_lean_version_checked']
 mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
 for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
 files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,'lean/manifests/check_ground_positive_residual_axioms.lean','lean/manifests/check_ground_positive_residual_statements.lean','math/GROUND_POSITIVE_SOURCE_RESIDUALS_2026-10-04.md','scripts/de_ground_positive_residual_verify.py'}
 files.update(sourcepath(m) for m in MODS)
 files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
 assert len(files)==1455,len(files)
 v=dict(baseline_commit=BASE,scope='Exact original-seed .3 native sixty-update source diagnostics',
  axiom_audit=dict(declarations_cumulative=2994,declarations_preserved=2966,declarations_fresh=28,new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
  lean_build=dict(command='lake build',jobs=8892,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
  statement_check=dict(declarations=28,success=True),mathlib=mathlib,actual_lean_version_checked=version,
  original_return=dict(coupling=caps['coupling'],convergence_tolerance=caps['convergence_epsilon'],updates=60,exact_native_orbit_original_seed=True,positive_coupling_sixty_source_tests=True,
   all_four_source_tests_earned=True,actual_sourced_candidate_and_ground_energy=True,source_double_phase_retained=True,source_conjugated_phase_retained=True,actual_rayleigh_energy_retained=True,
   selector_coordinate_lipschitz_earned=True,State_coordinate_to_complex_Euclidean_bridge_earned=True,sourced_potential_bound_earned=True,all_original_orbit_inputs_active_and_legal=True,
   sourcing_repeated_same_expression_not_independent_consistency=True,IEEE_per_operation_emulation=False,first_source_stopping_index_claimed=False,background_offset_kernel_instances=0),
  exact_Fraction_budgets=caps,Fraction_replay_rerun=True,no_floating_solver_rerun=True,prior_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,python_test_suite_rerun=False,
  paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,next_construction='Remaining background-offset kernel instances and positive-coupling seed returns',
  source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
 (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
 print('2994 cumulative standard-only closures;28 fresh statements;all four .3 sixty source tests;1455 fingerprints')
if __name__=='__main__':verify()
