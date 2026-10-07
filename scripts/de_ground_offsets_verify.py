"""Audit eighteen whole-background-box roots and actual source readouts."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='38165c2'
PRIOR='results/ground_positive_residual_2026-10-04/verification.json'
PACKET='results/ground_offsets_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundUncertainBackgroundTube']+[f'GroundOffsets.Point{i:03d}' for i in range(18)]+['GroundOriginalOffsets']
OLD_AUDIT='lean/manifests/axiom_audit_ground_positive_residual_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_offsets_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_offsets_2026-10-04.txt'
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
 assert len(MODS)==20 and len(ns)==len(set(ns))==71
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
 assert len(prior['source_sha256'])==1455
 for p,h in prior['source_sha256'].items():
  if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
 new=names();old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
 old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==2994
 imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
 assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
 assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
 for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
  assert read('lean/manifests/check_ground_offsets_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
 oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT);assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
 closures(oldraw,old);closures(newraw,new)
 header=('Cumulative audit: immutable 2994-declaration raw prefix plus freshly audited 71-declaration suffix.\n'
  'Baseline: 38165c2; proof-source/toolchain identity checked by de_ground_offsets_verify.py.\n'
  'Full 3065-declaration command was not rerun in this packet.\n\n')
 combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
 raw=read(PACKET+'theorem_statements.txt')
 assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
 assert not re.search(r'error:|warning:',raw)
 starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
 for i,m in enumerate(starts):decls[m.group().rstrip('.')]=flatten(raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)].replace(PREFIX,''))
 def require(n,*ts):
  for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
 require('GroundUncertainBackgroundTube.certified_actual_root','h : GroundUncertainBackgroundTube.Arithmetic','hb','GroundRootCertificate.residual','GroundState.IsGround','GroundSourceJacobian.groundMap')
 require('GroundOriginalOffsets.exact_root_spec','i : Fin 18','GroundRootCertificate.residual','GroundOriginalOffsets.b i','GroundState.IsGround','∀ x ∈ Metric.closedBall')
 require('GroundOriginalOffsets.rounded_ground_return','i : Fin 18','GroundBorder.groundPair','GroundOriginalOffsets.rounded_b i')
 require('GroundOriginalOffsets.exact_native_fixed','i : Fin 18','m : ℝ','GroundNativeIteration.nativeUpdate','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
 require('GroundOriginalOffsets.uniform_background_return','GroundOriginalOffsets.b i j = ↑GroundOriginalFirstTube.originalBackground j + ↑GroundOriginalOffsets.offsets i')
 require('GroundOriginalOffsets.model_root_proximity','≤ 2 * ↑GroundOriginalOffsets.certificates i .r')
 require('GroundOriginalOffsets.actual_exact_fields_separated','+ 3 / 10 <')
 require('GroundOriginalOffsets.actual_exact_densities_separated','Complex.normSq','+ 9 / 100 <')
 require('GroundOriginalOffsets.actual_rounded_densities_separated','Complex.normSq','+ 9 / 100 <')
 require('GroundOriginalOffsets.zero_exact_root_eq_original','GroundOriginalContinuation.branch','GroundOriginalSamples.couplings 2')
 require('GroundOriginalOffsets.zero_rounded_root_eq_original','GroundOriginalContinuation.branch','GroundOriginalSamples.couplings 2')
 require('GroundOriginalOffsets.whole_background_box_root','hβ','GroundRootCertificate.residual β','∃ x ∈ Metric.closedBall','GroundSourceJacobian.groundMap β')
 for n in ['actual_exact_fields_separated','actual_rounded_fields_separated','actual_exact_densities_separated','actual_rounded_densities_separated','zero_exact_root_eq_original','zero_rounded_root_eq_original']:
  assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalOffsets.'+n])
 from de_ground_offsets_generate import proposals,render
 w=json.loads(read(PACKET+'witnesses.json'));assert proposals()==w
 generated=render(w);assert len(generated)==18
 for p,s in generated.items():assert read(p)==s,p
 assert all(F(p['r'])==F(1,2**32) and F(p['q'])==F(1,2**20) for p in w['points'])
 maxdelta=max(abs(F(a)-F(b)) for p in w['points'] for a,b in zip(p['exact_background'],p['rounded_background']))
 assert maxdelta<F(1,2500000000000000)
 generic=read(sourcepath('GroundUncertainBackgroundTube'))
 for t in ['box_sound B a c z r hb hk hx','defect_norm_bound','corrected_residual_norm_bound','field_positive :=','(tube h hb).positive_root_exists hk']:
  assert t in generic,t
 family=read(sourcepath('GroundOriginalOffsets'))
 for i in range(18):assert f'GroundOffsets.Point{i:03d}.arithmetic' in family
 for t in ['positive_ground_unique','ground_energy hg','root_spec (exact_interval i)','root_spec (rounded_interval i)','Rat.cast_lt.mpr separation_arithmetic','Complex.normSq_ofReal','zero_preconditioner_rejected','zero_offset_arithmetic.2.2.2.1','sample_ground_return 2','Point002']:
  assert t in family,t
 build=read(PACKET+'lean_build.txt');assert 'Build completed successfully (8912 jobs).' in build
 assert not re.search(r'error:|warning:|build failed',build)
 leaves=read(PACKET+'leaf_builds.txt');assert leaves.count('Build completed successfully (8056 jobs).')==18
 for i in range(18):
  assert f'Fresh leaf command: lake build {PREFIX}GroundOffsets.Point{i:03d}' in leaves
  r=read(PACKET+f'point{i:03d}_build.txt');assert 'Built '+PREFIX+f'GroundOffsets.Point{i:03d}' in r
  assert not re.search(r'error:|warning:|build failed',r)
 for p in ['generic_build.txt','family_build.txt']:
  r=read(PACKET+p);assert 'Build completed successfully' in r and not re.search(r'error:|warning:|build failed',r)
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip();assert version==prior['actual_lean_version_checked']
 mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
 for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
 files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,'lean/manifests/check_ground_offsets_axioms.lean','lean/manifests/check_ground_offsets_statements.lean','math/GROUND_OFFSETS_2026-10-04.md','scripts/de_ground_offsets_generate.py','scripts/de_ground_offsets_verify.py'}
 files.update(sourcepath(m) for m in MODS)
 files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
 assert len(files)==1508,len(files)
 v=dict(baseline_commit=BASE,scope='All18 original offset roots, both exact and rounded inputs and whole background boxes',
  axiom_audit=dict(declarations_cumulative=3065,declarations_preserved=2994,declarations_fresh=71,new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
  lean_build=dict(command='lake build',jobs=8912,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
  statement_check=dict(declarations=71,success=True),fresh_leaf_compilation=dict(modules=18,receipt=PACKET+'leaf_builds.txt',success=True),mathlib=mathlib,actual_lean_version_checked=version,
  original_return=dict(coupling=w['points'][0]['coupling'],background_offset_kernel_instances=18,exact_uniform_shift_and_saved_rounded_models_distinguished=True,whole_background_boxes_earned=True,
   max_input_discrepancy=str(maxdelta),radius='1/2^32',Newton_defect_rate='1/2^20',positive_unit_actual_sourced_grounds=True,local_root_uniqueness=True,global_nonlinear_uniqueness_claimed=False,
   actual_ground_pair_and_energy_earned=True,native_real_fixed_for_any_real_mixing=True,original_threshold_guards_earned=True,model_root_Point_sup_distance_bound='2/2^32',
   endpoint_field_separation='greater than3/10',endpoint_actual_density_separation='greater than9/100',separation_exact_and_rounded=True,zero_offset_actual_branch_identity_both_models=True,
   local_native_attraction_earned=False,all_offset_frozen_seed_sixty_source_tests=False,IEEE_per_operation_emulation=False,physical_Lambda_bridge=False,control='zero Newton preconditioner rejected'),
  Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,no_floating_solver_rerun=True,saved_matrices_proposal_role_only=True,prior_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,python_test_suite_rerun=False,
  paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,next_construction='Actual native local stability at18 offsets and remaining frozen-seed returns',
  source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
 (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
 print('3065 cumulative standard-only closures;71 fresh statements;18 background boxes,both input models;1508 fingerprints')
if __name__=='__main__':verify()
