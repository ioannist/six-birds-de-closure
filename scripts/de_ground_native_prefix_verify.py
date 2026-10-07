"""Audit the exact 16-step original-seed native prefix at coupling .3."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE='cf950e6'
PRIOR='results/ground_source_residual_2026-10-04/verification.json'
PACKET='results/ground_native_prefix_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundBackgroundKernel','GroundIntervalReciprocal','GroundNativeBox','GroundNativePrefixInitial']+[f'GroundNativePrefix.Step{n:03d}' for n in range(16)]+['GroundOriginalNativePrefix']
OLD_AUDIT='lean/manifests/axiom_audit_ground_source_residual_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_native_prefix_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_native_prefix_2026-10-04.txt'
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

def closures(raw,names):
 es=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
 assert [n for n,a in es]==names
 assert not re.search(r'error:|warning:|sorryAx',raw)
 for n,a in es:assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},n

def flatten(t):
 t=' '.join(t.replace('(',' ').replace(')',' ').split())
 t=re.sub(r'\s+,',',',t)
 return t.replace('| ','|').replace(' |','|').replace('‖ ','‖').replace(' ‖','‖').replace('↑ ','↑')

prior=json.loads(read(PRIOR));assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
assert len(prior['source_sha256'])==1377
for p,h in prior['source_sha256'].items():
 if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
 s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
 new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==21 and len(new)==len(set(new))==65
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==2815
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
 assert read('lean/manifests/check_ground_native_prefix_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2815-declaration raw prefix plus freshly audited 65-declaration suffix.\n'
 'Baseline: cf950e6; proof-source/toolchain identity checked by de_ground_native_prefix_verify.py.\n'
 'Full 2880-declaration command was not rerun in this packet.\n\n')
combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
raw=read(PACKET+'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
assert not re.search(r'error:|warning:',raw)
starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
for i,m in enumerate(starts):
 t=raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)]
 decls[m.group().rstrip('.')]=flatten(t.replace(PREFIX,'').replace('⇑',''))
def require(n,*ts):
 for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
require('GroundBackgroundKernel.actual_ground_pair_enclosed','GroundBorder.groundPair b','Metric.closedBall','B i .Contains b i')
require('GroundIntervalReciprocal.inverse_sqrt_sound','0 < n','K.Contains √n ⁻¹')
require('GroundNativeBox.arithmetic_native_step','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal','D.Contains','GroundNativeIteration.nativeUpdate')
require('GroundNativePrefixInitial.original_seed_enclosed','GroundOriginalSeed.initial')
require('GroundOriginalNativePrefix.native_prefix_enclosed','i : Fin 17','GroundOriginalNativePrefix.boxes i','GroundOriginalNativePrefix.orbit ↑i')
require('GroundOriginalNativePrefix.native_prefix_guards','i : Fin 16','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
require('GroundOriginalNativePrefix.native_prefix_unit','i : Fin 17','GroundState.complexNormSq','= 1')
require('GroundOriginalNativePrefix.actual_seed_sixteen_near_negative_ground','GroundOriginalNativePrefix.orbit 16','GroundOriginalContinuation.branch','< 1 / 100000')
assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalNativePrefix.actual_seed_sixteen_near_negative_ground'])
from de_ground_native_prefix_generate import replay
from de_ground_native_prefix_render import render
w=json.loads(read(PACKET+'witnesses.json'));assert len(w['steps'])==16 and replay(w)
generated=render(w);assert len(generated)==18
for p,s in generated.items():assert read(p)==s,p
bg=read(sourcepath('GroundBackgroundKernel'))
for t in ['positive_root_exists','zero_coupling_groundMap','ground_energy hg','groundPair b = x','box_sound B z r hb hx','corrected_residual_norm_bound','defect_norm_bound']:
 assert t in bg,t
box=read(sourcepath('GroundNativeBox'))
for t in ['sourceBox_sound β κ hx','actual_selected_enclosed h.ground hs','inverse_sqrt_sound h.overlap_inverse hr','inverse_sqrt_sound h.mixed_inverse hn','threshold_guard hr hτ hb','threshold_guard hn hτ hnb','fullMap_native_return','(dotBox G B.I).neg.mul K']:
 assert t in box,t
family=read(sourcepath('GroundOriginalNativePrefix'))
for n in range(16):assert 'GroundNativePrefix.Step'+f'{n:03d}.arithmetic' in family
for t in ['Fin.induction','seams j','original_seed_enclosed','branch_in_sample_ball 2','distance_arithmetic i','zero_selector_preconditioner_rejected']:
 assert t in family,t
assert 'double_normalization' in read(sourcepath('GroundNativePrefixInitial'))
build=read(PACKET+'lean_build.txt');assert 'Build completed successfully (8879 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
leaves=read(PACKET+'leaf_builds.txt')
assert not re.search(r'error:|warning:|build failed',leaves)
for n in range(16):assert 'Fresh leaf command: lake build '+PREFIX+f'GroundNativePrefix.Step{n:03d}' in leaves
assert leaves.count('Build completed successfully (8660 jobs).')==16
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
 'lean/manifests/check_ground_native_prefix_axioms.lean','lean/manifests/check_ground_native_prefix_statements.lean',
 'math/GROUND_NATIVE_PREFIX_2026-10-04.md','scripts/de_ground_native_prefix_generate.py',
 'scripts/de_ground_native_prefix_render.py','scripts/de_ground_native_prefix_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
assert len(files)==1412,len(files)
v=dict(baseline_commit=BASE,scope='Exact 16-step original-seed native prefix at original coupling .3',
 axiom_audit=dict(declarations_cumulative=2880,declarations_preserved=2815,declarations_fresh=65,
 new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
 preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
 lean_build=dict(command='lake build',jobs=8879,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
 fresh_leaf_compilation=dict(modules=16,success=True,receipt=PACKET+'leaf_builds.txt'),
 statement_check=dict(declarations=65,success=True),mathlib=mathlib,actual_lean_version_checked=version,
 original_return=dict(coupling=w['coupling'],mixing='1/2',finite_updates=16,
 exact_native_orbit_original_seed=True,unit_states=list(range(17)),active_legal_inputs=list(range(16)),
 original_both_initial_normalizations_preserved=True,whole_sourced_potential_boxes=True,
 actual_selected_ground_not_midpoint=True,both_inverse_square_roots_and_guards_earned=True,
 source_conjugated_phase_retained=True,fully_populated_prefix_seams=True,
 endpoint_target='negative actual continuation branch ground',State_sup_coordinate_distance='strictly below1/100000',
 Euclidean_distance_1e_5_claimed=False,explicit_attracting_radius_earned=False,basin_entry_claimed=False,
 positive_coupling_infinite_convergence=False,positive_coupling_sixty_source_tests=False,
 IEEE_per_operation_emulation=False,background_offset_kernel_instances=0,
 controls=['zero reciprocal interval rejected','zero ground preconditioner rejected']),
 Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,NumPy_proposal_role_only=True,
 prior_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,floating_scout_rerun=False,python_test_suite_rerun=False,
 paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,
 next_construction='Explicit quantitative positive-coupling attracting neighborhood and prefix basin return',
 source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2880 cumulative standard-only closures;65 fresh statements;16 original native steps at.3;1412 fingerprints')
