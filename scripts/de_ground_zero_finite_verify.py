"""Audit exact finite native zero-coupling original-seed distance."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='f9d17d2'
PRIOR='results/ground_zero_native_2026-10-04/verification.json'
PACKET='results/ground_zero_finite_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundNativeZeroFinite','GroundOriginalSeedFinite']
OLD_AUDIT='lean/manifests/axiom_audit_ground_zero_native_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_zero_finite_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_zero_finite_2026-10-04.txt'
MUTABLE={'README.md','lean/README.md','lean/lakefile.lean','lean/manifests/check_axioms.lean','lean/manifests/coverage_table.md','math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
DATA='external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step24_derived_physical_audits_artifacts/toy_field_samples_step24.json'

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


prior=json.loads(read(PRIOR))
assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
assert len(prior['source_sha256'])==1350
for p,h in prior['source_sha256'].items():
    if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
    s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
    new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==2 and len(new)==len(set(new))==17
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
assert len(old)==2747
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
    assert read('lean/manifests/check_ground_zero_finite_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2747-declaration raw prefix plus freshly audited 17-declaration suffix.\n'
        'Baseline: f9d17d2; proof-source/toolchain identity checked by de_ground_zero_finite_verify.py.\n'
        'Full 2764-declaration command was not rerun in this packet.\n\n')
combined=header+oldraw+'\n'+newraw
closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
raw=read(PACKET+'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
assert not re.search(r'error:|warning:',raw)
starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
for i,m in enumerate(starts):
    t=raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)]
    decls[m.group().rstrip('.')]=flatten(t.replace(PREFIX,'').replace('⇑',''))


def require(n,*ts):
    for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])


require('GroundNativeZeroFinite.half_hinge','ha : 1 / 2 ≤ a','har : a ≤ r','hr1 : r ≤ 1','0 ≤')
require('GroundNativeZeroFinite.half_contraction','ha : 1 / 2 ≤ a','hd : d =','hc : c =','1 - c ^ 2 ≤ 1 / 2 * 1 - a ^ 2')
require('GroundNativeZeroFinite.orbit_half_distance_sq','ha : 1 / 2 ≤','GroundNativePhase.stateNormSq','≤ 2 * 1 / 2 ^ n')
require('GroundNativeZeroFinite.first_overlap_half','ha : 1 / 5 <','hr : GroundNativeZeroGeometry.radius g x < 21 / 100','1 / 2 <')
require('GroundNativeZeroFinite.radius_normalize_sq','hx : 0 < GroundNativePhase.stateNormSq x',
        'GroundNativeIteration.normalizeState x','GroundNativeZeroGeometry.radius g x ^ 2')
require('GroundOriginalSeedFinite.finite_seed_arithmetic','99 / 100','GroundOriginalSeed.rawNorm','GroundOriginalSeedFinite.radiusBox.hi <','207 / 1000')
require('GroundOriginalSeedFinite.initial_radius_bound','GroundNativePhase.unpack GroundOriginalSeed.initial','< 21 / 100')
require('GroundOriginalSeedFinite.reflected_conditions','GroundNativePhase.stateNormSq GroundOriginalSeedFinite.reflected = 1','1 / 5 <','< 21 / 100')
require('GroundOriginalSeedFinite.initial_half_region_rejected','¬1 / 2 ≤','GroundOriginalSeedFinite.reflected')
require('GroundOriginalSeedFinite.first_reflected_overlap','GroundNativePhase.stateNormSq','1 / 2 <','GroundNativeZeroGeometry.step')
for n,power,bound in [('actual_seed_distance_sq','n + 1','2 * 1 / 2 ^ n'),
                      ('actual_seed_sixty_distance_sq','60','1 / 500000000 ^ 2'),
                      ('actual_seed_fifty_nine_distance_sq','59','3 / 1000000000 ^ 2')]:
    require('GroundOriginalSeedFinite.'+n,'GroundState.complexNormSq','GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance',
            'GroundOriginalFirstTube.originalBackground','0 1 / 2 ^['+power+'] GroundOriginalSeed.initial',
            'GroundState.realEmbed - GroundOriginalContinuation.branch 0 .1',bound)
for n in [x.split('.')[-1] for x in new if '.GroundOriginalSeedFinite.' in x]:
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalSeedFinite.'+n]),n
scalar=read(sourcepath('GroundNativeZeroFinite'))
for t in ['nonneg_of_mul_nonneg_right','by_cases he : r = 1/2','orbit_unit_overlap',
          'coefficient_square','distance_identity','radius_normalize_sq','mul_nonneg']:
    assert t in scalar,t
seed=read(sourcepath('GroundOriginalSeedFinite'))
assert seed.count('decide +kernel')==1 and 'constructor <;> decide +kernel' in seed
for t in ['Expr.enclose_sound radiusExpr hbox','box_sound originalBackground','ground_identity',
          'imag_expression_return','radius_normalize_sq','initial_overlap_negative',
          'first_overlap_half','native_iterate_neg','actual_seed_zero_convergence.2','packCLE.map_sub']:
    assert t in seed,t
import de_ground_seed_generate as gen
assert read(sourcepath('GroundOriginalSeed'))==gen.render()
build=read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8853 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=json.loads(json.dumps(prior['mathlib']));libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
    'lean/manifests/check_ground_zero_finite_axioms.lean','lean/manifests/check_ground_zero_finite_statements.lean',
    'math/GROUND_NATIVE_ZERO_FINITE_2026-10-04.md','scripts/de_ground_zero_finite_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name!='verification.json')
assert len(files)==1362,len(files)
v=dict(baseline_commit=BASE,scope='Finite exact original native zero-coupling seed distance',
    axiom_audit=dict(declarations_cumulative=2764,declarations_preserved=2747,declarations_fresh=17,
        new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
        preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED,success=True),
    lean_build=dict(command='lake build',jobs=8853,success=True,warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
    statement_check=dict(declarations=17,success=True),mathlib=mathlib,actual_lean_version_checked=version,
    original_return=dict(mixing='1/2',coupling=0,original_phase_bug_and_fallback_retained=True,
        fast_region='positive real overlap >= 1/2',squared_defect_rate='1/2',
        raw_norm_lower_bound='(99/100)^2',raw_radius_squared_upper_bound='(207/1000)^2',
        original_normalized_radius_upper_bound='21/100',actual_root_box_used_whole=True,
        rational_kernel_seed_comparisons=2,one_step_fast_region_entry_earned=True,
        initial_fast_region_membership_rejected=True,
        original_seed_both_exact_initial_normalizations_preserved=True,
        prior_global_native_guards_preserved=True,
        actual_native_sixty_squared_Euclidean_distance_bound='strictly below (1/500000000)^2',
        actual_native_fifty_nine_squared_Euclidean_distance_bound='strictly below (3/1000000000)^2',
        target='negative actual original branch ground at0',
        concrete_seed_endpoint_has_no_hard_premises=True,
        source_four_residual_convergence_verdict=False,IEEE_per_operation_emulation=False,
        original_seed_positive_coupling_basin_return=False,background_offset_kernel_instances=0),
    original_seed_regenerated_read_only=True,prior_evidence_immutable_from_baseline=PRIOR,
    old_numeric_replay_rerun=False,floating_scout_rerun=False,python_test_suite_rerun=False,
    paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,
    next_construction='Four exact source residual returns; positive-coupling original-seed basins;18 offset kernel instances',
    source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2764 cumulative standard-only closures;17 fresh statements;exact original seed finite0 distance at59/60;1362 fingerprints')
