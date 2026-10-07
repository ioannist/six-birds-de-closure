"""Audit exact global native zero coupling and closed original-seed return."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='72946bc'
PRIOR='results/ground_reflection_2026-10-04/verification.json'
PACKET='results/ground_zero_native_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundNativeZeroGeometry','GroundNativeZeroScalar','GroundNativeZeroOrbit','GroundOriginalSeed']
OLD_AUDIT='lean/manifests/axiom_audit_ground_reflection_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_zero_native_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_zero_native_2026-10-04.txt'
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
assert len(prior['source_sha256'])==1335
for p,h in prior['source_sha256'].items():
    if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
    s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
    new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==4 and len(new)==len(set(new))==44
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
assert len(old)==2703
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
    assert read('lean/manifests/check_ground_zero_native_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2703-declaration raw prefix plus freshly audited 44-declaration suffix.\n'
        'Baseline: 72946bc; proof-source/toolchain identity checked by de_ground_zero_native_verify.py.\n'
        'Full 2747-declaration command was not rerun in this packet.\n\n')
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


require('GroundNativeZeroGeometry.decomposition','GroundState.normSq g = 1','GroundNativePhase.stateNormSq x -',
        'GroundNativeZeroGeometry.realPart g x ^ 2','GroundNativeZeroGeometry.imagPart g x ^ 2')
require('GroundNativeZeroGeometry.mixed_norm','GroundNativePhase.stateNormSq x = 1','hr : GroundNativeZeroGeometry.radius g x ≠ 0',
        'GroundNativePhase.stateNormSq GroundNativeZeroGeometry.mix g x =')
require('GroundNativeZeroGeometry.native_return','hτ : 0 ≤ τ','ha : τ < GroundNativeZeroGeometry.radius',
        'GroundNativeIteration.nativeUpdate τ b 0 1 / 2')
require('GroundNativeZeroScalar.mixed_bounds','ha : 0 < a','har : a ≤ r','hr1 : r ≤ 1','0 < d ∧ a ≤ √d ∧ √d ≤ 1')
require('GroundNativeZeroScalar.gain_numerator','hr0 : 0 ≤ r','hr1 : r ≤ 1','has : a ^ 2 ≤ r ^ 2','1 - a ^ 2 ≤')
require('GroundNativeZeroScalar.defect_contraction','ha : 0 < a','hc : c =','1 - c ^ 2 ≤ 1 - a ^ 2 / 4 * 1 - a ^ 2')
require('GroundNativeZeroOrbit.orbit_defect_bound','0 ≤ 1 -','≤ GroundNativeZeroOrbit.rate g x ^ n *')
require('GroundNativeZeroOrbit.orbit_distance_bound','‖','≤ √ 2 *','GroundNativeZeroOrbit.rate g x ^ n')
require('GroundNativeZeroOrbit.orbit_native_return','n : ℕ','GroundNativeIteration.nativeUpdate τ b 0 1 / 2 ^[n]')
for n,sign in [('actual_positive_zero_convergence',''),('actual_negative_zero_convergence','-')]:
    require('GroundNativeZeroOrbit.'+n,'b : GroundState.Field','hz : GroundState.complexNormSq z = 1','hτ : 0 ≤ τ',
            'ha : τ < '+sign+'GroundNativeZeroGeometry.realPart','Tendsto','GroundNativeIteration.nativeUpdate τ b 0 1 / 2',
            'GroundState.realEmbed '+sign+'GroundState.positiveGround b','∀ n',
            'GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
require('GroundOriginalSeed.seed_arithmetic','1 / 2 < GroundOriginalSeed.rawNorm','101 / 100','GroundOriginalSeed.dotBox.hi < -101 / 500')
require('GroundOriginalSeed.initial_native_normalization','GroundOriginalSeed.initial = GroundNativeIteration.complexNormalize',
        'GroundNativeIteration.complexNormalize','GroundNativePhase.pack GroundOriginalSeed.rawState')
require('GroundOriginalSeed.initialization_guards','GroundNativeControls.originalTolerance < √',
        'GroundState.complexNormSq GroundNativePhase.pack GroundOriginalSeed.rawState',
        'GroundNativeIteration.complexNormalize','∧')
require('GroundOriginalSeed.double_normalization','GroundOriginalSeed.initial = GroundNativePhase.pack','GroundOriginalSeed.rawState')
require('GroundOriginalSeed.initial_unit','GroundState.complexNormSq GroundOriginalSeed.initial = 1')
require('GroundOriginalSeed.ground_identity','GroundState.positiveGround','GroundOriginalContinuation.branch 0 .1')
require('GroundOriginalSeed.initial_overlap_negative','GroundNativeZeroGeometry.realPart','GroundNativePhase.unpack GroundOriginalSeed.initial','< -1 / 5')
require('GroundOriginalSeed.positive_overlap_rejected','¬0 < GroundNativeZeroGeometry.realPart','GroundOriginalSeed.initial')
require('GroundOriginalSeed.actual_seed_zero_convergence','Tendsto','GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance',
        'GroundOriginalSeed.initial','GroundOriginalContinuation.branch 0 .1','GroundState.realEmbed -',
        '∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
for n in ['seed_arithmetic','initial_native_normalization','initialization_guards','double_normalization','initial_unit','ground_identity',
          'initial_overlap_negative','positive_overlap_rejected','actual_seed_zero_convergence']:
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalSeed.'+n]),n
src=read(sourcepath('GroundNativeZeroOrbit'))
for t in ['tendsto_pow_atTop_nhds_zero_of_lt_one','orbit_native_guards','orbit_native_return',
          'native_iterate_neg','rate_bounds','state_norm_bound']:
    assert t in src,t
for t in ['gain_numerator','mixed_bounds','coefficient_square','mul_nonneg','nlinarith']:
    assert t in read(sourcepath('GroundNativeZeroScalar'))
seed=read(sourcepath('GroundOriginalSeed'))
assert seed.count('decide +kernel')==3
for t in ['Expr.enclose_sound dotExpr hbox','box_sound originalBackground','ground_identity',
          'dot_expression_return','initial_overlap_negative','actual_negative_zero_convergence']:
    assert t in seed,t
import de_ground_seed_generate as gen
assert seed==gen.render()
data=json.loads(read(DATA));assert len(data['fields'][0]['psi_re'])==len(data['fields'][0]['psi_im'])==8
beta_source=read(sourcepath('GroundOriginalFirstTube'))
beta_block=re.search(r'def originalBackground : Fin 8 → ℚ := !\[([^\]]+)\]',beta_source).group(1)
beta=[F(int(n),int(d)) for n,d in re.findall(r'\((-?\d+)/(\d+)\)',beta_block)]
assert len(beta)==8 and beta==[F.from_float(x) for x in data['potential']]
coefficients=[F.from_float(x) for k in ['psi_re','psi_im'] for x in data['fields'][0][k]]
for x in coefficients:assert '('+str(x.numerator)+'/'+str(x.denominator)+')' in seed
q=sum(x*x for x in coefficients)
assert F(1,2)<q<=F(101,100)**2
build=read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8851 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=json.loads(json.dumps(prior['mathlib']));libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
    'lean/manifests/check_ground_zero_native_axioms.lean','lean/manifests/check_ground_zero_native_statements.lean',
    'math/GROUND_NATIVE_ZERO_SEED_2026-10-04.md','scripts/de_ground_seed_generate.py','scripts/de_ground_zero_native_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name!='verification.json')
assert len(files)==1350,len(files)
v=dict(baseline_commit=BASE,scope='Global original native complex zero-coupling convergence and closed original-seed return',
    axiom_audit=dict(declarations_cumulative=2747,declarations_preserved=2703,declarations_fresh=44,
        new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
        preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED,success=True),
    lean_build=dict(command='lake build',jobs=8851,success=True,warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
    statement_check=dict(declarations=44,success=True),mathlib=mathlib,actual_lean_version_checked=version,
    original_return=dict(global_complex_zero_coupling_convergence=True,all_real_backgrounds=True,mixing='1/2',
        signed_real_overlap_must_exceed_nonnegative_source_threshold=True,geometric_rate='1-a0^2/4',
        active_and_normalization_guards_at_every_iterate=True,original_phase_bug_and_fallback_retained=True,
        original_raw_seed_coefficients_kernel_reified=16,original_normalization_count_represented=2,
        exact_second_normalization_idempotence=True,initialization_normalization_threshold_guards_kernel=True,IEEE_second_normalization_bitwise_identity_claimed=False,
        closed_rational_seed_kernel_comparisons=3,actual_branch_root_box_used_whole=True,
        original_seed_signed_real_overlap_bound='below -1/5',original_seed_zero_coupling_basin_return=True,
        original_seed_convergence_target='negative actual branch ground at0',
        concrete_seed_convergence_has_no_hard_premises=True,original_seed_positive_coupling_basin_return=False,
        finite_60_step_source_verdict=False,IEEE_per_operation_emulation=False,JSON_parsing_kernel_proved=False,
        all_complex_initial_fields_converge=False,all_30_original_sample_kernel_instances=False,
        background_offset_norm_instances=0,substantive_false_target_control='actual_seed_positive_overlap_rejected'),
    rational_seed_data_regenerated_read_only=True,prior_evidence_immutable_from_baseline=PRIOR,
    old_numeric_replay_rerun=False,floating_scout_rerun=False,python_test_suite_rerun=False,
    paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,
    next_construction='Sharper finite-step zero-coupling return; positive-coupling original-seed basin/orbit estimates;18 offset kernel instances',
    source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2747 cumulative standard-only closures;44 fresh statements;global native0 convergence;closed original seed to negative ground;1350 fingerprints')
