"""Audit guarded native reflection, actual signed returns and inactive controls."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE='b012aa1'
PRIOR='results/ground_spectral_2026-10-04/verification.json'
PACKET='results/ground_reflection_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundNativeReflection','GroundOriginalReflection','GroundReflectionControls']
OLD_AUDIT='lean/manifests/axiom_audit_ground_spectral_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_reflection_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_reflection_2026-10-04.txt'
MUTABLE={'README.md','lean/README.md','lean/lakefile.lean','lean/manifests/check_axioms.lean','lean/manifests/coverage_table.md','math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
NPY='/mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin/python'
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
assert len(prior['source_sha256'])==1319
for p,h in prior['source_sha256'].items():
    if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
    s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
    new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==3 and len(new)==len(set(new))==25
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
assert len(old)==2678
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
    assert read('lean/manifests/check_ground_reflection_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2678-declaration raw prefix plus freshly audited 25-declaration suffix.\n'
        'Baseline: b012aa1; proof-source/toolchain identity checked by de_ground_reflection_verify.py.\n'
        'Full 2703-declaration command was not rerun in this packet.\n\n')
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


require('GroundNativeReflection.complexSourcePotential_neg','GroundState.complexSourcePotential b κ -z = GroundState.complexSourcePotential b κ z')
require('GroundNativeReflection.nativeUpdate_neg','hτ : 0 ≤ τ','ho : GroundNativeIteration.ActivePhase τ b κ z',
        'GroundNativeIteration.nativeUpdate τ b κ m -z = -GroundNativeIteration.nativeUpdate τ b κ m z')
require('GroundNativeReflection.nativeLegal_neg_iff','ho : GroundNativeIteration.ActivePhase τ b κ z','↔')
require('GroundNativeReflection.native_iterate_neg','N : ℕ','ha : ∀ j < N,','GroundNativeIteration.ActivePhase',
        'GroundNativeIteration.nativeUpdate τ b κ m ^[N] -z = - GroundNativeIteration.nativeUpdate τ b κ m ^[N] z')
require('GroundNativeReflection.native_negative_local_attraction','hd : ‖GroundNativeLocal.coordinateDerivative T b κ m u‖ < 1',
        'T.symm -u, 0','Tendsto','GroundState.realEmbed -u',
        '∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
require('GroundNativeReflection.native_negative_local_escape','heigen :','hgap :','∃ s > 0, ∀ ε > 0, ∃ z N,',
        'GroundState.complexNormSq z = 1','T.symm -u, 0','s / 2 ≤','∀ k ≤ N',
        'GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
require('GroundOriginalReflection.actual_negative_native_fixed','κ m : ℝ','hk : κ ∈ Set.Icc 0 30',
        'GroundOriginalContinuation.branch κ .1','GroundState.realEmbed -',
        'GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
require('GroundOriginalReflection.actual_negative_native_attraction','i : Fin 10','∃ r > 0, ∀ z : GroundState.ComplexField',
        'Metric.closedBall','-GroundOriginalCoordinates.root','Tendsto','GroundState.realEmbed',
        'GroundNativeControls.originalTolerance','∀ n','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
for n,i in [('twenty',10),('thirty',11)]:
    require('GroundOriginalReflection.actual_negative_'+n+'_native_escape','∃ s > 0, ∀ ε > 0, ∃ z N,',
            'GroundState.complexNormSq z = 1','-GroundOriginalCoordinates.root '+str(i),'< ε','s / 2 ≤',
            'GroundNativeControls.originalTolerance','∀ j ≤ N',
            'GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalReflection.actual_negative_'+n+'_native_escape'])
require('GroundReflectionControls.fallback_reference_unit','GroundState.complexNormSq GroundReflectionControls.fallbackReference = 1')
require('GroundReflectionControls.fallback_overlap_zero','GroundNativePhase.overlap','GroundState.realEmbed GroundState.uniform','= 0')
require('GroundReflectionControls.zero_native_candidate_uniform','GroundNativeIteration.nativeCandidate 0 0 z = GroundState.realEmbed GroundState.uniform')
require('GroundReflectionControls.fallback_native_outputs','GroundNativeIteration.nativeUpdate 0 0 0 1',
        'GroundReflectionControls.fallbackReference','-GroundReflectionControls.fallbackReference','GroundState.realEmbed GroundState.uniform','∧')
require('GroundReflectionControls.fallback_legal_inactive','GroundNativeIteration.NativeLegal 0 0 0 1',
        '¬GroundNativeIteration.ActivePhase 0 0 0')
require('GroundReflectionControls.unconditional_unit_reflection_rejected','¬∀ z : GroundState.ComplexField, GroundState.complexNormSq z = 1 →',
        'GroundNativeIteration.NativeLegal 0 0 0 1 z →','GroundNativeIteration.nativeUpdate 0 0 0 1 -z =')
for n in ['fallback_reference_unit','fallback_overlap_zero','fallback_native_outputs','fallback_legal_inactive','unconditional_unit_reflection_rejected']:
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundReflectionControls.'+n])
src=read(sourcepath('GroundNativeReflection'))
for t in ['nativePhase_ratio hτ','native_complex_local_attraction T hu hf','native_complex_local_escape T hu hf',
          'native_iterate_neg','nativeLegal_neg_iff','activePhase_neg_iff']:
    assert t in src,t
assert not re.search(r'\b(?:nativePhase|nativeUpdate)_neg_reference\b',read(sourcepath('GroundOriginalReflection')))
build=read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8847 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=json.loads(json.dumps(prior['mathlib']));libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
assert canonical(DATA)==baseline(DATA)
scout=json.loads(read(PACKET+'seed_scout.json'))
fresh=json.loads(subprocess.check_output([NPY,'scripts/de_ground_seed_scout.py'],cwd=ROOT))
assert scout==fresh and scout['numpy_version']=='1.26.4'
assert scout['kind']=='floating heuristic scout, not exact orbit/basin certificate'
assert scout['initial_data_sha256']==sha((ROOT/DATA).read_bytes())
assert scout['source_initialization_normalization_count']==2 and scout['source_eigensolver_sign_retained_in_updates']
assert scout['original_phase_bug_and_fallback_retained'] and not scout['formal_initial_seed_basin_claimed']
assert not scout['IEEE_per_operation_emulation_proved']
assert [float.fromhex(x['coupling_hex']) for x in scout['couplings']]==[0,.3,15,20,30]
for row in scout['couplings']:
    assert [x['iteration'] for x in row['checkpoints']]==[1,6,60,200,1000]
    assert row['observed_minimum_overlap']>1e-10 and row['observed_minimum_mixed_norm']>1e-10
for row in scout['couplings'][:3]:
    assert row['checkpoints'][-1]['distance_to_negative_previous_candidate']<1e-12
    assert row['checkpoints'][-1]['distance_to_positive_previous_candidate']>1.99
files=set(prior['source_sha256'])|{PRIOR,DATA,NEW_AUDIT,COMBINED,
    'lean/manifests/check_ground_reflection_axioms.lean','lean/manifests/check_ground_reflection_statements.lean',
    'math/GROUND_NATIVE_REFLECTION_2026-10-04.md','scripts/de_ground_seed_scout.py','scripts/de_ground_reflection_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name!='verification.json')
assert len(files)==1335,len(files)
v=dict(baseline_commit=BASE,scope='Active native reflection and concrete negative original branch representatives',
    axiom_audit=dict(declarations_cumulative=2703,declarations_preserved=2678,declarations_fresh=25,
        new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
        preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED,success=True),
    lean_build=dict(command='lake build',jobs=8847,success=True,warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
    statement_check=dict(declarations=25,success=True),mathlib=mathlib,actual_lean_version_checked=version,
    original_return=dict(negative_native_fixed_branch_interval='[0,30]',mixing_for_fixed_points='all real',
        negative_native_local_attraction_kernel_instances=10,negative_native_local_escape_kernel_instances=2,
        negative_escape_couplings=[20,30],actual_active_phase_oddness=True,global_threshold_map_oddness=False,
        finite_orbit_reflection_requires_activity_only_before_returned_iterate=True,
        active_and_normalization_guards_returned_through_all_claimed_steps=True,
        original_phase_bug_and_fallback_retained=True,arbitrary_complex_phase_equivalence_claimed=False,
        substantive_unit_legal_inactive_counterexample=True,concrete_escape_theorems_have_no_hard_premises=True,
        original_frozen_initialization_basin=False,finite_60_step_source_verdict=False,
        unbounded_amplitude_runaway=False,all_orbit_escape=False,all_coupling_interval_instability=False,
        all_30_original_sample_kernel_instances=False,background_offset_norm_instances=0),
    seed_scout=dict(kind='floating heuristic only',fresh_read_only_replay=True,numpy_version='1.26.4',
        negative_target_observed_at=[0,.3,15],exact_basin_certificate=False,exact_branch_root_distance=False,
        supplies_proof_input=False,IEEE_per_operation_emulation_proved=False),
    prior_numeric_evidence_immutable_from_baseline=PRIOR,old_numeric_replay_rerun=False,python_test_suite_rerun=False,
    paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,
    next_construction='Global native half-mixing at coupling0 with signed real overlap; exact frozen-seed return; positive-coupling basin/finite orbit and offset instances',
    source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2703 cumulative standard-only closures;25 fresh statements;negative fixed/attraction/escape returns;unit/legal inactive control;1335 fingerprints')
