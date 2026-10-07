"""Audit closed signs, full expanding modes and guarded nonlinear native escape."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
from fractions import Fraction as F

ROOT=Path(__file__).resolve().parents[1]
BASE='ef2d81f'
PRIOR='results/ground_coordinates_2026-10-04/verification.json'
PACKET='results/ground_spectral_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
GENERIC=['GroundDeterminantDefect','GroundTriangularSign','GroundRealModeNormalize',
         'GroundTriangularArithmetic','GroundSpectralEnclosure']
MODS=GENERIC+[f'GroundSpectralTests.Test{i:03d}' for i in range(7)]+['GroundOriginalSpectrum','GroundSpectralControls']
ROOTS=GENERIC+['GroundOriginalSpectrum','GroundSpectralControls']
OLD_AUDIT='lean/manifests/axiom_audit_ground_coordinates_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_spectral_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_spectral_2026-10-04.txt'
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


prior=json.loads(read(PRIOR))
assert (ROOT/PRIOR).read_bytes()==baseline(PRIOR)
assert len(prior['source_sha256'])==1290
for p,h in prior['source_sha256'].items():
    if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
    s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
    new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==14 and len(new)==len(set(new))==49
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
assert len(old)==2629
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in ROOTS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
    assert read('lean/manifests/check_ground_spectral_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2629-declaration raw prefix plus freshly audited 49-declaration suffix.\n'
        'Baseline: ef2d81f; proof-source/toolchain identity checked by de_ground_spectral_verify.py.\n'
        'Full 2678-declaration command was not rerun in this packet.\n\n')
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


for i,k in enumerate([12,13,10,10,10,11,11]):
    p=f'GroundSpectralTests.Test{i:03d}'
    require(p+'.factor_arithmetic','GroundTriangularArithmetic.Arithmetic',p+'.CI',p+'.LI',p+'.UI',p+'.sign')
    require(p+'.box_return',p+'.B = GroundOriginalResponses.enclosures '+str(k))
    require(p+'.defect_arithmetic','GroundSpectralEnclosure.Arithmetic',p+'.C','GroundSpectralEnclosure.shifted','1 / 1000')
    for n in ['factor_arithmetic','box_return','defect_arithmetic']:
        assert '→' not in decls[PREFIX+p+'.'+n]
require('GroundDeterminantDefect.small_norm_det_positive','hn : ‖L‖ < 1','0 <','Matrix.det')
require('GroundTriangularArithmetic.scaled_product','GroundTriangularArithmetic.Arithmetic',
        'GroundTriangularArithmetic.scaled L dL * GroundTriangularArithmetic.scaled U dU =')
require('GroundSpectralEnclosure.actual_shifted_sign','GroundSpectralEnclosure.Arithmetic','hB : ∀','0 <','GroundMatrixCoordinates.entries L')
require('GroundRealModeNormalize.bracket_full_mode','hs :','∃ ell ∈ Set.Ioo a c','∃ v, ‖v‖ = 1',
        'GroundNativeLocal.coordinateDerivative','ell • v')
require('GroundOriginalSpectrum.actual_signed_test','i : Fin 7','0 <',
        'GroundOriginalSpectrum.shiftedDet GroundOriginalSpectrum.tests i .sample')
require('GroundOriginalSpectrum.concrete_signs','0 < GroundOriginalSpectrum.shiftedDet 12 -1',
        'GroundOriginalSpectrum.shiftedDet 13 -1 < 0','-36 / 25','-71 / 50','-249 / 100','-247 / 100')
require('GroundOriginalSpectrum.crossing_signs','GroundOriginalSpectrum.contactDet 79 / 5',
        'GroundOriginalSpectrum.contactDet 159 / 10','GroundOriginalSpectrum.contactDet 20')
require('GroundOriginalSpectrum.actual_two_contacts','∃ k₁ ∈ Set.Ioo 79 / 5 159 / 10',
        '∃ k₂ ∈ Set.Ioo 159 / 10 20','k₁ < k₂','GroundParameterPatchReturn.ModeContact',
        'GroundOriginalContinuation.branch','GroundNativeControls.originalTolerance')
for n,k,i,left,right in [('twenty',20,10,'36 / 25','71 / 50'),('thirty',30,11,'249 / 100','247 / 100')]:
    require('GroundOriginalSpectrum.actual_'+n+'_mode','∃ ell ∈ Set.Ioo -'+left+' -'+right,
            '∃ v, ‖v‖ = 1','GroundOriginalCoordinates.fullBasis '+str(i),
            'GroundNativeLocal.coordinateDerivative','ell • v')
    require('GroundOriginalSpectrum.actual_'+n+'_native_escape','∃ s > 0, ∀ ε > 0, ∃ z N,',
            'GroundState.complexNormSq z = 1','< ε','s / 2 ≤',
            'GroundNativeIteration.nativeUpdate','GroundNativeControls.originalTolerance',
            '∀ j ≤ N','GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
for n in ['concrete_signs','crossing_signs','actual_two_contacts','actual_twenty_mode',
          'actual_thirty_mode','actual_twenty_native_escape','actual_thirty_native_escape']:
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalSpectrum.'+n])
require('GroundSpectralControls.zero_preconditioner_rejected','¬GroundSpectralEnclosure.Arithmetic 0')
require('GroundSpectralControls.reversed_sign_rejected','¬GroundTriangularArithmetic.Arithmetic','-GroundSpectralTests.Test003.sign')
src=flatten(read(sourcepath('GroundTriangularArithmetic')))
for t in ['c_pos : 0 < dC','l_pos : 0 < dL','u_pos : 0 < dU',
          'product : dC • (L * U) = (dL * dU) • C','sign : 0 < s * (∏ i, U i i)']:
    assert flatten(t) in src,t
for t in ['actual_half_entries','factor_arithmetic','defect_arithmetic','two_distinct_contacts',
          'bracket_full_mode','native_complex_local_escape','sample_ground_return']:
    assert t in read(sourcepath('GroundOriginalSpectrum')),t
import de_ground_spectral_generate as sg
import de_ground_spectral_family as sf
ds=sg.proposals();assert len(ds)==7
assert sg.TESTS==[(12,F(-1),1),(13,F(-1),-1),(10,F(-1),1),
                 (10,F(-36,25),1),(10,F(-71,50),-1),(11,F(-249,100),1),(11,F(-247,100),-1)]
for i,d in enumerate(ds):
    s=read(sourcepath(f'GroundSpectralTests.Test{i:03d}'))
    assert s==sg.render(i,d)
    assert s.count('decide +kernel')==12 if d['sample']>=12 else s.count('decide +kernel')==11
    assert 0<=d['defect_bound']<F(1,1000)
assert read(sourcepath('GroundOriginalSpectrum'))==sf.render()
status=json.loads(read(PACKET+'leaf_build_status.json'))
assert status['total_targets']==status['successful_targets']==7 and status['batch_size']==2 and status['all_success']
assert len(status['terminal_batches'])==4
for i,row in enumerate(status['terminal_batches']):
    targets=[PREFIX+f'GroundSpectralTests.Test{j:03d}' for j in range(2*i,min(2*i+2,7))]
    assert row['targets']==targets and row['command']==['lake','build',*targets] and row['exit_code']==0
log=read(PACKET+'leaf_build.txt')
assert log.count('Batch targets: ')==log.count('Terminal exit: 0')==4
assert log.count('Build completed successfully')==4
assert not re.search(r'error:|warning:|build failed',log)
build=read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8844 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=json.loads(json.dumps(prior['mathlib']));libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
for p in ['Mathlib/LinearAlgebra/Matrix/Block.lean']:
    assert (libroot/p).read_bytes()==subprocess.check_output(['git','show','HEAD:'+p],cwd=libroot),p
    mathlib['direct_proof_source_sha256'][p]=sha((libroot/p).read_bytes())
files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
    'lean/manifests/check_ground_spectral_axioms.lean','lean/manifests/check_ground_spectral_statements.lean',
    'math/GROUND_KERNEL_SPECTRUM_2026-10-04.md','scripts/de_ground_spectral_generate.py',
    'scripts/de_ground_spectral_family.py','scripts/de_ground_spectral_build.py','scripts/de_ground_spectral_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name!='verification.json')
assert len(files)==1319,len(files)
v=dict(baseline_commit=BASE,scope='Kernel actual determinant signs, distinct contacts, full expanding modes and native escape at20/30',
    axiom_audit=dict(declarations_cumulative=2678,declarations_preserved=2629,declarations_fresh=49,
        new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
        preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED,success=True),
    lean_build=dict(command='lake build',jobs=8844,success=True,warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
    statement_check=dict(declarations=49,success=True),mathlib=mathlib,actual_lean_version_checked=version,
    original_return=dict(actual_determinant_sign_kernel_tests=7,earned_integer_triangular_factorizations=7,
        actual_derivative_entry_boxes_from_prior_kernel=True,actual_near_inverse_loss_retained=True,
        determinant_signs_supplied_as_hypotheses_to_concrete_theorems=False,
        two_distinct_minus_one_contacts_kernel=True,contact_intervals=['(79/5,159/10)','(159/10,20)'],
        first_contact_proved=False,unique_contact_proved=False,simple_or_transverse_contact_proved=False,
        full_coordinate_unit_expanding_mode_kernel_instances=2,eigenvalue_brackets=['(-36/25,-71/50)','(-249/100,-247/100)'],
        actual_nonlinear_native_escape_kernel_instances=2,escape_couplings=[20,30],
        arbitrarily_close_unit_complex_starts=True,finite_active_legal_orbit_segments=True,
        original_phase_bug_retained=True,original_frozen_initialization_basin=False,
        unbounded_amplitude_runaway=False,all_orbit_escape=False,all_coupling_interval_instability=False,
        all_30_original_sample_kernel_instances=False,background_offset_norm_instances=0,
        concrete_numeric_theorems_have_no_hard_spectral_or_escape_premises=True,
        IEEE_per_operation_emulation=False,JSON_or_IEEE_parsing_kernel_proved=False,
        false_certificate_controls=['zero_preconditioner','reversed_determinant_sign']),
    rational_data_proposals_regenerated=True,prior_numeric_evidence_immutable_from_baseline=PRIOR,
    old_numeric_replay_rerun=False,python_test_suite_rerun=False,paper_edited=False,original_runtime_edited=False,
    review='adversarial self-review, not independent review',goal_complete=False,
    next_construction='Original frozen initialization basin and finite-step source outcomes; offset kernel instances',
    source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2678 cumulative standard-only closures;49 fresh statements;2 contacts;2 full modes;2 native escapes;1319 fingerprints')
