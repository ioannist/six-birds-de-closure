"""Audit exact coordinate bases and actual native coupling attraction returns."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
from fractions import Fraction as F

ROOT=Path(__file__).resolve().parents[1]
BASE='5c61442'
PRIOR='results/ground_samples_2026-10-04/verification.json'
PACKET='results/ground_coordinates_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundMatrixCoordinates']+[f'GroundCoordinates.Point{i:03d}' for i in range(12)]+['GroundOriginalCoordinates','GroundCoordinateControls']
ROOTS=['GroundMatrixCoordinates','GroundOriginalCoordinates','GroundCoordinateControls']
OLD_AUDIT='lean/manifests/axiom_audit_ground_samples_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_coordinates_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_coordinates_2026-10-04.txt'
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
assert len(prior['source_sha256'])==1260
for p,h in prior['source_sha256'].items():
    if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
    s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
    new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==15 and len(new)==len(set(new))==95
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
assert len(old)==2534
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in ROOTS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
    assert read('lean/manifests/check_ground_coordinates_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2534-declaration raw prefix plus freshly audited 95-declaration suffix.\n'
        'Baseline: 5c61442; proof-source/toolchain identity checked by de_ground_coordinates_verify.py.\n'
        'Full 2629-declaration command was not rerun in this packet.\n\n')
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


for i in range(12):
    p=f'GroundCoordinates.Point{i:03d}'
    for name,kind in [('real_inverse','InverseArithmetic'),('imag_inverse','InverseArithmetic'),('real_rows','RowArithmetic'),('imag_rows','RowArithmetic')]:
        require(p+'.'+name,'GroundMatrixCoordinates.'+kind,p)
        assert '→' not in decls[PREFIX+p+'.'+name]
    require(p+'.realBox_return',p+'.realBox = GroundOriginalResponses.enclosures '+str(i))
    require(p+'.imagBox_return',p+'.imagBox = GroundMatrixCoordinates.imaginaryIntervals',f'GroundSamples.Point{i:03d}')
require('GroundMatrixCoordinates.basis_apply','InverseArithmetic','GroundMatrixCoordinates.basis h x i = ∑ j,')
require('GroundMatrixCoordinates.basis_symm_apply','InverseArithmetic','GroundMatrixCoordinates.basis h .symm x i = ∑ j,')
require('GroundMatrixCoordinates.conjugate_entries','InverseArithmetic','∑ a, ∑ b,','GroundMatrixCoordinates.entries L a b')
require('GroundMatrixCoordinates.conjugate_norm','GroundMatrixCoordinates.RowArithmetic','hB : ∀','GroundMatrixCoordinates.conjugate','≤ ↑q')
require('GroundMatrixCoordinates.imaginaryIntervals_sound','Metric.closedBall','GroundNativeJacobian.imaginaryDerivative 1 / 2')
for n in ['actual_real_rows','actual_real_norm','actual_imag_rows','actual_imag_norm','actual_full_norm']:
    require('GroundOriginalCoordinates.'+n,'i : Fin 12','GroundOriginalCoordinates.root i')
    assert 'hreal' not in decls[PREFIX+'GroundOriginalCoordinates.'+n] and 'hB :' not in decls[PREFIX+'GroundOriginalCoordinates.'+n]
require('GroundOriginalCoordinates.actual_stable_full_norm','i : Fin 10','GroundNativeLocal.coordinateDerivative','< 1')
require('GroundOriginalCoordinates.actual_native_attraction','i : Fin 10','∃ r > 0, ∀ z : GroundState.ComplexField',
        'Tendsto','GroundNativeIteration.nativeUpdate','GroundNativeControls.originalTolerance',
        'GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
for n,c,q in [('actual_twenty_norm','20','3 / 2'),('actual_thirty_norm','30','3')]:
    require('GroundOriginalCoordinates.'+n,'GroundNativeLocal.coordinateDerivative',c,'≤ '+q)
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalCoordinates.'+n])
require('GroundCoordinateControls.zero_inverse_rejected','¬GroundMatrixCoordinates.InverseArithmetic','GroundCoordinates.Point009.S 0')
require('GroundCoordinateControls.zero_row_budget_rejected','¬GroundMatrixCoordinates.RowArithmetic','GroundCoordinates.Point009.realBox 0')
src=flatten(read(sourcepath('GroundMatrixCoordinates')))
for t in ['left : P * S = 1','right : S * P = 1','Matrix.toLin\'OfInv','GroundLocalDynamics.operator_norm_le_rows',
          'Expr.sum fun a => Expr.sum fun b =>','P i a','S b j','GroundNativeJacobian.imaginaryDerivative (1/2)']:
    assert flatten(t) in src,t
import de_ground_coordinates_generate as cg
import de_ground_coordinates_family as cf
ds=cg.proposals();assert len(ds)==12
assert all(0<=d['rate']<1 for d in ds[:10])
assert ds[10]['rate']==F(3,2) and ds[11]['rate']==3
assert ds[9]['rate']<F('0.911617')
for i,d in enumerate(ds):
    s=read(sourcepath(f'GroundCoordinates.Point{i:03d}'))
    assert s==cg.render(i,d) and s.count('decide +kernel')==6 and s.count('norm_num [')==2
assert read(sourcepath('GroundOriginalCoordinates'))==cf.render()
assert 'Fin.cases' in read(sourcepath('GroundOriginalCoordinates'))
status=json.loads(read(PACKET+'leaf_build_status.json'))
assert status['total_targets']==status['successful_targets']==12 and status['batch_size']==2 and status['all_success']
assert len(status['terminal_batches'])==6
for i,row in enumerate(status['terminal_batches']):
    targets=[PREFIX+f'GroundCoordinates.Point{j:03d}' for j in range(2*i,2*i+2)]
    assert row['targets']==targets and row['command']==['lake','build',*targets] and row['exit_code']==0
log=read(PACKET+'leaf_build.txt')
assert log.count('Batch targets: ')==log.count('Terminal exit: 0')==6
assert log.count('Build completed successfully')==6
assert not re.search(r'error:|warning:|build failed',log)
build=read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8830 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=json.loads(json.dumps(prior['mathlib']));libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
for p in ['Mathlib/LinearAlgebra/Matrix/ToLin.lean','Mathlib/Topology/Algebra/Module/FiniteDimension.lean']:
    assert (libroot/p).read_bytes()==subprocess.check_output(['git','show','HEAD:'+p],cwd=libroot),p
    mathlib['direct_proof_source_sha256'][p]=sha((libroot/p).read_bytes())
files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
    'lean/manifests/check_ground_coordinates_axioms.lean','lean/manifests/check_ground_coordinates_statements.lean',
    'math/GROUND_KERNEL_COORDINATES_2026-10-04.md','scripts/de_ground_coordinates_generate.py',
    'scripts/de_ground_coordinates_family.py','scripts/de_ground_coordinates_build.py','scripts/de_ground_coordinates_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name!='verification.json')
assert len(files)==1290,len(files)
v=dict(baseline_commit=BASE,scope='Kernel coordinate norms and actual native complex local attraction at original coupling samples',
    axiom_audit=dict(declarations_cumulative=2629,declarations_preserved=2534,declarations_fresh=95,
        new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
        preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED,success=True),
    lean_build=dict(command='lake build',jobs=8830,success=True,warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
    statement_check=dict(declarations=95,success=True),mathlib=mathlib,actual_lean_version_checked=version,
    original_return=dict(original_coupling_sample_kernel_norm_instances=12,exact_two_sided_rational_basis_inverses=24,
        original_phase_bug_retained=True,real_and_imaginary_blocks=True,actual_operator_norm_return=True,
        native_complex_local_attraction_kernel_instances=10,stable_couplings=[str(x) for x in [0,F.from_float(.1),F.from_float(.3),F(1,2),1,2,3,5,10,15]],
        coupling15_real_operator_bound=str(ds[9]['rate']),all_imaginary_operator_bounds='501/1000',
        coupling20_full_operator_bound='3/2',coupling30_full_operator_bound='3',
        actual_nonlinear_native_escape_kernel_instantiated=False,determinant_signs_and_eigenmodes_kernel_instantiated=False,
        all_30_original_sample_kernel_instances=False,background_offset_norm_instances=0,
        concrete_numeric_theorems_have_only_finite_indices=True,original_frozen_initialization_basin=False,
        all_coupling_interval_stability=False,universal_runaway=False,
        IEEE_per_operation_emulation=False,JSON_or_IEEE_parsing_kernel_proved=False,
        false_certificate_controls=['zero_inverse_at15','zero_row_budget_at15']),
    rational_data_proposals_regenerated=True,prior_numeric_evidence_immutable_from_baseline=PRIOR,
    old_numeric_replay_rerun=False,python_test_suite_rerun=False,paper_edited=False,original_runtime_edited=False,
    review='adversarial self-review, not independent review',goal_complete=False,
    next_construction='Kernel determinant signs and actual expanding modes; native escape return; frozen initialization basin',
    source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2629 cumulative standard-only closures;95 fresh statements;12 full derivative norms;10 native attractions;1290 fingerprints')
