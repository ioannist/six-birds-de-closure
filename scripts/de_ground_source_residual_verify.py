"""Audit exact four original source convergence tests at zero coupling."""
import hashlib,json,re,subprocess
from pathlib import Path
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
BASE='c307cf7'
PRIOR='results/ground_zero_finite_2026-10-04/verification.json'
PACKET='results/ground_source_residual_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
MODS=['GroundComplexEuclidean','GroundComplexResidual','GroundSourceDiagnostics','GroundOriginalResiduals','GroundSourceDiagnosticControls']
OLD_AUDIT='lean/manifests/axiom_audit_ground_zero_finite_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_source_residual_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_source_residual_2026-10-04.txt'
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
assert len(prior['source_sha256'])==1362
for p,h in prior['source_sha256'].items():
    if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline(p),p
new=[]
for m in MODS:
    s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
    new += [PREFIX+m+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
assert len(MODS)==5 and len(new)==len(set(new))==51
old_manifest=baseline('lean/manifests/check_axioms.lean').decode()
old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
assert len(old)==2764
imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean')==baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
    assert read('lean/manifests/check_ground_source_residual_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT)
assert (ROOT/OLD_AUDIT).read_bytes()==baseline(OLD_AUDIT)
closures(oldraw,old);closures(newraw,new)
header=('Cumulative audit: immutable 2764-declaration raw prefix plus freshly audited 51-declaration suffix.\n'
        'Baseline: c307cf7; proof-source/toolchain identity checked by de_ground_source_residual_verify.py.\n'
        'Full 2815-declaration command was not rerun in this packet.\n\n')
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


require('GroundComplexEuclidean.l2_sq','GroundComplexEuclidean.l2 z ^ 2 = GroundState.complexNormSq z')
require('GroundComplexEuclidean.overlap_inner','GroundNativePhase.overlap z w = inner ℂ','WithLp.toLp 2 z','WithLp.toLp 2 w')
require('GroundComplexEuclidean.phase_distance','hg : GroundState.complexNormSq g = 1','hz : GroundState.complexNormSq z = 1',
        'ho : τ < ‖GroundNativePhase.overlap g z‖','ha : 0 ≤','GroundNativePhase.nativePhase τ g z - g',
        '≤ GroundComplexEuclidean.l2 z - g')
require('GroundComplexEuclidean.double_phase_gap','hd : GroundComplexEuclidean.l2 z - g ≤ d','hd1 : 2 * d ^ 2 ≤ 1',
        'hτ1 : τ < 1 - 2 * d ^ 2','GroundNativePhase.overlap GroundNativePhase.nativePhase τ g z z',
        'GroundNativePhase.nativePhase τ GroundNativePhase.nativePhase τ g z z - z','≤ 4 * d')
require('GroundComplexResidual.hamiltonian_symmetric','GroundState.complexHamiltonian b w','GroundState.complexHamiltonian b z')
require('GroundComplexResidual.shifted_l2_bound','hb : ∀','0 ≤ b i ∧ b i ≤ 2 / 5','he : 0 ≤ e ∧ e ≤ 2 / 5',
        'GroundComplexEuclidean.l2 GroundComplexResidual.shifted b e z ≤ 12 / 5 * GroundComplexEuclidean.l2 z')
require('GroundComplexResidual.ground_energy_budget','GroundState.IsGround b g e','0 ≤ e ∧ e ≤ 2 / 5')
require('GroundComplexResidual.rayleigh_error','hg : ∀','hz : GroundState.complexNormSq z = 1','hM : ∀',
        '|GroundState.complexEnergy b z - e|≤ M * GroundComplexEuclidean.l2 z - g ^ 2')
require('GroundComplexResidual.eigen_residual_bound','GroundComplexResidual.shifted b GroundState.complexEnergy b z z',
        'M * GroundComplexEuclidean.l2 z - g + M * GroundComplexEuclidean.l2 z - g ^ 2')
require('GroundSourceDiagnostics.sourcing_self_comparison_zero','GroundSourceDiagnostics.finalSourcingResidual b κ z = 0')
require('GroundOriginalResiduals.target_ground_data','GroundState.complexNormSq GroundOriginalResiduals.target = 1',
        'GroundState.complexHamiltonian GroundOriginalResiduals.b GroundOriginalResiduals.target',
        'GroundOriginalResiduals.eigenvalue ≤ 2 / 5')
require('GroundOriginalResiduals.orbit_unit','n : ℕ','GroundState.complexNormSq GroundOriginalResiduals.orbit n = 1')
for n,t in [('last_update_threshold','GroundSourceDiagnostics.lastUpdateResidual'),
            ('final_fixed_gap_threshold','GroundSourceDiagnostics.finalFixedGap'),
            ('final_eigen_threshold','GroundSourceDiagnostics.finalEigenResidual'),
            ('final_sourcing_threshold','GroundSourceDiagnostics.finalSourcingResidual')]:
    require('GroundOriginalResiduals.'+n,t,'GroundOriginalResiduals.b 0','< GroundOriginalResiduals.ε')
require('GroundOriginalResiduals.final_fixed_gap_threshold','GroundNativePhase.overlap',
        'GroundNativePhase.nativePhase','GroundOriginalResiduals.orbit 60')
require('GroundOriginalResiduals.actual_seed_zero_sixty_convergence_tests','GroundSourceDiagnostics.MeetsConvergence',
        'GroundOriginalResiduals.τ GroundOriginalResiduals.ε GroundOriginalResiduals.b 0 1 / 2',
        'GroundOriginalResiduals.orbit 59','GroundOriginalResiduals.orbit 60','∀ n',
        'GroundNativeIteration.ActivePhase','GroundNativeIteration.NativeLegal')
require('GroundSourceDiagnosticControls.actual_double_gap_control',
        'GroundSourceDiagnostics.finalFixedGap τ 0 0 GroundSourceDiagnosticControls.z = 0',
        'GroundNativeIteration.nativeCandidate 0 0 GroundSourceDiagnosticControls.z','= 2')
require('GroundSourceDiagnosticControls.imaginary_half_update_illegal','GroundNativeIteration.ActivePhase',
        '¬GroundNativeIteration.NativeLegal τ 0 0 1 / 2')
for n in [x.split('.')[-1] for x in new if '.GroundOriginalResiduals.' in x]:
    assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalResiduals.'+n]),n
models=read(sourcepath('GroundSourceDiagnostics'))
for t in ['l2 (nativeUpdate τ b κ m previous-previous)',
          'l2 (nativePhase τ (nativePhase τ (nativeCandidate b κ z) z) z-z)',
          'l2 (shifted (complexSourcePotential b κ z) (complexEnergy (complexSourcePotential b κ z) z) z)',
          'Real.sqrt (normSq (complexSourcePotential b κ z-complexSourcePotential b κ z))',
          'lastUpdateResidual τ b κ m previous ≤ ε ∧ finalFixedGap τ b κ z ≤ ε ∧',
          'finalEigenResidual b κ z ≤ ε ∧ finalSourcingResidual b κ z ≤ ε']:
    assert t in models,t
for t in ['EuclideanSpace.norm_sq_eq','norm_inner_le_norm','nativePhase_ratio','phase_guard_of_distance',
          'distance_unit_identity','l2_sub_triangle']:
    assert t in read(sourcepath('GroundComplexEuclidean')),t
for t in ['complexHamiltonian, next, prev, Fin.sum_univ_succ','l2_shift_next','l2_shift_prev','l2_diagonal',
          'ground_energy_budget','shifted_symmetric','overlap d (shifted b e d)','Complex.abs_re_le_norm']:
    assert t in read(sourcepath('GroundComplexResidual')),t
concrete=read(sourcepath('GroundOriginalResiduals'))
assert concrete.count('decide +kernel')==1
for t in ['actual_seed_zero_convergence.2','actual_seed_sixty_distance_sq','actual_seed_fifty_nine_distance_sq',
          'double_phase_gap','nativePhase_real_sign_invariant','eigen_residual_bound','shifted_l2_bound',
          'target_ground_data','sourcing_self_comparison_zero']:
    assert t in concrete,t
import de_ground_seed_generate as gen
assert read(sourcepath('GroundOriginalSeed'))==gen.render()

# Read-only source AST coverage; this is a semantic mapping check, not kernel parsing.
import ast
SOURCE='external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py'
source=read(SOURCE)
assert sha(source.encode())=='391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd'
tree=ast.parse(source)
fs={n.name:n for n in tree.body if isinstance(n,ast.FunctionDef)}
def eq_ast(x,s):return ast.dump(x)==ast.dump(ast.parse(s,mode='eval').body)
def assignments(body):
    out={}
    for n in body:
        if isinstance(n,ast.Assign):
            for t in n.targets:
                if isinstance(t,ast.Name):out[t.id]=n.value
    return out
const=assignments(tree.body)
assert eq_ast(const['DX'],'1.0') and eq_ast(const['STEPS'],'60')
assert F.from_float(const['TOL'].value)==F(7737125245533627,77371252455336267181195264)
assert F.from_float(const['CONVERGENCE_TOL'].value)==F(3022314549036573,302231454903657293676544)
assert 'def ε : ℝ := 3022314549036573/302231454903657293676544' in concrete
case=assignments(fs['run_case'].body)
expected={'final_potential':'background + kappa * stress_energy_density(psi, background)',
          'final_h':'hamiltonian(kinetic, final_potential)',
          'final_phi':'phase_align(final_phi, psi)',
          'final_fixed_point_residual':'fixed_point_gap(final_phi, psi)',
          'final_sourcing_residual':'float(np.linalg.norm(final_potential - (background + kappa * stress_energy_density(psi, background))))',
          'final_update_residual':'float(trace_rows[-1]["update_residual"])',
          'converged':'final_update_residual <= CONVERGENCE_TOL and final_fixed_point_residual <= CONVERGENCE_TOL and final_eigen_residual <= CONVERGENCE_TOL and final_sourcing_residual <= CONVERGENCE_TOL'}
for n,t in expected.items():assert eq_ast(case[n],t),(n,t)
fixed=assignments(fs['fixed_point_gap'].body)
assert eq_ast(fixed['phi_aligned'],'phase_align(phi, psi)')
assert eq_ast(next(n.value for n in fs['fixed_point_gap'].body if isinstance(n,ast.Return)),
              'float(np.linalg.norm(phi_aligned - psi))')
eig=assignments(fs['eigen_residual'].body)
for n,t in {'hpsi':'h @ psi','energy':'float(np.real(np.vdot(psi, hpsi)))',
            'residual':'float(np.linalg.norm(hpsi - energy * psi))'}.items():assert eq_ast(eig[n],t)
loops=[n for n in fs['run_case'].body if isinstance(n,ast.For)]
assert len(loops)==1 and eq_ast(loops[0].iter,'range(steps)')
iteration=assignments(loops[0].body)
for n,t in {'candidate':'normalize((1.0 - mix) * psi + mix * phi)',
            'update_residual':'float(np.linalg.norm(candidate - psi))',
            'phi':'phase_align(phi, psi)','psi':'candidate'}.items():assert eq_ast(iteration[n],t)
# The final energy and residual genuinely come from the final sourced Hamiltonian.
assert any(isinstance(n,ast.Assign) and any(isinstance(t,ast.Tuple) and
    [x.id for x in t.elts]==['final_energy','final_eigen_residual'] for t in n.targets) and
    eq_ast(n.value,'eigen_residual(final_h, psi)') for n in fs['run_case'].body)
assert ast.unparse(case['converged']).count('CONVERGENCE_TOL')==4

build=read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8858 jobs).' in build
assert not re.search(r'error:|warning:|build failed',build)
version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
assert version==prior['actual_lean_version_checked']
mathlib=json.loads(json.dumps(prior['mathlib']));libroot=ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
added_mathlib=['Mathlib/Analysis/InnerProductSpace/PiL2.lean','Mathlib/Analysis/InnerProductSpace/Basic.lean',
    'Mathlib/Analysis/Normed/Lp/WithLp.lean','Mathlib/Data/Complex/Basic.lean','Mathlib/Analysis/Complex/Basic.lean']
for p in added_mathlib:
    raw=(libroot/p).read_bytes()
    assert raw==subprocess.check_output(['git','show',mathlib['revision']+':'+p],cwd=libroot),p
    mathlib['direct_proof_source_sha256'][p]=sha(raw)
files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
    'lean/manifests/check_ground_source_residual_axioms.lean','lean/manifests/check_ground_source_residual_statements.lean',
    'math/GROUND_SOURCE_RESIDUALS_2026-10-04.md','scripts/de_ground_source_residual_verify.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name!='verification.json')
assert len(files)==1377,len(files)
v=dict(baseline_commit=BASE,scope='All four exact original source convergence tests at zero coupling after60 updates',
    axiom_audit=dict(declarations_cumulative=2815,declarations_preserved=2764,declarations_fresh=51,
        new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,
        preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED,success=True),
    lean_build=dict(command='lake build',jobs=8858,success=True,warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
    statement_check=dict(declarations=51,success=True),mathlib=mathlib,actual_lean_version_checked=version,
    original_return=dict(mixing='1/2',coupling=0,source_iterations=60,previous_iteration=59,
        original_phase_bug_and_fallback_retained=True,source_double_phase_alignment_retained=True,
        source_Rayleigh_energy_retained=True,source_same_expression_sourcing_comparison_retained=True,
        exact_convergence_tolerance='3022314549036573/302231454903657293676544',
        all_four_original_exact_mathematical_thresholds_pass=True,
        last_update_residual_bound='below5e-9',double_fixed_gap_bound='at most8e-9',
        eigen_residual_bound='below4.81e-9',sourcing_residual=0,
        source_sourcing_diagnostic_independent_self_consistency_claimed=False,
        Euclidean_norm_bridge_exact=True,shifted_Hamiltonian_budget='12/5',
        actual_ground_energy_interval='[0,2/5]',quadratic_Rayleigh_error_earned=True,
        concrete_original_orbit_endpoint_no_hard_premises=True,
        all_iterate_native_guards=True,both_final_diagnostic_phase_guards=True,
        original_both_initial_normalizations_preserved=True,
        actual_double_gap_control='unit pure-imaginary uniform: double gap0, single gap2;half update illegal',
        source_AST_semantic_mapping_checked=True,source_parsing_kernel_proved=False,
        IEEE_per_operation_emulation=False,original_seed_positive_coupling_basin_return=False,
        background_offset_kernel_instances=0),
    source_AST_checked_read_only=True,original_seed_regenerated_read_only=True,
    prior_evidence_immutable_from_baseline=PRIOR,
    old_numeric_replay_rerun=False,floating_scout_rerun=False,python_test_suite_rerun=False,
    paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,
    next_construction='Positive-coupling original-seed orbit/basin construction;18 offset kernel sample instances',
    source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print('2815 cumulative standard-only closures;51 fresh statements;four exact original60 source tests at0;1377 fingerprints')
