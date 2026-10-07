"""Original coupling-continuation packet: exact replay, analytic coverage and provenance."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

import de_ground_branch_certificate as branch

ROOT = branch.ROOT
BASE = 'e2bd0fb'
PACKET = 'results/ground_branch_2026-10-03/'
PRIOR = 'results/ground_native_2026-10-03/verification.json'
MODS = ['GroundParameterEquations', 'GroundParameterBranch', 'GroundParameterTube', 'GroundParameterSpectrum']
PREFIX = 'SbtCosmo.Derivation.'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_native_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_branch_new_2026-10-03.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_branch_2026-10-03.txt'
MUTABLE = {'README.md', 'lean/README.md', 'lean/lakefile.lean',
           'lean/manifests/check_axioms.lean', 'lean/manifests/coverage_table.md',
           'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}


def read(p):
    return (ROOT/p).read_text()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def baseline(p):
    return subprocess.check_output(['git', 'show', BASE+':'+p], cwd=ROOT)


def canonical(p):
    b = (ROOT/p).read_bytes()
    if b'\r\n' in b:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', p], cwd=ROOT).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in b
        b = b.replace(b'\r\n', b'\n')
    return b


def closures(raw, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
    assert [n for n, _ in entries] == names
    assert not re.search(r'error:|warning:|sorryAx', raw)
    for n, a in entries:
        assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, n


def flatten(t):
    t = ' '.join(t.replace('(', ' ').replace(')', ' ').split())
    t = re.sub(r'\s+,', ',', t)
    return t.replace('| ', '|').replace(' |', '|')


prior = json.loads(read(PRIOR))
assert (ROOT/PRIOR).read_bytes() == baseline(PRIOR)
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT/p).read_bytes()) == h and canonical(p) == baseline(p), p
new = []
for mod in MODS:
    source = read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source)
    new += [PREFIX+mod+'.'+n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
assert len(new) == 31
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1782
imports = ''.join('import '+PREFIX+mod+'\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+mod for mod in MODS)+']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_branch_'+suffix+'.lean') == imports+'\n'+''.join(cmd+n+'\n' for n in new)
assert (ROOT/OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old); closures(newraw, new)
header = ('Cumulative audit: immutable 1782-declaration raw prefix plus freshly audited 31-declaration suffix.\n'
          'Baseline: e2bd0fb; proof-source/toolchain identity checked by de_ground_branch_verify.py.\n'
          'Full 1813-declaration command was not rerun in this packet.\n\n')
combined = header+oldraw+'\n'+newraw
closures(combined, old+new)
(ROOT/COMBINED).write_text(combined)
statements = read(PACKET+'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)] == new
assert not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^'+re.escape(PREFIX)+r'(\w+)\.([\w.]+)', statements, re.M))
decls = {}
for i, m in enumerate(starts):
    t = statements[m.start():starts[i+1].start() if i+1 < len(starts) else len(statements)]
    t = re.sub(r'SbtCosmo\.Derivation\.\w+\.', '', t).replace('⇑', '')
    decls[m.group(1)+'.'+m.group(2).rstrip('.')] = flatten(t)


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[name], (name, token, decls[name])


E, B, T, S = [m+'.' for m in MODS]
require(E+'jointResidual_smooth', 'ContDiff ℝ ↑⊤ jointResidual')
require(E+'jointResidual_partial', 'fderiv ℝ jointResidual p, x', 'inr ℝ Parameter Point',
        'residualDerivative p.1 p.2 x')
for name in ['defect_bijective', 'defect_preconditioner_bijective']:
    require(E+name, '‖ContinuousLinearMap.id ℝ Point - C.comp D‖ < 1', 'Function.Bijective')
require(B+'certified_local_positive_branch', '‖correctionDerivative p.1 p.2 C x‖ < 1',
        'hz : residual p.1 p.2 x = 0', 'hp : ∀ i : Fin 8 , 0 < x.1 i',
        'ContDiffAt ℝ ↑⊤', 'residual q.1 q.2', 'y = f q')
require(B+'branch_ground_eventually', 'groundPair sourcePotential', 'groundMap', 'normSq', '∀ᶠ')
require(T+'TubeCertificate.positive_root_exists', 't : TubeCertificate b', 'k ∈ t.interval',
        '∃ x ∈ Metric.closedBall t.center t.radius', 'residual b k x = 0', 'groundMap b k x.1 = x.1',
        'residual b k y = 0 → y = x')
require(T+'TubeCertificate.root_distance_lt', 'dist t.root k t.center < t.radius')
require(T+'TubeCertificate.root_implicit_germ', 'ContDiffAt ℝ ↑⊤ g k', 'g k = t.root k',
        't.root =ᶠ[nhdsWithin k t.interval] g')
require(T+'TubeCertificate.root_smooth_within', 'ContDiffWithinAt ℝ ↑⊤ t.root t.interval k')
require(T+'common_root_glues', 'hz : residual b k x = 0', 't.root k = v.root k')
require(S+'jointGround_partial', 'jacobian z.1.1 z.1.2 z.2')
require(S+'halfMatrix_continuous', 'Continuous halfMatrix')
require(S+'crossingDet_continuous', 'Continuous crossingDet')
require(S+'strict_sign_crossing', 'f a * f c < 0', '∃ k ∈ Set.Ioo a c, f k = 0')
require(S+'actual_minus_one_crossing', 'hu : ContinuousOn u Set.Icc a c',
        'hfixed : ∀ k ∈ Set.Icc a c', 'normSq u k = 1', 'groundMap b k u k = u k',
        'crossingDet b, a, u a * crossingDet b, c, u c < 0',
        '∃ k ∈ Set.Ioo a c', 'h ≠ 0', 'dot u k h = 0', 'normalizedJacobian b k 1 / 2 u k h = -h',
        'fullDerivative b k 1 / 2 u k h, 0 = - h, 0', 'HasFDerivAt', 'nativePairMap τ b k 1 / 2')
tube_source = flatten(read('lean/SbtCosmo/Derivation/GroundParameterTube.lean'))
for token in ['defect : ∀ k ∈ interval, ∀ x ∈ closedBall center radius,',
              'residual_strict : ∀ k ∈ interval,', 'field_positive : ∀ x ∈ closedBall center radius,',
              'radius_pos : 0 < radius', 'rate_lt : rate < 1']:
    assert flatten(token) in tube_source, token

build = read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8200 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT/'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']; libroot = ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot/p).read_bytes()) == h
for p in ['Mathlib/Analysis/Calculus/ImplicitContDiff.lean',
          'Mathlib/Analysis/Calculus/ContDiff/Defs.lean',
          'Mathlib/Topology/Order/IntermediateValue.lean',
          'Mathlib/Topology/Instances/Matrix.lean', 'Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean',
          'Mathlib/Topology/MetricSpace/Pseudo/Defs.lean', 'Mathlib/Order/Filter/Prod.lean']:
    b = (libroot/p).read_bytes(); assert b == subprocess.check_output(['git', 'show', 'HEAD:'+p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = sha(b)
data = json.loads(read(PACKET+'witnesses.json'))
result = branch.replay(data)
assert result == json.loads(read(PACKET+'certificates.json'))
assert branch.controls(data) == json.loads(read(PACKET+'controls.json'))
assert result['uniform_root_tubes'] == 286 and result['common_certified_anchors'] == 287
assert result['original_coupling_roots_returned'] == 12
assert result['actual_half_mixing_minus_one_crossing_interval'] == ['79/5', '159/10']
assert result['additional_distinct_minus_one_crossing_interval'] == ['159/10', '20']
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_branch_axioms.lean', 'lean/manifests/check_ground_branch_statements.lean',
    'math/GROUND_COUPLING_BRANCH_2026-10-03.md', 'scripts/de_ground_branch_verify.py', 'scripts/de_ground_branch_certificate.py'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 583, len(files)
v = dict(baseline_commit=BASE,
         scope='Original [0,30] positive coupling branch through all12 original roots; two actual half-mixing minus-one contacts',
         axiom_audit=dict(declarations_cumulative=1813, declarations_preserved=1782, declarations_fresh=31,
                         new_local_theorems=new, axioms=['Classical.choice', 'Quot.sound', 'propext'],
                         full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
                         preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
                         combined_receipt=COMBINED, success=True),
         lean_build=dict(command='lake build', jobs=8200, success=True, warnings_as_errors=True,
                         receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
         statement_check=dict(declarations=31, success=True), mathlib=mathlib, actual_lean_version_checked=version,
         original_return=dict(joint_actual_equations_smooth_and_partial_return=True,
                              actual_partial_and_preconditioner_invertible_from_defect=True,
                              local_positive_implicit_branch_and_uniqueness_earned=True,
                              uniform_tube_root_and_boundary_smoothness_earned=True,
                              common_root_tube_identity_lean_criterion=True,
                              mathematical_connected_positive_C_infinity_branch_interval=['0', '30'],
                              exact_uniform_tubes=286, exact_common_anchors=287, original_coupling_sample_roots_returned=12,
                              actual_normalized_jacobian_and_determinant_continuity_earned=True,
                              actual_minus_one_contacts=[['79/5', '159/10'], ['159/10', '20']],
                              minus_one_tangent_and_native_complex_derivative_return=True,
                              concrete_certificate_kernel_instantiations=False,
                              concrete_global_finite_patch_lean_definition=False,
                              global_root_uniqueness=False, first_unique_transverse_crossing=False,
                              all_interval_stability=False, nonlinear_escape=False,
                              background_offset_continuum=False, frozen_complex_initialization_basin=False,
                              physical_Lambda_bridge=False),
         python_test_suite_rerun=False, exact_sample_and_uniform_replay_fresh=True,
         original_runtime_edited=False, paper_edited=False,
         review='adversarial self-review, not independent review', goal_complete=False,
         next_construction='Concrete kernel tube/root/sign certificates and finite patch definition; original-init basin; sharper crossing classification if useful',
         source_sha256={p: sha((ROOT/p).read_bytes()) for p in sorted(files)},
         git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v, indent=2)+'\n')
print('1813 cumulative standard-only closures; 31 new statements; [0,30] branch and two minus-one contacts; 583 fingerprints')
