"""Verify native nonlinear escape statements, closures and immutable provenance.

This audits an actual analytical bridge with explicit linear hypotheses. Prior
numeric spectral certificates remain protected evidence, not a fresh replay.
"""
import hashlib
from fractions import Fraction as F
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = '7cc37e1'
PRIOR = 'results/ground_continuation_2026-10-04/verification.json'
PACKET = 'results/ground_escape_2026-10-04/'
MODULE = 'SbtCosmo.Derivation.GroundNativeEscape'
SOURCE = 'lean/SbtCosmo/Derivation/GroundNativeEscape.lean'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_continuation_2026-10-04.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_escape_new_2026-10-04.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_escape_2026-10-04.txt'
MUTABLE = {'README.md', 'lean/README.md', 'lean/lakefile.lean',
           'lean/manifests/check_axioms.lean', 'lean/manifests/coverage_table.md',
           'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}


def read(p):
    return (ROOT / p).read_text()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def baseline(p):
    return subprocess.check_output(['git', 'show', BASE + ':' + p], cwd=ROOT)


def canonical(p):
    b = (ROOT / p).read_bytes()
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
    return t.replace('| ', '|').replace(' |', '|').replace('‖ ', '‖').replace(' ‖', '‖')


prior = json.loads(read(PRIOR))
assert (ROOT / PRIOR).read_bytes() == baseline(PRIOR)
assert len(prior['source_sha256']) == 1201
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT / p).read_bytes()) == h and canonical(p) == baseline(p), p
source = read(SOURCE)
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source)
new = [MODULE + '.' + n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
assert len(new) == 18 and len(set(new)) == 18
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 2459
imports = 'import ' + MODULE + '\n'
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2] + ',\n    `' + MODULE + ']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_escape_' + suffix + '.lean') == imports + '\n' + ''.join(cmd + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old)
closures(newraw, new)
header = ('Cumulative audit: immutable 2459-declaration raw prefix plus freshly audited 18-declaration suffix.\n'
          'Baseline: 7cc37e1; proof-source/toolchain identity checked by de_ground_escape_verify.py.\n'
          'Full 2477-declaration command was not rerun in this packet.\n\n')
combined = header + oldraw + '\n' + newraw
closures(combined, old + new)
(ROOT / COMBINED).write_text(combined)
statements = read(PACKET + 'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)] == new
assert not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo[\w.]*', statements, re.M))
decls = {}
for i, m in enumerate(starts):
    t = statements[m.start():starts[i + 1].start() if i + 1 < len(starts) else len(statements)]
    decls[m.group().rstrip('.')] = flatten(t.replace('SbtCosmo.Derivation.', '').replace('⇑', ''))


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[MODULE + '.' + name], (name, token, decls[MODULE + '.' + name])


require('c2_quadratic_remainder', 'hc : ContDiffAt ℝ 2 f u', '∃ r > 0, ∃ K',
        '‖f x - f u - fderiv ℝ f u x - u‖', '↑K * ‖x - u‖ ^ 2')
require('quadratic_tracking_step', '4 * K + M * A ≤ A * R ^ 2', 'hL : ‖L‖ ≤ M',
        '‖f x - L x‖ ≤ K * ‖x‖ ^ 2', '‖f x - L y‖ ≤ A * α * R ^ 2')
require('quadratic_tracking', 'hend : δ * R ^ N ≤ r', 'k : ℕ', 'k ≤ N →', 'f^[k]',
        'A * δ * R ^ k ^ 2', '2 * δ * R ^ k')
require('arbitrarily_close_eigenmode_escape', 'ε : ℝ', 'ε > 0 → ∃ x N,', '1 ≤ N', '‖x‖ < ε',
        's / 2 ≤ ‖f^[N] x‖', '∀ k ≤ N, ‖f^[k] x‖ ≤ 2 * s')
require('c2_eigenmode_escape', 'hc : ContDiffAt ℝ 2 f 0', 'hf : f 0 = 0',
        'hd : HasFDerivAt f L 0', 'heigen : L h = ℓ • h', 'hgap : ‖L‖ < |ℓ| ^ 2',
        '∃ s > 0, ∀ ε > 0,')
require('c2_eigenmode_escape_within', 'hB : 0 < B', '2 * s ≤ B', '∀ ε > 0,')
require('c2_eigenmode_output_escape', 'hP : ∀ x : E, ‖x‖ ≤ B → P f x', '∃ z N,',
        '‖z‖ < ε ∧ P z', 's / 2 ≤ ‖f^[N] z‖', '∀ k ≤ N, ‖f^[k] z‖ ≤ B')
require('nativeUpdate_unit', 'hτ : 0 ≤ τ', 'hz : GroundNativeIteration.NativeLegal τ b κ m z',
        'GroundState.complexNormSq GroundNativeIteration.nativeUpdate τ b κ m z = 1')
require('displacement_hasFDerivAt', 'HasFDerivAt', 'GroundNativeEscape.displacementMap',
        'GroundNativeLocal.coordinateDerivative T b κ m u')
require('displacement_iterate_return', 'GroundNativeEscape.displacementMap',
        'GroundNativeJacobian.nativePairMap τ b κ m ^[n]')
require('native_complex_local_escape', 'hu : GroundState.normSq u = 1',
        'hf : GroundSourceJacobian.groundMap b κ u = u', 'hτ0 : 0 ≤ τ', 'hτ1 : τ < 1',
        'hv : ‖v‖ = 1', 'heigen : GroundNativeLocal.coordinateDerivative T b κ m u v = ℓ • v',
        'hℓ : 1 < |ℓ|', 'hgap : ‖GroundNativeLocal.coordinateDerivative T b κ m u‖ < |ℓ| ^ 2',
        '∃ s > 0, ∀ ε > 0, ∃ z N,', 'GroundState.complexNormSq z = 1',
        's / 2 ≤', '∀ k ≤ N,', 'GroundNativeIteration.ActivePhase τ b κ',
        'GroundNativeIteration.NativeLegal τ b κ m')
# The main theorem has only ground/tolerance and two linear spectral inputs,
# rather than a supplied quadratic-error or nonlinear escape premise.
main = source.split('theorem native_complex_local_escape', 1)[1].split(':= by', 1)[0]
assert 'hrem' not in main and 'hP' not in main and 'ContDiff' not in main
assert 'hgap' in main and 'coordinateDerivative' in main
# Recompare the protected historical certificate bounds; do not represent this
# as a fresh replay of their interval matrix/determinant computations.
real = json.loads(read('results/ground_interval_2026-10-03/certificates.json'))
native = json.loads(read('results/ground_native_2026-10-03/native_certificates.json'))
assert real['scale'] == native['scale']
scale = int(real['scale'])
gaps = {}
for k, M in [(20, F(3, 2)), (30, F(3))]:
    rr = [w for w in real['certificates'] if w['sweep'] == 'kappa' and F.from_float(float.fromhex(w['parameter_hex'])) == k]
    nr = [w for w in native['certificates'] if w['sweep'] == 'kappa' and F.from_float(float.fromhex(w['parameter_hex'])) == k]
    assert len(rr) == len(nr) == 1
    rr, nr = rr[0], nr[0]
    lo, hi = map(F, rr['unstable_bracket'])
    assert lo < hi < -1
    assert rr['spectral_radius_upper'] == nr['real_transformed_norm_upper']
    U = F(int(rr['spectral_radius_upper']), scale)
    V = F(int(nr['imaginary_transformed_norm_upper']), scale)
    assert nr['real_unstable_mode_retained'] and max(U, V) < M < hi*hi
    gaps[str(k)] = dict(derivative_norm_upper_choice=str(M), eigen_growth_lower=str(-hi),
                       squared_growth_lower=str(hi*hi), historical_bounds_comparison_checked=True)
build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8783 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = dict(prior['mathlib'])
mathlib['direct_proof_source_sha256'] = dict(mathlib['direct_proof_source_sha256'])
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / p).read_bytes()) == h
for p in ['Mathlib/Analysis/Calculus/MeanValue.lean',
          'Mathlib/Analysis/Calculus/ContDiff/Comp.lean',
          'Mathlib/Analysis/Calculus/ContDiff/RCLike.lean',
          'Mathlib/Analysis/SpecificLimits/Basic.lean']:
    mathlib['direct_proof_source_sha256'][p] = sha((libroot / p).read_bytes())
files = set(prior['source_sha256']) | {PRIOR, SOURCE, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_escape_axioms.lean', 'lean/manifests/check_ground_escape_statements.lean',
    'math/GROUND_NATIVE_ESCAPE_2026-10-04.md', 'scripts/de_ground_escape_verify.py'}
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 1212, len(files)
v = dict(baseline_commit=BASE, scope='Actual native nonlinear local escape from arbitrarily close unit complex inputs',
    axiom_audit=dict(declarations_cumulative=2477, declarations_preserved=2459, declarations_fresh=18,
        new_local_theorems=new, axioms=['Classical.choice', 'Quot.sound', 'propext'],
        full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
        preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED, success=True),
    lean_build=dict(command='lake build', jobs=8783, success=True, warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
    statement_check=dict(declarations=18, success=True), mathlib=mathlib, actual_lean_version_checked=version,
    original_return=dict(C2_quadratic_remainder_earned=True, finite_tracking_losses_retained=True,
        actual_native_derivative_and_affine_iteration_conjugacy_earned=True,
        nonlinear_native_escape_from_arbitrarily_close_unit_inputs=True,
        fixed_escape_radius_before_initial_epsilon=True, phase_and_normalization_guards_through_escape=True,
        explicit_linear_hypotheses=['actual_real_eigenmode_abs_greater_than_one', 'coordinate_derivative_norm_less_than_squared_eigenvalue_abs'],
        numeric_kernel_instantiations_at_20_and_30=False,
        old_exact_20_30_bounds_permit_linear_gap=True,
        historical_20_30_linear_gap_comparison=gaps,
        nonlinear_native_local_instability_20_30_mathematical_return=True,
        sample_roots_and_identities_kernel_instantiated=False, determinant_signs_kernel_instantiated=False,
        frozen_initialization_basin=False, all_interval_stability=False, unbounded_runaway=False,
        IEEE_per_operation_emulation=False),
    exact_numeric_python_replay_fresh=False, prior_numeric_evidence_immutable_from_baseline=PRIOR,
    python_test_suite_rerun=False, paper_edited=False, original_runtime_edited=False,
    review='adversarial self-review, not independent review', goal_complete=False,
    next_construction='Concrete sample identity/spectral certificates and frozen-original initialization basin estimates',
    source_sha256={p: sha((ROOT / p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('2477 cumulative standard-only closures;18 fresh statements;actual guarded unit-input escape;1212 fingerprints')
