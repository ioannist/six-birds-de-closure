"""Verify actual Schur derivatives, trace-dual adjoints and original qualified stationarity."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '8c77586'
packet = 'results/schur_differential_2026-10-03/'
mods = ['MatrixDifferential', 'SchurDifferential', 'SchurAdjointStationarity', 'SchurDifferentialExamples']


def read(p):
    return (root / p).read_text()


def digest(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(ref, p):
    return subprocess.check_output(['git', 'show', ref + ':' + p], cwd=root)


def closure_gate(raw, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
    assert [n for n, _ in entries] == names
    assert not re.search(r'error:|warning:|sorryAx', raw)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    actual = set()
    for name, axioms in entries:
        axs = {a.strip() for a in axioms.split(',') if a.strip()}
        assert axs <= allowed, (name, axs)
        actual.update(axs)
    assert actual == allowed
    return actual


new = []
for mod in mods:
    src = read('lean/SbtCosmo/Derivation/' + mod + '.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', src)
    new += ['SbtCosmo.Derivation.' + mod + '.' + n for n in re.findall(r'^theorem (\w+)', src, re.M)]
assert len(new) == 28
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1083 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_schur_differential_axioms.lean'), re.M) == new
prior_path = 'results/relative_split_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_relative_split_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_schur_differential_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_schur_differential_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1083-declaration raw prefix plus freshly audited 28-declaration suffix.\n'
          'Baseline: 8c77586; earlier proof-source/toolchain identity checked by de_schur_differential_verify.py.\n'
          'Full 1111-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_schur_differential_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['ConvexSubgradient', 'ExtendedClosurePrice', 'MatrixDifferential', 'SchurDifferential', 'SchurDifferentialExamples']:
        d = d.replace(group + '.', '')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


require('MatrixDifferential.hasFDerivAt_mul', 'Matrix i j ℝ', 'Matrix j k ℝ',
        "HasFDerivAt f f' x", "HasFDerivAt g g' x", 'mulRight (g x)', 'mulLeft (f x)')
require('SchurDifferential.jacobian_apply', '(jacobian L Z) H =', 'H * complement L * Z.transpose + Z * complement L * H.transpose')
require('SchurDifferential.jacobian_symmetric', '((jacobian L Z) H).transpose = (jacobian L Z) H')
res = require('SchurDifferential.hasFDerivAt_residual', 'HasFDerivAt', 'Support.residual L', '(jacobian L Z) Z')
assert '(h' not in res
require('SchurDifferential.fderiv_residual', 'fderiv ℝ', 'Support.residual L', '= jacobian L Z')
require('SchurDifferential.traceAdjoint_pairing', '((traceAdjoint J) P) h =', '(P * J h).trace')
require('SchurDifferential.trace_jacobian_formula', 'P + P.transpose', 'complement L', 'H.transpose', '(P * (jacobian L Z) H).trace')
require('SchurDifferential.trace_jacobian_psd', '(hP : P.PosSemidef)', '2 *', '(P * Z * complement L * H.transpose).trace')
require('SchurDifferential.hasFDerivAt_composed_residual', "(hD : HasFDerivAt D D' x)", 'Support.residual L (D z)', ".comp D'")
require('SchurDifferential.hasFDerivAt_composed_trace_gap', "(hD : HasFDerivAt D D' x)", 'traceAdjoint', 'Support.residual L (D z) - B')
for name in ['hasFDerivAt_probe', 'hasFDerivAt_affine_residual', 'hasFDerivAt_trace_gap']:
    d = require('SchurDifferential.'+name, '(D : E →ᵃ[ℝ]', 'HasFDerivAt', 'FiniteDimensional ℝ E')
    for forbidden in ['(hD :', '(hderiv :', '(hJac :', '(hAdj :']:
        assert forbidden not in d, (name, forbidden)
require('SchurDifferential.pricePullback_eq_adjoint_fderiv', 'pricePullback L D x P =', 'traceAdjoint (fderiv ℝ', 'Support.residual L (D z)')
require('SchurDifferential.fderiv_trace_gap', 'fderiv ℝ', 'Support.residual L (D z) - B', '= pricePullback L D x P')
require('SchurDifferential.pricePullback_psd', '(hP : P.PosSemidef)', '2 *', 'D.linear h', 'complement L')
for name in ['matrix_stationarity', 'matrix_stationarity_nonzero']:
    d = require('SchurAdjointStationarity.'+name, '{J : E → EReal}', '(D : E →ᵃ[ℝ]',
                'epigraph Set.univ J', 'intrinsicInterior ℝ (finiteDomain Set.univ J)',
                'intrinsicInterior ℝ A', 'P.PosSemidef', 'Subgradient J star q', 'NormalCone A star η',
                'traceAdjoint (fderiv ℝ', 'Support.residual L (D x)', ').PosDef)',
                '∀ (h : E),', 'q h + 2 *', 'D.linear h', 'η h = 0')
    for forbidden in ['(hsub :', '(hq :', '(hη :', '(hstationarity :', '(hdual :', 'HasFDerivAt']:
        assert forbidden not in d, (name, forbidden)
require('SchurAdjointStationarity.matrix_stationarity_nonzero', 'P ≠ 0', 'ExtendedConeClosurePrice.value', '(B + H) <')
require('SchurDifferentialExamples.singular_native_complement', 'complement', 'Support.rankOneNative = nativeComplement')
require('SchurDifferentialExamples.singular_pricePullback', 'Support.rankOneNative', 'singularProbe', '= 2 * x * h')
require('SchurDifferentialExamples.singular_trace_derivative', 'HasFDerivAt', 'Support.residual', 'singularProbe z', '2 * x', 'ContinuousLinearMap.id ℝ ℝ')
require('SchurDifferentialExamples.missing_second_term_control', 'pricePullback', '≠', '(singularProbe.linear 1).transpose')
require('SchurDifferentialExamples.price_not_hermitian', '¬nonsymmetricPrice.IsHermitian')
require('SchurDifferentialExamples.nonsymmetric_price_control', 'jacobian', '≠ 2 *', 'nonsymmetricPrice')
for name in ['singular_native_complement', 'missing_second_term_control', 'price_not_hermitian', 'nonsymmetric_price_control']:
    assert '(h' not in decls['SchurDifferentialExamples.'+name]
source = read('lean/SbtCosmo/Derivation/SchurDifferential.lean')
for token in ['hasFDerivAt_mul hR', 'hasFDerivAt_transpose hZ', 'Support.residual_projection',
              'hasFDerivAt_residual L (D x)', 'hasFDerivAt_probe D x', 'trace_jacobian_psd hP']:
    assert token in source
source = read('lean/SbtCosmo/Derivation/SchurAdjointStationarity.lean')
for token in ['RelativeSchurStationarity.matrix_stationarity', 'fderiv_trace_gap',
              'pricePullback_eq_adjoint_fderiv', 'pricePullback_psd hP']:
    assert token in source
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8137 jobs).' in build and not re.search(r'error:|warning:', build)
assert 'Adversarial self-review, not independent review' in read(packet + 'self_review.txt')

# Prior source and evidence stay immutable; only these cumulative metadata may grow.
mutable = {'README.md', 'lean/README.md', 'lean/lakefile.lean', 'lean/manifests/check_axioms.lean',
           'lean/manifests/coverage_table.md', 'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
for p, h in prior['source_sha256'].items():
    if p not in mutable:
        assert digest((root / p).read_bytes()) == h, p
        assert digest(git_blob(baseline, p)) == prior['git_blob_sha256'][p], p
for ref, paths in [('6a71e6c', ['paper', 'external']), (baseline, ['sbt_cosmo', 'tests', 'results/DE_window', 'results/DE_dual'])]:
    assert subprocess.check_output(['git', 'diff', '--name-only', ref, '--', *paths], cwd=root) == b''
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', baseline], cwd=root).decode().splitlines()
protected = [p for p in tracked if p not in mutable and p.startswith(('scripts/', 'lean/', 'results/', 'math/'))]
assert subprocess.check_output(['git', 'diff', '--name-only', baseline, '--', *protected], cwd=root) == b''
old_config = git_blob(baseline, 'lean/lakefile.lean').decode()
expected_config = old_config.replace('`SbtCosmo.Derivation.RelativeSplitExamples]',
    '`SbtCosmo.Derivation.RelativeSplitExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot / p).read_bytes()) == h
for p in ['Mathlib/Analysis/Calculus/FDeriv/Prod.lean', 'Mathlib/Analysis/Calculus/FDeriv/Add.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Mul.lean', 'Mathlib/Analysis/Calculus/FDeriv/Comp.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Linear.lean', 'Mathlib/Analysis/Calculus/FDeriv/Const.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Affine.lean', 'Mathlib/Analysis/Matrix/Normed.lean',
          'Mathlib/Data/Matrix/Basic.lean', 'Mathlib/LinearAlgebra/Matrix/Trace.lean',
          'Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean',
          'Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean']:
    source = (libroot / p).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_schur_differential_verify.py', 'math/SCHUR_DIFFERENTIAL_LEAN_2026-10-03.md',
              'lean/manifests/check_schur_differential_statements.lean', 'lean/manifests/check_schur_differential_axioms.lean',
              new_path, combined_path])
files.update(str(p.relative_to(root)) for p in (root / packet).iterdir() if p.name != 'verification.json')
hashes = {p: digest((root / p).read_bytes()) for p in sorted(files)}
git_hashes, normalized = {}, []
for p in sorted(files):
    blob = (root / p).read_bytes()
    if b'\r\n' in blob:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', p], cwd=root).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob, p
        blob = blob.replace(b'\r\n', b'\n')
        normalized.append(p)
    git_hashes[p] = digest(blob)
v = {
    'baseline_commit': baseline,
    'scope': 'Actual fixed-native Schur matrix derivative/trace-dual adjoint and qualified original extended stationarity',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8137, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_schur_differential_axioms.lean',
                    'success': True, 'declarations_cumulative': 1111, 'declarations_fresh': 28,
                    'declarations_preserved': 1083, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_schur_differential_statements.lean',
                        'success': True, 'declarations': 28, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'actual_matrix_norm': 'existing finite elementwise norm, no operator/Frobenius norm substitution',
        'rectangular_matrix_calculus': 'entry product derivatives, finite sums and actual pi derivative return',
        'native_support': 'original spectral generalized inverse/projector, no native invertibility hypothesis',
        'matrix_jacobian': 'H R Z^T + Z R H^T with R=I-projector(L)',
        'actual_residual_HasFDerivAt_and_fderiv_identity': True,
        'jacobian_symmetric_range_proved': True,
        'adjoint': 'actual trace-dual pullback into primal continuous dual; no unspecified primal inner product',
        'pairing_identity_definitional': True, 'actual_derivative_adjoint_equality_substantive': True,
        'general_trace_formula': 'trace(((P+P^T) Z R) H^T)', 'PSD_symmetry_earns_factor_two': True,
        'actual_affine_probe_derivative': 'earned continuous affine realization of original D.linear',
        'general_probe_chain_rule': 'actual HasFDerivAt probe input, no finite-dimensional primal required',
        'final_affine_derivative_or_adjoint_supplied': False, 'fixed_budget_derivative_zero': True,
        'matrix_jacobian_adjoint_formula_mechanized': True,
        'general_relative_interior_extended_objective_normal_split_mechanized': True,
        'original_extended_full_stationarity': 'q + traceAdjoint(fderiv actual_Xi) P + admissibility normal = zero',
        'pointwise_stationarity': 'q(h)+2*trace(P D(star) R (D.linear(h))^T)+normal(h)=0, every original primal h',
        'nonzero_price': 'strict decrease of original complete-lattice value in PSD budget direction',
        'singular_rectangular_example': 'actual rank-one 2x3 native, 1x3 affine probe, complement earned, price2*x*h',
        'controls': ['actual dropped product-rule term fails', 'actual nonsymmetric factor-two shortcut fails'],
        'native_L_fixed': True, 'moving_native_calculus_mechanized': False,
        'primal_attainment_derived': False, 'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Same-price scalar differentiable-value sensitivity and qualified stationarity assembly; remaining original-target audit',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1111 ordered cumulative standard-only closures (1083 immutable + 28 fresh), 28 actual matrix-calculus/Jacobian/adjoint/stationarity/control statements; {len(hashes)} fingerprints')
