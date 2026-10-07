"""Verify general matrix Slater price, qualified actual-adjoint stationarity and nonlinear Schur/scope controls."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '2f88d23'
packet = 'results/general_matrix_2026-10-03/'
mods = ['ExtendedSmoothStationarity', 'GeneralMatrixPrice', 'GeneralMatrixStationarity', 'GeneralMatrixExamples']


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
assert len(old_names) == 1130 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_general_matrix_axioms.lean'), re.M) == new
prior_path = 'results/scalar_stationarity_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_scalar_stationarity_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_general_matrix_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_general_matrix_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1130-declaration raw prefix plus freshly audited 28-declaration suffix.\n'
          'Baseline: 2f88d23; earlier proof-source/toolchain identity checked by de_general_matrix_verify.py.\n'
          'Full 1158-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_general_matrix_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['ConvexSubgradient', 'ExtendedClosurePrice', 'SchurDifferential', 'GeneralMatrixPrice', 'GeneralMatrixExamples', 'MatrixPriceRepresentation', 'MatrixClosurePriceExamples']:
        d = d.replace(group + '.', '')
    d = d.replace('MatrixClosurePrice.positive', 'positive')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


d = require('ExtendedSmoothStationarity.restricted_stationarity', '{J : E → EReal}',
            '(hJ : Convex ℝ (epigraph A J))', '(hmin :', '(hk : HasFDerivAt g k star)', 'SubgradientOn A J star (-k)')
assert 'ConvexOn' not in d and 'FiniteDimensional' not in d
require('ExtendedSmoothStationarity.qualified_stationarity', 'FiniteDimensional ℝ E', 'intrinsicInterior ℝ',
        'Subgradient J star q', 'NormalCone A star η', 'q + k + η = 0')
require('GeneralMatrixPrice.tracePrice_apply', '(tracePrice P) H =', '(P * ↑H).trace')
require('GeneralMatrixPrice.tracePrice_priceMatrix', 'priceMatrix ↑price', '= price')
for name in ['matrix_price', 'matrix_price_nonzero']:
    d = require('GeneralMatrixPrice.'+name, '{Xi : E →', 'Symmetric m', '(hXi : LoewnerConvexOn A Xi)',
                'epigraph A J', '(hstar :', 'PrimalOptimum A J Xi positive B star',
                '(hslater : (↑B - ↑(Xi x₀)).PosDef)', 'P.PosSemidef',
                'DualCertificate A J Xi positive B (tracePrice P) star',
                'dualValue A J Xi B (tracePrice P) =', 'value A J Xi positive B', '≠ ⊤', '≠ ⊥')
    for forbidden in ['HasFDerivAt', 'Differentiable', 'AffineMap', '→ᵃ', '(hc :', '(hdual :', '(hfinite :']:
        assert forbidden not in d, (name, forbidden)
require('GeneralMatrixPrice.matrix_price_nonzero', 'P ≠ 0', 'positive H', 'value A J Xi positive (B + H) <')
require('GeneralMatrixPrice.certificate_trace_energy_convex', '(hXi : LoewnerConvexOn Set.univ Xi)',
        '(hc : ExtendedConeClosurePrice.DualCertificate', 'ConvexOn ℝ Set.univ', '(P * ↑(Xi x)).trace')
require('GeneralMatrixStationarity.hasFDerivAt_trace_gap', '(hXi : HasFDerivAt (fun x => ↑(Xi x))',
        "Xi' star)", 'HasFDerivAt (fun x =>', "(traceAdjoint Xi') P")
for name in ['matrix_stationarity', 'matrix_stationarity_nonzero', 'matrix_stationarity_fderiv']:
    d = require('GeneralMatrixStationarity.'+name, '{Xi : E →', 'Symmetric m', '{J : E → EReal}',
                'epigraph Set.univ J', 'intrinsicInterior ℝ (finiteDomain Set.univ J)',
                'intrinsicInterior ℝ A', '(hXi : LoewnerConvexOn A Xi)', '(hderiv :',
                'PrimalOptimum A J Xi positive B star', '(hslater : (↑B - ↑(Xi x₀)).PosDef)',
                'P.PosSemidef', 'Subgradient J star q', 'NormalCone A star η', 'traceAdjoint',
                'DualCertificate A J Xi positive B (tracePrice P) star',
                'dualValue A J Xi B (tracePrice P) =', 'value A J Xi positive B', '≠ ⊤', '≠ ⊥')
    for forbidden in ['→ᵃ', '(hc :', '(hdual :', '(hstationarity :', '(hq :', '(hη :', '(hsub :', '(hfinite :']:
        assert forbidden not in d, (name, forbidden)
require('GeneralMatrixStationarity.matrix_stationarity', 'HasFDerivAt (fun x => ↑(Xi x))', "Xi' star", "(traceAdjoint Xi') P")
require('GeneralMatrixStationarity.matrix_stationarity_nonzero', 'P ≠ 0', 'positive H', 'value A J Xi positive (B + H) <')
require('GeneralMatrixStationarity.matrix_stationarity_fderiv', 'DifferentiableAt ℝ', 'fderiv ℝ (fun x => ↑(Xi x)) star')
d = require('GeneralMatrixStationarity.matrix_nonsmooth_stationarity', '(hXi : LoewnerConvexOn Set.univ Xi)',
            'RealSubgradient (fun x => (P * ↑(Xi x)).trace) star k', 'q + k + η = 0', 'DualCertificate', 'dualValue')
assert 'HasFDerivAt' not in d and 'Differentiable' not in d
require('GeneralMatrixExamples.quartic_actual_schur', 'quartic x =', 'MatrixClosurePrice.residual 0', 'matrixScalar (x ^ 2)')
require('GeneralMatrixExamples.quartic_derivative', 'HasFDerivAt', 'quartic z', '4 * x ^ 3', 'matrixScalar')
require('GeneralMatrixExamples.quartic_actual_values', 'budget 1) = 1', 'budget 16) = 0')
require('GeneralMatrixExamples.quartic_not_quadratic', '¬∃ a b c,', 'a * x ^ 2 + b * x + c')
require('GeneralMatrixExamples.constructed_quartic_stationarity', 'P ≠ 0', 'Subgradient', 'traceAdjoint',
        '4 • matrixScalar', 'DualCertificate', 'dualValue', '(tracePrice P) = 1')
require('GeneralMatrixExamples.kink_matrix_not_differentiable', '¬DifferentiableAt ℝ', 'kinkMatrix x', '(0, 0)')
require('GeneralMatrixExamples.constructed_kink_matrix_stationarity', 'RealSubgradient', 'kinkMatrix x', 'q + k + η = 0', 'DualCertificate')
require('GeneralMatrixExamples.restricted_matrix_loewner_convex', 'LoewnerConvexOn (Set.Ici 0) restrictedMatrix')
require('GeneralMatrixExamples.missing_extension_no_trace_support', '(hp : 0 < p)', '¬∃ r,', 'RealSubgradient', 'restrictedMatrix x')
for name in ['quartic_actual_schur', 'quartic_derivative', 'quartic_actual_values', 'quartic_not_quadratic',
             'constructed_quartic_stationarity', 'kink_matrix_not_differentiable',
             'constructed_kink_matrix_stationarity', 'restricted_matrix_loewner_convex']:
    assert '(h' not in decls['GeneralMatrixExamples.'+name], name
source = read('lean/SbtCosmo/Derivation/ExtendedSmoothStationarity.lean')
for token in ['EReal.coe_toReal', 'ConvexSubgradient.remove_smooth_summand', 'epigraph_objective_convex',
              'RelativeSumSplit.split_subgradient']:
    assert token in source
source = read('lean/SbtCosmo/Derivation/GeneralMatrixPrice.lean')
for token in ['MatrixSlaterTopology.posdef_mem_interior_positive', 'ExtendedNonsmoothConePrice.slater_strong_duality',
              'price_matrix_positive', 'tracePrice_priceMatrix', 'certificate_nonzero hc hdec']:
    assert token in source
source = read('lean/SbtCosmo/Derivation/GeneralMatrixStationarity.lean')
for token in ['MatrixDifferential.hasFDerivAt_tracePair', 'ExtendedSmoothStationarity.qualified_stationarity',
              'matrix_price_nonzero', 'hderiv.hasFDerivAt', 'certificate_trace_energy_convex hXi hc',
              'ConvexSumSplit.split_extended', 'RelativeSumSplit.split_subgradient']:
    assert token in source
source = read('lean/SbtCosmo/Derivation/GeneralMatrixExamples.lean')
for token in ['Support.residual_zero_native', 'convexOn_pow', '(hasDerivAt_id x).pow 4',
              'GeneralMatrixStationarity.matrix_stationarity_nonzero', 'GeneralMatrixStationarity.matrix_nonsmooth_stationarity',
              'kink_energy_not_differentiable', 'quartic_sensitive']:
    assert token in source
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8144 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.ScalarStationarityExamples]',
    '`SbtCosmo.Derivation.ScalarStationarityExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
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
          'Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean',
          'Mathlib/Analysis/Convex/Function.lean', 'Mathlib/Analysis/Convex/Intrinsic.lean',
          'Mathlib/Analysis/Calculus/Deriv/Abs.lean', 'Mathlib/Analysis/Calculus/LocalExtr/Basic.lean',
          'Mathlib/Data/EReal/Operations.lean', 'Mathlib/Analysis/Convex/Mul.lean',
          'Mathlib/Analysis/Calculus/LineDeriv/Basic.lean']:
    source = (libroot / p).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = digest(source)
files = set(prior['source_sha256']) | {prior_path, 'math/DERIVATION_LT1_2026-06-02.md'}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_general_matrix_verify.py', 'math/GENERAL_MATRIX_STATIONARITY_LEAN_2026-10-03.md',
              'lean/manifests/check_general_matrix_statements.lean', 'lean/manifests/check_general_matrix_axioms.lean',
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
    'scope': 'Corrected general smooth matrix/Loewner Theorem S, qualified nonsmooth extension and actual nonlinear Schur return',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8144, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_general_matrix_axioms.lean',
                    'success': True, 'declarations_cumulative': 1158, 'declarations_fresh': 28,
                    'declarations_preserved': 1130, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_general_matrix_statements.lean',
                        'success': True, 'declarations': 28, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'corrected_LT1_general_smooth_matrix_Theorem_S': True,
        'original_target_source': 'math/DERIVATION_LT1_2026-06-02.md section2.3',
        'map': 'arbitrary Xi:E->original symmetric matrix space, Loewner-convex on A',
        'original_extended_objective': True, 'no_affine_or_quadratic_map_restriction': True,
        'price': 'earned cone-positive whole-budget functional, earned PSD continuous trace representative',
        'Slater_local_finite_value_guards_earned': True, 'value_derivative_premise': False,
        'original_certificate_and_finite_EReal_strong_duality': True,
        'nonzero_price': 'actual strict complete-lattice value decrease in PSD budget direction',
        'competing_minus_infinity_safe': True, 'whole_matrix_activity_claimed': False,
        'local_smooth_removal': 'convex extended objective and actual local smooth summand derivative, no summand convexity',
        'actual_common_RI_qualification': True,
        'general_matrix_derivative_premise': 'actual HasFDerivAt of Xi at optimizer, legitimate original theorem hypothesis',
        'trace_Lagrangian_derivative_earned': True, 'fixed_budget_derivative_zero': True,
        'full_stationarity': 'q+traceAdjoint(actual_Xi_derivative)P+eta=0',
        'fderiv_only_after_actual_DifferentiableAt': True,
        'final_price_objective_support_normal_stationarity_dual_premises': False,
        'smooth_endpoint_requires_ambient_matrix_convex_extension': False,
        'nonsmooth_endpoint': 'finite ambient Loewner-convex extension earns actual scalar trace-energy support',
        'nonsmooth_derivative_premise': False,
        'nonlinear_Schur_example': 'actual Support residual native0/probe x^2 equals matrix[x^4]',
        'actual_quartic_derivative': '4*x^3 times actual scalar-to-matrix CLM',
        'actual_quartic_optimizers_values': 'star1/value1 at budget1; star2/value0 at budget16',
        'actual_quartic_nonzero_stationarity_certificate_dual1': True,
        'actual_entry_not_quadratic_proved': True,
        'nonsmooth_matrix_example': '[x+abs(y)] has no matrix derivative at optimizer0; full nonsmooth stationarity constructed',
        'nonsmooth_example_is_general_Loewner_map_not_adequacy_PSD_content': True,
        'off_A_control': 'convexity on A=[0,infinity) cannot supply ambient trace support for arbitrary continuation',
        'off_A_control_refutes_smooth_theorem': False,
        'primal_attainment_derived': False, 'matrix_price_uniqueness_claimed': False,
        'moving_native_calculus_mechanized': False, 'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Matrix sensitivity/price identification if needed; remaining original-target coverage audit and feasible constructions',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1158 ordered cumulative standard-only closures (1130 immutable + 28 fresh), general matrix stationarity and actual nonlinear Schur/scope controls; {len(hashes)} fingerprints')
