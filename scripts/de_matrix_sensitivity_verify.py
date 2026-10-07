"""Verify whole matrix-price sensitivity, uniqueness and same-price stationarity with actual returns."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'b059931'
packet = 'results/matrix_sensitivity_2026-10-03/'
mods = ['ConePriceSensitivity', 'MatrixPriceSensitivity', 'MatrixSensitivityStationarity', 'MatrixSensitivityExamples']


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
assert len(new) == 26
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1158 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_matrix_sensitivity_axioms.lean'), re.M) == new
prior_path = 'results/general_matrix_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_general_matrix_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_matrix_sensitivity_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_matrix_sensitivity_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1158-declaration raw prefix plus freshly audited 26-declaration suffix.\n'
          'Baseline: b059931; earlier proof-source/toolchain identity checked by de_matrix_sensitivity_verify.py.\n'
          'Full 1184-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_matrix_sensitivity_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['ConvexSubgradient', 'ExtendedClosurePrice', 'SchurDifferential', 'GeneralMatrixPrice', 'GeneralMatrixExamples', 'MatrixPriceRepresentation', 'MatrixClosurePriceExamples', 'ScalarStationarityExamples', 'ExtendedClosurePriceExamples']:
        d = d.replace(group + '.', '')
    d = d.replace('MatrixClosurePrice.positive', 'positive')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


# Semantic checks inspect actual exported declarations, not just catalog names.
d = require('ConePriceSensitivity.real_price_identification', '{E : Type', '{F : Type',
            'ConeClosurePrice.DualCertificate', '(hne :', 'feasibleCosts', '(hd : HasFDerivAt', 'price = -d')
assert 'Convex' not in d and 'FiniteDimensional' not in d
require('ConePriceSensitivity.certificate_real_domain_return', '{J : E → EReal}', 'J x ≠ ⊥',
        'ExtendedConeClosurePrice.DualCertificate', 'finiteDomain A J', 'realObjective J')
for name in ['price_identification','price_unique']:
    require('ConePriceSensitivity.'+name, '(hfinite :', 'value A J energy positive T ≠ ⊤',
            'value A J energy positive T ≠ ⊥', '(hd : HasFDerivAt', ').toReal) d B)')
require('ConePriceSensitivity.price_unique', '{star other : E}', 'price = otherPrice')
d = require('ConePriceSensitivity.slater_local_finiteness', '(hstar :', 'PrimalOptimum',
            '(hJ : Convex ℝ (epigraph A J))', '(hslater : B - energy x₀ ∈ interior',
            'value A J energy positive T ≠ ⊤', 'value A J energy positive T ≠ ⊥')
assert 'HasFDerivAt' not in d and 'FiniteDimensional' not in d and '(hfinite :' not in d
require('ConePriceSensitivity.slater_price_identification', '(hprice :', 'DualCertificate', '(hslater :',
        'interior', '(hd : HasFDerivAt', 'price = -d')
require('MatrixPriceSensitivity.priceMatrix_tracePrice', '(hP : P.IsHermitian)',
        'priceMatrix ↑(tracePrice P) = P')
require('MatrixPriceSensitivity.tracePrice_injective', '(hP : P.IsHermitian)', '(hQ : Q.IsHermitian)',
        'tracePrice P = tracePrice Q', 'P = Q')
require('MatrixPriceSensitivity.certificate_price_identification', '(hc :', '(hfinite :',
        'HasFDerivAt', ').toReal)', 'tracePrice P = -d')
require('MatrixPriceSensitivity.certificate_matrix_identification', '(hP : P.PosSemidef)',
        'P = priceMatrix ↑(-d)', '(P * ↑H).trace = -d H')
require('MatrixPriceSensitivity.certificate_matrix_unique', '{star other : E}', '(hP : P.PosSemidef)',
        '(hQ : Q.PosSemidef)', '(hc :', '(ho :', '(hfinite :', 'HasFDerivAt', 'P = Q')
d = require('MatrixPriceSensitivity.slater_price_identification', '(hXi : LoewnerConvexOn A Xi)',
            '(hslater : (↑B - ↑(Xi x₀)).PosDef)', 'HasFDerivAt', 'tracePrice P = -d')
assert '(hfinite :' not in d and 'FiniteDimensional' not in d
for name in ['matrix_stationarity','matrix_nonsmooth_stationarity']:
    d = require('MatrixSensitivityStationarity.'+name, '{J : E → EReal}',
                'epigraph Set.univ J', 'intrinsicInterior ℝ (finiteDomain Set.univ J)',
                'intrinsicInterior ℝ A', '(hstar :', 'PrimalOptimum A J Xi positive B star',
                '(hslater : (↑B - ↑(Xi x₀)).PosDef)', '(hd : HasFDerivAt', ').toReal)',
                '(hsensitive : ∃ H, positive H ∧ d H < 0)', 'P.PosSemidef', 'P ≠ 0',
                'tracePrice P = -d', 'P = priceMatrix ↑(-d)', '(P * ↑H).trace = -d H',
                'Subgradient J star q', 'NormalCone A star η', '(P * (↑(Xi star) - ↑B)).trace = 0',
                'DualCertificate A J Xi positive B (tracePrice P) star',
                'dualValue A J Xi B (tracePrice P) = ExtendedConeClosurePrice.value A J Xi positive B')
    for forbidden in ['(hfinite :','(hc :','(hdual :','(hq :','(hη :','(hstationarity :','→ᵃ']:
        assert forbidden not in d, (name,forbidden)
require('MatrixSensitivityStationarity.matrix_stationarity', '(hXi : LoewnerConvexOn A Xi)',
        '(hderiv : HasFDerivAt (fun x => ↑(Xi x)) Xi\' star)',
        'q + (traceAdjoint Xi\') P + η = 0', '≠ ⊤', '≠ ⊥')
d = require('MatrixSensitivityStationarity.matrix_nonsmooth_stationarity',
            '(hXi : LoewnerConvexOn Set.univ Xi)', 'RealSubgradient (fun x => (P * ↑(Xi x)).trace) star k',
            'q + k + η = 0')
assert '(hderiv :' not in d and 'DifferentiableAt' not in d
require('MatrixSensitivityExamples.actual_optimizer', 'PrimalOptimum Set.univ', 'objective', 'energy', '(budget 1) 1')
require('MatrixSensitivityExamples.actual_slater', '(↑(budget 1) - ↑(energy 0)).PosDef')
require('MatrixSensitivityExamples.actual_schur_derivative', 'HasFDerivAt (fun x => ↑(energy x)) (2 • matrixScalar) 1')
require('MatrixSensitivityExamples.tracePrice_one', 'tracePrice 1 = coordinate')
d = require('MatrixSensitivityExamples.actual_price_identified', '(hP : P.PosSemidef)', '{star : ℝ}',
            '(hc :', 'DualCertificate', '(budget 1) (tracePrice P) star', 'P = 1')
assert '(hfinite :' not in d and 'HasFDerivAt' not in d
require('MatrixSensitivityExamples.actual_same_price_stationarity', 'Subgradient', 'objective 1 q',
        'NormalCone Set.univ 1 η', 'q + (traceAdjoint (2 • matrixScalar)) 1 + η = 0',
        'DualCertificate', '(budget 1) (tracePrice 1) 1', 'dualValue', '(tracePrice 1) = 1')
require('MatrixSensitivityExamples.antisymmetric_price_control', 'A ≠ 0 ∧ tracePrice A = 0')
require('MatrixSensitivityExamples.one_direction_control', 'P.PosSemidef ∧ Q.PosSemidef ∧ H.PosSemidef ∧ P ≠ Q ∧ (P * H).trace = (Q * H).trace')
require('MatrixSensitivityExamples.kink_matrix_feasible', 'positive (B - kinkMatrix x)', 'kinkEnergy x ≤ coordinate B')
require('MatrixSensitivityExamples.kink_actual_value', 'ExtendedConeClosurePrice.value', 'kinkObjective', 'kinkMatrix positive B = ↑(-coordinate B)')
require('MatrixSensitivityExamples.kink_value_derivative', 'HasFDerivAt', 'kinkMatrix positive T).toReal)', '(-coordinate) B')
require('MatrixSensitivityExamples.actual_nonsmooth_same_price_stationarity', 'Subgradient', 'kinkObjective (0, 0) q',
        'RealSubgradient', 'kinkMatrix x', 'q + k + η = 0', 'DualCertificate', 'dualValue', '(tracePrice 1) = 0')
for name in ['actual_optimizer','actual_slater','actual_schur_derivative','tracePrice_one',
             'actual_same_price_stationarity','antisymmetric_price_control','one_direction_control',
             'kink_matrix_feasible','kink_actual_value','kink_value_derivative','actual_nonsmooth_same_price_stationarity']:
    assert '(h' not in decls['MatrixSensitivityExamples.'+name], name
source_checks = {
 'ConePriceSensitivity': ['NonsmoothConePrice.certificate_value_support', 'hm.hasFDerivAt_eq_zero',
    'EReal.coe_toReal', 'finite_value_domain_return', 'NonsmoothConePrice.slater_local_finiteness', 'value_domain_return'],
 'MatrixPriceSensitivity': ['Matrix.trace_mul_single', 'priceMatrix_tracePrice hP.1',
    'ConePriceSensitivity.price_unique', 'MatrixSlaterTopology.posdef_mem_interior_positive'],
 'MatrixSensitivityStationarity': ['GeneralMatrixStationarity.matrix_stationarity',
    'GeneralMatrixStationarity.matrix_nonsmooth_stationarity', 'slater_price_identification',
    'priceMatrix_tracePrice hP.1', 'hrestricted', 'rw [hz,zero_mul,trace_zero]'],
 'MatrixSensitivityExamples': ['ExtendedMatrixClosurePriceExamples.actual_value_derivative',
    'MatrixSensitivityStationarity.matrix_stationarity', 'MatrixSensitivityStationarity.matrix_nonsmooth_stationarity',
    'tracePrice_injective', 'kink_primal_optimum', 'ExtendedConeClosurePrice.optimum_value hs',
    'coordinate.hasFDerivAt.neg', 'actual_price_identified hP hc']}
for mod,tokens in source_checks.items():
    source=read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    for token in tokens:
        assert token in source,(mod,token)
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8148 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.GeneralMatrixExamples]',
    '`SbtCosmo.Derivation.GeneralMatrixExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
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
files.update(['scripts/de_matrix_sensitivity_verify.py', 'math/MATRIX_SENSITIVITY_LEAN_2026-10-03.md',
              'lean/manifests/check_matrix_sensitivity_statements.lean', 'lean/manifests/check_matrix_sensitivity_axioms.lean',
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
    'scope': 'Whole matrix-price sensitivity identification, uniqueness and same-price smooth/nonsmooth stationarity',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8148, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_matrix_sensitivity_axioms.lean',
                    'success': True, 'declarations_cumulative': 1184, 'declarations_fresh': 26,
                    'declarations_preserved': 1158, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_matrix_sensitivity_statements.lean',
                        'success': True, 'declarations': 26, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'target': 'full original matrix value derivative identifies whole symmetric price and same-price stationarity',
        'original_extended_value_derivative': True,
        'local_finiteness_earned_from_Slater': True,
        'whole_budget_derivative_required': True,
        'price_identity': 'tracePriceP=-d and P=priceMatrix(-d)',
        'PSD_certificate_matrix_uniqueness_across_optimizers': True,
        'optimizer_or_stationarity_support_uniqueness': False,
        'same_price_sensitivity_stationarity_complementarity_certificate_strong_duality': True,
        'nonzero_price': 'strict negative actual derivative in PSD direction',
        'smooth_Xi_convex_only_on_A': True,
        'smooth_Xi_derivative_actual_premise': True,
        'nonsmooth_ambient_finite_Loewner_extension_explicit': True,
        'nonsmooth_Xi_derivative_premise': False,
        'actual_Schur_example': 'original extended objective, Xi[x^2], canonical P1, actual adjoint stationarity, dual1',
        'actual_nonsmooth_example': 'Xi[x+abs(y)], full actual V=-coordinate, derivative=-coordinate, P1, stationarity, dual0',
        'actual_nonsmooth_example_is_adequacy_PSD_content': False,
        'controls': ['nonzero antisymmetric price invisible on symmetric budgets',
                     'distinct PSD prices agree on one PSD budget direction'],
        'primal_attainment_derived': False, 'moving_native_calculus_mechanized': False,
        'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Broader original-target coverage audit and feasible outstanding toy constructions',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1184 ordered cumulative standard-only closures (1158 immutable + 26 fresh), matrix sensitivity identification and same-price stationarity with actual Schur/nonsmooth returns; {len(hashes)} fingerprints')
