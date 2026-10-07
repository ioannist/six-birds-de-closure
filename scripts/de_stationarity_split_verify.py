"""Verify constructed sum splitting, actual Schur smoothness and qualified-scope stationarity."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '6e7db00'
packet = 'results/stationarity_split_2026-10-03/'
mods = ['ConvexSubgradient', 'ConvexSumSplit', 'SchurStationarity', 'StationarityExamples']

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
assert len(old_names) == 1030 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_stationarity_split_axioms.lean'), re.M) == new
prior_path = 'results/nonsmooth_price_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_nonsmooth_price_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_stationarity_split_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_stationarity_split_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1030-declaration raw prefix plus freshly audited 26-declaration suffix.\n'
          'Baseline: 6e7db00; earlier proof-source/toolchain identity checked by de_stationarity_split_verify.py.\n'
          'Full 1056-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_stationarity_split_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
restriction = decls['ConvexSubgradient.restricted_subgradient_iff']
assert 'Subgradient.restriction A J' in restriction and 'SubgradientOn A J star p' in restriction and '↔' in restriction
normal = decls['ConvexSubgradient.indicator_subgradient_iff']
assert 'Subgradient.indicator A' in normal and 'NormalCone A star p' in normal
unique = decls['ConvexSubgradient.smooth_real_subgradient_eq']
assert 'HasFDerivAt g d star' in unique and ': p = d' in unique
split = decls['ConvexSumSplit.split_real_of_continuous']
for token in ['(hJ : ConvexOn ℝ A J)', '(hg : ConvexOn ℝ Set.univ g)', '(hcont : Continuous g)',
              '(hmin : ∀ x ∈ A, J star + g star ≤ J x + g x)', '∃ d,', 'J star - d (x - star) ≤ J x', 'RealSubgradient g star d']:
    assert token in split, token
for forbidden in ['(hsupport :', '(hsubgradient :', '(hsplit :', '(hstationarity :']:
    assert forbidden not in split, forbidden
extended = decls['ConvexSumSplit.split_extended']
assert '{J : E → EReal}' in extended and 'epigraph A J' in extended and 'SubgradientOn A J star (-d)' in extended
finite = decls['ConvexSumSplit.finite_objective_stationarity']
for token in ['{J g : E → ℝ}', '(hJ : ConvexOn ℝ Set.univ J)', '(hk : HasFDerivAt g k star)',
              'RealSubgradient J star q', 'NormalCone A star n ∧ q + k + n = 0']:
    assert token in finite, token
for name in ['affine_probe_differentiable', 'schur_energy_differentiable', 'trace_energy_differentiable']:
    d = decls['SchurStationarity.'+name]
    assert 'Differentiable ℝ' in d and 'FiniteDimensional ℝ E' in d
    assert '(h' not in d and 'HasFDerivAt' not in d
for name in ['matrix_stationarity', 'matrix_stationarity_nonzero', 'matrix_restricted_stationarity']:
    d = decls['SchurStationarity.'+name]
    assert '(D : E →ᵃ[ℝ]' in d and '(hslater :' in d and ').PosDef)' in d
    assert 'P.PosSemidef ∧' in d and 'fderiv ℝ' in d and '.residual L (D x)' in d
    for forbidden in ['HasFDerivAt', '(hq :', '(hn :', '(hstationarity :', '(hdual :', '(hactive :']:
        assert forbidden not in d, (name, forbidden)
    if name != 'matrix_restricted_stationarity':
        assert '{J : E → ℝ}' in d and '(hJ : ConvexOn ℝ Set.univ J)' in d
        assert 'RealSubgradient J star q' in d and 'NormalCone A star n_1' in d
    else:
        assert '{J : E → EReal}' in d and 'SubgradientOn A J star (-fderiv ℝ' in d
        assert 'NormalCone' not in d
nonzero = decls['SchurStationarity.matrix_stationarity_nonzero']
assert 'P ≠ 0 ∧' in nonzero and 'ExtendedConeClosurePrice.value' in nonzero and '(B + H) <' in nonzero
for name in ['actual_nonsmooth_stationarity', 'actual_schur_stationarity']:
    d = decls['StationarityExamples.'+name]
    assert '(h' not in d and '≠ 0 ∧' in d and 'RealSubgradient' in d
assert 'NormalCone Set.univ 1 n' in decls['StationarityExamples.actual_schur_stationarity']
assert 'fderiv ℝ' in decls['StationarityExamples.actual_schur_stationarity']
assert 'SubgradientOn {0}' in decls['StationarityExamples.boundary_restricted_support']
assert '¬∃ p,' in decls['StationarityExamples.boundary_no_ambient_support']
control = decls['StationarityExamples.missing_qualification_no_split']
assert '¬∃ q n,' in control and '.Subgradient ' in control and 'NormalCone {0} 0 n' in control
assert 'epigraph Set.univ' in decls['StationarityExamples.boundary_epigraph_convex']
source = read('lean/SbtCosmo/Derivation/SchurStationarity.lean')
assert 'trace_energy_differentiable P L D B' in source and 'finite_objective_stationarity' in source
assert 'split_extended' in source and 'smooth_real_subgradient_eq' in source
assert 'actual_value_derivative' not in source

build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8127 jobs).' in build and not re.search(r'error:|warning:', build)
review = read(packet + 'self_review.txt')
assert 'Adversarial self-review, not independent review' in review

# Freeze every prior proof/evidence; only cumulative metadata may grow.
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
expected_config = old_config.replace('`SbtCosmo.Derivation.NonsmoothPriceExamples]',
    '`SbtCosmo.Derivation.NonsmoothPriceExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root / 'lean/.lake/packages/mathlib').decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
for path in ['Mathlib/Analysis/Calculus/FDeriv/Affine.lean', 'Mathlib/Analysis/Calculus/FDeriv/Mul.lean',
             'Mathlib/Analysis/Calculus/FDeriv/Pi.lean', 'Mathlib/Analysis/Calculus/LineDeriv/Basic.lean',
             'Mathlib/Analysis/Normed/Module/FiniteDimension.lean',
             'Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean', 'Mathlib/Data/Real/Sqrt.lean',
             'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean']:
    source = (root / 'lean/.lake/packages/mathlib' / path).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root / 'lean/.lake/packages/mathlib')
    mathlib['direct_proof_source_sha256'][path] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_stationarity_split_verify.py', 'math/STATIONARITY_SPLIT_LEAN_2026-10-03.md',
              'lean/manifests/check_stationarity_split_statements.lean',
              'lean/manifests/check_stationarity_split_axioms.lean', new_path, combined_path])
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
    'scope': 'Constructed finite-continuous-summand split, actual Schur smoothness and precise stationarity scope',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8127, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_stationarity_split_axioms.lean',
                    'success': True, 'declarations_cumulative': 1056, 'declarations_fresh': 26,
                    'declarations_preserved': 1030, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_stationarity_split_statements.lean',
                        'success': True, 'declarations': 26, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'ambient_subgradient': 'finite-at-star global original-objective supporting inequality',
        'restricted_subgradient': 'proved exactly partial(restriction A J), J original on A and top off A',
        'normal_cone': 'proved exactly subgradient of actual zero/top admissibility indicator, sign n(x-star)<=0',
        'finite_real_return': 'real supports iff actual EReal coercion supports',
        'split_constructed': 'actual strict finite-g hypograph and restricted-J epigraph, open Hahn-Banach separation',
        'vertical_normalization_earned': 'positive coefficient and exact star anchor by actual vertical tests/epsilon limit',
        'finite_summand_continuity': 'supplied for arbitrary normed spaces, earned from global convexity in finite dimensions',
        'ordinary_total_minimum_supplied_to_generic_split': True, 'split_or_stationarity_supplied': False,
        'extended_return': 'proved effective-domain restriction and support return to every original A point including top costs',
        'smooth_removal': 'convex primal mix plus actual line derivative', 'smooth_support_unique_derivative': True,
        'full_finite_objective_stationarity': 'ambient finite convex J, actual constraint derivative, earned admissibility normal',
        'actual_schur_smoothness': 'finite continuous affine realization and actual blind-Gram finite coordinate products',
        'final_Schur_derivative_supplied': False, 'final_Schur_stationarity_supplied': False,
        'original_matrix_price': 'prior nonsmooth actual extended Slater return, PD slack, ordinary optimum',
        'nonzero_price': 'strict decrease of original complete-lattice value in PSD budget direction',
        'actual_extended_restricted_stationarity': 'minus genuine fderiv of original trace-constraint in partial(restriction A J)',
        'matrix_jacobian_adjoint_formula_mechanized': False,
        'general_relative_interior_extended_objective_normal_split_mechanized': False,
        'complete_examples': ['nonsmooth finite objective with nonzero price and ambient objective support',
                              'original Schur x^2 finite objective with nonzero PSD price/full stationarity/complementarity'],
        'missing_qualification_control': 'convex -sqrt extended objective, singleton constrained minimizer/restricted zero support, no ambient support/full split',
        'relative_interior_control_computation_mechanized': False,
        'primal_attainment_derived': False, 'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'General relative-interior-qualified ambient extended objective/admissibility split, including lower-dimensional domains',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1056 ordered cumulative standard-only closures (1030 immutable + 26 fresh), 26 support/sum-split/Schur/stationarity/domain-control statements; {len(hashes)} fingerprints.')
