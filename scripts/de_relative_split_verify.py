"""Verify the earned relative-interior extended objective/normal split and Schur return."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '2a63edc'
packet = 'results/relative_split_2026-10-03/'
mods = ['RelativeConvexContinuity', 'RelativeDifference', 'RelativeEqualitySupport',
        'RelativeSumSplit', 'RelativeSchurStationarity', 'RelativeSplitExamples']


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
assert len(new) == 27
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1056 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_relative_split_axioms.lean'), re.M) == new
prior_path = 'results/stationarity_split_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_stationarity_split_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_relative_split_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_relative_split_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1056-declaration raw prefix plus freshly audited 27-declaration suffix.\n'
          'Baseline: 2a63edc; earlier proof-source/toolchain identity checked by de_relative_split_verify.py.\n'
          'Full 1083-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_relative_split_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['ConvexSubgradient', 'ExtendedClosurePrice', 'RelativeSplitExamples']:
        d = d.replace(group + '.', '')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


require('RelativeConvexContinuity.continuousOn_intrinsicInterior',
        'ConvexOn ℝ C f', 'ContinuousOn f (intrinsicInterior ℝ C)', 'FiniteDimensional ℝ E')
require('RelativeDifference.local_bounded_witnesses', 'intrinsicInterior ℝ C', 'intrinsicInterior ℝ A',
        'direction ⊔', '∃ x ∈ C, ∃ y ∈ A, x - y =', 'f x ≤ f x₀ + 1')
require('RelativeEqualitySupport.local_finiteness', 'BddBelow', 'feasibleCosts', 'energy z = 0', 'f z ≤ M')
require('RelativeEqualitySupport.supporting_functional', '∃ d, ∀ z ∈ T, f star + d (energy z) ≤ f z')
split = require('RelativeSumSplit.split_subgradient', '{J : E → EReal}', 'epigraph Set.univ J',
                'intrinsicInterior ℝ (finiteDomain Set.univ J)', 'intrinsicInterior ℝ A',
                'SubgradientOn A J star p', 'Subgradient J star q', 'NormalCone A star n ∧ q + n = p')
for name in ['RelativeSumSplit.split_real_relative', 'RelativeSumSplit.split_subgradient',
             'RelativeSumSplit.subgradient_sum_iff', 'RelativeSumSplit.subgradient_add_indicator_iff']:
    d = decls[name]
    for forbidden in ['(hfinite :', '(hupper :', '(hsplit :', '(hn :', '(hq :', '(hdual :', 'HasFDerivAt']:
        assert forbidden not in d, (name, forbidden)
require('RelativeSumSplit.subgradient_sum_iff', 'restriction A J', '↔', 'q + n = p')
require('RelativeSumSplit.objective_indicator_eq_restriction', '∀ (x : E), J x ≠ ⊥',
        'J x +', 'indicator A x', '= restriction A J')
require('RelativeSumSplit.subgradient_add_indicator_iff', 'J x +', 'indicator A x', '↔', 'Subgradient J star q')
for name in ['matrix_stationarity', 'matrix_stationarity_nonzero']:
    d = require('RelativeSchurStationarity.'+name, '{J : E → EReal}', '(D : E →ᵃ[ℝ]',
                'epigraph Set.univ J', 'intrinsicInterior ℝ (finiteDomain Set.univ J)',
                'intrinsicInterior ℝ A', 'P.PosSemidef', 'Subgradient J star q', 'NormalCone A star n_1',
                'fderiv ℝ', ').PosDef)', ').trace', '= 0')
    for forbidden in ['(hsub :', '(hq :', '(hn :', '(hstationarity :', '(hdual :', 'HasFDerivAt']:
        assert forbidden not in d, (name, forbidden)
require('RelativeSchurStationarity.matrix_stationarity_nonzero', 'P ≠ 0',
        'ExtendedConeClosurePrice.value', '(B + H) <')
require('RelativeSplitExamples.objective_relative_interior', 'intrinsicInterior ℝ', '= ↑line')
require('RelativeSplitExamples.objective_ambient_interior_empty', 'interior (finiteDomain Set.univ objective) = ∅')
example = require('RelativeSplitExamples.constructed_lower_dimensional_split',
                  'Subgradient objective 0 q', 'NormalCone {0} 0 n', 'q + n = 0 ∧ q ≠ 0')
assert '(h' not in example
sum_source = read('lean/SbtCosmo/Derivation/RelativeSumSplit.lean')
for token in ['RelativeDifference.local_bounded_witnesses', 'RelativeEqualitySupport.supporting_functional',
              'Real.exists_extension_norm_eq', 'epigraph_objective_convex', 'EReal.coe_toReal']:
    assert token in sum_source
schur_source = read('lean/SbtCosmo/Derivation/RelativeSchurStationarity.lean')
assert 'SchurStationarity.matrix_restricted_stationarity' in schur_source and 'RelativeSumSplit.split_subgradient' in schur_source
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8133 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.StationarityExamples]',
    '`SbtCosmo.Derivation.StationarityExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot / p).read_bytes()) == h
for p in ['Mathlib/Analysis/Convex/Intrinsic.lean', 'Mathlib/Analysis/Convex/Continuous.lean',
          'Mathlib/Analysis/Normed/Module/HahnBanach.lean', 'Mathlib/Analysis/Normed/Affine/Isometry.lean',
          'Mathlib/Topology/Algebra/Module/ModuleTopology.lean', 'Mathlib/Topology/Algebra/Module/FiniteDimension.lean',
          'Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Basic.lean',
          'Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean', 'Mathlib/Topology/ContinuousOn.lean',
          'Mathlib/Topology/Homeomorph/Defs.lean', 'Mathlib/Algebra/Module/Submodule/Lattice.lean']:
    source = (libroot / p).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_relative_split_verify.py', 'math/RELATIVE_SPLIT_LEAN_2026-10-03.md',
              'lean/manifests/check_relative_split_statements.lean', 'lean/manifests/check_relative_split_axioms.lean',
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
    'scope': 'Earned general relative-interior-qualified ambient extended objective/normal split and actual Schur stationarity',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8133, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_relative_split_axioms.lean',
                    'success': True, 'declarations_cumulative': 1083, 'declarations_fresh': 27,
                    'declarations_preserved': 1056, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_relative_split_statements.lean',
                        'success': True, 'declarations': 27, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'qualification': 'actual common point in intrinsicInterior of original finite domain and convex admissibility',
        'relative_convex_continuity': 'constructed using actual affine-span direction chart and inducing subtype topology',
        'actual_budget_space': 'sum of the actual two affine-span directions, possibly proper ambient subspace',
        'bounded_cost_witnesses': 'earned by chart continuity and openness of constructed surjective difference map',
        'actual_infimum_guards': 'earned by midpoint mixing with bounded-cost opposite witnesses',
        'actual_support': 'prior nonsmooth actual equality-cost value separation and global primal mixing',
        'ambient_extension': 'imported real Hahn-Banach exact continuous extension, not supplied',
        'arbitrary_restricted_support_split': 'subtract/restore actual linear functional, original domains unchanged',
        'extended_return': 'original finite-domain epigraph convexity and all original top-cost points',
        'literal_objective_indicator_identity_proved': True,
        'general_relative_interior_extended_objective_normal_split_mechanized': True,
        'sum_rule_bidirectional': True, 'finite_everywhere_objective_required': False,
        'ambient_full_dimensional_domain_required': False, 'local_finite_value_or_split_supplied': False,
        'actual_extended_Schur_full_stationarity': 'ambient objective support + genuine actual trace derivative + admissibility normal = zero',
        'actual_Schur_derivative_or_stationarity_supplied': False,
        'nonzero_matrix_price': 'strict decrease of original complete-lattice value in PSD budget direction',
        'lower_dimensional_example': 'computed line-domain relative interior, empty ambient interior, forced nonzero objective support/cancelling normal',
        'example_final_statement_zero_premises': True,
        'matrix_jacobian_adjoint_formula_mechanized': False, 'primal_attainment_derived': False,
        'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Explicit matrix Jacobian/adjoint return for actual affine-probe fixed-native Schur residual',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1083 ordered cumulative standard-only closures (1056 immutable + 27 fresh), 27 relative split/Schur/domain statements; {len(hashes)} fingerprints')
