"""Verify derivative-free Slater dual construction and actual extended Schur matrix return."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'e40938d'
packet = 'results/nonsmooth_price_2026-10-03/'
mods = ['ConvexValueSupport', 'NonsmoothConePrice', 'MatrixSlaterTopology',
        'ExtendedNonsmoothConePrice', 'NonsmoothMatrixPrice', 'NonsmoothPriceExamples']

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
assert len(old_names) == 1003 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_nonsmooth_price_axioms.lean'), re.M) == new
prior_path = 'results/extended_matrix_price_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_extended_matrix_price_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_nonsmooth_price_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_nonsmooth_price_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1003-declaration raw prefix plus freshly audited 27-declaration suffix.\n'
          'Baseline: e40938d; earlier proof-source/toolchain identity checked by de_nonsmooth_price_verify.py.\n'
          'Full 1030-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_nonsmooth_price_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
support = decls['ConvexValueSupport.supporting_functional']
for token in ['[FiniteDimensional ℝ F]', '(hU : IsOpen U)', '(hf : ConvexOn ℝ U f)', '(hB : B ∈ U)', '∃ d, ∀ T ∈ U, f B + d (T - B) ≤ f T']:
    assert token in support, token
assert 'HasFDerivAt' not in support and '(hcont :' not in support
convex = decls['NonsmoothConePrice.value_convex']
assert 'feasibleCosts A J energy positive T).Nonempty' in convex and 'BddBelow' in convex
assert 'ConvexOn ℝ U (SbtCosmo.Derivation.ConeClosurePrice.value A J energy positive)' in convex
local = decls['NonsmoothConePrice.slater_local_finiteness']
assert '(hslater : B - energy x₀ ∈ interior {H | positive H})' in local
assert 'Nonempty' in local and 'BddBelow' in local and '(hfinite :' not in local
for mod in ['NonsmoothConePrice', 'ExtendedNonsmoothConePrice']:
    d = decls[mod+'.slater_price_certificate']
    assert 'PrimalOptimum A J energy positive B star' in d
    assert 'interior {H | positive H}' in d and '∃ price,' in d and 'DualCertificate' in d
    for forbidden in ['HasFDerivAt', '(hfinite :', '(hsupport :', '(hdual :', '(hactive :']:
        assert forbidden not in d, (mod, forbidden)
    src = read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    assert 'HasFDerivAt' not in src
extended = decls['ExtendedNonsmoothConePrice.slater_strong_duality']
for token in ['{J : E → EReal}', 'epigraph A J', '(hfinite₀ : J x₀ ≠ ⊤)', 'dualValue A J energy B price', '≠ ⊤', '≠ ⊥']:
    assert token in extended, token
assert '(hT :' not in decls['ExtendedNonsmoothConePrice.certificate_nonzero']
topology = decls['MatrixSlaterTopology.posdef_mem_interior_positive']
assert 'Symmetric n' in topology and '(hA : (↑A).PosDef)' in topology and 'interior' in topology and '.positive M}' in topology
matrix = decls['NonsmoothMatrixPrice.matrix_price']
for token in ['(D : E →ᵃ[ℝ]', 'Symmetric m', '{J : E → EReal}', '(hx₀ : x₀ ∈ A)', '(hfinite₀ : J x₀ ≠ ⊤)',
              '(hslater :', ').PosDef)', 'P.PosSemidef ∧', 'sInf', 'ExtendedConeClosurePrice.value', '≠ ⊤', '≠ ⊥']:
    assert token in matrix, token
for forbidden in ['HasFDerivAt', '(hfinite :', '(he :', '(hdual :', '(hactive :', '(hsupport :']:
    assert forbidden not in matrix, forbidden
nonzero = decls['NonsmoothMatrixPrice.matrix_price_nonzero']
for token in ['(hs : ∃ H,', '.positive H ∧', '.positive (B + H) <', 'P ≠ 0 ∧']:
    assert token in nonzero, token
assert '¬DifferentiableAt ℝ' in decls['NonsmoothPriceExamples.actual_value_not_differentiable']
for name in ['actual_nonsmooth_price', 'actual_extended_matrix_price']:
    example = decls['NonsmoothPriceExamples.'+name]
    assert '(h' not in example and '≠ 0 ∧' in example
assert 'dualValue' in decls['NonsmoothPriceExamples.actual_nonsmooth_price']
assert 'sInf' in decls['NonsmoothPriceExamples.actual_extended_matrix_price']
example_source = read('lean/SbtCosmo/Derivation/NonsmoothPriceExamples.lean')
assert 'NonsmoothMatrixPrice.matrix_price_nonzero' in example_source
assert 'actual_value_derivative' not in example_source and 'HasFDerivAt' not in example_source

build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8123 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.ExtendedMatrixClosurePriceExamples]',
    '`SbtCosmo.Derivation.ExtendedMatrixClosurePriceExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root / 'lean/.lake/packages/mathlib').decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
for path in ['Mathlib/Analysis/Convex/Continuous.lean', 'Mathlib/Analysis/Convex/Function.lean',
             'Mathlib/Analysis/LocallyConvex/Separation.lean', 'Mathlib/Topology/Compactness/Compact.lean',
             'Mathlib/Analysis/Matrix/Normed.lean', 'Mathlib/LinearAlgebra/Matrix/PosDef.lean',
             'Mathlib/Analysis/Calculus/Deriv/Abs.lean', 'Mathlib/Order/ConditionallyCompleteLattice/Basic.lean',
             'Mathlib/Order/CompleteLattice/Defs.lean']:
    source = (root / 'lean/.lake/packages/mathlib' / path).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root / 'lean/.lake/packages/mathlib')
    mathlib['direct_proof_source_sha256'][path] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_nonsmooth_price_verify.py', 'math/NONSMOOTH_PRICE_LEAN_2026-10-03.md',
              'lean/manifests/check_nonsmooth_price_statements.lean',
              'lean/manifests/check_nonsmooth_price_axioms.lean', new_path, combined_path])
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
    'scope': 'Nonsmooth conic Slater dual construction and original extended Schur matrix return',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8123, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_nonsmooth_price_axioms.lean',
                    'success': True, 'declarations_cumulative': 1030, 'declarations_fresh': 27,
                    'declarations_preserved': 1003, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_nonsmooth_price_statements.lean',
                        'success': True, 'declarations': 27, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'objective': 'EReal-valued, nowhere minus infinity on A, convex real epigraph',
        'domain': 'proved effective-domain convexity and objective/optimizer/certificate return',
        'actual_value': 'unchanged actual real guarded or complete-lattice EReal conic infimum',
        'value_convexity_earned': 'approximate actual feasible costs, cone-convex primal mixing',
        'support_constructed': 'actual strict-epigraph point-open Hahn-Banach, earned positive vertical coefficient',
        'value_continuity_earned': 'finite-dimensional convex open budget domain',
        'price_constructed': 'normalized separating functional, cone positivity derived from actual optimizer',
        'primal_optimum_supplied': True, 'dual_or_complementarity_supplied': False,
        'Slater_local_finite_cost_guards_earned': 'interior slack and attained optimum; midpoint uniform lower bound',
        'Slater_value_derivative_supplied': False, 'Slater_local_finite_value_supplied': False,
        'complementarity_derived': True, 'full_matrix_activity_assumed': False,
        'global_extended_lagrangian_over_original_A': True,
        'actual_extended_primal_dual_infimum_equality': True, 'dual_neither_infinity_derived': True,
        'PSD_slack_interior_earned': 'compact unit sphere, joint quadratic continuity and tube lemma on symmetric matrices',
        'actual_schur_residual': 'constructed singular-support residual with fixed L and affine D, earned Loewner convexity',
        'matrix_PSD_and_trace_return': 'prior explicit symmetrized matrix units and rank-one PSD direction tests',
        'nonzero_price': 'strict decrease of actual complete-lattice value in a PSD direction',
        'complete_kink_example': 'J=max(-x,-2x), e=x, actual V=J, not differentiable at0, Slater gives nonzero price and dual0',
        'complete_extended_matrix_example': 'actual one-by-one Schur x^2, J=(x-2)^2 on x>=0 and top otherwise, Slater/nonzero price/dual1',
        'general_nonsmooth_Slater_duality_mechanized': True,
        'matrix_extended_objective_reduction_mechanized': True,
        'primal_attainment_derived': False, 'split_subdifferentials_or_normal_cone_mechanized': False,
        'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Qualified split subgradient/normal-cone stationarity; physical identification remains parked',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1030 ordered cumulative standard-only closures (1003 immutable + 27 fresh), 27 nonsmooth-support/Slater/matrix/kink statements; {len(hashes)} fingerprints.')
