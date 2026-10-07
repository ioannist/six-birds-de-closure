"""Verify constructed scalar convex closure price and actual Schur return evidence."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '85ef263'
packet = 'results/convex_closure_price_2026-10-03/'
mods = ['ConvexClosurePrice', 'SchurClosurePrice', 'SchurClosurePriceExamples']

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
assert len(new) == 34
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 895 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_convex_closure_price_axioms.lean'), re.M) == new
prior_path = 'results/allocation_sensitivity_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_allocation_sensitivity_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_convex_closure_price_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_convex_closure_price_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 895-declaration raw prefix plus freshly audited 34-declaration suffix.\n'
          'Baseline: 85ef263; earlier proof-source/toolchain identity checked by de_convex_closure_price_verify.py.\n'
          'Full 929-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_convex_closure_price_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
compact = ' '.join(statements.split())
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(ConvexClosurePrice|SchurClosurePrice|SchurClosurePriceExamples)\.(\w+)', statements, re.M))
declarations = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for required in [
    'ConvexClosurePrice.strict_sensitivity_forces_activity',
    'ConvexClosurePrice.positive_price_certificate', 'price = -d ∧ 0 < price',
    'ConvexClosurePrice.certificate_dual_isGLB', 'ConvexClosurePrice.weak_duality',
    'ConvexClosurePrice.certificate_strong_duality', 'ConvexClosurePrice.certificate_price_identification',
    'SchurClosurePrice.affine_schur_energy_convex', 'SchurClosurePrice.positive_schur_price',
    'SchurClosurePrice.original_lagrangian_return',
    'SchurClosurePriceExamples.actual_value_derivative', 'SchurClosurePriceExamples.actual_positive_schur_certificate',
    'SchurClosurePriceExamples.actual_slater_and_singular_native', 'SchurClosurePriceExamples.varying_native_nonconvex',
]:
    assert required in compact, required
for name in ['derivative_global_support', 'strict_sensitivity_forces_activity', 'positive_price_certificate']:
    decl = declarations['ConvexClosurePrice.'+name]
    assert '(hJ : ConvexOn ℝ A J)' in decl and '(he : ConvexOn ℝ A energy)' in decl
    assert 'PrimalOptimum A J energy B star' in decl
    assert '(hfinite : ∀ T ∈ Set.Ioo lo hi,' in decl and ').Nonempty' in decl and 'BddBelow' in decl
    assert 'HasDerivAt (SbtCosmo.Derivation.ConvexClosurePrice.budgetValue A J energy) d B' in decl
    assert 'hactive' not in decl and 'hdual' not in decl
assert '(hs : d < 0)' in declarations['ConvexClosurePrice.positive_price_certificate']
assert 'energy star = B' in declarations['ConvexClosurePrice.strict_sensitivity_forces_activity']
assert 'BddBelow' in declarations['ConvexClosurePrice.weak_duality']
assert 'DualCertificate' in declarations['ConvexClosurePrice.certificate_strong_duality']
schur = declarations['SchurClosurePrice.positive_schur_price']
assert '(hW : W.PosSemidef)' in schur and '(D : E →ᵃ[ℝ]' in schur
assert '(he :' not in schur and '(hactive :' not in schur and 'hfinite' in schur and 'HasDerivAt' in schur
assert 'HasDerivAt' in declarations['SchurClosurePriceExamples.actual_value_derivative']
assert '(-1) 1' in declarations['SchurClosurePriceExamples.actual_value_derivative']
assert 'DualCertificate Set.univ' in declarations['SchurClosurePriceExamples.actual_positive_schur_certificate']
assert '¬ConvexOn ℝ Set.univ' in declarations['SchurClosurePriceExamples.varying_native_nonconvex']

build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8107 jobs).' in build and not re.search(r'error:|warning:', build)

# Immutable prior artifacts and frozen paper/runtime. Current metadata may grow.
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
# Only default derivation roots have been extended in the build configuration.
old_config = git_blob(baseline, 'lean/lakefile.lean').decode()
expected_config = old_config.replace('`SbtCosmo.Derivation.AllocationSensitivity]',
    '`SbtCosmo.Derivation.AllocationSensitivity, `SbtCosmo.Derivation.ConvexClosurePrice, `SbtCosmo.Derivation.SchurClosurePrice, `SbtCosmo.Derivation.SchurClosurePriceExamples]')
assert read('lean/lakefile.lean') == expected_config

for mod in mods:
    assert '`SbtCosmo.Derivation.' + mod in read('lean/lakefile.lean')

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root / 'lean/.lake/packages/mathlib').decode().strip() == mathlib['revision']
# Verify every prior direct import before extending the cumulative source map.
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
for path in ['Mathlib/Analysis/Convex/Function.lean', 'Mathlib/Analysis/Calculus/Deriv/Slope.lean',
             'Mathlib/Analysis/Calculus/LocalExtr/Basic.lean',
             'Mathlib/Order/ConditionallyCompleteLattice/Basic.lean',
             'Mathlib/LinearAlgebra/Matrix/Trace.lean', 'Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean',
             'Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean']:
    source = (root / 'lean/.lake/packages/mathlib' / path).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root / 'lean/.lake/packages/mathlib')
    mathlib['direct_proof_source_sha256'][path] = digest(source)
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_convex_closure_price_verify.py',
              'math/CONVEX_CLOSURE_PRICE_LEAN_2026-10-03.md', 'lean/manifests/check_convex_closure_price_statements.lean',
              'lean/manifests/check_convex_closure_price_axioms.lean', new_path, combined_path])
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
    'scope': 'Construct scalar convex price from actual infimum derivative; derive activity and instantiate actual Schur energy',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8107, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_convex_closure_price_axioms.lean',
                    'success': True, 'declarations_cumulative': 929, 'declarations_fresh': 34,
                    'declarations_preserved': 895, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_convex_closure_price_statements.lean',
                        'success': True, 'declarations': 34, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'actual_primal_budget_value': 'sInf of nonempty bounded-below feasible objective costs',
        'objective_domain': 'real-valued convex objective on a convex admissible domain',
        'generic_primal_assumptions': ['objective convexity', 'energy convexity', 'ordinary primal optimum',
                                      'value finite on an open budget neighborhood', 'actual infimum value derivative d<0'],
        'dual_or_value_support_input_assumed': False, 'activity_input_assumed': False,
        'activity_derived': True, 'positive_price_constructed': '-d',
        'certificate': 'nonnegative price, membership, feasibility, complementarity, global Lagrangian minimum',
        'actual_finite_primal_dual_infimum_equality': True,
        'dual_infimum_guards_derived_for_certificate': True, 'competing_dual_weak_bound': 'nonnegative competing price and bounded-below Lagrangian image',
        'any_dual_price_identified_with_actual_derivative': True,
        'schur_energy': 'trace(W*Support.residual L D), constructed generalized Gram inverse',
        'affine_schur_energy_convexity_derived': 'fixed native probes L, fixed PSD audit W, affine dissolving probes D',
        'singular_native_Gram_blocks_allowed': True, 'unchanged_positiveDefinite_schur_and_lagrangian_return': True,
        'unconditional_schur_example': 'L=0,W=1,D(x)=x,J(x)=(x-2)^2,Omega=1; optimizer1, value1, derivative-1, price1, Slaterx0',
        'example_value_and_derivative_supplied': False,
        'varying_native_false_convexity_control': 'L(x)=x,D=1,W=1; energies at +1,-1 are0 and at0 is1',
        'extended_real_subdifferential_sum_rules_mechanized': False,
        'matrix_Loewner_dual_construction_mechanized': False,
        'Slater_alone_used_to_assume_local_finite_differentiable_value': False,
        'physical_lambda_identification': False,
    },
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'Adversarial self-review; no independent mathematical reviewer',
    'next_construction': 'Further extended-objective/normal-cone or Loewner closure-price returns, or exact robustness ratios; prior physical and contradicted claim boundaries remain',
    'goal_complete': False, 'source_sha256': hashes,
    'source_byte_representation': 'Working checkout bytes; canonical Git blob hashes checked separately',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'929 ordered cumulative standard-only closures (895 immutable + 34 fresh), 34 statement domains/actual infimum and Schur controls checked; {len(hashes)} fingerprints.')
