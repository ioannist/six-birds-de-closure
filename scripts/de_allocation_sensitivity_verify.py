"""Verify derived original allocation value regularity and cumulative proof evidence."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'b01df36'
packet = 'results/allocation_sensitivity_2026-10-03/'
mods = ['AllocationSensitivity']

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
assert len(new) == 21
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 874 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_allocation_sensitivity_axioms.lean'), re.M) == new
prior_path = 'results/global_starvation_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_global_starvation_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_allocation_sensitivity_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_allocation_sensitivity_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 874-declaration raw prefix plus freshly audited 21-declaration suffix.\n'
          'Baseline: b01df36; earlier proof-source/toolchain identity checked by de_allocation_sensitivity_verify.py.\n'
          'Full 895-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_allocation_sensitivity_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
compact = ' '.join(statements.split())
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.AllocationSensitivity\.(\w+)', statements, re.M))
declarations = {m.group(1): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for required in [
    'AllocationSensitivity.cost_value_hasDerivAt',
    'HasDerivAt (SbtCosmo.Derivation.AllocationPrice.costValue w c b hw hc) (-SbtCosmo.Derivation.AllocationPrice.selectedPrice w c b hw hc B) B',
    'AllocationSensitivity.cost_value_contDiffOn_one',
    'ContDiffOn ℝ 1 (SbtCosmo.Derivation.AllocationPrice.costValue w c b hw hc) (Set.Ioi 0)',
    'AllocationSensitivity.cost_value_deriv_lipschitzOn',
    'AllocationSensitivity.cost_remainder_bounds',
    'AllocationSensitivity.actual_strict_sensitivity_iff',
    'AllocationSensitivity.central_difference_price_error',
    'AllocationSensitivity.demo_actual_derivative',
    'AllocationSensitivity.changed_weights_actual_derivative',
    'AllocationSensitivity.active_zero_derivative_control',
]:
    assert required in compact, required
# Exact domains and no supplied differentiability/regularity/optimizer premise in exported returns.
for name in ['cost_value_hasDerivAt', 'cost_value_contDiffOn_one', 'cost_value_deriv_lipschitzOn',
             'cost_remainder_bounds', 'actual_strict_sensitivity_iff', 'central_difference_price_error']:
    declaration = declarations[name]
    assert '{ι : Type' in declaration and '[Fintype ι]' in declaration
    assert '(hw : ∀ (i : ι), 0 < w i)' in declaration and '(hc : ∀ (i : ι), 0 < c i)' in declaration
    assert not re.search(r'\((?:hd|hcont|hkkt|hopt)\s*:', declaration)
    if name in ['cost_value_hasDerivAt', 'actual_strict_sensitivity_iff']:
        assert '(hB : 0 < B)' in declaration
    if name == 'cost_remainder_bounds':
        assert '(hB : 0 < B) (hC : 0 < C)' in declaration
    if name == 'central_difference_price_error':
        assert '(hh : 0 < h) (hB : h < B)' in declaration
        assert 'priceModulus w c * h / 2' in declaration

build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8104 jobs).' in build and not re.search(r'error:|warning:', build)

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
expected_config = old_config.replace('`SbtCosmo.Derivation.WindowGlobalStarvation]',
    '`SbtCosmo.Derivation.WindowGlobalStarvation, `SbtCosmo.Derivation.AllocationSensitivity]')
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
for path in ['Mathlib/Analysis/Calculus/ContDiff/Deriv.lean',
             'Mathlib/Analysis/Calculus/Deriv/Basic.lean',
             'Mathlib/Analysis/Asymptotics/Lemmas.lean', 'Mathlib/Analysis/Asymptotics/Defs.lean',
             'Mathlib/Topology/MetricSpace/Lipschitz.lean']:
    source = (root / 'lean/.lake/packages/mathlib' / path).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root / 'lean/.lake/packages/mathlib')
    mathlib['direct_proof_source_sha256'][path] = digest(source)
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_allocation_sensitivity_verify.py',
              'math/ALLOCATION_SENSITIVITY_LEAN_2026-10-03.md', 'lean/manifests/check_allocation_sensitivity_statements.lean',
              'lean/manifests/check_allocation_sensitivity_axioms.lean', new_path, combined_path])
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
    'scope': 'Derived original allocation cost derivative and C1 value through active-set/active-slack switches',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8104, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_allocation_sensitivity_axioms.lean',
                    'success': True, 'declarations_cumulative': 895, 'declarations_fresh': 21,
                    'declarations_preserved': 874, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_allocation_sensitivity_statements.lean',
                        'success': True, 'declarations': 21, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'same_original_utility_and_cost_value': True, 'same_original_constructed_price_and_allocation': True,
        'all_finite_patch_families_including_empty': True, 'positive_weights_and_curvatures': True,
        'heterogeneous_offsets_allowed': True, 'budget_domain': 'B>0',
        'supplied_differentiability_or_price_continuity': False,
        'derived_price_lipschitz_modulus': 'K=sum_i(w_i+c_i)',
        'derived_cost_value_hasDerivAt': 'V_prime(B)=-selectedPrice(B)',
        'value_regularity': 'C1 with Lipschitz derivative on all positive budgets',
        'quadratic_remainder': '0<=V(C)-V(B)+p(B)*(C-B)<=K*abs(C-B)^2, all B,C>0',
        'arbitrary_active_set_switches_covered': True, 'active_slack_switch_covered': True,
        'exact_negative_derivative_iff': '0<B<S(0)',
        'central_difference_error': 'abs((V(B+h)-V(B-h))/(2*h)+p(B))<=K*h/2 for 0<h<B',
        'exact_controls': ['Existing heterogeneous demo: B=3, derivative=-1',
                           'Changed weights same allocation/budget: derivative=-2',
                           'One patch w=2,c=1,b=0 at B=1: active, price=0, derivative=0'],
        'zero_budget_price_choice_regularized': False, 'C2_or_price_differentiability_claimed': False,
        'general_schur_budget_convex_duality_mechanized': False,
        'floating_solver_or_reported_finite_difference_error_certified': False,
        'physical_lambda_identification': False,
    },
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'Adversarial self-review; no independent mathematical reviewer',
    'next_construction': 'Further original convex/adequacy theorem return or exact robustness ratio constructions; prior physical and contradicted claim boundaries remain',
    'goal_complete': False, 'source_sha256': hashes,
    'source_byte_representation': 'Working checkout bytes; canonical Git blob hashes checked separately',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'895 ordered cumulative standard-only closures (874 immutable + 21 fresh), all 21 statement domains and derived regularity/controls checked; {len(hashes)} fingerprints.')
