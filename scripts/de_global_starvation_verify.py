"""Verify the exact global starvation packet and its preserved cumulative evidence."""
import hashlib
import json
import re
import subprocess
from fractions import Fraction
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '52cfe0e'
packet = 'results/global_starvation_2026-10-03/'
mods = ['WindowStarvationData', 'GrowthStarvationCertified', 'WindowGlobalStarvation']

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
assert len(new) == 19
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 855 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_global_starvation_axioms.lean'), re.M) == new
prior_path = 'results/eternal_ratio_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_eternal_ratio_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_global_starvation_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_global_starvation_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 855-declaration raw prefix plus freshly audited 19-declaration suffix.\n'
          'Baseline: 52cfe0e; earlier proof-source/toolchain identity checked by de_global_starvation_verify.py.\n'
          'Full 874-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_global_starvation_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
compact = ' '.join(statements.split())
for required in [
    'GrowthStarvationCertified.limiting_growth_upper : SbtCosmo.Derivation.GrowthInfinite.nativeInfinite (1 / 1000) 32 < 485',
    'GrowthStarvationCertified.global_growth_upper {lam a : ℝ} (hlam : 32 ≤ lam) (ha : 1 / 1000 ≤ a)',
    'GrowthScaleReturn.nativeGrowth (1 / 1000) lam a < 485',
    'WindowGlobalStarvation.no_original_patch_ever {lam : ℝ} (hlam : 32 ≤ lam) (j : Fin 12) (i : Fin 64)',
    'WindowGlobalStarvation.no_robustness_patch_ever (v : Bool) {lam : ℝ} (hlam : 32 ≤ lam) (j : Fin 12) (i : Fin (SbtCosmo.Derivation.WindowPatchCountData.patchCount v))',
    '¬∃ a, 1 / 1000 ≤ a ∧',
    'WindowGlobalStarvation.original_record_count_zero {lam A : ℝ} (hlam : 32 ≤ lam)',
    'WindowGlobalStarvation.robustness_record_count_zero (v : Bool) {lam A : ℝ} (hlam : 32 ≤ lam)',
]:
    assert required in compact, required
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8103 jobs).' in build and not re.search(r'error:|warning:', build)

# Immutable prior artifacts and frozen paper/runtime. Current metadata may grow.
mutable = {'README.md', 'lean/README.md', 'lean/lakefile.lean', 'lean/manifests/check_axioms.lean',
           'lean/manifests/coverage_table.md', 'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
for p, h in prior['source_sha256'].items():
    if p not in mutable:
        assert digest((root / p).read_bytes()) == h, p
        assert digest(git_blob(baseline, p)) == prior['git_blob_sha256'][p], p
for ref, paths in [('6a71e6c', ['paper', 'external']), (baseline, ['sbt_cosmo', 'tests', 'results/DE_window'])]:
    assert subprocess.check_output(['git', 'diff', '--name-only', ref, '--', *paths], cwd=root) == b''
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', baseline], cwd=root).decode().splitlines()
protected = [p for p in tracked if p not in mutable and p.startswith(('scripts/', 'lean/', 'results/', 'math/'))]
assert subprocess.check_output(['git', 'diff', '--name-only', baseline, '--', *protected], cwd=root) == b''
# Only default derivation roots have been extended in the build configuration.
old_config = git_blob(baseline, 'lean/lakefile.lean').decode()
expected_config = old_config.replace('`SbtCosmo.Derivation.WindowEternalRatio]',
    '`SbtCosmo.Derivation.WindowEternalRatio,\n    `SbtCosmo.Derivation.WindowStarvationData, `SbtCosmo.Derivation.GrowthStarvationCertified,\n    `SbtCosmo.Derivation.WindowGlobalStarvation]')
assert read('lean/lakefile.lean') == expected_config
for mod in mods:
    assert '`SbtCosmo.Derivation.' + mod in read('lean/lakefile.lean')

# Independent rational validation of every whole-cell enclosure, sum, root and tail bound.
f = Fraction
cells = json.loads(read(packet + 'cells.json'))
assert cells['arithmetic'] == 'Python Fraction and integer isqrt; no floating arithmetic'
assert cells['lambda'] == '32' and cells['cells'] == 64 and cells['domain'] == ['1/1000', '4']
assert cells['false_certificate_controls'] == {'zero_upper_cell_rejected': True, 'lowered_sum_target_rejected': True}
grid = list(map(f, cells['grid']))
highs = list(map(f, cells['upper']))
lam, a0 = f(32), f(1, 1000)
assert len(grid) == 65 and len(highs) == len(cells['upper_branch']) == 64
assert grid[0] == a0 and grid[-1] == 4 and f(1, 4) in grid
for a, b, hi, branch in zip(grid, grid[1:], highs, cells['upper_branch']):
    assert 0 < a < b and hi >= 0
    if 2 * lam * b**3 <= 1:
        assert branch == 'increasing' and b**3 <= hi**2 * (1 + lam * b**3)**3
    elif 1 <= 2 * lam * a**3:
        assert branch == 'decreasing' and a**3 <= hi**2 * (1 + lam * a**3)**3
    else:
        assert branch == 'peak' and 4 <= 27 * lam * hi**2
upper_sum = sum(((b - a) * hi for a, b, hi in zip(grid, grid[1:], highs)), f(0))
assert upper_sum == f(136242057, 4000000000) == f(cells['upper_sum'])
assert f(34, 1000) < upper_sum <= f(341, 10000)
alpha = lam * a0**2 + 5 / (2 * a0)
assert f(1, 4**3) + lam <= f(566, 100)**2
assert 30000**2 <= 1 / a0**3 + lam
finite_bound = f(566, 100) * (f(1, 30000) + alpha * f(341, 10000))
tail = alpha / (2 * lam * 4**2)
assert finite_bound < f(9651, 20) and tail < f(49, 20) and finite_bound + tail < 485

# Recheck every original patch, not just the tagged-max certificates. No new RNG or solver run.
pops64 = json.loads(read('results/window_population_2026-10-03/population.json'))['populations']
variants = json.loads(read('results/patch_count_2026-10-03/populations.json'))['variants']
groups = [(64, pops64)] + [(v['n_patches'], v['populations']) for v in variants]
assert sorted(n for n, _ in groups) == [32, 64, 128]
margins = {}
for n, pops in groups:
    assert len(pops) == 12 and [p['seed'] for p in pops] == list(range(1100, 1112))
    maximum = f(0)
    for pop in pops:
        amps = list(map(f, pop['amplitudes_exact']))
        tags = pop['tags']
        assert len(amps) == len(tags) == n and all(type(t) is bool for t in tags)
        assert all(0 <= amp and 485 * amp < f(843, 500) for amp in amps)
        maxima = [max(a for a, t in zip(amps, tags) if t == b) for b in [False, True]]
        assert maxima == list(map(f, pop['tag_maxima_exact']))
        maximum = max(maximum, max(amps))
    margins[str(n)] = {'patches_checked': 12*n, 'largest_amplitude_exact': str(maximum),
                       'minimum_any_patch_threshold_exact': str(f(843, 500) / maximum),
                       'strict_margin_at_485': True}
fresh = subprocess.check_output(['python3', 'scripts/de_global_starvation_certificate.py'], cwd=root).decode()
assert fresh == read(packet + 'replay.txt')

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root / 'lean/.lake/packages/mathlib').decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_global_starvation_verify.py', 'scripts/de_global_starvation_certificate.py',
              'math/GLOBAL_STARVATION_LEAN_2026-10-03.md', 'lean/manifests/check_global_starvation_statements.lean',
              'lean/manifests/check_global_starvation_axioms.lean', new_path, combined_path])
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
    'scope': 'Actual all-time starvation of every original N=32,64,128 patch at every lambda>=32',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8103, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean manifests/check_global_starvation_axioms.lean',
                    'success': True, 'declarations_cumulative': 874, 'declarations_fresh': 19,
                    'declarations_preserved': 855, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean manifests/check_global_starvation_statements.lean',
                        'success': True, 'declarations': 19, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {'same_original_native_ivp_and_exact_decimal_model_scalars': True,
                       'all_original_populations_retained': [32, 64, 128], 'all_twelve_seeds_retained': True,
                       'sufficient_lambda_cutoff': 32, 'sharp_cutoff_claimed': False,
                       'global_growth_upper': 'D(a0,lambda,a)<485 for all lambda>=32 and finite a>=a0',
                       'all_time_no_single_patch_collapse': True, 'both_tag_record_count_at_every_horizon': 0,
                       'amplitude_margin_assumed_in_generic_theorem': True,
                       'amplitude_margin_derived_for_all_original_populations': True,
                       'universal_random_population_starvation_claimed': False,
                       'original_floating_solver_total_correctness_certified': False,
                       'physical_crunch_or_lambda_identification': False},
    'exact_certificate': {'new_cells': 64, 'arithmetic': 'Fraction and integer isqrt only',
                          'upper_sum': str(upper_sum), 'upper_certificate': '341/10000',
                          'finite_native_bound': str(finite_bound), 'tail_bound_at_32_a4': str(tail),
                          'false_controls': cells['false_certificate_controls'], 'receipt': 'cells.json',
                          'byte_replay_success': True, 'command': 'python3 scripts/de_global_starvation_certificate.py',
                          'replay_receipt': 'replay.txt'},
    'independent_exact_population_margin_recheck': margins,
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_growth_solver_rerun': False, 'population_reification_tools_rerun': False,
    'review': 'Adversarial self-review; no independent mathematical reviewer',
    'next_construction': 'Actual first-time ratio returns for reified robustness populations, or remaining feasible original optimization/adequacy mechanizations; prior physical and contradicted claim boundaries remain',
    'goal_complete': False, 'source_sha256': hashes,
    'source_byte_representation': 'Working checkout bytes; canonical Git blob hashes checked separately',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'874 ordered cumulative standard-only closures (855 immutable + 19 fresh), 19 statements, exact cell/sum/tail and all 2688 original patch margins checked; {len(hashes)} fingerprints.')
