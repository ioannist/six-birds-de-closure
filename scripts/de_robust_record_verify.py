"""Verify actual robust signed first records and uniform no-pinching on the declared rectangle."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'd4af1e7'
packet = 'results/robust_record_2026-10-03/'
mods = ['WindowRobustRecord', 'WindowRobustRatio']


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
assert len(new) == 39
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1184 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_robust_record_axioms.lean'), re.M) == new
prior_path = 'results/matrix_sensitivity_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_matrix_sensitivity_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_robust_record_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_robust_record_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1184-declaration raw prefix plus freshly audited 39-declaration suffix.\n'
          'Baseline: d4af1e7; earlier proof-source/toolchain identity checked by de_robust_record_verify.py.\n'
          'Full 1223-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_robust_record_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['WindowRobustRecord','WindowRobustRatio','WindowSensitivity','WindowFirstRecord','WindowSignedRecord','GrowthScaleReturn']:
        d = d.replace(group + '.', '')
    d = d.replace('MatrixClosurePrice.positive', 'positive')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


# Checks cover every actual exported theorem and its meaningful domain/readout.
require('WindowRobustRecord.rectangle_positive','(hR : Rectangle d s)','0 < d ∧ 0 < s')
require('WindowRobustRecord.factor_positive','(hR : Rectangle d s)','0 < factor d s')
require('WindowRobustRecord.factor_corner_bounds','factor (6 / 5) 3 ≤ factor d s','factor d s ≤ factor 2 (1 / 3)')
require('WindowRobustRecord.factor_bounds','1 / 5 < factor d s ∧ factor d s < 4')
require('WindowRobustRecord.maximum_spec','(j : Fin 12)','0 < maximum s j',
        'scaledAmplitude s j i ≤ maximum s j','∃ i, scaledAmplitude s j i = maximum s j')
require('WindowRobustRecord.threshold_return','d / maximum s j = threshold d s j')
require('WindowRobustRecord.threshold_bounds','100 < threshold d s j ∧ threshold d s j < 3588')
require('WindowRobustRecord.threshold_below_aggregate','threshold d s j < scaledThreshold d s')
require('WindowRobustRecord.gate_iff_window','(hR : Rectangle d s)',
        'gate d s lam ↔ lam ∈ Set.Ioc (-(1 / 8000)) (scaledEndpoint d s)')
require('WindowRobustRecord.endpoint_spec','0 < scaledEndpoint d s',
        'nativeGrowth (1 / 1000) (scaledEndpoint d s) 20 = scaledThreshold d s')
require('WindowRobustRecord.gate_cutoff','(hg : gate d s lam)','-(1 / 20 ^ 3) < lam')
require('WindowRobustRecord.final_above_threshold','(hR : Rectangle d s)','(hg : gate d s lam)',
        'threshold d s j ≤ nativeGrowth (1 / 1000) lam 20')
require('WindowRobustRecord.time_spec','(hR : Rectangle d s)','(hg : gate d s lam)',
        'time d s j lam ∈ Set.Icc (1 / 1000) 20',
        'nativeGrowth (1 / 1000) lam (time d s j lam) = threshold d s j')
require('WindowRobustRecord.time_iff_any_collapse','(hR : Rectangle d s)','(hg : gate d s lam)',
        '(ha : a ∈ Set.Icc (1 / 1000) 20)',
        '(∃ i, d ≤ scaledAmplitude s j i * nativeGrowth (1 / 1000) lam a) ↔ time d s j lam ≤ a')
require('WindowRobustRecord.time_is_first_collapse','nativeGrowth (1 / 1000) lam (time d s j lam)',
        '∀ a ∈ Set.Icc (1 / 1000) 20, a < time d s j lam → ¬∃ i,')
require('WindowRobustRecord.gate_zero','gate d s 0')
require('WindowRobustRecord.time_at_zero','time d s j 0 = threshold d s j / 1000')
require('WindowRobustRecord.time_positive','0 < time d s j lam')
require('WindowRobustRecord.time_nonpositive_upper','(hl : lam ≤ 0)', 'time d s j lam ≤ threshold d s j / 1000')
require('WindowRobustRecord.time_nonnegative_lower','(hl : 0 ≤ lam)', 'threshold d s j / 1000 ≤ time d s j lam')
require('WindowRobustRecord.time_strictMono','StrictMonoOn (time d s j)',
        'Set.Ioc (-(1 / 8000)) (scaledEndpoint d s)')
require('WindowRobustRecord.original_time_return','time WindowSample.delta 1 j lam = time j lam')
require('WindowRobustRatio.corner_rectangles','Rectangle 2 (1 / 3) ∧ Rectangle (6 / 5) 3')
require('WindowRobustRatio.corner_endpoints_positive','0 < minimumEndpoint ∧ 0 < maximumEndpoint')
require('WindowRobustRatio.endpoint_corner_bounds','(hR : Rectangle d s)',
        'minimumEndpoint ≤ scaledEndpoint d s ∧ scaledEndpoint d s ≤ maximumEndpoint')
require('WindowRobustRatio.common_positive_window','(hl : lam ∈ Set.Icc 0 minimumEndpoint)', 'gate d s lam')
require('WindowRobustRatio.ratio_density_readout','ratio d s j lam = |lam| / (time d s j lam ^ 3)⁻¹')
require('WindowRobustRatio.ratio_nonnegative','(hg : gate d s lam)', '0 ≤ ratio d s j lam')
require('WindowRobustRatio.ratio_positive','(hg : gate d s lam)', '(hne : lam ≠ 0)', '0 < ratio d s j lam')
require('WindowRobustRatio.ratio_zero','ratio d s j 0 = 0')
require('WindowRobustRatio.ratio_nonnegative_upper','(hl : 0 ≤ lam)', 'ratio d s j lam ≤ 8000 * lam')
require('WindowRobustRatio.ratio_nonpositive_small','(hl : lam ≤ 0)', 'ratio d s j lam < 1 / 125')
require('WindowRobustRatio.full_window_ratios','0 ≤ ratio d s j lam',
        'ratio d s j lam ≤ max (8000 * maximumEndpoint) (1 / 125)')
require('WindowRobustRatio.endpoint_ratios','minimumEndpoint / 1000 < ratio d s j (scaledEndpoint d s)',
        'ratio d s j (scaledEndpoint d s) ≤ 8000 * maximumEndpoint')
d=require('WindowRobustRatio.ratios_uniformly_arbitrarily_small','(he : 0 < epsilon)',
          '∃ lam, 0 < lam ∧ lam ≤ minimumEndpoint ∧ ∀ (d s : ℝ), Rectangle d s →',
          'gate d s lam ∧ ∀ (j : Fin 12), 0 < ratio d s j lam ∧ ratio d s j lam < epsilon')
assert '(hg :' not in d and '(hR :' not in d
require('WindowRobustRatio.ratio_strictMono_nonnegative','StrictMonoOn (ratio d s j)',
        'Set.Icc 0 (scaledEndpoint d s)')
require('WindowRobustRatio.equal_factor_return','(h : factor d1 s1 = factor d2 s2)',
        'scaledEndpoint d1 s1 = scaledEndpoint d2 s2', 'time d1 s1 j lam = time d2 s2 j lam',
        'ratio d1 s1 j lam = ratio d2 s2 j lam')
require('WindowRobustRatio.original_ratio_return','ratio WindowSample.delta 1 j lam = ratio j lam')
d=require('WindowRobustRatio.compensated_original_return','Rectangle (3 * WindowSample.delta / 4) (3 / 4)',
          '∀ (j : Fin 12) (lam : ℝ),',
          'time (3 * WindowSample.delta / 4) (3 / 4) j lam = time j lam',
          'ratio (3 * WindowSample.delta / 4) (3 / 4) j lam = ratio j lam')
assert '(h' not in d
source=read('lean/SbtCosmo/Derivation/WindowRobustRecord.lean')
for token in ['def Rectangle','d ∈ Icc (6/5) 2 ∧ s ∈ Icc (1/3) 3',
              'GrowthPopulation.nativeAggregate', 'scaledAmplitude s', 'WindowSampleData.tag',
              'GrowthFirstRecordLive.firstTime', 'WindowFirstRecord.maximum_spec',
              'original_aggregate_bounds.1', 'robustness_rectangle_native_window',
              'native_endpoint_strictAntiOn', 'GrowthFirstRecord.any_patch_collapse_iff',
              'GrowthFirstRecordLive.firstTime_iff_threshold', 'GrowthFirstRecordLive.firstTime_strict_parameter']:
    assert token in source,token
source=read('lean/SbtCosmo/Derivation/WindowRobustRatio.lean')
for token in ['scaledEndpoint 2 (1/3)', 'scaledEndpoint (6/5) 3',
              'GrowthEndpointSensitivity.endpoint_strictAntiOn', 'factor_corner_bounds hR',
              'def ratio', '|lam| *(time d s j lam)^3',
              'min minimumEndpoint (epsilon/16000)', 'intro d s hR', 'intro j',
              'common_positive_window hR', 'time_nonnegative_lower hR',
              'time_nonpositive_upper hR', 'original_time_return j lam', 'original_ratio_return j lam']:
    assert token in source,token
for name,d in decls.items():
    if name.startswith('WindowRobustRecord.') and name.split('.')[-1] not in ['threshold_return','original_time_return']:
        assert '(hR : Rectangle d s)' in d,name
    for token in ['(hfinal :','(hfirst :','(hroot :','(htime :','(hbound :','(hminimumEndpoint :']:
        assert token not in d,(name,token)
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8150 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.MatrixSensitivityExamples]',
    '`SbtCosmo.Derivation.MatrixSensitivityExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
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
files = set(prior['source_sha256']) | {prior_path, 'paper/sections/sec_05_window.tex', 'paper/appendices/app_a_carriers.tex'}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_robust_record_verify.py', 'math/ROBUST_RECORD_LEAN_2026-10-03.md',
              'lean/manifests/check_robust_record_statements.lean', 'lean/manifests/check_robust_record_axioms.lean',
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
    'scope': 'Full robustness-rectangle signed first records, uniform actual ratios and common no-pinching',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8150, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_robust_record_axioms.lean',
                    'success': True, 'declarations_cumulative': 1223, 'declarations_fresh': 39,
                    'declarations_preserved': 1184, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_robust_record_statements.lean',
                        'success': True, 'declarations': 39, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'target': 'original first-collapse/matter-ratio readouts across full coupled robustness rectangle',
        'original_target_sources': ['paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'],
        'population': 'unchanged reified twelve seeds, sixty-four patches, original tags',
        'coupling': 'exact real common scaling of original amplitudes; no floating/resampled array identity',
        'rectangle': {'threshold': '[6/5,2]','amplitude_multiplier': '[1/3,3]'},
        'actual_growth_IVP_and_horizon_unchanged': True,
        'actual_attained_scaled_maximum_constructed': True,
        'first_threshold_bounds_earned': '(100,3588), strictly below actual scaled aggregate threshold',
        'actual_signed_gate': '(-1/8000,actual_scaled_endpoint]',
        'first_time_root_applicability_earned': True,
        'actual_ANY_patch_collapse_equivalence_and_minimality': True,
        'same_original_signed_functions_at_original_scaling': True,
        'ratio': 'abs(lambda)*actual_first_time^3=abs(lambda)/matter_density',
        'actual_corner_endpoint_bounds': 'u(2,1/3)<=u(d,s)<=u(6/5,3)',
        'common_positive_window_earned': True,
        'nonpositive_admitted_ratio_bound': '<1/125',
        'nonnegative_admitted_ratio_bound': '<=8000*lambda',
        'full_signed_uniform_bound': '<=max(8000*u_max,1/125)',
        'endpoint_uniform_bounds': 'u_min/1000<R<=8000*u_max',
        'numerical_order_unity_rectangle_certificate': False,
        'uniform_no_pinching_quantifier': 'forall epsilon>0, exists one lambda>0, forall d,s in rectangle, forall12 seeds: gate and0<R<epsilon',
        'nonnegative_ratio_strict_parameter_ordering': True,
        'equal_factor_actual_endpoint_time_ratio_return': True,
        'changed_knob_control': '(3delta0/4,3/4) inside rectangle returns original time/ratio functions',
        'first_time_joint_regular_or_C1_proved': False,
        'other_sampled_population_ratio_estimates': False,
        'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Tighter numerical robustness-edge ratios, first-time joint regularity and broader original-target audit',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1223 ordered cumulative standard-only closures (1184 immutable + 39 fresh), actual robust signed first-record returns and uniform no-pinching; {len(hashes)} fingerprints')
