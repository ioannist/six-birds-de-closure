"""Verify actual N32/N128 first-record numerical ratios and exact original return."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '0e29ce6'
packet = 'results/patch_ratio_2026-10-03/'
mods = ['WindowPatchCountFirstData', 'WindowPatchCountRatio']


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
assert len(new) == 33
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1251 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_patch_ratio_axioms.lean'), re.M) == new
prior_path = 'results/robust_edge_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_robust_edge_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_patch_ratio_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_patch_ratio_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1251-declaration raw prefix plus freshly audited 33-declaration suffix.\n'
          'Baseline: 0e29ce6; earlier proof-source/toolchain identity checked by de_patch_ratio_verify.py.\n'
          'Full 1284-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_patch_ratio_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['WindowPatchCounts', 'WindowPatchCountData', 'WindowPatchCountRatio',
                  'WindowPatchCountFirstData', 'GrowthScaleReturn']:
        d = d.replace(group + '.', '')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


D = 'WindowPatchCountFirstData.'
R = 'WindowPatchCountRatio.'
require(D+'rational_scale_bounds', '(v : Bool)', '1 / 5 < scaleRat v ∧ scaleRat v < 4')
require(D+'rational_scale_tight', '129 / 100 < scaleRat false', 'scaleRat false < 131 / 100',
        '83 / 100 < scaleRat true', 'scaleRat true < 84 / 100')
require(D+'rational_first_bounds', '(v : Bool) (j : Fin 12)', '1 < firstThresholdRat v j',
        'firstThresholdRat v j < 2000', '450 * scaleRat v < firstThresholdRat v j',
        'firstThresholdRat v j < 897 * scaleRat v')
require(D+'rational_original_lower_fails', '∃ j, firstThresholdRat false j ≤ 500 * scaleRat false')
require(R+'scale_bounds', '(v : Bool)', 'scale v ∈ Set.Ioo (1 / 5) 4')
require(R+'scale_tight', '129 / 100 < scale false', 'scale false < 131 / 100',
        '83 / 100 < scale true', 'scale true < 84 / 100')
require(R+'aggregate_normalized', '(v : Bool)', 'aggregateThreshold v = 965 * scale v')
require(R+'maximum_spec', '(v : Bool) (j : Fin 12)', '0 < maximum v j',
        '∀ (i : Fin (patchCount v)), amplitude v j i ≤ maximum v j',
        '∃ i, amplitude v j i = maximum v j')
require(R+'threshold_bounds', '(v : Bool) (j : Fin 12)', '1 < threshold v j',
        'threshold v j < 2000', '450 * scale v < threshold v j', 'threshold v j < 897 * scale v')
require(R+'gate_cutoff', '(hg : realizedGate v lam)', '-(1 / 20 ^ 3) < lam')
require(R+'final_above_threshold', '(hg : realizedGate v lam)', '(j : Fin 12)',
        'threshold v j ≤ nativeGrowth (1 / 1000) lam 20')
require(R+'endpoint_normalized_bounds', '(v : Bool)',
        '3 < upper v * scale v ^ 3 ∧ upper v * scale v ^ 3 < 7 / 2')
require(R+'endpoint_numerical', '13 / 10 < upper false ∧ upper false < 17 / 10 ∧',
        '5 < upper true ∧ upper true < 25 / 4')
require(R+'endpoint_gate', '(v : Bool)', 'realizedGate v (upper v)')
require(R+'time_spec', '(hg : realizedGate v lam)', '(j : Fin 12)',
        'time v j lam ∈ Set.Icc (1 / 1000) 20', 'nativeGrowth (1 / 1000) lam (time v j lam) = threshold v j')
require(R+'time_positive', '(hg : realizedGate v lam)', '0 < time v j lam')
require(R+'time_iff_any_collapse', '(hg : realizedGate v lam)', '(ha : a ∈ Set.Icc (1 / 1000) 20)',
        '(∃ i, delta ≤ amplitude v j i * nativeGrowth (1 / 1000) lam a) ↔ time v j lam ≤ a')
require(R+'time_is_first_collapse', '(hg : realizedGate v lam)',
        'nativeGrowth (1 / 1000) lam (time v j lam)',
        '∀ a ∈ Set.Icc (1 / 1000) 20, a < time v j lam → ¬∃ i,')
require(R+'time_at_zero', '(v : Bool) (j : Fin 12)', 'time v j 0 = threshold v j / 1000')
require(R+'time_strictMono', '(v : Bool) (j : Fin 12)',
        'StrictMonoOn (time v j) (Set.Ioc (-(1 / 8000)) (upper v))')
require(R+'time_nonnegative_lower', '(hg : realizedGate v lam)', '(hl : 0 ≤ lam)',
        '9 / 20 * scale v < time v j lam')
require(R+'time_nonpositive_upper', '(hg : realizedGate v lam)', '(hl : lam ≤ 0)', 'time v j lam < 2')
require(R+'endpoint_time_bounds', '(v : Bool) (j : Fin 12)',
        '9 / 20 * scale v < time v j (upper v)', 'time v j (upper v) ≤ 8 / 3 * scale v')
require(R+'ratio_density_readout', '(v : Bool) (j : Fin 12) (lam : ℝ)',
        'ratio v j lam = |lam| / (time v j lam ^ 3)⁻¹')
require(R+'ratio_nonnegative', '(hg : realizedGate v lam)', '0 ≤ ratio v j lam')
require(R+'ratio_positive', '(hg : realizedGate v lam)', '(hne : lam ≠ 0)', '0 < ratio v j lam')
require(R+'ratio_zero', '(v : Bool) (j : Fin 12)', 'ratio v j 0 = 0')
require(R+'ratio_strictMono_nonnegative', '(v : Bool) (j : Fin 12)',
        'StrictMonoOn (ratio v j) (Set.Icc 0 (upper v))')
require(R+'ratio_nonpositive_small', '(hg : realizedGate v lam)', '(hl : lam ≤ 0)', 'ratio v j lam < 1 / 1000')
require(R+'ratio_nonnegative_upper', '(hg : realizedGate v lam)', '(hl : 0 ≤ lam)', 'ratio v j lam ≤ 8000 * lam')
require(R+'endpoint_ratios', '(v : Bool) (j : Fin 12)',
        '2187 / 8000 < ratio v j (upper v) ∧ ratio v j (upper v) < 1792 / 27')
require(R+'full_window_ratios', '(hg : realizedGate v lam)', '(j : Fin 12)',
        '0 ≤ ratio v j lam ∧ ratio v j lam < 1792 / 27')
require(R+'ratios_uniformly_arbitrarily_small', '(he : 0 < epsilon)',
        '∃ lam, 0 < lam ∧ ∀ (v : Bool), realizedGate v lam ∧ ∀ (j : Fin 12),',
        '0 < ratio v j lam ∧ ratio v j lam < epsilon')
assert len(decls) == 33
for name,d in decls.items():
    for forbidden in ['(hroot :', '(hfinite :', '(hbound :', '(hfirst :', '(htime :',
                      '(hquadrature :', '(hmax :', '(hrank :', '(hendpoint :']:
        assert forbidden not in d, (name,forbidden)
    if name.split('.')[-1].startswith('endpoint_'):
        assert not re.search(r'\(h\w* :', d), (name,d)
source = read('lean/SbtCosmo/Derivation/WindowPatchCountRatio.lean')
for token in ['aggregateThreshold v / 965', 'max (maximumFalse v j) (maximumTrue v j)',
              'delta / maximum v j', 'GrowthFirstRecordLive.firstTime (1/1000) 20 (threshold v j) lam',
              '|lam| * (time v j lam)^3', 'sampled_maxima v j', 'rational_first_bounds v j',
              'upper_spec v', 'lower_prefix_growth hc', 'upper_horizon_growth hc',
              'upper_prefix_growth hc', 'native_endpoint_strictAntiOn',
              'GrowthFirstRecord.any_patch_collapse_iff', 'GrowthFirstRecordLive.firstTime_iff_threshold',
              'GrowthFirstRecord.firstTime_lower_matter', 'GrowthFirstRecordLive.firstTime_nonpositive_upper',
              'ratio_strictMono_nonnegative v j', 'ratio_nonpositive_small hg',
              'min (min (upper false) (upper true)) (epsilon/16000)']:
    assert token in source,token
replay = subprocess.check_output([sys.executable,str(root/'scripts/de_patch_ratio_certificate.py')],cwd=root).decode().strip()
assert replay == 'Exact N32/N128 first-threshold bounds and false-target controls passed; byte replay matched.'
report = json.loads(read(packet+'thresholds.json'))
assert report['arithmetic'] == 'Python Fraction only; no float, RNG or ODE'
assert [g['n_patches'] for g in report['variants']] == [32,128]
assert report['variants'][0]['false_500_lower_bound_failing_seeds']
assert all(len(g['first_ANY_patch_thresholds_exact']) == 12 and g['changed_two_tag_readout_detected_seeds'] for g in report['variants'])
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8158 jobs).' in build and not re.search(r'error:|warning:', build)
assert 'Adversarial self-review, not independent review' in read(packet + 'self_review.txt')

mutable = {'README.md', 'lean/README.md', 'lean/lakefile.lean', 'lean/manifests/check_axioms.lean',
           'lean/manifests/coverage_table.md', 'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
for p,h in prior['source_sha256'].items():
    if p not in mutable:
        assert digest((root / p).read_bytes()) == h,p
        assert digest(git_blob(baseline,p)) == prior['git_blob_sha256'][p],p
for ref,paths in [('6a71e6c',['paper','external']), (baseline,['sbt_cosmo','tests','results/DE_window','results/DE_dual'])]:
    assert subprocess.check_output(['git','diff','--name-only',ref,'--',*paths],cwd=root) == b''
tracked = subprocess.check_output(['git','ls-tree','-r','--name-only',baseline],cwd=root).decode().splitlines()
protected = [p for p in tracked if p not in mutable and p.startswith(('scripts/','lean/','results/','math/'))]
assert subprocess.check_output(['git','diff','--name-only',baseline,'--',*protected],cwd=root) == b''
old_config = git_blob(baseline,'lean/lakefile.lean').decode()
expected = old_config.replace('`SbtCosmo.Derivation.WindowRobustEdge]',
    '`SbtCosmo.Derivation.WindowRobustEdge, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected

lean_version = subprocess.check_output(['lake','env','lean','--version'],cwd=root/'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip() == mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot/p).read_bytes()) == h,p
files = set(prior['source_sha256']) | {prior_path, 'paper/sections/sec_05_window.tex', 'paper/appendices/app_a_carriers.tex'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_patch_ratio_certificate.py','scripts/de_patch_ratio_verify.py',
              'math/PATCH_RATIO_LEAN_2026-10-03.md', 'lean/manifests/check_patch_ratio_statements.lean',
              'lean/manifests/check_patch_ratio_axioms.lean', new_path, combined_path])
files.update(str(p.relative_to(root)) for p in (root/packet).iterdir() if p.name != 'verification.json')
hashes = {p:digest((root/p).read_bytes()) for p in sorted(files)}
git_hashes,normalized = {},[]
for p in sorted(files):
    blob = (root/p).read_bytes()
    if b'\r\n' in blob:
        attrs = subprocess.check_output(['git','check-attr','text','eol','--',p],cwd=root).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob,p
        blob = blob.replace(b'\r\n',b'\n')
        normalized.append(p)
    git_hashes[p] = digest(blob)
v = {
    'baseline_commit':baseline,
    'scope':'Actual separately realized N32/N128 first-ANY-patch numerical edge ratios and full signed windows',
    'lean_build':{'command':'lake build','success':True,'jobs':8158,'warnings_as_errors':True,'receipt':'lean_build.txt'},
    'axiom_audit':{'command_fresh_suffix':'lake env lean -DwarningAsError=true manifests/check_patch_ratio_axioms.lean',
        'success':True,'declarations_cumulative':1284,'declarations_fresh':33,'declarations_preserved':1251,
        'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,
        'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),
        'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,
        'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
    'statement_check':{'command':'lake env lean -DwarningAsError=true manifests/check_patch_ratio_statements.lean',
        'success':True,'declarations':33,'receipt':'theorem_statements.txt'},
    'mathlib':mathlib,'actual_lean_version_checked':lean_version,
    'certificate_replay':{'success':True,'command':'python3 scripts/de_patch_ratio_certificate.py',
        'seeds':24,'populations':[32,128],'arithmetic':'Fraction only; no float, RNG or ODE',
        'false_500_transfer_control':True,'changed_readout_control':True,'receipt':'thresholds.json'},
    'original_return':{
        'target':'other original sampled population edge ratios and first-record readouts',
        'original_target_sources':['paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'],
        'original_population_data_tags_and_IVP_retained':True,'populations':[32,128],
        'normalization':'c=T_aggregate/965, analytic only','first_threshold':'delta/max(tag0max,tag1max)',
        'actual_initial_D1_and_parameter_dependent_prefactor_retained':True,
        'original_start_and_horizon':['1/1000','20'],'actual_all24_first_thresholds':'450c<Tfirst<897c',
        'false_500_normalized_lower_bound_kernel_counterexample':True,
        'actual_endpoint_normalized':'3<u*c^3<7/2','actual_endpoints':{'32':'(13/10,17/10)','128':'(5,25/4)'},
        'actual_ANY_patch_first_time_at_endpoint':'(9/20)c<a_first<=(8/3)c',
        'actual_endpoint_ratios_all24':'2187/8000<R<1792/27','all_signed_admitted_ratios':'0<=R<1792/27',
        'nonpositive_admitted_ratios':'R<1/1000','one_positive_lambda_all24_arbitrarily_small':True,
        'actual_first_collapse_equivalence_and_minimality':True,
        'previous_population_ordering_preserved':True,'smooth_in_discrete_N_claimed':False,
        'populations_nested_or_coupled':False,'new_sampling_or_floating_interpolation_used':False,
        'sharp_observed_ratio_or_typicality_claimed':False,'historical_grid_values_as_continuum_roots':False,
        'combined_new_population_and_knob_sweeps':False,'physical_Lambda_bridge':False},
    'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
    'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
    'python_test_suite_rerun':False,'original_carrier_solver_rerun':False,
    'review':'adversarial self-review, not independent review',
    'next_construction':'First-time joint regularity, combined population-and-knob robustness and broader original-target audit',
    'goal_complete':False,'source_sha256':hashes,
    'source_byte_representation':'checkout bytes; historical CRLF preserved',
    'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized,
}
(root/packet/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'1284 ordered cumulative standard-only closures (1251 immutable + 33 fresh), actual N32/N128 first-record numerical ratios and no-pinching; {len(hashes)} fingerprints')
