"""Verify explicit actual robustness-edge ratio certificates and native finite-start return."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '42f228c'
packet = 'results/robust_edge_2026-10-03/'
mods = ['RobustEdgeLowerData','RobustEdgePrefixData','RobustEdgeUpperData','RobustEdgeQuadrature','GrowthRescaledCertificate','WindowRobustEdge']


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
assert len(old_names) == 1223 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_robust_edge_axioms.lean'), re.M) == new
prior_path = 'results/robust_record_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_robust_record_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_robust_edge_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_robust_edge_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1223-declaration raw prefix plus freshly audited 28-declaration suffix.\n'
          'Baseline: 42f228c; earlier proof-source/toolchain identity checked by de_robust_edge_verify.py.\n'
          'Full 1251-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_robust_edge_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['WindowRobustRecord','WindowRobustRatio','WindowSensitivity','WindowFirstRecord','WindowSignedRecord','GrowthScaleReturn','GrowthQuadrature']:
        d = d.replace(group + '.', '')
    d = d.replace('MatrixClosurePrice.positive', 'positive')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


# Original numerical target returns to actual native endpoint/time/ratio functions.
for mod,n,start,end,lam in [('RobustEdgeLowerData',619,'1 / 200','5 / 1','3 / 1'),
                          ('RobustEdgePrefixData',522,'1 / 200','8 / 3','7 / 2'),
                          ('RobustEdgeUpperData',784,'1 / 4000','100 / 1','7 / 2')]:
    require(mod+'.grid_endpoints',f'{mod}.grid 0 = {start}',f'{mod}.grid {n} = {end}')
    require(mod+'.cells',f'(i : Fin {n})',f'{mod}.grid',f'{mod}.bound',lam)
    require(mod+'.integral_sum',f'Finset.range {n}',f'{mod}.bound')
    assert '(h' not in decls[mod+'.cells']
require('RobustEdgeQuadrature.lower_grid','(hlam : 1 ≤ lam)','(hcell :','(hsum :',
        '↑cap ≤ integral ↑lam ↑(a 0) ↑(a n)')
require('RobustEdgeQuadrature.upper_grid','(hlam : 0 < lam)','(hcell :','(hsum :',
        'integral ↑lam ↑(a 0) ↑(a n) ≤ ↑cap')
require('RobustEdgeQuadrature.lower_integral','224 / 1000 ≤ integral 3 (1 / 200) 5')
require('RobustEdgeQuadrature.prefix_integral','1909 / 10000 ≤ integral (7 / 2) (1 / 200) (8 / 3)')
require('RobustEdgeQuadrature.upper_integral','integral (7 / 2) (1 / 4000) 100 ≤ 2035 / 10000')
require('GrowthRescaledCertificate.native_scale_covariance','(hc : c ≠ 0)',
        'nativeGrowth a0 (lam / c ^ 3) (c * A) = nativeGrowth (a0 / c) lam A')
require('GrowthRescaledCertificate.rescaled_start_bounds','(hc : c ∈ Set.Ioo (1 / 5) 4)',
        '1 / 1000 / c ∈ Set.Icc (1 / 4000) (1 / 200)')
require('GrowthRescaledCertificate.integral_interval_mono','(hl : 0 ≤ lam)',
        '(hu : 0 < u)', '(hua : u ≤ a)', '(hab : a ≤ b)', '(hbv : b ≤ v)',
        'integral lam a b ≤ integral lam u v')
require('GrowthRescaledCertificate.prefactor_lower','(hc : 0 < c)', '(hl : 0 ≤ lam)',
        '2500 * c ≤ nativePrefactor lam (1 / 1000 / c)')
require('GrowthRescaledCertificate.prefactor_upper','nativePrefactor (7 / 2) (1 / 1000 / c) ≤ (2500 + 1 / 1000) * c')
require('GrowthRescaledCertificate.initial_term_upper','(nativeRoot (7 / 2) (1 / 1000 / c))⁻¹ ≤ c / 500')
require('GrowthRescaledCertificate.lower_prefix_growth','970 * c < nativeGrowth (1 / 1000) (3 / c ^ 3) (5 * c)')
require('GrowthRescaledCertificate.upper_prefix_growth','897 * c < nativeGrowth (1 / 1000) (7 / 2 / c ^ 3) (8 / 3 * c)')
require('GrowthRescaledCertificate.upper_horizon_growth','nativeGrowth (1 / 1000) (7 / 2 / c ^ 3) 20 < 960 * c')
require('WindowRobustEdge.original_aggregate_tight','960 < WindowSample.aggregateThreshold ∧ WindowSample.aggregateThreshold < 970')
require('WindowRobustEdge.endpoint_normalized_bounds','(hR : Rectangle d s)',
        '3 < scaledEndpoint d s * factor d s ^ 3 ∧ scaledEndpoint d s * factor d s ^ 3 < 7 / 2')
require('WindowRobustEdge.endpoint_time_bounds','(hR : Rectangle d s)', '(j : Fin 12)',
        'factor d s / 2 < time d s j (scaledEndpoint d s)',
        'time d s j (scaledEndpoint d s) ≤ 8 / 3 * factor d s')
require('WindowRobustEdge.endpoint_ratios','(hR : Rectangle d s)', '(j : Fin 12)',
        '3 / 8 < ratio d s j (scaledEndpoint d s)', 'ratio d s j (scaledEndpoint d s) < 1792 / 27')
require('WindowRobustEdge.full_window_ratios','(hR : Rectangle d s)', '(hg : gate d s lam)',
        '0 ≤ ratio d s j lam ∧ ratio d s j lam < 1792 / 27')
for name,d in decls.items():
    if name.startswith(('WindowRobustEdge.','GrowthRescaledCertificate.')):
        for forbidden in ['(hroot :','(hfinite :','(hbound :','(hfirst :','(htime :','(hquadrature :','(hI :']:
            assert forbidden not in d,(name,forbidden)
    if name.startswith('WindowRobustEdge.') and name!='WindowRobustEdge.original_aggregate_tight':
        assert '(hR : Rectangle d s)' in d
    if name.startswith('GrowthRescaledCertificate.') and name.split('.')[-1] in [
        'prefactor_upper','initial_term_upper','lower_prefix_growth','upper_prefix_growth','upper_horizon_growth']:
        assert '(hc : c ∈ Set.Ioo (1 / 5) 4)' in d
source_checks={
 'RobustEdgeQuadrature':['GrowthQuadratureSharp.integral_grid_bounds','exact_mod_cast hcell',
    'density_cell_lower','density_cell_upper','RobustEdgeLowerData.cells',
    'RobustEdgePrefixData.cells','RobustEdgeUpperData.cells'],
 'GrowthRescaledCertificate':['unfold nativeGrowth logScale',"native_scale_covariance hp.ne'",
    'native_growth_quadrature','initial_term_upper hc','prefactor_upper hc','prefactor_lower hp',
    'intervalIntegral.integral_mono_interval','lower_integral.trans','prefix_integral.trans',
    '.trans upper_integral','(nativeRoot (7/2) ((1/1000)/c))⁻¹'],
 'WindowRobustEdge':['WindowSample.sampled_threshold_exact','lower_prefix_growth hc',
    'upper_horizon_growth hc','native_endpoint_strictAntiOn','endpoint_spec hR',
    'upper_prefix_growth hc','GrowthFirstRecordLive.firstTime_iff_threshold',
    'ratio_strictMono_nonnegative hR j','ratio_nonpositive_small hR hg']}
for mod,tokens in source_checks.items():
    source=read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    for token in tokens:assert token in source,(mod,token)
replay=subprocess.check_output([sys.executable,str(root/'scripts/de_robust_edge_certificate.py')],cwd=root).decode().strip()
assert replay=='Three exact profiles and false-cell controls passed; byte replay matched.'
cells=json.loads(read(packet+'cells.json'))
assert cells['arithmetic']=='Python Fraction and integer isqrt; no floating arithmetic'
assert cells['sqrt_denominator']==1_000_000
assert [(p['lambda'],p['domain'],p['direction'],p['cells'],p['integral_bound']) for p in cells['profiles']]==[
    ('3',['1/200','5'],'lower',619,'28/125'),
    ('7/2',['1/200','8/3'],'lower',522,'1909/10000'),
    ('7/2',['1/4000','100'],'upper',784,'407/2000')]
assert sum(p['cells'] for p in cells['profiles'])==1925
assert all(p['false_cell_detected'] for p in cells['profiles'])
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8156 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.WindowRobustRatio]',
    '`SbtCosmo.Derivation.WindowRobustRatio, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot / p).read_bytes()) == h
for p in ['Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean','Mathlib/Analysis/Calculus/FDeriv/Prod.lean', 'Mathlib/Analysis/Calculus/FDeriv/Add.lean',
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
files.update(['scripts/de_robust_edge_certificate.py','scripts/de_robust_edge_verify.py', 'math/ROBUST_EDGE_LEAN_2026-10-03.md',
              'lean/manifests/check_robust_edge_statements.lean', 'lean/manifests/check_robust_edge_axioms.lean',
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
    'scope': 'Explicit kernel-certified actual robustness-edge ratios throughout the full coupled rectangle',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8156, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_robust_edge_axioms.lean',
                    'success': True, 'declarations_cumulative': 1251, 'declarations_fresh': 28,
                    'declarations_preserved': 1223, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_robust_edge_statements.lean',
                        'success': True, 'declarations': 28, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'certificate_replay': {'success': True,'command':'python3 scripts/de_robust_edge_certificate.py',
        'cells':1925,'profiles':3,'arithmetic':'Fraction/isqrt, no floating arithmetic',
        'false_cell_controls':True,'receipt':'cells.json'},
    'original_return': {
        'target':'actual numerical edge-ratio bounds throughout full coupled robustness rectangle',
        'original_target_sources':['paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'],
        'original_population_data_tags_and_IVP_retained':True,
        'rectangle':'d[6/5,2],s[1/3,3],c=d/(delta0*s)',
        'native_scale_covariance':'D(a0,lambda/c^3,c*A)=D(a0/c,lambda,A)',
        'initial_D_equals1_retained':True,'original_left_side_start':'1/1000',
        'actual_initial_inverse_root_retained':True,'actual_parameter_dependent_prefactor_retained':True,
        'rescaled_start_range':'[1/4000,1/200]','rescaled_horizon_range':'[5,100]',
        'whole_cell_to_actual_integral_to_original_growth_return':True,
        'actual_native_endpoint_bound':'3<u*c^3<7/2',
        'actual_ANY_patch_first_time_at_endpoint':'c/2<a_first<=(8/3)*c',
        'actual_endpoint_ratio_all12_seeds_and_entire_rectangle':'3/8<R<1792/27',
        'all_signed_admitted_ratios':'0<=R<1792/27',
        'free_corner_root_constants_in_final_bound':False,
        'original_no_pinching_preserved':True,
        'floating_sampling_interpolation_or_ODE_error_used':False,
        'floating_or_independently_resampled_arrays_identified_with_exact_coupling':False,
        'sharp_observed_ratio_or_typicality_claimed':False,
        'other_sampled_population_edge_ratio_certificate':False,
        'physical_Lambda_bridge':False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Other sampled population edge ratios, first-time joint regularity and broader original-target audit',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1251 ordered cumulative standard-only closures (1223 immutable + 28 fresh), explicit actual robustness-edge ratios and finite-start scale-covariance return; {len(hashes)} fingerprints')
