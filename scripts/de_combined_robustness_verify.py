"""Verify actual combined population/knob robustness and finite-start quadrature returns."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'a5b1dd9'
packet = 'results/combined_robustness_2026-10-03/'
mods = ['CombinedEdgeLowerData','CombinedEdgePrefixData','CombinedEdgeUpperData','CombinedEdgeQuadrature','GrowthCombinedCertificate','WindowPatchRobust','WindowPatchRobustRegularity','WindowPatchRobustEdge']


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
assert len(new) == 81
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1383 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_combined_robustness_axioms.lean'), re.M) == new
prior_path = 'results/first_differential_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_first_differential_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_combined_robustness_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_combined_robustness_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1383-declaration raw prefix plus freshly audited 81-declaration suffix.\n'
          'Baseline: a5b1dd9; earlier proof-source/toolchain identity checked by de_combined_robustness_verify.py.\n'
          'Full 1464-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_combined_robustness_statements.lean'), re.M)
statements = read(packet+'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new == checks == printed and not re.search(r'error:|warning:',statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.('+'|'.join(mods)+r')\.(\w+)',statements,re.M))
decls = {m.group(1)+'.'+m.group(2):' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name,d in decls.items():
    d = d.replace('SbtCosmo.Derivation.','').replace('⇑','')
    for group in mods+['GrowthScaleReturn','GrowthExistence','GrowthParameter','WindowSensitivity','GrowthQuadrature','GrowthEndpointDerivative','WindowRobustRecord','WindowRobustRatio','GrowthPopulationSensitivity']:
        d = d.replace(group+'.','')
    decls[name]=d


def require(name,*tokens):
    d=decls[name]
    for token in tokens:assert token in d,(name,token)
    return d


# Every fresh exported conclusion is matched to the actual original model.
W='WindowPatchRobust.'
R='WindowPatchRobustRegularity.'
E='WindowPatchRobustEdge.'
G='GrowthCombinedCertificate.'
for mod,n,start,end,lam in [('CombinedEdgeLowerData',607,'3 / 500','4 / 1','5 / 2'),
                          ('CombinedEdgePrefixData',522,'3 / 500','8 / 3','7 / 2'),
                          ('CombinedEdgeUpperData',785,'1 / 5000','120 / 1','7 / 2')]:
    require(mod+'.grid_endpoints',f'grid 0 = {start}',f'grid {n} = {end}')
    require(mod+'.cells',f'(i : Fin {n})','grid','bound',lam)
    require(mod+'.integral_sum',f'Finset.range {n}','bound')
    assert '(h' not in decls[mod+'.cells']
require('CombinedEdgeQuadrature.lower_integral','245 / 1000 ≤ integral (5 / 2) (3 / 500) 4')
require('CombinedEdgeQuadrature.prefix_integral','1908 / 10000 ≤ integral (7 / 2) (3 / 500) (8 / 3)')
require('CombinedEdgeQuadrature.upper_integral','integral (7 / 2) (1 / 5000) 120 ≤ 2036 / 10000')
require(G+'rescaled_start_bounds','(hc : c ∈ Set.Ioo (1 / 6) 5)',
        '1 / 1000 / c ∈ Set.Icc (1 / 5000) (3 / 500)')
require(G+'prefactor_upper','nativePrefactor (7 / 2) (1 / 1000 / c) ≤ (2500 + 1 / 1000) * c')
require(G+'initial_term_upper','(nativeRoot (7 / 2) (1 / 1000 / c))⁻¹ ≤ c / 300')
require(G+'lower_prefix_growth','970 * c < nativeGrowth (1 / 1000) (5 / 2 / c ^ 3) (4 * c)')
require(G+'upper_prefix_growth','897 * c < nativeGrowth (1 / 1000) (7 / 2 / c ^ 3) (8 / 3 * c)')
require(G+'upper_horizon_growth','nativeGrowth (1 / 1000) (7 / 2 / c ^ 3) 20 < 960 * c')
require(W+'original_aggregate_return','aggregateThreshold (WindowPatchCounts.amplitude v)',
        '(WindowPatchCountData.tag v) WindowSample.delta 10 = WindowPatchCounts.aggregateThreshold v')
require(W+'scaled_aggregate_return','(hd : 0 < d) (hs : 0 < s)',
        'aggregateThreshold (scaledAmplitude v s) (WindowPatchCountData.tag v) d 10 = aggregate v d s')
require(W+'normalization_bounds','(hR : Rectangle d s) (v : Bool)',
        'normalization v d s ∈ Set.Ioo (1 / 6) 5')
require(W+'normalization_outside_old_range','4 < normalization false 2 (1 / 3)',
        'normalization true (6 / 5) 3 < 1 / 5')
require(W+'aggregate_normalized','aggregate v d s = 965 * normalization v d s')
require(W+'aggregate_bounds','160 < aggregate v d s','aggregate v d s < 4825')
require(W+'endpoint_native_window','0 < upper v d s',
        'nativeGrowth (1 / 1000) (upper v d s) 20 = aggregate v d s',
        '∀ (lam : ℝ), gate v d s lam ↔ -(1 / 8000) < lam ∧ lam ≤ upper v d s')
require(W+'gate_iff_window','gate v d s lam ↔ lam ∈ Set.Ioc (-(1 / 8000)) (upper v d s)')
require(W+'threshold_bounds','450 * normalization v d s < threshold v d s j',
        'threshold v d s j < 897 * normalization v d s')
require(W+'strict_final','(hg : gate v d s lam)',
        'threshold v d s j < nativeGrowth (1 / 1000) lam 20')
require(W+'maximum_spec','(i : Fin (WindowPatchCountData.patchCount v))',
        'scaledAmplitude v s j i ≤ s * WindowPatchCountRatio.maximum v j',
        '∃ i, scaledAmplitude v s j i = s * WindowPatchCountRatio.maximum v j')
require(W+'threshold_return','d / (s * WindowPatchCountRatio.maximum v j) = threshold v d s j')
require(W+'time_iff_any_collapse','(ha : a ∈ Set.Icc (1 / 1000) 20)',
        '(∃ i, d ≤ scaledAmplitude v s j i * nativeGrowth (1 / 1000) lam a) ↔ time v d s j lam ≤ a')
require(W+'time_is_first_collapse','∀ a ∈ Set.Icc (1 / 1000) 20, a < time v d s j lam →',
        '¬∃ i, d ≤ scaledAmplitude v s j i * nativeGrowth (1 / 1000) lam a')
for suffix,old in [('gate','WindowPatchCounts.realizedGate v lam'),
                   ('time','WindowPatchCountRatio.time v j lam'),
                   ('ratio','WindowPatchCountRatio.ratio v j lam')]:
    require(W+'original_'+suffix+'_return','WindowSample.delta 1',old)
require(W+'endpoint_order','upper false d s < scaledEndpoint d s',
        'scaledEndpoint d s < upper true d s')
require(W+'gate_inclusions','gate false d s lam → gate d s lam','gate d s lam → gate true d s lam')
require(W+'strict_gate_witnesses','¬gate false d s (scaledEndpoint d s)',
        '¬gate d s (upper true d s)')
require(R+'endpoint_c1','ContDiffAt ℝ 1 (fun q => upper v q.1 q.2) p')
require(R+'endpoint_delta_derivative','HasDerivAt (fun u => upper v u s)',
        'endpointSensitivity (1 / 1000) (Real.log 20000) (aggregate v d s)',
        'WindowPatchCounts.aggregateThreshold v / (WindowSample.delta * s)')
require(R+'endpoint_delta_derivative_negative','deriv (fun u => upper v u s) d < 0')
require(R+'endpoint_amplitude_derivative','HasDerivAt (fun u => upper v d u)',
        '-d * WindowPatchCounts.aggregateThreshold v / (WindowSample.delta * s ^ 2)')
require(R+'endpoint_amplitude_derivative_positive','0 < deriv (fun u => upper v d u) s')
require(R+'time_joint_c1','{p : (ℝ × ℝ) × ℝ}', '(hg : gate v p.1.1 p.1.2 p.2)',
        'ContDiffAt ℝ 1 (fun q => time v q.1.1 q.1.2 j q.2) p')
require(R+'time_parameter_derivative','HasDerivAt (time v d s j)',
        '-finalSensitivity (1 / 1000)','/ nativeDerivative (1 / 1000) lam')
require(R+'time_parameter_derivative_positive','0 < deriv (time v d s j) lam')
require(R+'ratio_joint_c1','(hl : p.2 ≠ 0)', 'ContDiffAt ℝ 1')
require(R+'ratio_joint_continuousAt','ContinuousAt (fun q => ratio v q.1.1 q.1.2 j q.2) p')
for suffix in ['time','ratio']:
    require(R+'endpoint_'+suffix+'_c1','(hR : Rectangle p.1 p.2)',
            'ContDiffAt ℝ 1 (fun q => '+suffix+' v q.1 q.2 j (upper v q.1 q.2)) p')
require(R+'ratio_not_differentiable_at_zero','¬DifferentiableAt ℝ (ratio v d s j) 0')
require(E+'endpoint_normalized_bounds','5 / 2 < upper v d s * normalization v d s ^ 3',
        'upper v d s * normalization v d s ^ 3 < 7 / 2')
require(E+'original_endpoint_return','upper v WindowSample.delta 1 = WindowPatchCounts.upper v')
require(E+'endpoint_time_bounds','9 / 20 * normalization v d s < time v d s j (upper v d s)',
        'time v d s j (upper v d s) ≤ 8 / 3 * normalization v d s')
require(E+'endpoint_ratios','3645 / 16000 < ratio v d s j (upper v d s)',
        'ratio v d s j (upper v d s) < 1792 / 27')
require(E+'ratio_nonpositive_small','(hl : lam ≤ 0)','ratio v d s j lam < 1 / 64')
require(E+'full_window_ratios','(hg : gate v d s lam)',
        '0 ≤ ratio v d s j lam ∧ ratio v d s j lam < 1792 / 27')
require(E+'ratios_uniformly_arbitrarily_small','(he : 0 < epsilon)',
        '∃ lam, 0 < lam ∧ lam ≤ minimumEndpoint ∧ ∀ (d s : ℝ), Rectangle d s →',
        '∀ (v : Bool), gate v d s lam ∧ ∀ (j : Fin 12), 0 < ratio v d s j lam ∧ ratio v d s j lam < epsilon')
require(E+'all_populations_uniformly_arbitrarily_small','∃ lam, 0 < lam ∧ ∀ (d s : ℝ), Rectangle d s →',
        '∀ (v : Bool), gate v d s lam ∧ ∀ (j : Fin 12), 0 < ratio v d s j lam ∧ ratio v d s j lam < epsilon',
        'gate d s lam ∧ ∀ (j : Fin 12), 0 < ratio d s j lam ∧ ratio d s j lam < epsilon')
assert len(decls)==81
for name,d in decls.items():
    for token in ['(hd : DifferentiableAt','(hf : DifferentiableAt','(hs : HasDerivAt',
                  '(hderivative :','(hinverse :','(hcontinuity :','(hselector :',
                  '(hroot :','(hquadrature :','(hfirst :','(htime :','(hI :']:
        assert token not in d,(name,token)
    if name.startswith(G):assert '(hc : c ∈ Set.Ioo (1 / 6) 5)' in d
    if name.startswith(R) and 'aggregate_c1' not in name and 'threshold_c1' not in name:
        assert '(hR : Rectangle' in d
    if name.startswith((W,R,E)) and any(x in name.split('.')[-1] for x in ['time','ratio']):
        assert '(j : Fin 12)' in d or '∀ (j : Fin 12)' in d,(name,d)
source_checks={
 'CombinedEdgeQuadrature':['lower_grid','upper_grid','CombinedEdgeLowerData.cells',
    'CombinedEdgePrefixData.cells','CombinedEdgeUpperData.cells'],
 'GrowthCombinedCertificate':["native_scale_covariance hp.ne'",'native_growth_quadrature',
    'initial_term_upper hc','prefactor_upper hc','prefactor_lower hp','integral_interval_mono',
    '(nativeRoot (7/2) ((1/1000)/c))⁻¹'],
 'WindowPatchRobust':['WindowPatchCounts.sampled_maxima','WindowPatchCounts.sampled_rank_counts',
    'aggregateThreshold_amplitude_mul_pos','aggregateThreshold_delta_mul_pos',
    'populationEndpoint_native_window','scaled_aggregate_return hd hs v',
    'GrowthFirstRecord.any_patch_collapse_iff','threshold_return','time_iff_any_collapse',
    'WindowPatchCounts.threshold_order'],
 'WindowPatchRobustRegularity':['aggregate_c1 (rectangle_positive hR).2 v',
    'GrowthFirstDifferential.firstTime_joint_contDiffAt','strict_final hR hg j',
    'firstTime_parameter_derivative_positive','weighted_abs_not_differentiable'],
 'WindowPatchRobustEdge':['lower_prefix_growth hc','upper_horizon_growth hc','upper_prefix_growth hc',
    'native_endpoint_strictAntiOn','GrowthFirstRecordLive.firstTime_iff_threshold',
    'ratio_strictMono_nonnegative hR v j','let lam := min minimumEndpoint (epsilon/16000)',
    '(gate_inclusions hR lam).1 (hg false)']}
for mod,tokens in source_checks.items():
    src=read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    for token in tokens:assert token in src,(mod,token)
replay=subprocess.check_output([sys.executable,str(root/'scripts/de_combined_edge_certificate.py')],cwd=root).decode().strip()
assert replay=='Three exact profiles and false-cell controls passed; byte replay matched.'
cells=json.loads(read(packet+'cells.json'))
assert cells['arithmetic']=='Python Fraction and integer isqrt; no floating arithmetic'
assert cells['sqrt_denominator']==1_000_000
assert [(p['lambda'],p['domain'],p['direction'],p['cells'],p['integral_bound']) for p in cells['profiles']]==[
    ('5/2',['3/500','4'],'lower',607,'49/200'),
    ('7/2',['3/500','8/3'],'lower',522,'477/2500'),
    ('7/2',['1/5000','120'],'upper',785,'509/2500')]
assert sum(p['cells'] for p in cells['profiles'])==1914
assert all(p['false_cell_detected'] for p in cells['profiles'])
build=read(packet+'lean_build.txt')
assert 'Build completed successfully (8174 jobs).' in build and not re.search(r'error:|warning:',build)
assert 'Adversarial self-review, not independent review' in read(packet+'self_review.txt')

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
expected = old_config.replace('`SbtCosmo.Derivation.WindowFirstDifferential]',
    '`SbtCosmo.Derivation.WindowFirstDifferential, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected

lean_version = subprocess.check_output(['lake','env','lean','--version'],cwd=root/'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip() == mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot/p).read_bytes()) == h,p
for p in ['Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean',
          'Mathlib/MeasureTheory/Integral/DominatedConvergence.lean',
          'Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean',
          'Mathlib/Topology/Order/Compact.lean', 'Mathlib/Topology/Algebra/Module/Equiv.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Equiv.lean', 'Mathlib/Analysis/Calculus/FDeriv/Prod.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Mul.lean', 'Mathlib/Analysis/Calculus/Deriv/Inv.lean',
          'Mathlib/Analysis/SpecialFunctions/Sqrt.lean', 'Mathlib/Analysis/Calculus/ContDiff/Defs.lean']:
    blob=(libroot/p).read_bytes()
    assert blob==subprocess.check_output(['git','show','HEAD:'+p],cwd=libroot),p
    mathlib['direct_proof_source_sha256'][p]=digest(blob)
files=set(prior['source_sha256'])|{prior_path,'paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_combined_robustness_verify.py','scripts/de_combined_edge_certificate.py',
              'math/COMBINED_ROBUSTNESS_LEAN_2026-10-03.md',
              'lean/manifests/check_combined_robustness_statements.lean','lean/manifests/check_combined_robustness_axioms.lean',
              new_path,combined_path])
files.update(str(p.relative_to(root)) for p in (root/packet).iterdir() if p.name!='verification.json')
hashes={p:digest((root/p).read_bytes()) for p in sorted(files)}
git_hashes,normalized={},[]
for p in sorted(files):
    blob=(root/p).read_bytes()
    if b'\r\n' in blob:
        attrs=subprocess.check_output(['git','check-attr','text','eol','--',p],cwd=root).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob,p
        blob=blob.replace(b'\r\n',b'\n')
        normalized.append(p)
    git_hashes[p]=digest(blob)
v={
 'baseline_commit':baseline,
 'scope':'Actual original N32/N128 coupled rectangle windows, C1 first collapse, wider endpoint ratios and uniform all-population no-pinching',
 'lean_build':{'command':'lake build','success':True,'jobs':8174,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean -DwarningAsError=true manifests/check_combined_robustness_axioms.lean',
    'success':True,'declarations_cumulative':1464,'declarations_fresh':81,'declarations_preserved':1383,
    'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,
    'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),
    'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,
    'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean -DwarningAsError=true manifests/check_combined_robustness_statements.lean',
    'success':True,'declarations':81,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
    'target':'original population and knob robustness across full exact coupled rectangle',
    'original_target_sources':['paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'],
    'populations':[32,64,128],'seeds_each':12,
    'threshold_rectangle':['6/5','2'],'amplitude_rectangle':['1/3','3'],
    'additional_populations_separately_realized_fixed_tags':True,
    'actual_aggregate_from_original_maxima_and_rank_counts':True,
    'actual_scaled_aggregate':'965*c, c=factor(d,s)*T(v)/965',
    'earned_normalization_range':['1/6','5'],
    'both_actual_corners_outside_old_certificate_domain_proved':True,
    'whole_cell_exact_quadrature_cells':1914,'false_cell_controls_rejected':True,
    'finite_initial_scale_inverse_root_term_and_prefactor_retained':True,
    'actual_gate':'(-1/8000, actualPositiveEndpoint]',
    'normalized_actual_endpoint_bounds':['5/2','7/2'],
    'normalized_actual_endpoint_time_bounds':['9/20','8/3'],
    'actual_endpoint_ratio_bounds':['3645/16000','1792/27'],
    'full_actual_signed_window_ratio_upper_bound':'1792/27',
    'nonpositive_actual_ratio_upper_bound':'1/64',
    'first_ANY_patch_collapse_iff_and_minimality_returned':True,
    'strict_first_threshold_slack_earned_even_at_aggregate_endpoint':True,
    'endpoint_and_endpoint_time_ratio_joint_C1_in_knobs':True,
    'first_time_joint_C1_in_knobs_and_lambda':True,
    'actual_parameter_derivative':'-actualSensitivity/nativeVelocity>0',
    'ratios_continuous_all_lambda_C1_away_zero_nondifferentiable_zero':True,
    'actual_gate_nesting_and_strict_endpoint_order_across_entire_rectangle':True,
    'one_positive_lambda_for_all36_ratios_and_all_rectangle_points':True,
    'supplied_roots_derivatives_inverses_continuity':False,
    'population_reseeding_or_new_numeric_solver_used':False,
    'smooth_discrete_population_size_claimed':False,
    'identity_with_separately_rounded_numpy_rescaling_claimed':False,
    'sharp_edge_clustering_or_measure_typicality_claimed':False,
    'prior_stronger_narrow_range_estimates_preserved':True,
    'original_population_tags_IVP_and_initialD1_retained':True,
    'physical_Lambda_bridge':False},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_carrier_solver_rerun':False,
 'review':'adversarial self-review, not independent review',
 'next_construction':'Broader original-target audit; prior false/project-sized boundaries retained',
 'goal_complete':False,'source_sha256':hashes,'source_byte_representation':'checkout bytes; historical CRLF preserved',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized,
}
(root/packet/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'1464 ordered cumulative standard-only closures (1383 immutable + 81 fresh), actual combined robustness and uniform36-readout no-pinching; {len(hashes)} fingerprints')
