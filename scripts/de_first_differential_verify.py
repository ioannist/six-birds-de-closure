"""Verify earned actual joint growth/first-time calculus and original readout returns."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '29acb05'
packet = 'results/first_differential_2026-10-03/'
mods = ['GrowthJointContinuity','GrowthUnitDifferential','GrowthJointDifferential','GrowthFirstDifferential','WindowFirstDifferential']


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
assert len(new) == 61
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1322 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_first_differential_axioms.lean'), re.M) == new
prior_path = 'results/first_regularity_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_first_regularity_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_first_differential_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_first_differential_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1322-declaration raw prefix plus freshly audited 61-declaration suffix.\n'
          'Baseline: 29acb05; earlier proof-source/toolchain identity checked by de_first_differential_verify.py.\n'
          'Full 1383-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_first_differential_statements.lean'), re.M)
statements = read(packet+'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new == checks == printed and not re.search(r'error:|warning:',statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.('+'|'.join(mods)+r')\.(\w+)',statements,re.M))
decls = {m.group(1)+'.'+m.group(2):' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name,d in decls.items():
    d = d.replace('SbtCosmo.Derivation.','').replace('⇑','')
    for group in mods+['GrowthScaleReturn','GrowthExistence','GrowthParameter','WindowSensitivity']:
        d = d.replace(group+'.','')
    decls[name]=d


def require(name,*tokens):
    d=decls[name]
    for token in tokens:assert token in d,(name,token)
    return d


C='GrowthJointContinuity.'
U='GrowthUnitDifferential.'
D='GrowthJointDifferential.'
F='GrowthFirstDifferential.'
W='WindowFirstDifferential.'
require(C+'moving_interval_margin','(hx : 0 ≤ p.2)', '(hp : 0 < rootSquared p.1 p.2)',
        '∃ eps, 0 < eps', '∀ᶠ (q : ℝ × ℝ) in nhds p', 'eps ≤ rootSquared q.1 t')
require(U+'primitive_unit_return','(c x : ℝ)', 'primitive c x = x *', 'unitKernel (c, x) t')
require(U+'unit_live_rectangle','(hx : 0 ≤ p.2)', '(hp : 0 < rootSquared p.1 p.2)',
        'U ∈ nhds p', 'IsCompact K', 'U ⊆ K', 'eps ≤ rootSquared q.1 (q.2 * t)')
require(U+'unit_uniform_derivative_bound','U ∈ nhds p', '‖unitGradient q t‖ ≤ B',
        'HasFDerivAt (fun r => unitKernel r t) (unitGradient q t) q')
require(U+'unit_integral_hasFDerivAt','HasFDerivAt (fun q =>', 'unitKernel q t', 'unitGradient p t')
require(U+'primitive_joint_hasFDerivAt','(hx : 0 ≤ p.2)', '(hp : 0 < rootSquared p.1 p.2)',
        'HasFDerivAt (fun q => primitive q.1 q.2) (primitiveGradient p) p')
require(D+'product_gradient_of_partials','(hf : DifferentiableAt ℝ f p)',
        '(hs : HasDerivAt (fun c => f (c, p.2)) s p.1)', 'HasFDerivAt f')
require(D+'growth_joint_hasFDerivAt','(hx : 0 ≤ p.2)', '(hp : 0 < rootSquared p.1 p.2)',
        'HasFDerivAt (fun q => growth q.1 q.2) (growthGradient p) p')
require(D+'native_growth_joint_hasFDerivAt','(ha0 : 0 < a0) (hA : a0 ≤ A)',
        '(hl : -(1 / A ^ 3) < p.1)', '(ha : p.2 ∈ Set.Icc a0 A)',
        'HasFDerivAt (fun q => nativeGrowth a0 q.1 q.2) (nativeGradient a0 p) p')
require(D+'native_growth_joint_c1','ContDiffOn ℝ 1 (fun q => nativeGrowth a0 q.1 q.2)',
        'Set.Ioi (-(1 / A ^ 3)) ×ˢ Set.Ioo a0 A')
require(F+'rootInverse_left','(hv : v ≠ 0)', 'Function.LeftInverse (rootInverse s v) (rootJacobian s v)')
require(F+'rootInverse_right','(hv : v ≠ 0)', 'Function.RightInverse (rootInverse s v) (rootJacobian s v)')
require(F+'firstTime_joint_hasFDerivAt','(ha0 : 0 < a0) (hA : a0 ≤ A)',
        '(hl : -(1 / A ^ 3) < p.2)', '(hT : 1 < p.1)', '(hf : p.1 < nativeGrowth a0 p.2 A)',
        'HasFDerivAt (fun q => GrowthFirstRecordLive.firstTime a0 A q.1 q.2) (firstGradient a0 A p) p')
require(F+'firstTime_joint_c1','ContDiffOn ℝ 1', 'GrowthFirstRecordLive.firstTime a0 A q.1 q.2',
        'InteriorDomain a0 A')
require(F+'firstTime_parameter_derivative','(hf : T < nativeGrowth a0 lam A)',
        'HasDerivAt (GrowthFirstRecordLive.firstTime a0 A T)', '-finalSensitivity a0',
        '/ nativeDerivative a0 lam', 'lam')
require(F+'firstTime_parameter_derivative_positive','(hf : T < nativeGrowth a0 lam A)',
        '0 < deriv (GrowthFirstRecordLive.firstTime a0 A T) lam')
require(W+'robust_time_joint_c1','{p : (ℝ × ℝ) × ℝ}',
        '(hR : WindowRobustRecord.Rectangle p.1.1 p.1.2)',
        '(hg : WindowRobustRecord.gate p.1.1 p.1.2 p.2)',
        'ContDiffAt ℝ 1 (fun q => WindowRobustRecord.time q.1.1 q.1.2 j q.2) p')
require(W+'robust_time_parameter_derivative','HasDerivAt (WindowRobustRecord.time d s j)',
        '-finalSensitivity (1 / 1000)', '/ nativeDerivative (1 / 1000) lam')
require(W+'robust_time_parameter_derivative_positive','0 < deriv (WindowRobustRecord.time d s j) lam')
require(W+'robust_ratio_joint_c1','(hl : p.2 ≠ 0)', 'ContDiffAt ℝ 1', 'WindowRobustRatio.ratio')
for suffix in ['time','ratio']:
    require(W+'robust_endpoint_'+suffix+'_c1','(hR : WindowRobustRecord.Rectangle p.1 p.2)',
            'ContDiffAt ℝ 1', 'scaledEndpoint q.1 q.2')
    require(W+'original_'+suffix+'_c1','(hg : WindowSample.realizedGate lam)',
            'ContDiffAt ℝ 1', 'WindowSignedRecord.'+suffix+' j')
    require(W+'patch_'+suffix+'_c1','{v : Bool}', '(hg : WindowPatchCounts.realizedGate v lam)',
            'ContDiffAt ℝ 1', 'WindowPatchCountRatio.'+suffix+' v j')
for prefix,fn in [('original','WindowSignedRecord.time j'),('patch','WindowPatchCountRatio.time v j')]:
    require(W+prefix+'_time_parameter_derivative','HasDerivAt ('+fn+')', '-finalSensitivity (1 / 1000)',
            '/ nativeDerivative (1 / 1000) lam')
    require(W+prefix+'_time_parameter_derivative_positive','0 < deriv ('+fn+') lam')
    require(W+prefix+'_ratio_c1','(hl : lam ≠ 0)')
    require(W+prefix+'_ratio_not_differentiable_at_zero','¬DifferentiableAt ℝ', 'ratio', '0')
require(W+'robust_ratio_not_differentiable_at_zero','(hR : WindowRobustRecord.Rectangle d s)',
        '¬DifferentiableAt ℝ (WindowRobustRatio.ratio d s j) 0')
require(W+'weighted_abs_not_differentiable','(hd : DifferentiableAt ℝ f 0)', '(hp : 0 < f 0)',
        '¬DifferentiableAt ℝ (fun lam => |lam| * f lam ^ 3) 0')
assert len(decls)==61
for name,d in decls.items():
    if name!=D+'product_gradient_of_partials' and name!=W+'weighted_abs_not_differentiable':
        for token in ['(hd : DifferentiableAt','(hf : DifferentiableAt','(hs : HasDerivAt',
                      '(hderivative :','(hinverse :','(hcontinuity :','(hselector :']:
            assert token not in d,(name,token)
    if name.startswith(W) and name!=W+'weighted_abs_not_differentiable':
        assert '(j : Fin 12)' in d
        assert '(hf :' not in d and '(hs :' not in d and '(hv :' not in d
        if 'robust_' in name: assert '(hR : WindowRobustRecord.Rectangle' in d
        if name.startswith(W+'robust_time') or name==W+'robust_ratio_joint_c1':
            assert '(hg : WindowRobustRecord.gate' in d
sources={
 'GrowthJointContinuity':['moving_interval_margin hx hp','root_margin_below',
    'intervalIntegral.continuous_parametric_primitive_of_continuous', 'native_log_chart_continuousAt'],
 'GrowthUnitDifferential':['smul_integral_comp_mul_left','unit_live_rectangle hx hp',
    'bddAbove_image hsafe','safeGradient_eq (eps := eps)',
    'hasFDerivAt_integral_of_dominated_of_fderiv_le','unit_uniform_derivative_bound hx hp',
    'unitKernel_hasFDerivAt (p := q)', 'primitive_unit_return q.1 q.2'],
 'GrowthJointDifferential':['primitive_joint_hasFDerivAt hx hp','hf.hasFDerivAt.comp',
    'hc.hasDerivAt.unique hs','hx.hasDerivAt.unique hv','growth_parameter_derivative hx hp',
    'growth_derivative hl','native_parameter_derivative ha0 hA hl ha',
    'contDiffOn_succ_iff_fderiv_of_isOpen'],
 'GrowthFirstDifferential':['ContinuousLinearEquiv.equivOfInverse','rootInverse_left hv','rootInverse_right hv',
    'native_growth_joint_hasFDerivAt (p := (p.2,a))','HasFDerivAt.of_local_left_inverse',
    'domain_mem_nhds ha0 hA hl hT hf','firstTime_spec ha0 hA hq.1 hq.2.1 hq.2.2',
    'firstTime_interior ha0 hA hl hT hf','native_parameter_derivative_negative',
    'firstGradient_continuousAt','contDiffOn_succ_iff_fderiv_of_isOpen'],
 'WindowFirstDifferential':['robust_strict_final hR hg j','patch_strict_final hg j',
    'firstTime_parameter_derivative_positive','robust_time_joint_c1 hR hg j',
    'GrowthEndpointDerivative.robustness_rectangle_c1','not_differentiableAt_abs_zero habs',
    'WindowPatchCounts.zero_passes v']}
for mod,tokens in sources.items():
    src=read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    for token in tokens:assert token in src,(mod,token)
build=read(packet+'lean_build.txt')
assert 'Build completed successfully (8166 jobs).' in build and not re.search(r'error:|warning:',build)
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
expected = old_config.replace('`SbtCosmo.Derivation.WindowFirstRegularity]',
    '`SbtCosmo.Derivation.WindowFirstRegularity, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
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
files.update(['scripts/de_first_differential_verify.py','math/FIRST_DIFFERENTIAL_LEAN_2026-10-03.md',
              'lean/manifests/check_first_differential_statements.lean','lean/manifests/check_first_differential_axioms.lean',
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
 'scope':'Earned actual quadrature/native joint derivative and first-time joint C1/signed implicit sensitivity',
 'lean_build':{'command':'lake build','success':True,'jobs':8166,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean -DwarningAsError=true manifests/check_first_differential_axioms.lean',
    'success':True,'declarations_cumulative':1383,'declarations_fresh':61,'declarations_preserved':1322,
    'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,
    'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),
    'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,
    'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean -DwarningAsError=true manifests/check_first_differential_statements.lean',
    'success':True,'declarations':61,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
    'target':'actual first-record joint C1 and signed implicit sensitivity under original parameters',
    'original_target_sources':['paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'],
    'selector':'unchanged GrowthFirstRecordLive.firstTime',
    'primitive_return':'exact x times unit-interval integral, retaining finite-start IVP',
    'actual_joint_kernel_derivative_constructed':True,
    'single_positive_root_margin_on_compact_live_neighborhood_constructed':True,
    'uniform_actual_derivative_bound_and_measurability_earned':True,
    'differentiation_under_integral_hypotheses_earned':True,
    'joint_differentiability_precedes_partial_derivative_identification':True,
    'actual_native_joint_derivative':'sensitivity dLambda + nativeVelocity dScale',
    'actual_firstTime_domain':'lambda>-1/A^3,1<T,T<nativeGrowth(a0,lambda,A)',
    'actual_nearby_root_equations_earn_local_inverse':True,
    'supplied_selector_continuity_derivative_or_inverse':False,
    'joint_firstTime_C1_including_lambda':True,
    'actual_parameter_derivative':'-actualSensitivity/nativeVelocity>0',
    'original_signed_population_lambda_C1':[32,64,128],
    'entire_original_coupled_rectangle_joint_time_C1':True,
    'entire_original_coupled_rectangle_joint_ratio_C1_away_from_zero':True,
    'actual_endpoint_time_and_ratio_joint_C1_in_knobs':True,
    'actual_N32_N64_N128_ratios_nondifferentiable_at_lambda_zero':True,
    'actual_coupled_rectangle_ratios_nondifferentiable_at_lambda_zero':True,
    'horizon_equality_ambient_smoothness_claimed':False,
    'arbitrary_rank_max_switch_smoothness_claimed':False,
    'population_reseeding_or_new_numeric_solver_used':False,
    'original_population_tags_IVP_and_initialD1_retained':True,'physical_Lambda_bridge':False},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_carrier_solver_rerun':False,
 'review':'adversarial self-review, not independent review',
 'next_construction':'Combined population-and-knob robustness and broader original-target audit; prior false/project-sized boundaries retained',
 'goal_complete':False,'source_sha256':hashes,'source_byte_representation':'checkout bytes; historical CRLF preserved',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized,
}
(root/packet/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'1383 ordered cumulative standard-only closures (1322 immutable + 61 fresh), actual joint first-time C1 and earned positive signed sensitivity; {len(hashes)} fingerprints')
