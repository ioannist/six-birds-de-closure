"""Verify earned joint first-time continuity and actual original knob regularity."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '999d7ae'
packet = 'results/first_regularity_2026-10-03/'
mods = ['GrowthFirstContinuity','FirstPopulationContinuity','WindowFirstRegularity']


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
assert len(new) == 38
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1284 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_first_regularity_axioms.lean'), re.M) == new
prior_path = 'results/patch_ratio_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_patch_ratio_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_first_regularity_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_first_regularity_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1284-declaration raw prefix plus freshly audited 38-declaration suffix.\n'
          'Baseline: 999d7ae; earlier proof-source/toolchain identity checked by de_first_regularity_verify.py.\n'
          'Full 1322-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_first_regularity_statements.lean'), re.M)
statements = read(packet+'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new == checks == printed and not re.search(r'error:|warning:',statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.('+'|'.join(mods)+r')\.(\w+)',statements,re.M))
decls = {m.group(1)+'.'+m.group(2):' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name,d in decls.items():
    d = d.replace('SbtCosmo.Derivation.','')
    for group in ['GrowthFirstContinuity','FirstPopulationContinuity','GrowthScaleReturn']:
        d = d.replace(group+'.','')
    decls[name]=d


def require(name,*tokens):
    d=decls[name]
    for token in tokens:assert token in d,(name,token)
    return d


G='GrowthFirstContinuity.'
P='FirstPopulationContinuity.'
W='WindowFirstRegularity.'
require(G+'firstTime_eq_of_root','(hf : T ≤ nativeGrowth a0 lam A)',
        '(he : nativeGrowth a0 lam a = T)', 'GrowthFirstRecordLive.firstTime a0 A T lam = a')
require(G+'firstTime_interior','(hf : T < nativeGrowth a0 lam A)',
        'GrowthFirstRecordLive.firstTime a0 A T lam ∈ Set.Ioo a0 A')
require(G+'domain_mem_nhds','(hl : -(1 / A ^ 3) < p.2)', '(hT : 1 < p.1)',
        '(hf : p.1 < nativeGrowth a0 p.2 A)', 'Domain a0 A ∈ nhds p')
require(G+'firstTime_joint_continuousOn','(ha0 : 0 < a0) (hA : a0 ≤ A)',
        'ContinuousOn (fun p => GrowthFirstRecordLive.firstTime a0 A p.1 p.2) (Domain a0 A)')
require(G+'firstTime_joint_continuousAt','(hf : p.1 < nativeGrowth a0 p.2 A)',
        'ContinuousAt (fun q => GrowthFirstRecordLive.firstTime a0 A q.1 q.2) p')
require(G+'firstTime_threshold_continuousAt','(hf : T < nativeGrowth a0 lam A)',
        'ContinuousAt (fun d => GrowthFirstRecordLive.firstTime a0 A d lam) T')
require(G+'firstTime_parameter_continuousAt','(hf : T < nativeGrowth a0 lam A)',
        'ContinuousAt (GrowthFirstRecordLive.firstTime a0 A T) lam')
require(G+'firstTime_threshold_derivative','(hf : T < nativeGrowth a0 lam A)',
        'HasDerivAt (fun d => GrowthFirstRecordLive.firstTime a0 A d lam)',
        '(nativeDerivative a0 lam (GrowthFirstRecordLive.firstTime a0 A T lam))⁻¹ T')
require(G+'firstTime_threshold_derivative_positive','(hf : T < nativeGrowth a0 lam A)',
        '0 < deriv (fun d => GrowthFirstRecordLive.firstTime a0 A d lam) T')
require(G+'firstTime_threshold_sensitivity_continuousAt','(hf : T < nativeGrowth a0 lam A)',
        'ContinuousAt (fun d => (nativeDerivative a0 lam (GrowthFirstRecordLive.firstTime a0 A d lam))⁻¹) T')
require(G+'firstTime_threshold_c1','(hl : -(1 / A ^ 3) < lam)',
        'ContDiffOn ℝ 1 (fun d => GrowthFirstRecordLive.firstTime a0 A d lam)',
        '(Set.Ioo 1 (nativeGrowth a0 lam A))')
require(G+'horizon_equality_not_continuous','(ha0 : 0 < a0) (hA : a0 < A)',
        '¬ContinuousAt (fun d => GrowthFirstRecordLive.firstTime a0 A d 0) (A / a0)')
require(P+'maximum_spec','[Fintype ι] [Nonempty ι]',
        '(∀ (i : ι), amplitude i ≤ maximum amplitude) ∧ ∃ i, amplitude i = maximum amplitude')
require(P+'maximum_lipschitz','[Fintype ι]', 'LipschitzWith 1 maximum')
require(P+'maximum_eq_of_attained','(hb : ∀ (i : ι), amplitude i ≤ m)',
        '(he : ∃ i, amplitude i = m)', 'maximum amplitude = m')
require(P+'threshold_continuousAt','(ha : ∀ (i : ι), ContinuousAt (fun q => amplitude q i) p)',
        '(hd : ContinuousAt delta p)', '(hm : maximum (amplitude p) ≠ 0)',
        'ContinuousAt (fun q => threshold (amplitude q) (delta q)) p')
require(P+'time_continuousAt','(hlc : ContinuousAt lam p)', '(hm : 0 < maximum (amplitude p))',
        '(hl : -(1 / A ^ 3) < lam p)', '(hT : 1 < threshold (amplitude p) (delta p))',
        '(hf : threshold (amplitude p) (delta p) < nativeGrowth a0 (lam p) A)',
        'ContinuousAt (fun q => time a0 A (amplitude q) (delta q) (lam q)) p')
require(P+'time_iff_any_collapse','[Fintype ι] [Nonempty ι]', '(hm : 0 < maximum amplitude)',
        '(ha : a ∈ Set.Icc a0 A)',
        '(∃ i, delta ≤ amplitude i * nativeGrowth a0 lam a) ↔ time a0 A amplitude delta lam ≤ a')
require(P+'tied_maximum','maximum fun b => if b = true then 1 + t else 1 - t', '1 + |t|')
require(P+'tied_maximum_not_differentiable','¬DifferentiableAt ℝ',
        'maximum fun b => if b = true then 1 + t else 1 - t', '0')
require(P+'tied_time_eq','(ht : t ∈ Set.Ioo (-1) 1)',
        'time (1 / 1000) 20 (fun b => if b = true then 1 + t else 1 - t) 500 0 = 1 / 2 / (1 + |t|)')
require(P+'tied_time_not_differentiable','¬DifferentiableAt ℝ',
        'time (1 / 1000) 20 (fun b => if b = true then 1 + t else 1 - t) 500 0)', '0')
require(W+'robust_strict_final','(hR : WindowRobustRecord.Rectangle d s)',
        '(hg : WindowRobustRecord.gate d s lam)', 'WindowRobustRecord.threshold d s j < nativeGrowth (1 / 1000) lam 20')
require(W+'robust_threshold_c1','(hs : 0 < p.2)', '(j : Fin 12)',
        'ContDiffAt ℝ 1 (fun q => WindowRobustRecord.threshold q.1 q.2 j) p')
require(W+'robust_time_joint_continuousAt','{p : (ℝ × ℝ) × ℝ}',
        'ContinuousAt (fun q => WindowRobustRecord.time q.1.1 q.1.2 j q.2) p')
require(W+'robust_ratio_joint_continuousAt','{p : (ℝ × ℝ) × ℝ}',
        'ContinuousAt (fun q => WindowRobustRatio.ratio q.1.1 q.1.2 j q.2) p')
require(W+'robust_time_knobs_c1','{p : ℝ × ℝ} {lam : ℝ}',
        'ContDiffAt ℝ 1 (fun q => WindowRobustRecord.time q.1 q.2 j lam) p')
require(W+'robust_time_delta_derivative','HasDerivAt (fun u => WindowRobustRecord.time u s j lam)',
        '(WindowFirstRecord.threshold j / (WindowSample.delta * s) *',
        '(nativeDerivative (1 / 1000) lam (WindowRobustRecord.time d s j lam))⁻¹) d')
require(W+'robust_time_delta_derivative_positive',
        '0 < deriv (fun u => WindowRobustRecord.time u s j lam) d')
require(W+'robust_time_amplitude_derivative','HasDerivAt (fun u => WindowRobustRecord.time d u j lam)',
        '(-(d * WindowSample.delta * WindowFirstRecord.threshold j) / (WindowSample.delta * s) ^ 2 *',
        '(nativeDerivative (1 / 1000) lam (WindowRobustRecord.time d s j lam))⁻¹) s')
require(W+'robust_time_amplitude_derivative_negative',
        'deriv (fun u => WindowRobustRecord.time d u j lam) s < 0')
require(W+'robust_endpoint_time_continuousAt',
        'ContinuousAt (fun q => WindowRobustRecord.time q.1 q.2 j (WindowSensitivity.scaledEndpoint q.1 q.2)) p')
require(W+'robust_endpoint_ratio_continuousAt',
        'ContinuousAt (fun q => WindowRobustRatio.ratio q.1 q.2 j (WindowSensitivity.scaledEndpoint q.1 q.2)) p')
require(W+'original_time_continuousAt','(hg : WindowSample.realizedGate lam)',
        'ContinuousAt (WindowSignedRecord.time j) lam')
require(W+'original_ratio_continuousAt','(hg : WindowSample.realizedGate lam)',
        'ContinuousAt (WindowSignedRecord.ratio j) lam')
require(W+'patch_strict_final','(hg : WindowPatchCounts.realizedGate v lam)',
        'WindowPatchCountRatio.threshold v j < nativeGrowth (1 / 1000) lam 20')
require(W+'patch_time_continuousAt','(hg : WindowPatchCounts.realizedGate v lam)',
        'ContinuousAt (WindowPatchCountRatio.time v j) lam')
require(W+'patch_ratio_continuousAt','(hg : WindowPatchCounts.realizedGate v lam)',
        'ContinuousAt (WindowPatchCountRatio.ratio v j) lam')
assert len(decls)==38
for name,d in decls.items():
    for forbidden in ['(htime :','(hinverse :','(hselector :','(hcontinuity :','(hderivative :']:
        assert forbidden not in d,(name,forbidden)
    if name.startswith(W):
        if name!=W+'robust_threshold_c1': assert '(j : Fin 12)' in d
        assert '(hf :' not in d and '(hm :' not in d and '(he :' not in d
        if name.startswith(W+'robust_') and name!=W+'robust_threshold_c1':
            assert '(hR : WindowRobustRecord.Rectangle' in d
        if name.startswith(W+'robust_') and 'endpoint' not in name and name!=W+'robust_threshold_c1':
            assert '(hg : WindowRobustRecord.gate' in d
sources={
 'GrowthFirstContinuity':[
    '{p | -(1/A^3) < p.2 ∧ 1 < p.1 ∧ p.1 ≤ nativeGrowth a0 p.2 A}',
    'apply tendsto_order.mpr','self_mem_nhdsWithin','b < a0','A < b',
    'GrowthParameter.native_parameter_derivative','GrowthFirstRecord.native_strictMonoOn',
    'firstTime_joint_continuousOn ha0 hA','domain_mem_nhds ha0 hA',
    'HasDerivAt.of_local_left_inverse','Ioo_mem_nhds hT hf',
    '(firstTime_spec ha0 hA hl hd.1 hd.2.le).2','native_velocity_derivative ha0 hA',
    'tendsto_nhds_unique hconst hlimit','simp only [firstTime,dif_neg hn]'],
 'FirstPopulationContinuity':[
    'tagMaximumValue amplitude (fun _ => false) false','delta / maximum amplitude',
    'GrowthFirstRecordLive.firstTime a0 A (threshold amplitude delta) lam',
    'tagMaximumValue_spec amplitude ht','tagMaximumValue_lipschitz (fun _ => false) false',
    'firstTime_joint_continuousAt ha0 hA hl hT hf','GrowthFirstRecord.any_patch_collapse_iff',
    'GrowthFirstRecordLive.firstTime_iff_threshold','not_differentiableAt_abs_zero ha',
    'GrowthFirstRecordLive.firstTime_at_zero','hquot.congr_of_eventuallyEq he'],
 'WindowFirstRegularity':[
    '(threshold_below_aggregate hR j).trans_le hm','robust_strict_final hR hg j',
    'firstTime_joint_continuousAt','firstTime_threshold_c1','firstTime_threshold_derivative',
    'WindowFirstRecord.threshold j/(WindowSample.delta*s)',
    '-(d*WindowSample.delta*WindowFirstRecord.threshold j)/(WindowSample.delta*s)^2',
    'GrowthEndpointDerivative.robustness_rectangle_c1 hR.1 hR.2',
    'WindowPatchCountRatio.aggregate_normalized v','patch_strict_final hg j']}
for mod,tokens in sources.items():
    src=read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    for token in tokens:assert token in src,(mod,token)
build=read(packet+'lean_build.txt')
assert 'Build completed successfully (8161 jobs).' in build and not re.search(r'error:|warning:',build)
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
expected = old_config.replace('`SbtCosmo.Derivation.WindowPatchCountRatio]',
    '`SbtCosmo.Derivation.WindowPatchCountRatio, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected

lean_version = subprocess.check_output(['lake','env','lean','--version'],cwd=root/'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip() == mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot/p).read_bytes()) == h,p
for p in ['Mathlib/Topology/Order/Basic.lean','Mathlib/Topology/Order/OrderClosed.lean',
          'Mathlib/Topology/ContinuousOn.lean','Mathlib/Analysis/Calculus/Deriv/Inverse.lean',
          'Mathlib/Analysis/Calculus/ContDiff/Deriv.lean','Mathlib/Analysis/Calculus/FDeriv/Congr.lean',
          'Mathlib/Analysis/Calculus/Deriv/Abs.lean']:
    blob=(libroot/p).read_bytes()
    assert blob==subprocess.check_output(['git','show','HEAD:'+p],cwd=libroot),p
    mathlib['direct_proof_source_sha256'][p]=digest(blob)
files=set(prior['source_sha256'])|{prior_path,'paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_first_regularity_verify.py','math/FIRST_REGULARITY_LEAN_2026-10-03.md',
              'lean/manifests/check_first_regularity_statements.lean','lean/manifests/check_first_regularity_axioms.lean',
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
 'scope':'Earned actual first-time joint continuity, finite amplitude stability and original coupled-knob C1',
 'lean_build':{'command':'lake build','success':True,'jobs':8161,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean -DwarningAsError=true manifests/check_first_regularity_axioms.lean',
    'success':True,'declarations_cumulative':1322,'declarations_fresh':38,'declarations_preserved':1284,
    'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,
    'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),
    'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,
    'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean -DwarningAsError=true manifests/check_first_regularity_statements.lean',
    'success':True,'declarations':38,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
    'target':'actual first-record regularity under original robustness parameters',
    'original_target_sources':['paper/sections/sec_05_window.tex','paper/appendices/app_a_carriers.tex'],
    'selector':'unchanged GrowthFirstRecordLive.firstTime',
    'actual_domain':'lambda>-1/A^3,1<T,T<=nativeGrowth(a0,lambda,A)',
    'joint_relative_continuity_including_horizon_equality':True,
    'strict_final_slack_earns_ambient_neighborhood_and_joint_continuity':True,
    'supplied_selector_continuity_or_inverse':False,
    'actual_local_root_equations_supply_left_inverse':True,
    'actual_threshold_derivative':'1/nativeVelocity>0',
    'threshold_C1_at_fixed_lambda':'1<T<nativeGrowth(a0,lambda,A)',
    'finite_maximum':'actual attained1-Lipschitz global maximum, no fixed maximizing patch',
    'generic_continuous_finite_input_first_time':'explicit maximum/domain margins and input continuity',
    'actual_ANY_patch_collapse_return':True,
    'original_first_threshold_strict_slack_earned_from_gate':True,
    'original_signed_population_lambda_continuity':[32,64,128],
    'entire_original_coupled_rectangle_joint_time_ratio_continuity':True,
    'coupled_knob_C1_at_fixed_signed_lambda':True,
    'actual_delta_derivative':'Tfirst_original/(delta0*s)/nativeVelocity>0',
    'actual_amplitude_derivative':'-d*delta0*Tfirst_original/(delta0*s)^2/nativeVelocity<0',
    'actual_endpoint_time_and_ratio_continuity':True,
    'boundary_control':'matter horizon equality: ambient fallback selector discontinuous',
    'tie_control':'positive two-patch switch: actual maximum AND actual first time nondifferentiable',
    'tie_control_delta':'500, generic control, not original rectangle threshold',
    'joint_C1_including_lambda_or_implicit_lambda_derivative_claimed':False,
    'universal_smoothness_through_maximizing_switches_claimed':False,
    'population_reseeding_or_new_numeric_solver_used':False,
    'original_population_tags_IVP_and_initialD1_retained':True,'physical_Lambda_bridge':False},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_carrier_solver_rerun':False,
 'review':'adversarial self-review, not independent review',
 'next_construction':'Joint C1 including lambda/implicit sensitivity, combined population-and-knob robustness and broader original-target audit',
 'goal_complete':False,'source_sha256':hashes,'source_byte_representation':'checkout bytes; historical CRLF preserved',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized,
}
(root/packet/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'1322 ordered cumulative standard-only closures (1284 immutable + 38 fresh), actual joint first-time continuity and earned knob C1; {len(hashes)} fingerprints')
