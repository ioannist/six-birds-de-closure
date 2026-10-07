"""Verify original32-patch allocation mechanics, exact selected screening and actual must-flip controls."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = '5b18121'
packet = 'results/allocation_sample_2026-10-03/'
mods = ['AllocationSampleData','AllocationScreening','AllocationSample','AllocationSampleControls']


def read(p):
    return (root / p).read_text()


def digest(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(ref, p):
    return subprocess.check_output(['git', 'show', ref + ':' + p], cwd=root)


def canonical_git_bytes(p):
    blob = (root / p).read_bytes()
    if b'\r\n' in blob:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', p], cwd=root).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob, p
        blob = blob.replace(b'\r\n', b'\n')
    return blob


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
assert len(new) == 54
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1474 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_allocation_sample_axioms.lean'), re.M) == new
prior_path = 'results/smooth_prior_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_smooth_prior_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_allocation_sample_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_allocation_sample_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1474-declaration raw prefix plus freshly audited 54-declaration suffix.\n'
          'Baseline: 5b18121; earlier proof-source/toolchain identity checked by de_allocation_sample_verify.py.\n'
          'Full 1528-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_allocation_sample_statements.lean'), re.M)
statements = read(packet+'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new == checks == printed and not re.search(r'error:|warning:',statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.('+'|'.join(mods)+r')\.(\w+)',statements,re.M))
decls = {m.group(1)+'.'+m.group(2):' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name,d in decls.items():
    d = d.replace('SbtCosmo.Derivation.','').replace('⇑','')
    for group in mods+['AllocationPrice','AllocationSensitivity','GrowthScaleReturn','GrowthExistence','GrowthParameter','WindowSensitivity','WindowPatchRobust','WindowPatchRobustEdge','GrowthQuadrature','GrowthEndpointDerivative','WindowRobustRecord','WindowRobustRatio','GrowthPopulationSensitivity']:
        d = d.replace(group+'.','')
    decls[name]=d


def require(name,*tokens):
    d=decls[name]
    for token in tokens:assert token in d,(name,token)
    return d


# Original represented inputs, exact selected functions and controls.
D='AllocationSampleData.'
G='AllocationScreening.'
A='AllocationSample.'
C='AllocationSampleControls.'
require(D+'parameter_bounds','(i : Fin 32)','7 / 10 < weight i','1 / 5 < curvature i')
require(D+'budget_bounds','∀ (j : Fin 10), 0 < budgets j','22 < budget','budget < 23')
require(D+'cells','(q : Fin 5) (i : Fin 32)','0 < lower q i','price q ≤ weight i / (1 + lower q i)',
        'weight i / (1 + upper q i) - curvature i * upper q i ≤ price q')
require(D+'sweep_mass_bounds','(j : Fin 10)','if ↑j < 7 then','budgets j < ∑ i, lower 0 i',
        'else ∑ i, upper 0 i < budgets j')
require(D+'original_offsets','∀ (j : Fin 3)','-(1 / 4) ≤ offsets j','offsets j ≤ 1 / 4',
        'offsets 0 < -(1 / 5)','1 / 5 < offsets 2')
require(G+'demand_margin_bounds','(hw : 0 < w) (hc : 0 < c)','(hml : p ≤ marginal w c b lo)',
        '(hmh : marginal w c b hi ≤ p)','lo ≤ demand w c b p ∧ demand w c b p ≤ hi')
require(G+'selected_price_response_bounds','(hB : 0 < B) (hlo : 0 < lo)',
        'B < mass fun i => demand (w i) (c i) (b i) lo',
        '(mass fun i => demand (w i) (c i) (b i) hi) < B',
        'lo < selectedPrice w c b hw hc B','selectedPrice w c b hw hc B < hi')
require(G+'selected_offset_screened','(ha : mass (selectedAllocation w c b hw hc B) = B)',
        '(hp : 0 ≤ selectedPrice w c b hw hc B + s)',
        'selectedAllocation w c (fun i => b i + s) hw hc B = selectedAllocation w c b hw hc B',
        'selectedPrice w c (fun i => b i + s) hw hc B = selectedPrice w c b hw hc B + s')
require(A+'original_price_bounds','46112 / 100000 < price 0 ∧ price 0 < 46113 / 100000')
require(A+'actual_kkt','(s : ℝ)','AllocationKKT weights curvatures (fun x => s) (allocation s) budget (price s)')
require(A+'actual_global_optimal','{x : Fin 32 → ℝ} (hx : ∀ (i : Fin 32), 0 ≤ x i)',
        '(hb : mass x ≤ budget)','utility weights curvatures (fun x => s) x ≤',
        'penalty curvatures (allocation s) x')
require(A+'actual_unique_optimizer','(hb : mass x ≤ budget)', 'allocation s = x')
require(A+'original_active','mass (allocation 0) = budget')
require(A+'original_allocations_positive','(i : Fin 32)','0 < allocation 0 i')
require(A+'original_stationarity','(i : Fin 32)', 'marginal (weights i) (curvatures i) 0 (allocation 0 i) = price 0')
require(A+'original_heterogeneity','allocation 0 0 < allocation 0 1')
require(A+'screening','(hs : s ∈ Set.Icc (-(1 / 4)) (1 / 4))',
        'allocation s = allocation 0 ∧ price s = price 0 + s')
require(A+'screened_value','value s budget = value 0 budget - s * budget')
require(A+'original_offsets_return','(j : Fin 3)', 'allocation (offsets j) = allocation 0',
        'price (offsets j) = price 0 + offsets j')
require(A+'actual_value_derivative','(hB : 0 < B) (s : ℝ)','HasDerivAt (value s)',
        '-selectedPrice weights curvatures (fun x => s) weights_positive curvatures_positive B')
require(A+'original_negative_value_derivative','deriv (value 0) budget = -price 0',
        'deriv (value 0) budget < 0')
require(A+'sweep_active','{j : Fin 10} (hj : ↑j < 7)',
        '0 < selectedPrice weights curvatures (fun x => 0) weights_positive curvatures_positive (budgets j)',
        '(selectedAllocation weights curvatures (fun x => 0) weights_positive curvatures_positive (budgets j)) = budgets j')
require(A+'sweep_slack','{j : Fin 10} (hj : 7 ≤ ↑j)',
        'selectedPrice weights curvatures (fun x => 0) weights_positive curvatures_positive (budgets j) = 0',
        '(selectedAllocation weights curvatures (fun x => 0) weights_positive curvatures_positive (budgets j)) < budgets j')
require(C+'source_kkt','(s : ℝ)', 'AllocationKKT weights curvatures (fun x => s) (sourceAllocation s)',
        '(mass (sourceAllocation s)) 0')
require(C+'source_unconstrained_optimal','(s : ℝ) {x : Fin 32 → ℝ} (hx : ∀ (i : Fin 32), 0 ≤ x i)',
        'utility weights curvatures (fun x => s) x ≤',
        'penalty curvatures (sourceAllocation s) x')
assert '(hb :' not in decls[C+'source_unconstrained_optimal']
require(C+'source_unconstrained_unique','sourceAllocation s = x')
require(C+'local_controls','∀ (i : Fin 32), 0 < localPrice i','1 / 20 < localPrice 1 - localPrice 0')
require(C+'local_kkt','(i : Fin 32)', 'AllocationKKT (fun x => weights i) (fun x => curvatures i)',
        '(fun x => budget / 32) (budget / 32) (localPrice i)')
require(C+'local_selector_return','selectedAllocation (fun x => weights i)','fun x => budget / 32',
        'selectedPrice (fun x => weights i)','= localPrice i')
require(C+'local_selected_prices_unequal','selectedPrice (fun x => weights 0)',
        '≠ selectedPrice (fun x => weights 1)')
require(C+'local_budget_total','(mass fun x => budget / 32) = budget')
require(C+'local_allocation_differs','allocation 0 ≠ fun x => budget / 32')
require(C+'source_profile_return','response 0 = sourceAllocation 0','response 3 = sourceAllocation (-(1 / 5))',
        'response 4 = sourceAllocation (1 / 5)')
require(C+'source_signed_shift_gaps','1 / 2 < sourceAllocation 0 8 - sourceAllocation (-(1 / 5)) 8',
        '1 / 2 < sourceAllocation (1 / 5) 8 - sourceAllocation 0 8')
require(C+'source_movement_large','(hs : s ≤ -(1 / 5) ∨ 1 / 5 ≤ s)',
        '1 / 2 < |sourceAllocation s 8 - sourceAllocation 0 8|')
require(C+'original_source_controls','1 / 2 < |sourceAllocation (offsets 0) 8 - sourceAllocation 0 8|',
        '1 / 2 < |sourceAllocation (offsets 2) 8 - sourceAllocation 0 8|')
assert len(decls)==54
for name,d in decls.items():
    if name.startswith((A,C,D)):
        for token in ['(hroot :','(hprice :','(hKKT :','(hkkt :','(hactive :',
                      '(hderivative :','(hoptimizer :','(hresponse :','(hcontinuity :',
                      '(hw :','(hc :','(hdata :']:
            assert token not in d,(name,token)
    if name.startswith(D):assert '(h' not in d,(name,d)
sources={
 'AllocationScreening':['marginal_strictAntiOn','demand_certificate','demand_stationary_of_positive',
    'demand_antitone','hk.feasible','hk.budget_complementarity','active_offset_kkt','kkt_unique',
    'selected_offset_screened hw hc hB ha hp','utility_offset_return'],
 'AllocationSample':['exact_mod_cast AllocationSampleData.cells q i','demand_margin_bounds',
    'AllocationSampleData.price_mass_bounds','selected_price_response_bounds',
    'kkt_global_optimal','kkt_unique_optimizer','original_price_bounds.1','demand_positive',
    'selected_offset_screened','selected_cost_offset_return','cost_value_hasDerivAt',
    'AllocationSampleData.sweep_mass_bounds','below_unconstrained_price_positive',
    'below_unconstrained_budget_active','above_unconstrained_price_zero'],
 'AllocationSampleControls':['(fun _ : Fin 1 => weights i)', 'AllocationSampleData.local_price_control',
    'kkt_unique','kkt_strong_support','source_kkt s','penalty_zero_iff','local_kkt i','original_heterogeneity','demand_offset_return',
    'AllocationSampleData.source_shift_gaps','demand_antitone','source_offset_mono',
    'AllocationSampleData.original_offsets.2.1']}
for mod,tokens in sources.items():
    src=read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    for token in tokens:assert token in src,(mod,token)
python='/mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin/python'
replay=subprocess.check_output([python,str(root/'scripts/de_allocation_sample_certificate.py')],cwd=root).decode().strip()
assert replay=='Original32 coefficients,10 budgets and160 rational response cells verified; byte replay matched.'
cells=json.loads(read(packet+'cells.json'))
assert cells['numpy_version']=='1.26.4' and cells['coefficient_count']==32 and cells['budget_count']==10
assert cells['cells']==160 and cells['denominator']==1_000_000 and cells['false_cell_detected']
assert cells['prices']==['0','1441/3125','46113/100000','1/5','-1/5']
assert len(cells['weights'])==len(cells['curvatures'])==32 and len(cells['offsets'])==3
assert len(cells['lower'])==len(cells['upper'])==5
assert all(len(xs)==32 for xs in cells['lower']+cells['upper'])
assert cells['source_shift_witness_patch']==8
assert cells['csv_formatted_inputs_and_budgets_match'] and not cells['optimizer_or_root_finding_solver_rerun']
assert cells['coefficients_rng_used']==False and cells['original_config_seed_unused_by_coefficient_generator']
assert digest((root/'scripts/de_dual_carrier.py').read_bytes())==cells['original_source_sha256']
for p,h in cells['historical_inputs_sha256'].items():
    assert digest((root/p).read_bytes())==h and canonical_git_bytes(p)==git_blob(baseline,p),p
assert (root/'scripts/de_dual_carrier.py').read_bytes()==git_blob(baseline,'scripts/de_dual_carrier.py')
build=read(packet+'lean_build.txt')
assert 'Build completed successfully (8179 jobs).' in build and not re.search(r'error:|warning:',build)
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
expected = old_config.replace('`SbtCosmo.Derivation.WindowSmoothPrior]',
    '`SbtCosmo.Derivation.WindowSmoothPrior, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected

lean_version = subprocess.check_output(['lake','env','lean','--version'],cwd=root/'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip() == mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot/p).read_bytes()) == h,p
for p in ['Mathlib/Data/Rat/Cast/Order.lean',
          'Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean',
          'Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean',
          'Mathlib/Analysis/Calculus/ContDiff/Operations.lean',
          'Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean',
          'Mathlib/MeasureTheory/Integral/DominatedConvergence.lean',
          'Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean',
          'Mathlib/Topology/Order/Compact.lean', 'Mathlib/Topology/Algebra/Module/Equiv.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Equiv.lean', 'Mathlib/Analysis/Calculus/FDeriv/Prod.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Mul.lean', 'Mathlib/Analysis/Calculus/Deriv/Inv.lean',
          'Mathlib/Analysis/SpecialFunctions/Sqrt.lean', 'Mathlib/Analysis/Calculus/ContDiff/Defs.lean']:
    blob=(libroot/p).read_bytes()
    assert blob==subprocess.check_output(['git','show','HEAD:'+p],cwd=libroot),p
    mathlib['direct_proof_source_sha256'][p]=digest(blob)
files=set(prior['source_sha256'])|{prior_path,'paper/sections/sec_05_window.tex',
    'paper/sections/sec_04_form.tex','paper/appendices/app_a_carriers.tex'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_allocation_sample_verify.py','scripts/de_allocation_sample_certificate.py',
              'scripts/de_dual_carrier.py','math/ALLOCATION_SAMPLE_LEAN_2026-10-03.md',
              'lean/manifests/check_allocation_sample_statements.lean','lean/manifests/check_allocation_sample_axioms.lean',
              new_path,combined_path])
files.update(cells['historical_inputs_sha256'])
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
 'scope':'Original32-patch generator inputs, exact selected screening and actual local/source controls',
 'lean_build':{'command':'lake build','success':True,'jobs':8179,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean -DwarningAsError=true manifests/check_allocation_sample_axioms.lean',
    'success':True,'declarations_cumulative':1528,'declarations_fresh':54,'declarations_preserved':1474,
    'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,
    'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),
    'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,
    'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean -DwarningAsError=true manifests/check_allocation_sample_statements.lean',
    'success':True,'declarations':54,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
    'target':'original section4.2 sum-allocation budget-dual mechanics and must-flip controls',
    'original_target_sources':['paper/sections/sec_04_form.tex','scripts/de_dual_carrier.py'],
    'patches':32,'original_budgets':10,'original_offsets':3,
    'input_bridge':'original current generator IEEE values in pinned NumPy1.26.4; all historical formatted fields match',
    'historical_unrecorded_bit_identity_claimed':False,
    'numpy_trig_closed_root_rounding_mechanized':False,
    'optimizer_root_finding_solver_rerun':False,
    'coefficient_seed_or_rng_dependence_claimed':False,
    'exact_marginal_response_cells':160,'false_cell_control_rejected':True,
    'actual_selected_price_bounds':['46112/100000','46113/100000'],
    'selected_activity_and_all32_positive_allocations_earned':True,
    'actual_global_optimality_unique_optimizer_and_strong_support':True,
    'actual_first_two_global_allocations_proved_unequal':True,
    'actual_value_derivative_earned':'-actual selectedPrice, every positive budget',
    'screening_offset_interval':['-1/4','1/4'],
    'actual_selected_screening':'x_s=x_0, p_s=p_0+s, value_s=value_0-s*B',
    'original_IEEE_offsets_inside_certified_interval':True,
    'local_control':'32 true singleton budget problems, each B/32, exact total B',
    'actual_local_selected_price_gap':'patch1 minus patch0 greater than 1/20',
    'actual_selected_local_allocation_differs_from_global':True,
    'source_control':'same linear coupling, sum constraint removed',
    'source_response_proved_unique_global_unconstrained_optimizer':True,
    'actual_source_control_movement':'patch8 moves by more than1/2 for both original IEEE shifts',
    'all_original_budget_sweep_activity_slack_earned':True,
    'supplied_KKT_optimizer_price_derivative_or_activity_premise':False,
    'reported_floating_optimizer_residual_or_FD_precision_certified':False,
    'Schur_budget_or_physical_Lambda_identification':False,
    'new_downgrade_of_previously_supported_claim':False},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_carrier_solver_rerun':False,
 'review':'adversarial self-review, not independent review',
 'next_construction':'Broader original-target audit; unsupported main-claim boundaries and numerical error obligations remain',
 'goal_complete':False,'source_sha256':hashes,'source_byte_representation':'checkout bytes; historical CRLF preserved',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized,
}
(root/packet/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'1528 ordered cumulative standard-only closures (1474 immutable + 54 fresh), original32-patch selected screening and actual controls; {len(hashes)} fingerprints')
