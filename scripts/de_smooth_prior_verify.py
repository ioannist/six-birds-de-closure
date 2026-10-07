"""Verify smooth full-support normalized priors on actual windows and uniform small-ratio prefix mass."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'cb12a5d'
packet = 'results/smooth_prior_2026-10-03/'
mods = ['WindowSmoothPrior']


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
assert len(new) == 10
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1464 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_smooth_prior_axioms.lean'), re.M) == new
prior_path = 'results/combined_robustness_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_combined_robustness_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_smooth_prior_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_smooth_prior_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1464-declaration raw prefix plus freshly audited 10-declaration suffix.\n'
          'Baseline: cb12a5d; earlier proof-source/toolchain identity checked by de_smooth_prior_verify.py.\n'
          'Full 1474-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_smooth_prior_statements.lean'), re.M)
statements = read(packet+'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new == checks == printed and not re.search(r'error:|warning:',statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.('+'|'.join(mods)+r')\.(\w+)',statements,re.M))
decls = {m.group(1)+'.'+m.group(2):' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name,d in decls.items():
    d = d.replace('SbtCosmo.Derivation.','').replace('⇑','')
    for group in mods+['GrowthScaleReturn','GrowthExistence','GrowthParameter','WindowSensitivity','WindowPatchRobust','WindowPatchRobustEdge','GrowthQuadrature','GrowthEndpointDerivative','WindowRobustRecord','WindowRobustRatio','GrowthPopulationSensitivity']:
        d = d.replace(group+'.','')
    decls[name]=d


def require(name,*tokens):
    d=decls[name]
    for token in tokens:assert token in d,(name,token)
    return d


# Inspect the exact exported full-window density and actual readout certificate.
P='WindowSmoothPrior.'
require(P+'raw_integral','(k a b : ℝ)', '∫ (t : ℝ) in a..b, raw k t',
        'Real.exp (-k * a) - Real.exp (-k * b)')
require(P+'normalizer_positive','(hk : 0 < k) (hU : 0 < U)', '0 < 1 - Real.exp (-k * U)')
require(P+'density_positive','(hk : 0 < k) (hU : 0 < U) (t : ℝ)', '0 < density k U t')
require(P+'density_smooth','(k U : ℝ)', 'ContDiff ℝ (↑⊤)', '(density k U)')
require(P+'density_integral','(hk : 0 < k) (hU : 0 < U)',
        '∫ (t : ℝ) in 0..U, density k U t = 1')
require(P+'prefix_integral','(k U a : ℝ)', '(1 - Real.exp (-k * a)) / (1 - Real.exp (-k * U))')
require(P+'concentration','(hk : 0 < k) (ha : 0 < a) (haU : a ≤ U)',
        '(he : eta ∈ Set.Ioo 0 1)', '(hdecay : Real.exp (-k * a) ≤ eta / 2)',
        '1 - eta < ∫ (t : ℝ) in 0..a, density k U t')
require(P+'rate_constructed','(ha : 0 < a) (he : eta ∈ Set.Ioo 0 1)',
        '0 < Real.log (2 / eta) / a', 'Real.exp (-(Real.log (2 / eta) / a) * a) = eta / 2')
d=require(P+'actual_all_windows_smooth_small_ratio',
    '{epsilon eta : ℝ} (he : 0 < epsilon) (heta : eta ∈ Set.Ioo 0 1)',
    '∃ k a, 0 < k ∧ 0 < a ∧ a ≤ minimumEndpoint ∧ ∀ (d s : ℝ), Rectangle d s →',
    '∀ (v : Bool),', 'ContDiff ℝ', '(density k (upper v d s))',
    '(∀ (t : ℝ), 0 < density k (upper v d s) t)',
    '∫ (t : ℝ) in 0..upper v d s, density k (upper v d s) t = 1',
    '1 - eta < ∫ (t : ℝ) in 0..a, density k (upper v d s) t',
    '∀ lam ∈ Set.Icc 0 a, gate v d s lam ∧',
    '∀ (j : Fin 12), 0 ≤ ratio v d s j lam ∧ ratio v d s j lam < epsilon',
    '(density k (scaledEndpoint d s))',
    '(∀ (t : ℝ), 0 < density k (scaledEndpoint d s) t)',
    '∫ (t : ℝ) in 0..scaledEndpoint d s, density k (scaledEndpoint d s) t = 1',
    '1 - eta < ∫ (t : ℝ) in 0..a, density k (scaledEndpoint d s) t',
    '∀ lam ∈ Set.Icc 0 a, gate d s lam ∧',
    '∀ (j : Fin 12), 0 ≤ ratio d s j lam ∧ ratio d s j lam < epsilon')
assert len(decls)==10
# The final construction has only epsilon and the target probability tolerance
# as hypotheses. Rate/cutoff/normalization/gates/ratios are conclusions.
assert d.count('(he :')==1 and d.count('(heta :')==1
for token in ['(hk :','(ha :','(hU :','(hdecay :','(hroot :','(hwindow :',
              '(hprior :','(hnormalization :','(htime :','(hbound :']:
    assert token not in d,token
src=read('lean/SbtCosmo/Derivation/WindowSmoothPrior.lean')
for token in ['def raw (k t : ℝ) : ℝ := k * Real.exp (-k*t)',
              'raw k t / (1-Real.exp (-k*U))',
              'intervalIntegral.integral_eq_sub_of_hasDerivAt',
              '(raw_continuous k).intervalIntegrable a b',
              'intervalIntegral.integral_div','normalizer_positive hk hU',
              'ContDiff ℝ ∞ (density k U)',
              'let a := min minimumEndpoint (epsilon/16000)',
              'let k := Real.log (2/eta)/a','rate_constructed ha heta',
              'common_corner_bounds hR v','(endpoint_order hR).1.le',
              'concentration hk ha hau heta hdecay.le',
              'common_positive_window hR','(gate_inclusions hR lam).1 hg32',
              'ratio_nonnegative_upper hR hg hl.1 j']:
    assert token in src,token
build=read(packet+'lean_build.txt')
assert 'Build completed successfully (8175 jobs).' in build and not re.search(r'error:|warning:',build)
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
expected = old_config.replace('`SbtCosmo.Derivation.WindowPatchRobustEdge]',
    '`SbtCosmo.Derivation.WindowPatchRobustEdge, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected

lean_version = subprocess.check_output(['lake','env','lean','--version'],cwd=root/'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip() == mathlib['revision']
for p,h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot/p).read_bytes()) == h,p
for p in ['Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean',
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
    'paper/sections/sec_07_measure.tex','paper/appendices/app_a_carriers.tex'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_smooth_prior_verify.py','math/SMOOTH_PRIOR_LEAN_2026-10-03.md',
              'lean/manifests/check_smooth_prior_statements.lean','lean/manifests/check_smooth_prior_axioms.lean',
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
 'scope':'Smooth full-support normalized density on every actual original positive window; uniform arbitrarily high low-ratio prefix mass',
 'lean_build':{'command':'lake build','success':True,'jobs':8175,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean -DwarningAsError=true manifests/check_smooth_prior_axioms.lean',
    'success':True,'declarations_cumulative':1474,'declarations_fresh':10,'declarations_preserved':1464,
    'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,
    'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),
    'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,
    'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean -DwarningAsError=true manifests/check_smooth_prior_statements.lean',
    'success':True,'declarations':10,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
    'target':'section7 nonsingular-near-zero sufficiency and original actual readout return',
    'original_target_sources':['paper/sections/sec_07_measure.tex','paper/sections/sec_05_window.tex'],
    'populations':[32,64,128],'seeds_each':12,
    'threshold_rectangle':['6/5','2'],'amplitude_rectangle':['1/3','3'],
    'density':'k*exp(-k*lambda)/(1-exp(-k*actualEndpoint))',
    'density_C_infinity_strictly_positive_and_finite_at_zero':True,
    'full_actual_positive_window_normalization_one_earned':True,
    'exact_antiderivative_FTC_and_interval_integrability_earned':True,
    'constructed_prefix':'a=min(actual common lower endpoint,epsilon/16000)',
    'constructed_rate':'k=log(2/eta)/a>0',
    'prefix_interval_mass':'greater than 1-eta for every actual endpoint',
    'same_rate_and_prefix_precede_all_knob_population_seed_quantifiers':True,
    'actual_low_ratio_prefix_subset':'all admitted, all36 R<epsilon over entire rectangle',
    'each_density_normalized_on_its_own_actual_full_window':True,
    'single_unnormalized_rate_for_all_actual_windows':True,
    'prior_is_an_atom_or_truncated_to_prefix':False,
    'separate_Mathlib_probability_measure_object_constructed':False,
    'record_abundance_pushforward_mechanized':False,
    'signed_negative_sliver_covered':False,
    'declared_flat_log_prior_results_changed':False,
    'physical_prior_inferred':False,
    'new_downgrade_of_previously_supported_claim':False,
    'already_known_false_local_regularity_target_formalized':True,
    'original_population_tags_IVP_and_first_ANY_selector_retained':True},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_carrier_solver_rerun':False,
 'review':'adversarial self-review, not independent review',
 'next_construction':'Stop local-nonsingularity restoration route; broader false/project-sized main-claim options remain',
 'goal_complete':False,'source_sha256':hashes,'source_byte_representation':'checkout bytes; historical CRLF preserved',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized,
}
(root/packet/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'1474 ordered cumulative standard-only closures (1464 immutable + 10 fresh), normalized smooth actual-window priors and uniform low-ratio prefix mass; {len(hashes)} fingerprints')
