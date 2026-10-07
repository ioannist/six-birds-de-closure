import hashlib,json,re,subprocess
from fractions import Fraction
from pathlib import Path
root=Path(__file__).resolve().parents[1]
baseline='c7e89b3'
def read(p): return (root/p).read_text()
def git_blob(ref,p): return subprocess.check_output(['git','show',ref+':'+p],cwd=root)
def digest(b): return hashlib.sha256(b).hexdigest()
def entries(raw):
 return re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
def closure_gate(raw,names):
 got=entries(raw)
 assert [n for n,_ in got]==names
 assert not re.search(r'error:|warning:|sorryAx',raw)
 allowed={'propext','Classical.choice','Quot.sound'};actual=set()
 for n,a in got:
  axs={s.strip() for s in a.split(',') if s.strip()}
  assert axs<=allowed,(n,axs)
  actual.update(axs)
 assert actual==allowed
 return actual
mods=['GrowthInfiniteTail','GrowthHorizonLimit','WindowEternalBounds','WindowEternalPatchCounts'];new=[]
for m in mods:
 src=read('lean/SbtCosmo/Derivation/'+m+'.lean')
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
 new+=['SbtCosmo.Derivation.'+m+'.'+n for n in re.findall(r'^theorem (\w+)',src,re.M)]
assert len(new)==32
old_manifest=git_blob(baseline,'lean/manifests/check_axioms.lean').decode()
old_names=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
all_names=re.findall(r'^#print axioms (\S+)',read('lean/manifests/check_axioms.lean'),re.M)
assert len(old_names)==798 and all_names==old_names+new
prior=json.loads(read('results/eternal_window_2026-10-03/verification.json'))
old_path='lean/manifests/axiom_audit_eternal_window_2026-10-03.txt'
old_raw=read(old_path)
assert (root/old_path).read_bytes()==git_blob(baseline,old_path)
assert digest((root/old_path).read_bytes())==prior['source_sha256'][old_path]
closure_gate(old_raw,old_names)
new_path='lean/manifests/axiom_audit_horizon_limit_new_2026-10-03.txt'
new_raw=read(new_path)
assert re.findall(r'^#print axioms (\S+)',read('lean/manifests/check_horizon_limit_axioms.lean'),re.M)==new
actual=closure_gate(new_raw,new)
# Preserve the earlier exact raw prefix; do not label this a fresh full rerun.
combined_path='lean/manifests/axiom_audit_horizon_limit_2026-10-03.txt'
header=('Cumulative audit: exact immutable earlier 798-declaration raw prefix plus freshly audited 32-declaration suffix.\n'
        'Baseline: c7e89b3; original proof-source/toolchain identity checked by de_horizon_limit_verify.py.\n'
        'Full 830-declaration command was not rerun in this packet.\n\n')
combined=header+old_raw+'\n'+new_raw
closure_gate(combined,all_names)
(root/combined_path).write_text(combined)
checks=re.findall(r'^#check (\S+)',read('lean/manifests/check_horizon_limit_statements.lean'),re.M)
statements=read('results/horizon_limit_2026-10-03/theorem_statements.txt')
printed=[n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new==checks==printed and not re.search(r'error:|warning:',statements)
compact=' '.join(statements.split())
for required in [
 '(lam * a0 ^ 2 + 5 / (2 * a0)) / (2 * lam * A ^ 2)',
 'finiteEndpoint_tendsto {a0 T : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)',
 'Filter.Tendsto (SbtCosmo.Derivation.GrowthHorizonLimit.finiteEndpoint a0 T) Filter.atTop (nhds (SbtCosmo.Derivation.GrowthEternalWindow.infiniteEndpoint a0 T))',
 '3 < SbtCosmo.Derivation.WindowEternalRecords.upper ∧ SbtCosmo.Derivation.WindowEternalRecords.upper < 4',
 'formationUpper 20 = SbtCosmo.Derivation.WindowEdgeCertified.upper',
 'closure {lam | SbtCosmo.Derivation.WindowEternalRecords.eternalGate lam} = Set.Icc 0 SbtCosmo.Derivation.WindowEternalRecords.upper',
 'WindowEternalPatchCounts.eternalGate v lam ↔ 0 ≤ lam ∧ lam < SbtCosmo.Derivation.WindowEternalPatchCounts.upper v',
 '(SbtCosmo.Derivation.WindowEternalPatchCounts.upper v)}.card = 9',
 'WindowEternalPatchCounts.upper false < SbtCosmo.Derivation.WindowEternalRecords.upper ∧ SbtCosmo.Derivation.WindowEternalRecords.upper < SbtCosmo.Derivation.WindowEternalPatchCounts.upper true',
 'WindowEternalPatchCounts.no_records_ever (v : Bool) {lam : ℝ} (hlam : 1000000000 ≤ lam) (j : Fin 12)',
]:
 assert required in compact,required
build=read('results/horizon_limit_2026-10-03/lean_build.txt')
assert 'Build completed successfully (8097 jobs).' in build and not re.search(r'error:|warning:',build)
for ref,paths in [('6a71e6c',['paper','external']),(baseline,['sbt_cosmo','tests','results/DE_window','results/window_population_2026-10-03','results/patch_count_2026-10-03','results/eternal_window_2026-10-03'])]:
 assert subprocess.check_output(['git','diff','--name-only',ref,'--',*paths],cwd=root)==b''
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',baseline],cwd=root).decode().splitlines()
protected=[p for p in tracked if (p.startswith('scripts/') or p.startswith('lean/SbtCosmo/') or p.startswith('results/') or p.startswith('lean/manifests/axiom_audit_') or p.startswith('lean/manifests/check_') and p!='lean/manifests/check_axioms.lean' or p.startswith('math/') and p!='math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md')]
assert subprocess.check_output(['git','diff','--name-only',baseline,'--',*protected],cwd=root)==b''
# Check the exact arithmetic giving the new bracket from the old finite certificate.
a0=Fraction(1,1000);tail=(4*a0**2+5/(2*a0))/(2*4*20**2)
assert 936+tail<937<960
# Exact independent margins/ranks for all unchanged populations; no RNG/solver.
original=json.loads(read('results/window_population_2026-10-03/population.json'))
variants=json.loads(read('results/patch_count_2026-10-03/populations.json'))['variants']
returns=[];Ts={}
for n,pop in [(64,original)]+[(v['n_patches'],v) for v in variants]:
 T=Fraction(pop['aggregate_threshold_exact']);thresholds=[];margins=[]
 assert [row['seed'] for row in pop['populations']]==list(range(1100,1112))
 for row in pop['populations']:
  amp=list(map(Fraction,row['amplitudes_exact']));tags=row['tags']
  assert len(amp)==len(tags)==n and all(a>=0 for a in amp)
  maxima=[max(a for a,b in zip(amp,tags) if b==t) for t in [False,True]]
  assert maxima==list(map(Fraction,row['tag_maxima_exact']))
  margin=Fraction(843,500)-3*max(maxima)
  assert margin>0
  margins.append(str(margin))
  thresholds.append(max(Fraction(843,500)/m for m in maxima))
 assert len(thresholds)==12 and sum(t<T for t in thresholds)==9 and sum(t<=T for t in thresholds)==10
 Ts[n]=T
 returns.append({'patch_count':n,'aggregate_threshold':str(T),'strict_and_nonstrict_rank_counts':[9,10],'exact_starvation_margins':margins})
assert Ts[128]<Ts[64]<Ts[32] and Fraction(1000000000)*a0**3==1
files=set(prior['source_sha256'])
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_horizon_limit_verify.py','math/HORIZON_LIMIT_LEAN_2026-10-03.md','lean/manifests/check_horizon_limit_statements.lean','lean/manifests/check_horizon_limit_axioms.lean',new_path,combined_path,'results/eternal_window_2026-10-03/verification.json'])
files.update(str(p.relative_to(root)) for p in (root/'results/horizon_limit_2026-10-03').iterdir() if p.name!='verification.json')
hashes={p:digest((root/p).read_bytes()) for p in sorted(files)}
git_hashes={};normalized=[]
for p in sorted(files):
 blob=(root/p).read_bytes()
 if b'\r\n' in blob:
  attrs=subprocess.check_output(['git','check-attr','text','eol','--',p],cwd=root).decode()
  assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob,p
  blob=blob.replace(b'\r\n',b'\n');normalized.append(p)
 git_hashes[p]=digest(blob)
lean_version=subprocess.check_output(['lake','env','lean','--version'],cwd=root/'lean').decode().strip()
assert 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip()=='leanprover/lean4:v4.28.0'
mathlib=prior['mathlib']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root/'lean/.lake/packages/mathlib').decode().strip()==mathlib['revision']
p='Mathlib/Topology/Order/DenselyOrdered.lean'
mathlib['direct_proof_source_sha256'][p]=digest((root/'lean/.lake/packages/mathlib'/p).read_bytes())
for p,h in mathlib['direct_proof_source_sha256'].items(): assert digest((root/'lean/.lake/packages/mathlib'/p).read_bytes())==h
v={
 'baseline_commit':baseline,
 'scope':'Actual IVP tails, finite-horizon endpoint convergence and actual original N=32/N=64/N=128 eternal robustness',
 'lean_build':{'command':'lake build','success':True,'jobs':8097,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean manifests/check_horizon_limit_axioms.lean','success':True,'declarations_cumulative':830,'declarations_fresh':32,'declarations_preserved':798,'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean manifests/check_horizon_limit_statements.lean','success':True,'declarations':32,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
  'same_original_native_ivp_and_exact_decimal_model_scalars':True,
  'tail_law_derived_from_actual_velocity':True,'native_tail_bound':'[lambda*a0^2+5/(2*a0)]/[2*lambda*A^2]',
  'guarded_finite_selector_domain':'a0>0,T>3/2,A>a0*T',
  'finite_endpoints_strictly_increase_and_converge_to_constructed_infinite_endpoint':True,
  'same_original_a20_endpoint_proved':True,
  'actual_original_finite_windows':'(-1/A^3,u(A)] for every A>T_aggregate/1000 and every real lambda',
  'infinite_64_endpoint_bracket':'3<u_infinity,64<4','tail_at_lambda4_a20_exact':str(tail),
  'limiting_growth_at_four_bound':'D_infinity(4)<937',
  'closed_envelope':'closure(actual eventual-record parameters)=[0,u_infinity,64]',
  'closure_membership_mistaken_for_finite_record_attainment':False,
  'actual_eternal_windows':'[0,u_infinity,N) for original N=32,64,128',
  'actual_eternal_endpoint_order':'0<u_infinity,32<u_infinity,64<u_infinity,128',
  'strict_inclusion_witnesses_at_smaller_excluded_endpoints':True,
  'every_eternal_endpoint_above_its_original_finite_endpoint':True,
  'actual_limiting_endpoint_both_tag_seed_counts':[9,9,9],'required_count':10,
  'fixed_formation_deadline_20_perpetual_retention_windows':'[0,u_20,N]',
  'all_time_no_patch_records_cutoff':'lambda>=10^9, every finite a>=1/1000, all seeds/patches in all three original populations',
  'exact_populations_independently_checked':returns,
  'population_inclusion_tag_coupling_or_universal_reseeding_order_assumed':False,
  'physical_crunch_or_lambda_identification':False,'floating_solver_total_correctness_certified':False},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_growth_solver_rerun':False,'population_reification_tools_rerun':False,
 'review':'Adversarial self-review; no independent mathematical reviewer',
 'next_construction':'Sharper all-time starvation or actual finite first-record ratios at the infinite endpoint, with selector guards explicitly earned',
 'goal_complete':False,'source_sha256':hashes,
 'source_byte_representation':'Working checkout bytes; expected canonical Git blob hashes separately checked',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized}
(root/'results/horizon_limit_2026-10-03/verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'830 ordered cumulative standard-only closures (798 immutable + 32 fresh), 32 statements, exact population/rank/tail controls and protected paths; {len(hashes)} fingerprints checked.')
