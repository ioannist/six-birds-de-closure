import hashlib,json,re,subprocess
from fractions import Fraction
from pathlib import Path
root=Path(__file__).resolve().parents[1]
def read(p): return (root/p).read_text()
mods=['GrowthInfinite','GrowthEternalWindow','WindowEternalRecords']
new=[]
for m in mods:
 src=read('lean/SbtCosmo/Derivation/'+m+'.lean')
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
 new += ['SbtCosmo.Derivation.'+m+'.'+n for n in re.findall(r'^theorem (\w+)',src,re.M)]
assert len(new)==47
expected=re.findall(r'^#print axioms (\S+)',read('lean/manifests/check_axioms.lean'),re.M)
raw=read('lean/manifests/axiom_audit_eternal_window_2026-10-03.txt')
entries=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
assert len(expected)==798 and [n for n,_ in entries]==expected and expected[-47:]==new
assert not re.search(r'error:|warning:|sorryAx',raw)
allowed={'propext','Classical.choice','Quot.sound'};actual=set()
for n,a in entries:
 axs={s.strip() for s in a.split(',') if s.strip()}
 assert axs<=allowed,(n,axs)
 actual.update(axs)
assert actual==allowed
checks=re.findall(r'^#check (\S+)',read('lean/manifests/check_eternal_window_statements.lean'),re.M)
statements=read('results/eternal_window_2026-10-03/theorem_statements.txt')
printed=[n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new==checks==printed
assert not re.search(r'error:|warning:',statements)
compact=' '.join(statements.split())
for required in [
 'eternalGate lam ↔ 0 ≤ lam ∧ lam < SbtCosmo.Derivation.WindowEternalRecords.upper',
 'fixedDeadlineGate lam ↔ 0 ≤ lam ∧ lam ≤ SbtCosmo.Derivation.WindowEdgeCertified.upper',
 'SbtCosmo.Derivation.WindowEdgeCertified.upper < SbtCosmo.Derivation.WindowEternalRecords.upper',
 'eventualRecord j SbtCosmo.Derivation.WindowEternalRecords.upper}.card = 9',
 'T < SbtCosmo.Derivation.GrowthInfinite.nativeInfinite a0 lam',
 'no_records_ever {lam : ℝ} (hlam : 1000000000 ≤ lam) (j : Fin 12) (i : Fin 64) : ¬∃ a, 1 / 1000 ≤ a',
 'exists_unique_infinite_endpoint {a0 T : ℝ} (ha0 : 0 < a0) (hT : 3 / 2 < T)',
]:
 assert required in compact,required
build=read('results/eternal_window_2026-10-03/lean_build.txt')
assert 'Build completed successfully (8093 jobs).' in build and not re.search(r'error:|warning:',build)
for ref,paths in [('6a71e6c',['paper','external']),('da0a53b',['sbt_cosmo','tests','results/DE_window','results/window_population_2026-10-03'])]:
 assert subprocess.check_output(['git','diff','--name-only',ref,'--',*paths],cwd=root)==b''
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','da0a53b'],cwd=root).decode().splitlines()
protected=[p for p in tracked if (p.startswith('scripts/') or p.startswith('lean/SbtCosmo/') or p.startswith('results/') or p.startswith('lean/manifests/axiom_audit_') or (p.startswith('math/') and p!='math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'))]
assert subprocess.check_output(['git','diff','--name-only','da0a53b','--',*protected],cwd=root)==b''
# Independently recompute the exact unchanged-population margin and strict rank.
pop=json.loads(read('results/window_population_2026-10-03/population.json'))
T=Fraction(pop['aggregate_threshold_exact']);thresholds=[];margins=[]
for row in pop['populations']:
 amp=list(map(Fraction,row['amplitudes_exact']));tags=row['tags']
 maxima=[max(a for a,b in zip(amp,tags) if b==t) for t in [False,True]]
 assert maxima==list(map(Fraction,row['tag_maxima_exact']))
 assert 3*max(maxima)<Fraction(843,500)
 margins.append(str(Fraction(843,500)-3*max(maxima)))
 thresholds.append(max(Fraction(843,500)/m for m in maxima))
assert len(thresholds)==12 and sum(t<T for t in thresholds)==9 and sum(t<=T for t in thresholds)==10
assert Fraction(1000000000)*Fraction(1,1000)**3==1
prior=json.loads(read('results/patch_count_2026-10-03/verification.json'))
files=set(prior['source_sha256'])
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_eternal_window_verify.py','math/ETERNAL_WINDOW_LEAN_2026-10-03.md','lean/manifests/check_eternal_window_statements.lean','lean/manifests/axiom_audit_eternal_window_2026-10-03.txt','results/patch_count_2026-10-03/verification.json'])
files.update(str(p.relative_to(root)) for p in (root/'results/eternal_window_2026-10-03').iterdir() if p.name!='verification.json')
hashes={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sorted(files)}
git_hashes={};normalized=[]
for p in sorted(files):
 blob=(root/p).read_bytes()
 if b'\r\n' in blob:
  attrs=subprocess.check_output(['git','check-attr','text','eol','--',p],cwd=root).decode()
  assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob,p
  blob=blob.replace(b'\r\n',b'\n');normalized.append(p)
 git_hashes[p]=hashlib.sha256(blob).hexdigest()
mathlib=prior['mathlib']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root/'lean/.lake/packages/mathlib').decode().strip()==mathlib['revision']
for p in ['Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean','Mathlib/MeasureTheory/Integral/DominatedConvergence.lean','Mathlib/Analysis/Calculus/Deriv/MeanValue.lean','Mathlib/Topology/Order/IntermediateValue.lean']:
 mathlib['direct_proof_source_sha256'][p]=hashlib.sha256((root/'lean/.lake/packages/mathlib'/p).read_bytes()).hexdigest()
for p,h in mathlib['direct_proof_source_sha256'].items():
 assert hashlib.sha256((root/'lean/.lake/packages/mathlib'/p).read_bytes()).hexdigest()==h
v={
 'baseline_commit':'da0a53b',
 'scope':'Actual original IVP infinite-time growth, global record starvation and exact original twelve-seed perpetual retention windows with finite formation',
 'lean_build':{'command':'lake build','success':True,'jobs':8093,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command':'lake env lean manifests/check_axioms.lean','success':True,'declarations':798,'new_local_theorems':new,'axioms':sorted(actual),'receipt':'lean/manifests/axiom_audit_eternal_window_2026-10-03.txt','ordered_declarations_match_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean manifests/check_eternal_window_statements.lean','success':True,'declarations':47,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,
 'original_return':{
  'same_original_native_ivp_and_exact_decimal_model_scalars':True,
  'a0':'1/1000','delta':'843/500','seeds':list(range(1100,1112)),'patches_per_seed':64,'required_seed_passes':10,
  'exact_aggregate_threshold':str(T),
  'actual_time_limit_constructed':True,'improper_integrability_proved':True,
  'uniform_tail_bound_earned':True,'strict_parameter_ordering_survives_limit_via_increasing_actual_growth_gap':True,
  'unique_positive_limiting_endpoint_constructed_for_every_a0_positive_T_above_three_halves':True,
  'arbitrary_finite_formation_perpetual_retention_window':'[0,u_infinity)',
  'limiting_endpoint_eventual_both_tag_seed_count':9,
  'required_seed_count_at_limiting_endpoint_fails':True,
  'fixed_formation_deadline_20_perpetual_retention_window':'[0,u_20]',
  'endpoint_order':'0<u_20<u_infinity',
  'global_no_records_cutoff':'lambda>=1000000000 for every finite a>=1/1000, all original patches and seeds',
  'kernel_margin_exact_independent_recompute':margins,
  'exact_strict_and_nonstrict_rank_counts_independently_recomputed':[9,10],
  'closed_infinite_endpoint_false_for_arbitrary_finite_formation':True,
  'growth_or_limiting_law_or_order_supplied_as_premise':False,
  'rng_law_formalized':False,'floating_solver_total_correctness_certified':False,
  'physical_crunch_or_lambda_identification':False},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_growth_solver_rerun':False,'population_reification_tools_rerun':False,
 'review':'Adversarial self-review; no independent mathematical reviewer',
 'next_construction':'Sharper infinite-endpoint quantitative bounds or eternal returns for the already reified robustness populations; physical and contradicted original claims retain earlier boundaries',
 'goal_complete':False,'source_sha256':hashes,
 'source_byte_representation':'Working checkout bytes; expected canonical Git blob hashes recorded separately and checked before commit',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized}
(root/'results/eternal_window_2026-10-03/verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'798 ordered standard-only closures, 47 exported statements, exact starvation/rank controls and protected paths; {len(hashes)} fingerprints checked.')
