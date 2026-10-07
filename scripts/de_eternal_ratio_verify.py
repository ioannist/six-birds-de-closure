import hashlib,json,re,subprocess
from fractions import Fraction
from pathlib import Path
root=Path(__file__).resolve().parents[1]
baseline='b4d57fc'
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
mods=['WindowEternalRatioData','WindowEternalRatioCertified','WindowEternalRatio'];new=[]
for m in mods:
 src=read('lean/SbtCosmo/Derivation/'+m+'.lean')
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src)
 new+=['SbtCosmo.Derivation.'+m+'.'+n for n in re.findall(r'^theorem (\w+)',src,re.M)]
assert len(new)==25
old_manifest=git_blob(baseline,'lean/manifests/check_axioms.lean').decode()
old_names=re.findall(r'^#print axioms (\S+)',old_manifest,re.M)
all_names=re.findall(r'^#print axioms (\S+)',read('lean/manifests/check_axioms.lean'),re.M)
assert len(old_names)==830 and all_names==old_names+new
prior=json.loads(read('results/horizon_limit_2026-10-03/verification.json'))
old_path='lean/manifests/axiom_audit_horizon_limit_2026-10-03.txt'
old_raw=read(old_path)
assert (root/old_path).read_bytes()==git_blob(baseline,old_path)
assert digest((root/old_path).read_bytes())==prior['source_sha256'][old_path]
closure_gate(old_raw,old_names)
new_path='lean/manifests/axiom_audit_eternal_ratio_new_2026-10-03.txt'
new_raw=read(new_path)
assert re.findall(r'^#print axioms (\S+)',read('lean/manifests/check_eternal_ratio_axioms.lean'),re.M)==new
actual=closure_gate(new_raw,new)
# Preserve the earlier exact raw prefix; do not label this a fresh full rerun.
combined_path='lean/manifests/axiom_audit_eternal_ratio_2026-10-03.txt'
header=('Cumulative audit: exact immutable earlier 830-declaration raw prefix plus freshly audited 25-declaration suffix.\n'
        'Baseline: b4d57fc; original proof-source/toolchain identity checked by de_eternal_ratio_verify.py.\n'
        'Full 855-declaration command was not rerun in this packet.\n\n')
combined=header+old_raw+'\n'+new_raw
closure_gate(combined,all_names)
(root/combined_path).write_text(combined)
checks=re.findall(r'^#check (\S+)',read('lean/manifests/check_eternal_ratio_statements.lean'),re.M)
statements=read('results/eternal_ratio_2026-10-03/theorem_statements.txt')
printed=[n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statements,re.M)]
assert new==checks==printed and not re.search(r'error:|warning:',statements)
compact=' '.join(statements.split())
for required in [
 'WindowEternalRecords.upper < 17 / 5',
 'GrowthInfinite.nativeInfinite (1 / 1000) (17 / 5) < 960',
 'WindowEternalRatio.time_iff_any_collapse {lam a : ℝ} (hlam : lam ∈ Set.Icc 0 SbtCosmo.Derivation.WindowEternalRecords.upper) (ha : 1 / 1000 ≤ a)',
 '∀ (a : ℝ), 1 / 1000 ≤ a → a < SbtCosmo.Derivation.WindowFirstRecord.time j lam',
 'WindowEternalRatio.endpoint_ratios (j : Fin 12) : 3 / 8 < SbtCosmo.Derivation.WindowFirstRecord.ratio j SbtCosmo.Derivation.WindowEternalRecords.upper',
 'WindowFirstRecord.ratio j SbtCosmo.Derivation.WindowEternalRecords.upper < 425 / 8',
 'WindowEternalRatio.arbitrarily_small_ratios {eps : ℝ} (heps : 0 < eps) : ∃ lam, 0 < lam ∧ SbtCosmo.Derivation.WindowEternalRecords.eternalGate lam',
 '∀ (j : Fin 12), 0 < SbtCosmo.Derivation.WindowFirstRecord.ratio j lam ∧ SbtCosmo.Derivation.WindowFirstRecord.ratio j lam < eps',
]:
 assert required in compact,required
build=read('results/eternal_ratio_2026-10-03/lean_build.txt')
assert 'Build completed successfully (8100 jobs).' in build and not re.search(r'error:|warning:',build)
for ref,paths in [('6a71e6c',['paper','external']),(baseline,['sbt_cosmo','tests','results/DE_window','results/window_population_2026-10-03','results/patch_count_2026-10-03','results/eternal_window_2026-10-03'])]:
 assert subprocess.check_output(['git','diff','--name-only',ref,'--',*paths],cwd=root)==b''
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',baseline],cwd=root).decode().splitlines()
protected=[p for p in tracked if (p.startswith('scripts/') or p.startswith('lean/SbtCosmo/') or p.startswith('results/') or p.startswith('lean/manifests/axiom_audit_') or p.startswith('lean/manifests/check_') and p!='lean/manifests/check_axioms.lean' or p.startswith('math/') and p!='math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md')]
assert subprocess.check_output(['git','diff','--name-only',baseline,'--',*protected],cwd=root)==b''
# Independently check every new cell and the finite-plus-tail arithmetic.
cells=json.loads(read('results/eternal_ratio_2026-10-03/cells.json'))
assert cells['arithmetic']=='Python Fraction and integer isqrt; no floating arithmetic'
assert cells['lambda']=='17/5' and cells['cells']==1024
assert cells['false_certificate_controls']=={'zero_upper_cell_rejected':True,'lowered_sum_target_rejected':True}
grid=list(map(Fraction,cells['grid']));highs=list(map(Fraction,cells['upper']))
lam=Fraction(17,5);a0=Fraction(1,1000)
assert len(grid)==1025 and len(highs)==len(cells['upper_branch'])==1024
assert grid[0]==a0 and grid[-1]==20
for a,b,hi,branch in zip(grid,grid[1:],highs,cells['upper_branch']):
 assert 0<a<b and hi>=0
 if 2*lam*b**3<=1:
  assert branch=='increasing' and b**3<=hi**2*(1+lam*b**3)**3
 elif 1<=2*lam*a**3:
  assert branch=='decreasing' and a**3<=hi**2*(1+lam*a**3)**3
 else:
  assert branch=='peak' and 4<=27*lam*hi**2
upper_sum=sum(((b-a)*hi for a,b,hi in zip(grid,grid[1:],highs)),Fraction(0))
assert upper_sum==Fraction(9981036619,48000000000)==Fraction(cells['upper_sum'])
assert upper_sum<=Fraction(4159,20000) and upper_sum>Fraction(207,1000)
alpha=lam*a0**2+5/(2*a0)
finite_bound=Fraction(1844,1000)*(Fraction(1,30000)+alpha*Fraction(4159,20000))
tail=alpha/(2*lam*20**2)
assert finite_bound<959 and tail<1 and finite_bound+tail<960
fresh=subprocess.check_output(['python3','scripts/de_eternal_ratio_certificate.py'],cwd=root).decode()
assert fresh==read('results/eternal_ratio_2026-10-03/replay.txt')
files=set(prior['source_sha256'])
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in mods)
files.update(['scripts/de_eternal_ratio_verify.py','scripts/de_eternal_ratio_certificate.py','math/ETERNAL_RATIO_LEAN_2026-10-03.md','lean/manifests/check_eternal_ratio_statements.lean','lean/manifests/check_eternal_ratio_axioms.lean',new_path,combined_path,'results/horizon_limit_2026-10-03/verification.json'])
files.update(str(p.relative_to(root)) for p in (root/'results/eternal_ratio_2026-10-03').iterdir() if p.name!='verification.json')
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
 'scope':'Actual original first-any-patch times and coincidence ratios at the infinite endpoint, with sharp actual IVP endpoint certificate',
 'lean_build':{'command':'lake build','success':True,'jobs':8100,'warnings_as_errors':True,'receipt':'lean_build.txt'},
 'axiom_audit':{'command_fresh_suffix':'lake env lean manifests/check_eternal_ratio_axioms.lean','success':True,'declarations_cumulative':855,'declarations_fresh':25,'declarations_preserved':830,'new_local_theorems':new,'axioms':sorted(actual),'full_cumulative_command_rerun':False,'preserved_raw_prefix':old_path,'preserved_prefix_sha256':digest(old_raw.encode()),'fresh_suffix_receipt':new_path,'combined_receipt':combined_path,'old_proof_sources_unchanged':True,'ordered_declarations_match_full_manifest':True,'proof_holes':False,'native_decide':False},
 'statement_check':{'command':'lake env lean manifests/check_eternal_ratio_statements.lean','success':True,'declarations':25,'receipt':'theorem_statements.txt'},
 'mathlib':mathlib,'actual_lean_version_checked':lean_version,
 'original_return':{
  'same_original_native_ivp_and_exact_decimal_model_scalars':True,
  'same_original_first_any_patch_time_and_ratio_definitions':True,
  'first_selector_guards_earned_on_enlarged_domain':'0<=lambda<=u_infinity,64',
  'first_collapse_equivalence_at_every_finite_epoch':'a>=1/1000, without a<=20 guard',
  'infinite_endpoint_bracket':'3<u_infinity,64<17/5',
  'all_original_seed_first_time_bounds':'1/2<a_first<=5/2',
  'near_edge_and_endpoint_ratio_bounds':'3/8<R<425/8 for all original seeds and 3<=lambda<=u_infinity,64',
  'entire_eternal_window_ratio_bound':'0<=R<425/8',
  'first_time_and_ratio_strict_parameter_order':True,
  'exact_zero_time':'T_first/1000',
  'arbitrary_small_positive_ratios':'every eps>0 has positive admitted lambda with every original seed 0<R<eps',
  'original_N64_population_and_twelve_seeds_retained':True,
  'first_any_patch_mistaken_for_both_tag_aggregate_pass':False,
  'endpoint_aggregate_count_retains_previous_nine_pass_exclusion':True,
  'sampled_R_max_17_4_mistaken_for_continuum_bound':False,
  'physical_crunch_or_lambda_identification':False,'floating_solver_total_correctness_certified':False},
 'exact_certificate':{'new_cells':1024,'arithmetic':'Fraction and integer isqrt only','upper_sum':str(upper_sum),'upper_certificate':'4159/20000','finite_native_bound':str(finite_bound),'tail_bound_at_17_5_a20':str(tail),'false_controls':cells['false_certificate_controls'],'receipt':'cells.json','byte_replay_success':True,'command':'python3 scripts/de_eternal_ratio_certificate.py','replay_receipt':'replay.txt'},
 'paper_edited':False,'frozen_external_edited':False,'original_python_runtime_edited':False,
 'previous_proof_modules_unchanged':True,'previous_certificate_artifacts_unchanged':True,
 'python_test_suite_rerun':False,'original_growth_solver_rerun':False,'population_reification_tools_rerun':False,
 'review':'Adversarial self-review; no independent mathematical reviewer',
 'next_construction':'Sharper original all-time starvation or actual ratio bounds for the already reified robustness populations; prior physical and contradicted claim boundaries remain',
 'goal_complete':False,'source_sha256':hashes,
 'source_byte_representation':'Working checkout bytes; expected canonical Git blob hashes separately checked',
 'git_blob_sha256':git_hashes,'git_crlf_to_lf_normalized_paths':normalized}
(root/'results/eternal_ratio_2026-10-03/verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(f'855 ordered cumulative standard-only closures (830 immutable + 25 fresh), 25 statements, exact cell/sum/tail controls and protected paths; {len(hashes)} fingerprints checked.')
