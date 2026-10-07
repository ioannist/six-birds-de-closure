"""Archive two completed, separately scoped mathematical checks."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,tarfile,subprocess

repo=Path('/home/repos/six-birds-de-closure');lean=repo/'lean'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def archive(out,paths):
 out.mkdir(exist_ok=False);entries=[];p=out/'checked_artifacts.tar.gz'
 with tarfile.open(p,'w:gz') as t:
  for q in sorted(set(paths)):
   name=('workspace/'+str(q.relative_to(repo))) if q.is_relative_to(repo) else str(q.relative_to('/tmp'))
   h=sha(q);t.add(q,arcname=name,recursive=False);assert sha(q)==h
   entries.append(dict(name=name,sha256=h,size=q.stat().st_size))
 with tarfile.open(p,'r|gz') as t:
  for member,row in zip(t,entries,strict=True):
   raw=t.extractfile(member).read();assert member.name==row['name'] and len(raw)==row['size'] and hashlib.sha256(raw).hexdigest()==row['sha256']
 (out/'archive-manifest.json').write_text(json.dumps(dict(archive_sha256=sha(p),entries=entries),indent=2)+'\n')
 return len(entries)
def bindings(roots,private):
 records={};external={}
 def visit(m):
  if m in records or m in external:return
  if m in private:src,obj=private[m]
  elif (lean/Path(*m.split('.')).with_suffix('.lean')).exists():
   src=lean/Path(*m.split('.')).with_suffix('.lean');obj=lean/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean')
  else:
   p=lean/'.lake/packages/mathlib'/Path(*m.split('.')).with_suffix('.lean')
   if p.exists():external[m]=dict(source=str(p),source_sha256=sha(p))
   else:assert m.split('.')[0] in {'Mathlib','Lean','Std','Batteries','Aesop','Qq','Plausible','ProofWidgets','ImportGraph'},m;external[m]={}
   return
  assert obj.is_file(),m
  text=src.read_text();assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b',text,re.M),m
  records[m]=dict(source=str(src),source_sha256=sha(src),object=str(obj),object_sha256=sha(obj))
  for line in text.splitlines():
   if line.startswith('import '):
    for dep in line[7:].split('--',1)[0].split():visit(dep)
 for m in roots:visit(m)
 return dict(module_bindings=records,external_imports=external)
def finish(out,data):
 (out/'checkpoint-verification.json').write_text(json.dumps(data,indent=2)+'\n')
 (out/'file-manifest.json').write_text(json.dumps({str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()},indent=2)+'\n')

base=Path('/tmp/de_source_normalization_failure');d=json.loads((base/'audit-summary.json').read_text());assert d['terminal_exit_code']==0 and d['standard_only'] and d['checked_declarations']==5
src=base/'lean/SbtCosmo/Derivation/GroundSourceNormalizationFailure.lean';obj=base/'GroundSourceNormalizationFailure.olean'
assert d['source_sha256']==sha(src) and d['object_sha256']==sha(obj) and d['log_sha256']==sha(base/'Audit.log')
parent=Path('/tmp/de_source_normalization_return')
owned={'SbtCosmo.Derivation.GroundSourceNormalizationFailure':(src,obj),'SbtCosmo.Derivation.GroundSourceNormalization':(parent/'lean/SbtCosmo/Derivation/GroundSourceNormalization.lean',parent/'overlay/SbtCosmo/Derivation/GroundSourceNormalization.olean')}
bound=bindings(['SbtCosmo.Derivation.GroundSourceNormalizationFailure'],owned)
paths=[p for p in base.rglob('*') if p.is_file() and 'overlay' not in p.relative_to(base).parts]
paths += [parent/'lean/SbtCosmo/Derivation/GroundSourceNormalization.lean',parent/'overlay/SbtCosmo/Derivation/GroundSourceNormalization.olean',Path(__file__)]
out=repo/'results/source_normalization_failure_checked_2026-10-05';members=archive(out,paths)
(out/'lean/SbtCosmo/Derivation').mkdir(parents=True);(out/'lean/SbtCosmo/Derivation/GroundSourceNormalizationFailure.lean').write_bytes(src.read_bytes())
(out/'source-bindings.json').write_text(json.dumps(bound,indent=2)+'\n');(out/'audit-summary.json').write_text(json.dumps(d,indent=2)+'\n')
(out/'README.md').write_text('Five exact source-execution failure statements and standard-only transitive axiom checks passed. Actual positive ground witnesses for every background/coupling produce unit imaginary starting states whose input/candidate normalizations succeed but whose half-mixed update is zero and execution returns none at every positive count. A phase-related pair has equal site densities and source potentials but one returns a state while the other aborts. These are exact mathematical executions of the retained phase-sign implementation, supplied starting states distinct from the experiment\'s original seed. Existing algebraic cancellation is imported; the new return to Option execution and all-parameter witness are derived. They provide no physical phase-dependence claim or IEEE theorem. Missing-import and overlay audit failures and the earlier successful four-theorem stage are preserved. Repository registration and integration remain pending; existing production plans are unchanged.\n')
finish(out,dict(utc=datetime.now(timezone.utc).isoformat(),terminal_exit_code=0,standard_only=True,checked_declarations=5,archive_members_verified=members,bound_modules=len(bound['module_bindings']),registered=False,original_seed_claim=False,IEEE_theorem=False,existing_production_plans_changed=False,new_integration_obligation=dict(modules=1,declarations=5),goal_complete=False))
print('Normalization failure packet checked:',members,'archive members;',len(bound['module_bindings']),'module bindings',flush=True)

base=Path('/tmp/de_native_stable15_priority_recovery');old=Path('/tmp/de_native_stable15_priority');plan=json.loads((base/'build-plan.json').read_text());rows=plan['rows'];d=json.loads((base/'FiniteVerdictsAudit-summary.json').read_text());assert d['terminal_exit_code']==0 and d['standard_only'] and d['checked_declarations']==18
assert d['log_sha256']==sha(base/'FiniteVerdictsAudit.log') and d['audit_source_sha256']==sha(base/'FiniteVerdictsAudit.lean')
roots=['NativeStableSeed009Prefix060','NativeStableSeed009Sixty','NativeStableSeed009PrefixFailures'];closure=set()
def visit(m):
 if m in closure:return
 closure.add(m)
 for dep in plan['dependencies'][m]:visit(dep)
for m in roots:visit(m)
assert len(closure)==110 and sum(bool(re.fullmatch('NativeStableSeed009Step[0-9]{3}',m)) for m in closure)==60 and sum(bool(re.fullmatch('NativeStableSeed009Pair[0-9]{3}',m)) for m in closure)==30
retained={r['module']:r for r in json.loads((base/'retained-receipts.json').read_text())};owned={};paths=[];historical=0
for m in sorted(closure):
 owner=old if m in retained else base;historical+=m in retained
 receipt=owner/'receipts'/(m+'-terminal.json');r=json.loads(receipt.read_text());src=Path(rows[m]['source']);obj=owner/'objects'/(m+'.olean');log=owner/'receipts'/(m+'.log')
 assert r['terminal_exit_code']==0 and r['source_sha256']==rows[m]['source_sha256']==sha(src)==sha(rows[m]['original_source'])
 assert r['object_sha256']==sha(obj) and r['log_sha256']==sha(log) and not re.search(r'error:|warning:',log.read_text())
 owned[m]=(src,obj);paths += [src,obj,log,receipt]
for m in roots:assert d['sources'][m]==sha(owned[m][0]) and d['objects'][m]==sha(owned[m][1])
bound=bindings(roots,owned)
assert set(owned)<=set(bound['module_bindings'])
paths += [base/'build-plan.json',base/'retained-receipts.json',base/'interruption.json',base/'FiniteVerdictsAudit.lean',base/'FiniteVerdictsAudit.log',base/'FiniteVerdictsAudit-terminal.json',base/'FiniteVerdictsAudit-summary.json',Path(__file__)]
out=repo/'results/native_stable15_finite_checked_2026-10-05';members=archive(out,paths)
(out/'source-bindings.json').write_text(json.dumps(bound,indent=2)+'\n');(out/'audit-summary.json').write_text(json.dumps(d,indent=2)+'\n')
(out/'README.md').write_text('Original coupling15 finite prefix passed eighteen fresh statement/standard-only axiom checks. Actual original-seed updates0..59 have both guards and all states0..60 have unit norm. Every convergence-test conjunction at counts1..60 fails, witnessed by last-update residual above the original binary threshold; each component does not individually fail. The dependency closure has110 checked modules,60 leaves/30 pairs, with the preserved/fresh interruption cohorts explicitly recorded. No infinite original-seed convergence, IEEE theorem or full campaign completion follows from this finite packet. The recovery continues to its178-update entry and final27-declaration combined audit. Original regular proofs and production integration remain mandatory. Paper/runtime/registered sources are unchanged. Review is adversarial self-review.\n')
finish(out,dict(utc=datetime.now(timezone.utc).isoformat(),terminal_exit_code=0,standard_only=True,checked_declarations=18,finite_dependency_modules=110,retained_terminal_zero_modules=historical,fresh_recovery_modules=110-historical,leaves=60,pairs=30,archive_members_verified=members,bound_modules=len(bound['module_bindings']),every_prefix_one_to_sixty_fails=True,guards_before_sixty=True,unit_states_zero_to_sixty=True,original_seed_infinite_return_checked=False,registered=False,goal_complete=False))
print('Finite15 packet checked:',members,'archive members;',len(bound['module_bindings']),'bindings;',historical,'retained and',110-historical,'fresh finite dependencies',flush=True)
