"""Prepare exact future native installation bytes; never mutate registered inputs."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json,re,tarfile,io

repo=Path('/home/repos/six-birds-de-closure')
out=repo/'results/native_registered_installation_candidate_2026-10-05'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
verifier=repo/'scripts/de_native_campaign_verify.py'
spec=importlib.util.spec_from_file_location('native_installation_source_parser',verifier)
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
groups=[
 ('main',Path('/tmp/de-native-campaign-production-plan.json'),Path('/tmp/de_native_campaign_production_preview'),'native_campaign',1734,20628),
 ('real',Path('/tmp/de-native-seed-real-returns-production-plan.json'),Path('/tmp/de_native_seed_real_returns_preview'),'native_seed_real_returns',4,6),
 ('additional',repo/'results/native_additional_constructions_candidate_2026-10-05/production-plan.json',repo/'results/native_additional_constructions_candidate_2026-10-05','native_additional_constructions',29,132),
 ('execution',repo/'results/source_execution_production_candidate_2026-10-05/production-plan.json',repo/'results/source_execution_production_candidate_2026-10-05','source_execution_supplement',3,18)]
payload={};rows=[];allnames=[];plans={};deps={};inputs={str(verifier):sha(verifier.read_bytes())}
for tag,pp,root,prefix,count,ncount in groups:
 plan=json.loads(pp.read_text());assert plan['module_count']==count and plan['fresh_theorem_count']==ncount
 plans[tag]=plan;inputs[str(pp)]=sha(pp.read_bytes())
 derived=[]
 for r in plan['modules']:
  module=r.get('production_module',r.get('module'));p=r['production_path'];src=root/p
  raw=src.read_bytes();assert sha(raw)==r['production_sha256']
  names=parser.declarations(raw.decode());assert names==r['declared_theorems'],module
  assert p=='lean/'+module.replace('.','/')+'.lean' and p not in payload
  assert not (repo/p).exists(),('Existing installation target',p)
  payload[p]=raw;allnames+=names;derived+=names
  rows.append(dict(group=tag,module=module,target=p,candidate_source=str(src),source_sha256=sha(raw),declared_theorems=names))
  deps[module]=parser.imports(raw.decode())
 assert len(derived)==ncount
 for stage,command in [('axioms','#print axioms'),('statements','#check')]:
  p=f'lean/manifests/check_{prefix}_{stage}.lean';raw=(root/p).read_bytes()
  ns=re.findall(r'^'+re.escape(command)+r' (\S+)',raw.decode(),re.M)
  assert ns==derived and p not in payload and not (repo/p).exists()
  payload[p]=raw
assert plans['real']['parent_plan_sha256']==inputs[str(groups[0][1])]
for tag in ('additional','execution'):
 assert plans[tag]['parent_plan_sha256']==inputs[str(groups[0][1])]
 assert plans[tag]['supplement_plan_sha256']==inputs[str(groups[1][1])]
assert plans['execution']['fixed29_plan_sha256']==inputs[str(groups[2][1])]
assert len(rows)==len({r['module'] for r in rows})==1770
assert len(allnames)==len(set(allnames))==20784
old_audit_path=repo/'lean/manifests/check_axioms.lean';old_audit=old_audit_path.read_bytes()
oldnames=re.findall(r'^#print axioms (\S+)',old_audit.decode(),re.M)
assert len(oldnames)==len(set(oldnames))==11776 and not set(oldnames).intersection(allnames)
old_lake_path=repo/'lean/lakefile.lean';old_lake=old_lake_path.read_bytes()
assert old_lake.endswith(b']\n')
modules=[r['module'] for r in rows]
oldroots=re.findall(r'`(SbtCosmo[\w.]*)',old_lake.decode())
assert not set(oldroots).intersection(modules)
new_lake=old_lake[:-2]+(',\n    '+', '.join('`'+m for m in modules)+']\n').encode()
append=('\n'+''.join('import '+m+'\n' for m in modules)+'\n'+''.join('#print axioms '+n+'\n' for n in allnames)).encode()
new_audit=old_audit+append
assert new_audit.startswith(old_audit)
assert re.findall(r'^#print axioms (\S+)',new_audit.decode(),re.M)==oldnames+allnames
assert len(set(oldnames+allnames))==32560
payload['lean/lakefile.lean']=new_lake
payload['lean/manifests/check_axioms.lean']=new_audit
for p in (old_lake_path,old_audit_path):inputs[str(p)]=sha(p.read_bytes())
remaining={m:set(imps).intersection(modules) for m,imps in deps.items()};topological=[];done=set()
while remaining:
 ready=sorted(m for m,ds in remaining.items() if ds<=done);assert ready,'Cyclic combined installation graph'
 for m in ready:remaining.pop(m);done.add(m);topological.append(m)
externals=sorted(set(i for imps in deps.values() for i in imps)-set(modules))
for m in externals:
 p=repo/'lean'/Path(*m.split('.')).with_suffix('.lean')
 if not p.exists():p=repo/'lean/.lake/packages/mathlib'/Path(*m.split('.')).with_suffix('.lean')
 assert p.exists(),('Unresolved external import',m)
 inputs[str(p)]=sha(p.read_bytes())
out.mkdir(exist_ok=False)
archive=out/'proposed_registered_files.tar.gz';entries=[]
with tarfile.open(archive,'w:gz') as tar:
 for p,raw in sorted(payload.items()):
  info=tarfile.TarInfo(p);info.size=len(raw);tar.addfile(info,io.BytesIO(raw))
  entries.append(dict(path=p,sha256=sha(raw),size=len(raw),existing_target_sha256=sha((repo/p).read_bytes()) if (repo/p).exists() else None))
with tarfile.open(archive,'r|gz') as tar:
 for member,row in zip(tar,entries,strict=True):
  assert member.name==row['path'] and member.isfile()
  raw=tar.extractfile(member).read();assert len(raw)==row['size'] and sha(raw)==row['sha256']
plan=dict(utc=datetime.now(timezone.utc).isoformat(),status='Prepared exact installation bytes; all final proof and integration gates remain mandatory',
 native_modules=1770,native_fresh_declarations=20784,preserved_default_declarations=11776,prospective_default_declarations=32560,
 group_counts={tag:dict(modules=count,declarations=ncount) for tag,_,_,_,count,ncount in groups},modules=rows,
 topological_order=topological,external_imports=externals,input_sha256=inputs,targets=entries,
 source_archive_sha256=sha(archive.read_bytes()),source_archive_members=len(entries),
 prerequisites=['All live source freezes released at authoritative terminal success',
 'Original twelve-sample aggregate and coupling15 obligations checked',
 'Main and real qualified campaigns and full qualified semantic verifier checked',
 'Both supplemental qualified campaigns checked',
 'Exact offset namespace repair installed and genuine default10003-job registered build checked',
 'Whole-offset11776-declaration semantic gate closed before native registration'],
 after_install=['Exact installed-byte and registry checks','Genuine registered Lake build','Required statement/axiom and semantic/source audits','Coverage/documentation updates and commit'],
 preserved_default_manifest_byte_prefix=True,qualified_objects_copied=False,registered_sources_changed=False,
 fresh_qualified_proof_completion_claimed=False,registered_build_claimed=False,paper_edited=False,original_runtime_edited=False,goal_complete=False)
(out/'installation-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
(out/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(out/'README.md').write_text('Prepared future installation bytes for the unchanged four candidate plans:1734+4+29+3 modules and20628+6+132+18 declarations. The source declarations, combined import DAG, exact fresh manifests, source hashes and collision-free32560 prospective default declarations were checked. All1780 archived target files were read back and hashed. The existing11776-declaration default manifest is an exact byte prefix. No registered input or object was changed. Qualified completion, release of all active freezes, the genuine registered whole-offset gate, native registration/build/audits and commit remain mandatory. This archive is a source candidate, not a proof-completion receipt.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in out.iterdir() if p.is_file()},indent=2)+'\n')
assert sha(old_lake_path.read_bytes())==inputs[str(old_lake_path)] and sha(old_audit_path.read_bytes())==inputs[str(old_audit_path)]
print(json.dumps(dict(terminal_exit_code=0,modules=1770,native_declarations=20784,prospective_default_declarations=32560,archive_members=len(entries),external_imports=len(externals),registered_inputs_changed=False,qualified_completion_claimed=False,output=str(out))))
