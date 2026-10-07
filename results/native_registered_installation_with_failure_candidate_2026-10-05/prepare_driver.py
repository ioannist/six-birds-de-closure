from pathlib import Path
import datetime,hashlib,importlib.util,io,json,re,tarfile
repo=Path('/home/repos/six-birds-de-closure');parent=repo/'results/native_registered_installation_candidate_2026-10-05';extra=repo/'results/source_normalization_failure_production_candidate_2026-10-05';out=repo/'results/native_registered_installation_with_failure_candidate_2026-10-05'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
for folder in [parent,extra]:
 for f,h in json.loads((folder/'file-manifest.json').read_text()).items():assert sha((folder/f).read_bytes())==h
old=json.loads((parent/'installation-plan.json').read_text());new=json.loads((extra/'production-plan.json').read_text())
assert (old['native_modules'],old['native_fresh_declarations'],old['prospective_default_declarations'])==(1770,20784,32560)
assert (new['module_count'],new['fresh_theorem_count'])==(1,5)
parser_path=repo/'scripts/de_native_campaign_verify.py';spec=importlib.util.spec_from_file_location('source_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
payload={}
with tarfile.open(parent/'proposed_registered_files.tar.gz','r|gz') as tar:
 for member,row in zip(tar,old['targets'],strict=True):
  assert member.isfile() and member.name==row['path'];raw=tar.extractfile(member).read();assert sha(raw)==row['sha256'];payload[member.name]=raw
assert len(payload)==1780
r=new['modules'][0];module=r['module'];path=r['production_path'];source=extra/path;raw=source.read_bytes();names=parser.declarations(raw.decode());imports=parser.imports(raw.decode())
assert sha(raw)==r['production_sha256'] and names==r['declared_theorems'] and imports==r['imports']
assert module not in {x['module'] for x in old['modules']} and path not in payload and not(repo/path).exists()
oldnames=[n for row in old['modules'] for n in row['declared_theorems']];assert not set(names).intersection(oldnames)
assert imports==['SbtCosmo.Derivation.GroundSourceNormalization','SbtCosmo.Derivation.GroundNativeControls']
assert imports[0] in {x['module'] for x in old['modules']}
controls=repo/'lean/SbtCosmo/Derivation/GroundNativeControls.lean';assert controls.exists()
payload[path]=raw
for kind,command in [('axioms','#print axioms'),('statements','#check')]:
 p=f'lean/manifests/check_source_normalization_failure_{kind}.lean';raw=(extra/p).read_bytes();assert re.findall(r'^'+re.escape(command)+r' (\S+)',raw.decode(),re.M)==names
 assert p not in payload and not(repo/p).exists();payload[p]=raw
lake='lean/lakefile.lean';audit='lean/manifests/check_axioms.lean';assert payload[lake].endswith(b']\n')
payload[lake]=payload[lake][:-2]+(',\n    `'+module+']\n').encode()
payload[audit]+=('\nimport '+module+'\n\n'+''.join('#print axioms '+n+'\n' for n in names)).encode()
current=(repo/audit).read_bytes();assert payload[audit].startswith(current)
allnames=re.findall(r'^#print axioms (\S+)',payload[audit].decode(),re.M);assert len(allnames)==len(set(allnames))==32565
assert len(payload)==1783
out.mkdir(exist_ok=False);archive=out/'proposed_registered_files.tar.gz';targets=[]
with tarfile.open(archive,'w:gz') as tar:
 for p,raw in sorted(payload.items()):
  member=tarfile.TarInfo(p);member.size=len(raw);tar.addfile(member,io.BytesIO(raw))
  targets.append(dict(path=p,sha256=sha(raw),size=len(raw),existing_target_sha256=sha((repo/p).read_bytes()) if(repo/p).exists() else None))
with tarfile.open(archive,'r|gz') as tar:
 for member,row in zip(tar,targets,strict=True):assert member.name==row['path'] and sha(tar.extractfile(member).read())==row['sha256']
plan=dict(old);plan.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='Exact extension of prior installation candidate by checked five-declaration execution-failure source; all final gates remain mandatory',native_modules=1771,native_fresh_declarations=20789,prospective_default_declarations=32565,modules=old['modules']+[dict(group='execution_failure',module=module,target=path,candidate_source=str(source),source_sha256=r['production_sha256'],declared_theorems=names)],topological_order=old['topological_order']+[module],targets=targets,source_archive_members=1783,source_archive_sha256=sha(archive.read_bytes()),parent_candidate_plan_sha256=sha((parent/'installation-plan.json').read_bytes()),additional_candidate_plan_sha256=sha((extra/'production-plan.json').read_bytes()),registered_checker_extension_pending=True)
plan['group_counts']=dict(old['group_counts'],execution_failure=dict(modules=1,declarations=5))
plan['external_imports']=sorted(set(old['external_imports'])|{imports[1]})
plan['input_sha256']=dict(old['input_sha256']);plan['input_sha256'][str(controls)]=sha(controls.read_bytes());plan['input_sha256'].update({str(extra/'production-plan.json'):sha((extra/'production-plan.json').read_bytes()),str(extra/'file-manifest.json'):sha((extra/'file-manifest.json').read_bytes())})
plan['prerequisites']=old['prerequisites']+['Exact checked five-declaration execution-failure source and parent preserved; fresh registered checks required','Registered verifier and runner extended and reviewed for all1771 modules/20789 native declarations/32565 cumulative declarations']
assert all(sha(Path(p).read_bytes())==h for p,h in plan['input_sha256'].items())
(out/'installation-plan.json').write_text(json.dumps(plan,indent=2)+'\n');(out/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(out/'README.md').write_text('Exact extension of the unchanged prior installation candidate by one checked source-execution-failure module and its two manifests.1771 modules,20789 fresh native declarations,32565 prospective cumulative declarations and1783 archived target files were enumerated, collision checked, read back and hashed. The old11776-declaration manifest remains a byte prefix; the original four candidate plans and32560 installation candidate remain unchanged. No registered source or object was changed. All prior proof gates, registered checker/runner extension and review, genuine builds and fresh full audits remain mandatory. This is a source candidate, not a proof-completion receipt.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in out.iterdir() if p.is_file()},indent=2)+'\n')
for folder in [parent,extra]:
 for f,h in json.loads((folder/'file-manifest.json').read_text()).items():assert sha((folder/f).read_bytes())==h
print(json.dumps(dict(modules=1771,native_declarations=20789,prospective_cumulative_declarations=32565,verified_archive_members=1783,parent_candidate_unchanged=True,registered_inputs_changed=False,output=str(out))))
