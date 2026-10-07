from pathlib import Path
import json,hashlib,tarfile,io,re,datetime,importlib.util
REPO=Path('/home/repos/six-birds-de-closure')
PARENT=REPO/'results/native_registered_header_installation_candidate_2026-10-05'
ADDON=REPO/'results/original_audit_nonidentifiability_production_candidate_2026-10-05'
CHECKED=REPO/'results/original_audit_nonidentifiability_checked_2026-10-05'
DEPS=REPO/'results/original_audit_nonidentifiability_dependency_checkpoint_2026-10-05'
OUT=REPO/'results/native_registered_original_audit_installation_candidate_2026-10-05'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rawsha(raw):return hashlib.sha256(raw).hexdigest()
def check(p):assert all(sha(p/f)==h for f,h in json.loads((p/'file-manifest.json').read_text()).items())
def hoist(raw):
    lines=raw.splitlines(keepends=True)
    return b''.join(l for l in lines if l.startswith(b'import '))+b''.join(l for l in lines if not l.startswith(b'import '))
for p in [PARENT,ADDON,CHECKED,DEPS]:check(p)
spec=importlib.util.spec_from_file_location('native_source_parser',REPO/'scripts/de_native_campaign_verify.py');parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
old=json.loads((PARENT/'installation-plan.json').read_text());extra=json.loads((ADDON/'production-plan.json').read_text())
assert (old['native_modules'],old['native_fresh_declarations'],old['prospective_default_declarations'])==(1771,20789,32565)
assert (extra['modules'],extra['declarations'])==(1,9)
payload={}
with tarfile.open(PARENT/'proposed_registered_files.tar.gz','r|gz') as t:
    for m,r in zip(t,old['targets'],strict=True):
        raw=t.extractfile(m).read();assert m.isfile() and m.name==r['path'] and rawsha(raw)==r['sha256'];payload[m.name]=raw
assert len(payload)==1783
source_rel='lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean'
source=ADDON/source_rel;mod=extra['module'];names=extra['names']
assert sha(source)==extra['source_sha256']==sha(CHECKED/source_rel)
assert parser.declarations(source.read_text())==names
newfiles={str(p.relative_to(ADDON)):p.read_bytes() for p in (ADDON/'lean').rglob('*.lean')}
assert len(newfiles)==3 and not (set(newfiles)&set(payload))
payload.update(newfiles)
audit='lean/manifests/check_axioms.lean';old_audit=payload[audit]
suffix=('\nimport '+mod+'\n\n'+''.join('#print axioms '+n+'\n' for n in names)).encode()
payload[audit]=hoist(old_audit+suffix)
queries=lambda b:re.findall(rb'^#print axioms (\S+)',b,re.M)
assert queries(payload[audit])[:32565]==queries(old_audit) and len(set(queries(payload[audit])))==32574
assert hoist(payload[audit])==payload[audit]
lake='lean/lakefile.lean';old_lake=payload[lake]
anchor=b'    `SbtCosmo.Derivation.GroundSourceNormalizationFailure]'
assert old_lake.count(anchor)==1
payload[lake]=old_lake.replace(anchor,b'    `SbtCosmo.Derivation.GroundSourceNormalizationFailure,\n    `'+mod.encode()+b']')
assert payload[lake].count(('`'+mod).encode())==1
row=dict(group='original_audit_nonidentifiability',module=mod,target=source_rel,candidate_source=str(source),source_sha256=sha(source),declared_theorems=names)
modules=old['modules']+[row]
order=old['topological_order']+[mod]
positions={m:i for i,m in enumerate(order)}
assert len(positions)==len(order)==1772
external=set(old['external_imports'])
for m in modules:
    for imp in parser.imports(payload[m['target']].decode()):
        if imp in positions:assert positions[imp]<positions[m['module']]
        else:external.add(imp)
assert not OUT.exists();OUT.mkdir()
archive=OUT/'proposed_registered_files.tar.gz';targets=[]
with tarfile.open(archive,'w:gz') as t:
    for p,raw in sorted(payload.items()):
        info=tarfile.TarInfo(p);info.size=len(raw);t.addfile(info,io.BytesIO(raw))
        existing=next((r['existing_target_sha256'] for r in old['targets'] if r['path']==p),None)
        assert p in {audit,lake} or not (REPO/p).exists() or sha(REPO/p)==existing
        targets.append(dict(path=p,sha256=rawsha(raw),size=len(raw),existing_target_sha256=existing))
with tarfile.open(archive,'r|gz') as t:
    for m,r in zip(t,targets,strict=True):assert m.isfile() and m.name==r['path'] and rawsha(t.extractfile(m).read())==r['sha256']
assert len(targets)==1786
plan=dict(old)
plan.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='Source candidate extended by the freshly checked original-audit1/9 construction; actual registered proof gates pending',native_modules=1772,native_fresh_declarations=20798,prospective_default_declarations=32574,modules=modules,topological_order=order,external_imports=sorted(external),targets=targets,source_archive_sha256=sha(archive),source_archive_members=1786,parent_header_candidate_plan_sha256=sha(PARENT/'installation-plan.json'),original_audit_addon_plan_sha256=sha(ADDON/'production-plan.json'),original_audit_checked_manifest_sha256=sha(CHECKED/'file-manifest.json'),original_audit_dependency_manifest_sha256=sha(DEPS/'file-manifest.json'))
plan['group_counts']=dict(old['group_counts']);plan['group_counts'][row['group']]=dict(modules=1,declarations=9)
plan['input_sha256']=dict(old['input_sha256'])
for p in [ADDON/'production-plan.json',ADDON/'file-manifest.json',CHECKED/'file-manifest.json',DEPS/'file-manifest.json',PARENT/'installation-plan.json',PARENT/'file-manifest.json']:
    plan['input_sha256'][str(p)]=sha(p)
for imp in parser.imports(source.read_text()):
    if imp not in positions:
        p=REPO/'lean'/Path(*imp.split('.')).with_suffix('.lean')
        assert p.is_file();plan['input_sha256'][str(p)]=sha(p)
plan['header_repair']=dict(old['header_repair']);plan['header_repair']['parent_native_repaired_sha256']=old['header_repair']['native_repaired_sha256'];plan['header_repair']['native_repaired_sha256']=rawsha(payload[audit]);plan['header_repair']['ordered_parent_native_query_prefix_preserved']=32565
plan['prerequisites']=old['prerequisites']+['Exact original-audit1/9 source, actual checked receipts and preserved historical dependencies verified','Registered verifier/runner explicitly extended to1772 modules/20798 native declarations/32574 cumulative queries, followed by actual fresh registered commands']
(OUT/'installation-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
(OUT/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(OUT/'README.md').write_text('Prepared extended source candidate:1772 modules,20798 native declarations,32574 cumulative queries,1786 verified archive targets. The1/9 original-audit add-on supplies one canonical source and two dedicated manifests; only lake registration and the default cumulative manifest change among old targets. All32565 prior ordered queries are preserved, and the default manifest retains a valid import header. No registered source/object is changed. All inherited proof/freeze/whole-offset gates and actual registered build/statement/cumulative-axiom commands remain mandatory. Prior candidate/archive/plan bytes remain unchanged.\n')
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
for p in [PARENT,ADDON,CHECKED,DEPS,OUT]:check(p)
print(json.dumps(dict(archive_targets=1786,native_modules=1772,native_declarations=20798,cumulative_queries=32574,registered_inputs_changed=False)),flush=True)
