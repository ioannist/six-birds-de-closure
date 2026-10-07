from pathlib import Path
import datetime,hashlib,io,json,re,tarfile
repo=Path('/home/repos/six-birds-de-closure')
parent=repo/'results/native_registered_installation_with_failure_candidate_2026-10-05'
header=repo/'results/audit_manifest_header_repair_candidate_2026-10-05'
out=repo/'results/native_registered_header_installation_candidate_2026-10-05'
sha=lambda b:hashlib.sha256(b).hexdigest()
def check(folder):
 for p,h in json.loads((folder/'file-manifest.json').read_text()).items():assert sha((folder/p).read_bytes())==h
def hoist(raw):
 lines=raw.splitlines(keepends=True)
 return b''.join(l for l in lines if l.startswith(b'import '))+b''.join(l for l in lines if not l.startswith(b'import '))
check(parent);check(header)
old=json.loads((parent/'installation-plan.json').read_text());repair=json.loads((header/'repair-plan.json').read_text())
payload={}
with tarfile.open(parent/'proposed_registered_files.tar.gz','r|gz') as tar:
 for m,r in zip(tar,old['targets'],strict=True):
  raw=tar.extractfile(m).read();assert m.isfile() and m.name==r['path'] and sha(raw)==r['sha256'];payload[m.name]=raw
audit='lean/manifests/check_axioms.lean'
before=(header/'native_manifest.before.lean').read_bytes();after=(header/'native_manifest.repaired.lean').read_bytes()
assert payload[audit]==before and hoist(before)==after and hoist(after)==after
current=(header/'current_manifest.before.lean').read_bytes();current_repaired=(header/'current_manifest.repaired.lean').read_bytes()
assert (repo/audit).read_bytes()==current and before.startswith(current)
assert hoist(current_repaired+before[len(current):])==after
queries=lambda raw:re.findall(rb'^#print axioms (\S+)',raw,re.M)
assert queries(before)==queries(after) and queries(after)[:11776]==queries(current_repaired)
assert len(set(queries(after)))==32565
payload[audit]=after;out.mkdir(exist_ok=False);archive=out/'proposed_registered_files.tar.gz';targets=[]
with tarfile.open(archive,'w:gz') as tar:
 for p,raw in sorted(payload.items()):
  m=tarfile.TarInfo(p);m.size=len(raw);tar.addfile(m,io.BytesIO(raw))
  existing=sha(current_repaired) if p==audit else sha((repo/p).read_bytes()) if (repo/p).exists() else None
  targets.append(dict(path=p,sha256=sha(raw),size=len(raw),existing_target_sha256=existing))
with tarfile.open(archive,'r|gz') as tar:
 for m,r in zip(tar,targets,strict=True):assert m.isfile() and m.name==r['path'] and sha(tar.extractfile(m).read())==r['sha256']
assert len(targets)==1783
plan=dict(old);plan.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='Source candidate with all imports moved to the header; proof and registered integration gates remain pending',targets=targets,source_archive_sha256=sha(archive.read_bytes()),parent_candidate_plan_sha256=sha((parent/'installation-plan.json').read_bytes()),preserved_default_manifest_byte_prefix=False,header_repair=dict(plan_sha256=sha((header/'repair-plan.json').read_bytes()),file_manifest_sha256=sha((header/'file-manifest.json').read_bytes()),frozen_before_sha256=sha(current),pre_native_repaired_sha256=sha(current_repaired),native_repaired_sha256=sha(after),ordered_query_prefix_preserved=11776,import_occurrences_preserved=True,nonimport_bytes_preserved=True,registered_11776_gate_pending=True))
plan['input_sha256']=dict(old['input_sha256']);plan['input_sha256'][str(repo/audit)]=sha(current_repaired)
plan['input_sha256'].update({str(header/'repair-plan.json'):sha((header/'repair-plan.json').read_bytes()),str(header/'file-manifest.json'):sha((header/'file-manifest.json').read_bytes())})
for p,h in plan['input_sha256'].items():assert sha(Path(p).read_bytes())==(sha(current) if p==str(repo/audit) else h)
plan['prerequisites']=old['prerequisites']+['Exact pre-native header repair and namespace repair after all source freezes release','Fresh actual registered11776 cumulative axiom audit, then fresh registered32565 cumulative audit; private overlay audits do not replace these commands']
(out/'installation-plan.json').write_text(json.dumps(plan,indent=2)+'\n');(out/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(out/'README.md').write_text('Prepared source candidate:1771 modules,20789 native declarations,32565 cumulative queries,1783 verified archive files. Only the default manifest differs from the previous installation candidate: all3736 import occurrences move before commands, preserving their order and every nonimport byte. The11776 ordered queries remain a prefix. The expected pre-native target is the repaired11776 manifest; the currently frozen invalid-layout file is explicitly recorded separately. No registered file changed. Actual builds and full audits remain mandatory.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in out.iterdir() if p.is_file()},indent=2)+'\n')
check(parent);check(header);check(out)
print(json.dumps(dict(verified_archive_files=len(targets),modules=1771,native_declarations=20789,cumulative_queries=32565,registered_sources_changed=False,goal_complete=False)))
