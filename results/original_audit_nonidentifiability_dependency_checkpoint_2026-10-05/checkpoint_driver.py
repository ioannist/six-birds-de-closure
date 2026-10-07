from pathlib import Path
import json,hashlib,tarfile,datetime,shutil
REPO=Path('/home/repos/six-birds-de-closure')
BASE=Path('/tmp/de_original_audit_nonidentifiability_v3')
PARENT=REPO/'results/original_audit_nonidentifiability_checked_2026-10-05'
OUT=REPO/'results/original_audit_nonidentifiability_dependency_checkpoint_2026-10-05'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
freeze=json.loads((PARENT/'audit-source-object-freeze.json').read_text())
assert all(sha(p)==h for p,h in freeze.items())
assert all(sha(PARENT/p)==h for p,h in json.loads((PARENT/'file-manifest.json').read_text()).items())
summary=json.loads((PARENT/'checkpoint-verification.json').read_text())
assert summary['standard_only'] and summary['compile_terminal_exit_code']==summary['audit_terminal_exit_code']==0
assert not OUT.exists();OUT.mkdir()
payload={}
for name,h in freeze.items():
    p=Path(name)
    if p.is_relative_to(REPO):arc='repo/'+str(p.relative_to(REPO))
    else:
        assert p.is_relative_to(BASE)
        arc='private/'+str(p.relative_to(BASE))
    assert arc not in payload
    payload[arc]=(p,h)
for p in PARENT.rglob('*'):
    if p.is_file():payload['checked_packet/'+str(p.relative_to(PARENT))]=(p,sha(p))
entries=[];archive=OUT/'checked_sources_objects_receipts.tar.gz'
print('Archiving the original audit dependency sources/objects and actual checked receipts:',len(payload),'members',flush=True)
with tarfile.open(archive,'w:gz',compresslevel=1,dereference=True) as t:
    for name,(p,h) in sorted(payload.items()):
        assert sha(p)==h
        t.add(p,arcname=name,recursive=False)
        entries.append(dict(name=name,size=p.stat().st_size,sha256=h))
verified=0
with tarfile.open(archive,'r|gz') as t:
    for m,e in zip(t,entries,strict=True):
        assert m.isfile() and m.name==e['name'] and m.size==e['size']
        h=hashlib.sha256()
        with t.extractfile(m) as f:
            for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
        assert h.hexdigest()==e['sha256'];verified+=1
assert verified==len(payload)
assert all(sha(p)==h for p,h in freeze.items())
assert all(sha(PARENT/p)==h for p,h in json.loads((PARENT/'file-manifest.json').read_text()).items())
write(OUT/'archive-manifest.json',dict(archive_sha256=sha(archive),entries=entries))
write(OUT/'checkpoint-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),archive_members_verified=verified,project_dependency_modules=1327,bound_inputs=len(freeze),checked_declarations=9,standard_only=True,new_compilation_claimed=False,registered_execution_claimed=False,parent_packet_manifest_sha256=sha(PARENT/'file-manifest.json'),parent_audit_log_sha256=sha(PARENT/'audit.log'),preserved_lakefile_sha256=freeze[str(REPO/'lean/lakefile.lean')],all_original_bound_inputs_unchanged=True,registered_inputs_changed=False))
shutil.copy2(Path(__file__),OUT/'checkpoint_driver.py')
(OUT/'README.md').write_text('Preserves every source/object/configuration bound by the actual nine-declaration original-audit check, plus the complete checked packet, before registered rebuilding can change object or registration bytes. All archive members were sequentially read back and hashed. This is evidence preservation, not an additional compile, new theorem, or registered proof gate. Earlier checked-packet historical object bindings remain immutable; this separate checkpoint supplies their archived bytes. Lean/mathlib dependencies outside the project retain their pinned-toolchain scope.\n')
write(OUT/'file-manifest.json',{str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file()})
assert all(sha(OUT/p)==h for p,h in json.loads((OUT/'file-manifest.json').read_text()).items())
print(json.dumps(dict(archive_members_verified=verified,archive_bytes=archive.stat().st_size,bound_inputs=len(freeze),registered_inputs_changed=False)),flush=True)
