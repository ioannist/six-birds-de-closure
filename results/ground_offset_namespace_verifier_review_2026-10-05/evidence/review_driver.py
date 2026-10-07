"""Check retained verifier gates and the checked repair packet's evidence."""
import ast
import copy
import hashlib
import json
import re
import tarfile
from pathlib import Path
from datetime import datetime, timezone

ROOT=Path('/home/repos/six-birds-de-closure')
BASE=Path('/tmp/de_offset_transport_namespace_recovery')
PACKET=ROOT/'results/ground_offset_namespace_recovery_checked_2026-10-05'
OUT=ROOT/'results/ground_offset_namespace_verifier_review_2026-10-05/evidence'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
old_path=ROOT/'scripts/de_ground_offset_transport_verify.py'
new_path=BASE/'de_ground_offset_transport_verify.repaired.py'
old=ast.parse(old_path.read_text());new=ast.parse(new_path.read_text())
ov=next(n for n in old.body if isinstance(n,ast.FunctionDef) and n.name=='verify')
nv=next(n for n in new.body if isinstance(n,ast.FunctionDef) and n.name=='verify')
first=next(i for i,n in enumerate(nv.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='repair_packet' for t in n.targets))
last=next(i for i,n in enumerate(nv.body) if isinstance(n,ast.Assert) and ast.unparse(n.test)=='set(changed) == set(allowed)')
historical=next(n for n in ov.body if isinstance(n,ast.For) and ast.unparse(n.iter)=="recovery['source_sha256'].items()")
nv.body[first:last+1]=[copy.deepcopy(historical)]
extra=[n for n in nv.body if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='update' and 'repair_packet.rglob' in ast.unparse(n)]
assert len(extra)==1
nv.body.remove(extra[0])
removed=[]
for n in ast.walk(nv):
    if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='dict':
        ks=[k for k in n.keywords if k.arg=='namespace_recovery']
        for k in ks:n.keywords.remove(k);removed.append(k)
assert len(removed)==1
assert ast.dump(old,include_attributes=False)==ast.dump(new,include_attributes=False), 'An original gate changed outside the three declared additions'

manifest=json.loads((PACKET/'file-manifest.json').read_text())
for p,h in manifest.items():assert sha((PACKET/p).read_bytes())==h,p
archive_manifest=json.loads((PACKET/'archive-manifest.json').read_text())
archive=PACKET/'checked_artifacts.tar.gz'
assert sha(archive.read_bytes())==archive_manifest['archive_sha256']
archived={}
with tarfile.open(archive,'r|gz') as saved:
    for member,row in zip(saved,archive_manifest['entries'],strict=True):
        assert member.name==row['name'] and member.isfile()
        raw=saved.extractfile(member).read()
        assert len(raw)==row['size'] and sha(raw)==row['sha256'],member.name
        archived[member.name]=raw
assert len(archived)==100
prefix='de_offset_transport_namespace_recovery/'
assert archived[prefix+'de_ground_offset_transport_verify.repaired.py']==new_path.read_bytes()
binding_path=PACKET/'source-bindings.json'
bindings=json.loads(binding_path.read_text())
audit=json.loads((PACKET/'audit-summary.json').read_text())
assert audit==json.loads(archived[prefix+'axiom-audit-summary.json'])
assert audit['terminal_exit_code']==0 and audit['standard_only'] and audit['checked_declarations']==6909
raw=archived[prefix+'check_ground_offset_transport_axioms.log'].decode()
assert sha(raw.encode())==audit['log_sha256']
ns=re.findall(r'^#print axioms (\S+)',archived[prefix+'check_ground_offset_transport_axioms.lean'].decode(),re.M)
assert len(ns)==len(set(ns))==6909
entries=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",raw)
assert [n for n,a in entries]==ns
assert not re.search(r'error:|warning:|sorryAx',raw)
for n,a in entries:assert {x.strip() for x in a.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},n
statement=archived[prefix+'check_ground_offset_transport_statements.log'].decode()
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',statement,re.M)]==ns
assert not re.search(r'error:|warning:',statement)
for kind in ('axioms','statements'):
    receipt=json.loads(archived[prefix+f'check_ground_offset_transport_{kind}-terminal.json'])
    assert receipt['terminal_exit_code']==0
for module,b in bindings['module_bindings'].items():
    for key in ('source','object'):
        assert sha(Path(b[key]).read_bytes())==b[key+'_sha256'],(module,key)
for module,b in bindings['external_imports'].items():
    if 'source' in b:assert sha(Path(b['source']).read_bytes())==b['source_sha256'],module

OUT.mkdir(exist_ok=False)
result=dict(utc=datetime.now(timezone.utc).isoformat(),terminal_exit_code=0,
            scope='Verifier exception self-review and revalidation of existing isolated proof evidence; registered integration still pending',
            original_verifier_gates_AST_identical_after_exactly_three_declared_additions=True,
            additions=['historical freeze namespace exception','repair packet files included in fingerprints','namespace recovery provenance field'],
            packet_manifest_files=len(manifest),archive_members=len(archived),fresh_historical_statement_receipts=6909,
            historical_standard_only_axiom_receipts=6909,bound_modules_revalidated=len(bindings['module_bindings']),
            external_import_entries=len(bindings['external_imports']),
            review='adversarial self-review, not independent review',new_Lean_commands_run=0,
            registered_sources_changed=False,whole_offset_gate_complete=False,goal_complete=False,
            inputs={str(p):sha(p.read_bytes()) for p in (old_path,new_path,binding_path,PACKET/'file-manifest.json',PACKET/'archive-manifest.json')})
(OUT/'review.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'review_driver.py').write_bytes(Path(__file__).read_bytes())
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(result))
