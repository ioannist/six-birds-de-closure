import ast,copy,datetime,hashlib,json,re
from pathlib import Path
ROOT=Path('/home/repos/six-birds-de-closure');proposal=Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_repaired.py');OUT=ROOT/'results/ground_offset_header_exception_review_2026-10-05'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
tree=ast.parse(proposal.read_text());verify=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='verify')
assign=lambda n,name:isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets)
first=next(i for i,n in enumerate(verify.body) if assign(n,'repair_packet'))
stop=next(i for i,n in enumerate(verify.body) if assign(n,'full_root'))
loopfirst=next(i for i,n in enumerate(verify.body) if assign(n,'changed'))
last=next(i for i,n in enumerate(verify.body) if isinstance(n,ast.Assert) and ast.unparse(n.test)=='set(changed) == set(allowed)')
block=ast.Module(body=copy.deepcopy(verify.body[first:stop]+verify.body[loopfirst:last+1]),type_ignores=[])
class Adapter(ast.NodeTransformer):
 counts={}
 def visit_Call(self,node):
  value=ast.unparse(node)
  for var in ['p','manifest_path']:
   if value=='(ROOT / '+var+').read_bytes()':
    self.counts[var]=self.counts.get(var,0)+1
    return ast.copy_location(ast.Call(func=ast.Name(id='virtual_bytes',ctx=ast.Load()),args=[ast.Name(id=var,ctx=ast.Load())],keywords=[]),node)
  return self.generic_visit(node)
adapter=Adapter();block=ast.fix_missing_locations(adapter.visit(block));assert adapter.counts=={'manifest_path':1,'p':1};code=compile(block,str(proposal),'exec')
recovery=json.loads((ROOT/'results/ground_offset_transport_2026-10-04/leaves_recovery.json').read_text());plan=json.loads(Path('/tmp/de_offset_transport_namespace_recovery/registered-integration-plan.json').read_text())
original={p:(ROOT/p).read_bytes() for p in recovery['source_sha256']};assert all(sha(original[p])==h for p,h in recovery['source_sha256'].items())
patched={}
for p,r in plan['namespace_repairs'].items():
 patched[p]=original[p].decode().replace(r['replacement']['old'],r['replacement']['new']).encode();assert sha(patched[p])==r['repaired_sha256']
mp='lean/manifests/check_axioms.lean';header=ROOT/'results/audit_manifest_header_repair_candidate_2026-10-05';patched[mp]=(header/'current_manifest.repaired.lean').read_bytes();assert len(patched)==20
def hoist(raw):
 ls=raw.splitlines(keepends=True);return b''.join(l for l in ls if l.startswith(b'import '))+b''.join(l for l in ls if not l.startswith(b'import '))
cases=[]
def run(name,edits,frozen,accept=False):
 reads=dict(original);reads.update(edits)
 def virtual_bytes(p):return reads[p] if p in reads else (ROOT/p).read_bytes()
 env=dict(ROOT=ROOT,Path=Path,json=json,re=re,sha=sha,hoist=hoist,recovery=frozen,expected_before=original[mp],read=lambda p:virtual_bytes(p).decode(),virtual_bytes=virtual_bytes)
 try:exec(code,env)
 except AssertionError as e:
  assert not accept,(name,str(e));cases.append(dict(name=name,expected='reject',actual='reject'))
 else:
  assert accept and set(env['changed'])==set(patched);cases.append(dict(name=name,expected='accept',actual='accept',changed=20))
run('exact_twenty_changes',patched,copy.deepcopy(recovery),True)
for path,label in [(mp,'missing_header_repair'),('scripts/de_ground_offset_transport_render.py','missing_renderer_repair'),('lean/SbtCosmo/Derivation/GroundOffsetTransport/Point000.lean','missing_family_repair')]:
 e=dict(patched);e.pop(path);run(label,e,copy.deepcopy(recovery))
ls=patched[mp].splitlines(keepends=True);qi=next(i for i,l in enumerate(ls) if l.startswith(b'#print axioms '));ii=next(i for i,l in enumerate(ls) if l.startswith(b'import '))
mutations={'dropped_query':b''.join(ls[:qi]+ls[qi+1:]),'duplicated_query':patched[mp]+ls[qi],'dropped_import':b''.join(ls[:ii]+ls[ii+1:]),'extra_nonimport_bytes':patched[mp]+b'\n','late_import':b''.join(ls[:ii]+ls[ii+1:])+ls[ii]}
swapped=list(ls);swapped[qi],swapped[qi+1]=swapped[qi+1],swapped[qi];mutations['reordered_queries']=b''.join(swapped)
for name,raw in mutations.items():e=dict(patched);e[mp]=raw;run(name,e,copy.deepcopy(recovery))
wrong=copy.deepcopy(recovery);wrong['source_sha256'][mp]='0'*64;run('wrong_original_manifest_digest',patched,wrong)
unrelated=next(p for p in original if '/Point000/' in p and p.endswith('.lean'));e=dict(patched);e[unrelated]=original[unrelated]+b'\n';run('unrelated_leaf_change',e,copy.deepcopy(recovery))
OUT.mkdir(exist_ok=False);(OUT/'review_driver.py').write_bytes(Path(__file__).read_bytes());(OUT/'verifier_proposal.py').write_bytes(proposal.read_bytes())
(OUT/'review.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),terminal_exit_code=0,controls=cases,historical_inputs=len(original),ast_adapters=adapter.counts,scope='Actual namespace/header exception and unchanged historical-freeze loop only; fresh registered receipt block excluded because evidence remains pending',fresh_registered_success_path_tested=False,registered_sources_changed=False,review='adversarial self-review, not independent review',goal_complete=False),indent=2)+'\n')
(OUT/'README.md').write_text('Actual proposed namespace/header exception accepts precisely20 bound repairs and rejects11 missing, altered or unrelated changes. Two documented in-memory read adapters expose proposed registered bytes. The new registered11776 receipt block is deliberately excluded from this exception-only review: no registered command or full success path is claimed.\n')
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n');print(json.dumps(dict(accepted=1,rejected=len(cases)-1,registered_commands_started=0)))
