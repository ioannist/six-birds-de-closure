"""Exercise the proposed historical-freeze exception without installing it."""
import ast
import copy
import hashlib
import json
import re
from pathlib import Path
from datetime import datetime, timezone

ROOT = Path('/home/repos/six-birds-de-closure')
PROPOSAL = Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.repaired.py')
OUT = ROOT / 'results/ground_offset_namespace_verifier_review_2026-10-05'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
text = PROPOSAL.read_text()
tree = ast.parse(text)
verify = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'verify')
first = next(i for i,n in enumerate(verify.body) if isinstance(n, ast.Assign) and any(isinstance(t,ast.Name) and t.id == 'repair_packet' for t in n.targets))
last = next(i for i,n in enumerate(verify.body) if isinstance(n, ast.Assert) and ast.unparse(n.test) == 'set(changed) == set(allowed)')
block = ast.Module(body=copy.deepcopy(verify.body[first:last+1]), type_ignores=[])

class VirtualRead(ast.NodeTransformer):
    count = 0
    def visit_Call(self, node):
        if ast.unparse(node) == '(ROOT / p).read_bytes()':
            self.count += 1
            return ast.copy_location(ast.Call(func=ast.Name(id='virtual_bytes',ctx=ast.Load()),args=[ast.Name(id='p',ctx=ast.Load())],keywords=[]),node)
        return self.generic_visit(node)

adapter = VirtualRead()
block = ast.fix_missing_locations(adapter.visit(block))
assert adapter.count == 1, 'Only the historical-loop file-read adapter is permitted'
code = compile(block, str(PROPOSAL), 'exec')
recovery_path = ROOT/'results/ground_offset_transport_2026-10-04/leaves_recovery.json'
recovery = json.loads(recovery_path.read_text())
plan_path = Path('/tmp/de_offset_transport_namespace_recovery/registered-integration-plan.json')
plan = json.loads(plan_path.read_text())
replacements = plan['namespace_repairs']
assert len(replacements) == 19
original = {p:(ROOT/p).read_bytes() for p in recovery['source_sha256']}
assert all(sha(original[p]) == h for p,h in recovery['source_sha256'].items())
patched = {}
for p,r in replacements.items():
    assert sha(original[p]) == r['original_sha256']
    old,new = r['replacement']['old'],r['replacement']['new']
    assert original[p].decode().count(old) == 1
    patched[p] = original[p].decode().replace(old,new).encode()
    assert sha(patched[p]) == r['repaired_sha256']
family = next(p for p in replacements if p.endswith('Point000.lean'))
renderer = 'scripts/de_ground_offset_transport_render.py'
unrelated = next(p for p in original if p.endswith('.lean') and p not in replacements and '/Point000/' in p)
cases = []

def run_case(name, edits, frozen, should_pass):
    reads = dict(original)
    reads.update(edits)
    def virtual_bytes(p):
        return reads[p] if p in reads else (ROOT/p).read_bytes()
    env = dict(ROOT=ROOT,Path=Path,json=json,re=re,sha=sha,recovery=frozen,
               read=lambda p:virtual_bytes(p).decode(),virtual_bytes=virtual_bytes)
    try:
        exec(code,env)
    except AssertionError as e:
        assert not should_pass, (name,str(e))
        cases.append(dict(name=name,expected='reject',actual='reject',assertion=str(e)))
    else:
        assert should_pass, name
        assert set(env['changed']) == set(replacements)
        cases.append(dict(name=name,expected='accept',actual='accept',explicit_changes=len(env['changed'])))

run_case('exact_nineteen_namespace_changes',patched,copy.deepcopy(recovery),True)
run_case('no_namespace_changes',{},copy.deepcopy(recovery),False)
missing=dict(patched);missing.pop(family)
run_case('one_missing_family_repair',missing,copy.deepcopy(recovery),False)
extra=dict(patched);extra[family]+=b'\n-- unauthorized proof-source change\n'
run_case('extra_family_source_change',extra,copy.deepcopy(recovery),False)
extra=dict(patched);extra[renderer]+=b'\n# unauthorized renderer change\n'
run_case('extra_renderer_change',extra,copy.deepcopy(recovery),False)
extra=dict(patched);extra[unrelated]=original[unrelated]+b'\n-- altered certificate\n'
run_case('unrelated_leaf_change',extra,copy.deepcopy(recovery),False)
wrong=copy.deepcopy(recovery);wrong['source_sha256'][family]='0'*64
run_case('wrong_original_family_digest',patched,wrong,False)
wrong=copy.deepcopy(recovery);wrong['source_sha256'][renderer]='0'*64
run_case('wrong_original_renderer_digest',patched,wrong,False)

OUT.mkdir(exist_ok=False)
inputs={str(PROPOSAL):sha(PROPOSAL.read_bytes()),str(plan_path):sha(plan_path.read_bytes()),
        str(recovery_path):sha(recovery_path.read_bytes()),
        str(ROOT/'scripts/de_ground_offset_transport_verify.py'):sha((ROOT/'scripts/de_ground_offset_transport_verify.py').read_bytes())}
result=dict(utc=datetime.now(timezone.utc).isoformat(),terminal_exit_code=0,
            scope='Historical-freeze namespace exception only; no registered compilation or whole-offset gate claimed',
            review='adversarial self-review, not independent review',
            proposal_sha256=sha(PROPOSAL.read_bytes()),extracted_source_line_range=[verify.body[first].lineno,verify.body[last].end_lineno],
            ast_adapter='Only (ROOT / p).read_bytes() in historical hash loop uses an in-memory proposed source view',
            ast_adapter_occurrences=adapter.count,historical_inputs=len(original),controls=cases,
            registered_source_inputs_changed=False,paper_edited=False,goal_complete=False,input_sha256=inputs)
(OUT/'review.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'review_driver.py').write_bytes(Path(__file__).read_bytes())
(OUT/'verifier_proposal.py').write_bytes(PROPOSAL.read_bytes())
(OUT/'README.md').write_text('The proposed historical-freeze namespace exception accepts the exact 18 family repairs plus renderer repair and rejects seven altered or incomplete views. The extracted block is executed with one documented in-memory file-read adapter. Registered sources are unchanged. This is adversarial self-review of the exception, not a fresh registered build or the whole-offset semantic gate. See review.json for input hashes and exact controls.\n')
manifest={p.name:sha(p.read_bytes()) for p in OUT.iterdir() if p.is_file()}
(OUT/'file-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(terminal_exit_code=0,controls=len(cases),accepted=1,rejected=7,historical_inputs=len(original),output=str(OUT))))
