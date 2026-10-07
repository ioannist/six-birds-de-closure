from pathlib import Path
import ast,datetime,hashlib,json,subprocess
repo=Path('/home/repos/six-birds-de-closure');old=Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_repaired.py');new=Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_binary_repaired.py');out=repo/'results/ground_offset_binary_fingerprint_candidate_2026-10-05'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
text=old.read_text();helper="""
def fingerprint_content(p):
    raw=(ROOT/p).read_bytes()
    # Git's automatic text classification checks the first8000 bytes for NUL.
    # Binary proof archives must retain their exact bytes, including CRLF pairs.
    return raw if b'\\0' in raw[:8000] else canonical(p)
"""
assert '\ndef fingerprint_content' not in text;text=text.replace('\ndef verify():',helper+'\ndef verify():',1)
before='git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)}'
after='git_blob_sha256={p:sha(fingerprint_content(p)) for p in sorted(files)}'
assert text.count(before)==1;text=text.replace(before,after)
new.write_text(text);tree=ast.parse(text);oldtree=ast.parse(old.read_text())
oldverify=next(n for n in oldtree.body if isinstance(n,ast.FunctionDef) and n.name=='verify');newverify=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='verify')
class Normalize(ast.NodeTransformer):
 count=0
 def visit_Call(self,node):
  if isinstance(node.func,ast.Name) and node.func.id=='fingerprint_content':self.count+=1;node.func.id='canonical'
  return self.generic_visit(node)
adapter=Normalize();normalized=adapter.visit(newverify);assert adapter.count==1 and ast.dump(normalized,include_attributes=False)==ast.dump(oldverify,include_attributes=False)
# Execute the actual added function against real repository artifacts, with the
# existing canonical implementation, without loading the pending verifier.
canonical_module=ast.parse((repo/'scripts/de_ground_offset_prefix_verify.py').read_text());canonical_def=next(n for n in canonical_module.body if isinstance(n,ast.FunctionDef) and n.name=='canonical');helper_def=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='fingerprint_content')
env=dict(ROOT=repo,subprocess=subprocess);exec(compile(ast.Module(body=[canonical_def,helper_def],type_ignores=[]),str(new),'exec'),env)
archive='results/ground_offset_namespace_recovery_checked_2026-10-05/checked_artifacts.tar.gz';raw=(repo/archive).read_bytes();assert b'\r\n' in raw and b'\0' in raw[:8000]
try:env['canonical'](archive)
except AssertionError:old_archive_rejected=True
else:raise AssertionError('Expected inherited binary-normalization failure')
assert env['fingerprint_content'](archive)==raw
prior=json.loads((repo/'results/ground_offset_sixty_2026-10-04/verification.json').read_text())
assert all(env['fingerprint_content'](p)==env['canonical'](p) for p in prior['source_sha256'])
out.mkdir(exist_ok=False);(out/'verifier_candidate.py').write_bytes(new.read_bytes());(out/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(out/'review.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),old_proposal_sha256=sha(old.read_bytes()),new_proposal_sha256=sha(new.read_bytes()),old_archive_handling_actual_failure=True,new_archive_exact_bytes_verified=True,preserved_prior_file_comparisons=len(prior['source_sha256']),inherited_verify_AST_identical_except_one_final_fingerprint_call=True,registered_commands_started=0,full_success_path_tested=False,goal_complete=False),indent=2)+'\n')
(out/'README.md').write_text('Prepared final fingerprint correction for the header-aware whole-offset verifier. The actual existing canonical helper rejects the compressed checked proof archive when its binary bytes contain CRLF and NUL. The corrected helper hashes binary bytes unchanged and uses the existing canonical text comparison otherwise. Actual archive bytes pass and all2858 prior file comparisons are identical. AST comparison shows no change to any verification gate; only the final fingerprint call changes. The latest proposal is header_binary_repaired.py. No registered success path ran.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in out.iterdir() if p.is_file()},indent=2)+'\n');print(json.dumps(dict(archive_exact_bytes_verified=True,prior_comparisons_preserved=len(prior['source_sha256']),registered_commands_started=0)))
