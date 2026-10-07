from pathlib import Path
import datetime,hashlib,json,re,subprocess,tarfile
repo=Path('/home/repos/six-birds-de-closure');packet=repo/'results/audit_manifest_header_repair_candidate_2026-10-05';root=Path('/tmp/de_audit_manifest_header_repair');assert not packet.exists() and not root.exists();packet.mkdir();root.mkdir()
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def hoist(raw):
 lines=raw.splitlines(keepends=True);imports=[line for line in lines if line.startswith(b'import ')];body=[line for line in lines if not line.startswith(b'import ')]
 assert imports and all(line.endswith(b'\n') for line in imports)
 return b''.join(imports)+b''.join(body)
def names(raw):return re.findall(rb'^#print axioms (\S+)',raw,re.M)
committed=subprocess.check_output(['git','show','HEAD:lean/manifests/check_axioms.lean'],cwd=repo);current=(repo/'lean/manifests/check_axioms.lean').read_bytes();native_candidate=repo/'results/native_registered_installation_with_failure_candidate_2026-10-05';native_plan=json.loads((native_candidate/'installation-plan.json').read_text())
with tarfile.open(native_candidate/'proposed_registered_files.tar.gz','r:gz') as tar:native=tar.extractfile('lean/manifests/check_axioms.lean').read()
assert len(names(committed))==4867 and len(names(current))==11776 and len(names(native))==32565
assert names(current)[:4867]==names(committed) and names(native)[:11776]==names(current)
rows={}
for tag,raw in [('committed',committed),('current',current),('native',native)]:
 repaired=hoist(raw);assert names(repaired)==names(raw) and hoist(repaired)==repaired
 imports=lambda b:[l for l in b.splitlines(keepends=True) if l.startswith(b'import ')]
 body=lambda b:b''.join(l for l in b.splitlines(keepends=True) if not l.startswith(b'import '))
 assert imports(raw)==imports(repaired) and body(raw)==body(repaired)
 first=next(i for i,l in enumerate(repaired.splitlines()) if l.startswith(b'#print axioms '));assert not any(l.startswith(b'import ') for l in repaired.splitlines()[first:])
 (packet/(tag+'_manifest.before.lean')).write_bytes(raw);(packet/(tag+'_manifest.repaired.lean')).write_bytes(repaired)
 rows[tag]=dict(before_sha256=sha(raw),repaired_sha256=sha(repaired),queries=len(names(raw)),imports=len(imports(raw)),import_occurrences_preserved=True,nonimport_bytes_preserved=True,query_order_preserved=True)
helper='from pathlib import Path\n\ndef hoist(raw: bytes) -> bytes:\n    lines=raw.splitlines(keepends=True)\n    imports=[line for line in lines if line.startswith(b"import ")]\n    assert all(line.endswith(b"\\n") for line in imports)\n    return b"".join(imports)+b"".join(line for line in lines if not line.startswith(b"import "))\n'
(packet/'hoist.py').write_text(helper)
controls=[]
for tag,raw,expected in [('late-import',b'import Lean\n#check True\nimport Init\n#check False\n',1),('header-imports',hoist(b'import Lean\n#check True\nimport Init\n#check False\n'),0)]:
 source=root/(tag+'.lean');source.write_bytes(raw);cmd=['lake','env','lean',str(source)];p=subprocess.run(cmd,cwd=repo/'lean',capture_output=True,text=True);log=root/(tag+'.log');log.write_text(p.stdout+p.stderr);assert p.returncode==expected,(tag,p.stdout,p.stderr)
 if expected:assert "invalid 'import' command" in log.read_text()
 else:assert 'True : Prop' in log.read_text() and 'False : Prop' in log.read_text() and 'error:' not in log.read_text()
 d=dict(command=cmd,cwd=str(repo/'lean'),terminal_exit_code=p.returncode,source_sha256=sha(raw),log_sha256=sha(log.read_bytes()));(root/(tag+'-terminal.json')).write_text(json.dumps(d,indent=2)+'\n');controls.append(d)
 for src in [source,log,root/(tag+'-terminal.json')]: (packet/src.name).write_bytes(src.read_bytes())
basecache=repo/'lean/.lake/build/lib/lean';recovery=Path('/tmp/de_offset_transport_namespace_recovery');overlay=root/'overlay';overlay.mkdir()
for p in basecache.rglob('*.olean'):
 q=overlay/p.relative_to(basecache);q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve(strict=True))
for p in (recovery/'objects').rglob('*.olean'):
 q=overlay/p.relative_to(recovery/'objects');q.parent.mkdir(parents=True,exist_ok=True)
 if q.is_symlink():q.unlink()
 q.symlink_to(p.resolve(strict=True))
source=root/'current_manifest.repaired.lean';source.write_bytes(hoist(current));bindings={}
for mod in dict.fromkeys(re.findall(rb'^import (\S+)',current,re.M)):
 module=mod.decode();rel=Path(*module.split('.'));obj=overlay/rel.with_suffix('.olean');assert obj.exists(),module
 repaired_source=recovery/'lean'/rel.with_suffix('.lean');src=repaired_source if repaired_source.exists() else repo/'lean'/rel.with_suffix('.lean')
 if not src.exists():src=repo/'lean/.lake/packages/mathlib'/rel.with_suffix('.lean')
 assert src.exists(),module;bindings[module]=dict(source=str(src),source_sha256=sha(src.read_bytes()),object=str(obj.resolve()),object_sha256=sha(obj.read_bytes()),uses_checked_namespace_repair=repaired_source.exists())
(root/'module-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n');(packet/'module-bindings.json').write_bytes((root/'module-bindings.json').read_bytes())
plan=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifests=rows,registered_target='lean/manifests/check_axioms.lean',current_registered_source_sha256=sha(current),historical_committed_manifest_layout_also_invalid=True,committed_query_prefix_preserved=4867,current_query_prefix_preserved=11776,prospective_native_query_count=32565,raw_byte_prefix_preservation_replaced_by_import_vector_and_nonimport_body_preservation=True,control_commands=controls,native_installation_plan_sha256=sha((native_candidate/'installation-plan.json').read_bytes()),fresh_private_11776_audit_pending=True,registered_sources_changed=False,live_frozen_sources_changed=False,proofs_changed=False,paper_edited=False,goal_complete=False)
(packet/'repair-plan.json').write_text(json.dumps(plan,indent=2)+'\n');(packet/'prepare_driver.py').write_bytes(Path(__file__).read_bytes());(packet/'README.md').write_text('Prepared import-header layout repair for the committed4867-query, current11776-query and prospective32565-query cumulative manifests. Actual pinned Lean rejects a late-import control and accepts the mechanically hoisted control. Every import occurrence and every nonimport byte is preserved, with identical ordered query names and historical query prefixes. Existing source/install/verifier candidates remain unchanged and are superseded for manifest layout. Registered/frozen files are unchanged. A fresh isolated11776-query audit using the checked namespace-repair objects is being prepared; it will not close registered integration. Native installed bytes, old-byte-prefix verifier assumptions and the whole-offset historical-freeze exception still require explicit updates and review.\n')
(packet/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in packet.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(dict(rows=rows,private_direct_import_bindings=len(bindings),negative_control_exit=1,positive_control_exit=0,registered_sources_changed=False,output=str(packet))))
