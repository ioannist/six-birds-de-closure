from pathlib import Path
import datetime,hashlib,io,json,tarfile
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/ground_offset_header_installation_candidate_2026-10-05';root=Path('/tmp/de_offset_transport_namespace_recovery');sha=lambda raw:hashlib.sha256(raw).hexdigest()
namespace=json.loads((root/'registered-integration-plan.json').read_text());header=repo/'results/audit_manifest_header_repair_candidate_2026-10-05';binary=repo/'results/ground_offset_binary_fingerprint_candidate_2026-10-05'
for packet in [header,binary,repo/'results/ground_offset_namespace_recovery_checked_2026-10-05']:
 assert all(sha((packet/p).read_bytes())==h for p,h in json.loads((packet/'file-manifest.json').read_text()).items())
rows=[];before={};after={}
for target,r in namespace['namespace_repairs'].items():
 raw=(repo/target).read_bytes()
 new=Path(r['repaired']).read_bytes() if 'repaired' in r else raw.decode().replace(r['replacement']['old'],r['replacement']['new']).encode()
 assert sha(raw)==r['original_sha256'] and sha(new)==r['repaired_sha256']
 assert raw.decode().count(r['replacement']['old'])==1 and new.decode()==raw.decode().replace(r['replacement']['old'],r['replacement']['new'])
 before[target]=raw;after[target]=new
target='lean/manifests/check_axioms.lean';before[target]=(repo/target).read_bytes();after[target]=(header/'current_manifest.repaired.lean').read_bytes();assert before[target]==(header/'current_manifest.before.lean').read_bytes()
target='scripts/de_ground_offset_transport_verify.py';before[target]=(repo/target).read_bytes();after[target]=(binary/'verifier_candidate.py').read_bytes();assert after[target]==(root/'de_ground_offset_transport_verify.header_binary_repaired.py').read_bytes()
assert len(after)==21
leaf=json.loads((repo/'results/ground_offset_transport_2026-10-04/leaves_recovery.json').read_text())['source_sha256'];assert target not in leaf
assert len(set(after)&set(leaf))==20 and all(sha(before[p])==leaf[p] for p in set(after)&set(leaf))
out.mkdir(exist_ok=False)
for name,payload in [('original_files.tar.gz',before),('repaired_files.tar.gz',after)]:
 with tarfile.open(out/name,'w:gz') as tar:
  for p,raw in sorted(payload.items()):m=tarfile.TarInfo(p);m.size=len(raw);tar.addfile(m,io.BytesIO(raw))
 with tarfile.open(out/name,'r|gz') as tar:
  for m,(p,raw) in zip(tar,sorted(payload.items()),strict=True):assert m.isfile() and m.name==p and tar.extractfile(m).read()==raw
rows=[dict(path=p,before_sha256=sha(before[p]),after_sha256=sha(after[p]),before_size=len(before[p]),after_size=len(after[p])) for p in sorted(after)]
inputs={str(p/'file-manifest.json'):sha((p/'file-manifest.json').read_bytes()) for p in [header,binary,repo/'results/ground_offset_namespace_recovery_checked_2026-10-05']};inputs[str(root/'registered-integration-plan.json')]=sha((root/'registered-integration-plan.json').read_bytes())
plan=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),targets=rows,registered_file_changes=21,historical_leaf_freeze_changes=20,new_proof_object_installations=0,original_archive_sha256=sha((out/'original_files.tar.gz').read_bytes()),repaired_archive_sha256=sha((out/'repaired_files.tar.gz').read_bytes()),input_sha256=inputs,source_freeze_release_required=True,full_native_private_gates_required=True,completed_private_11776_cumulative_audit_required=True,registered_build_and_semantic_verification_still_required=True,goal_complete=False)
(out/'installation-plan.json').write_text(json.dumps(plan,indent=2)+'\n');(out/'prepare_driver.py').write_bytes(Path(__file__).read_bytes());(out/'README.md').write_text('Exact guarded source-installation candidate:18 namespace repairs, one renderer repair, one11776-query header repair and the header/binary-aware whole-offset verifier. Both original and repaired21-file archives were read back and verified. Exactly20 targets belong to the historical leaf freeze; its verifier script was not a leaf-frozen input. No proof object is installed. All current source-freeze owners, final private native proof gates and the isolated11776 audit must finish before mutation. Actual registered family/aggregate builds, default10003-job build, fresh11776 audit and whole-offset semantics remain mandatory afterward.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in out.iterdir() if p.is_file()},indent=2)+'\n');print(json.dumps(dict(prepared_targets=len(rows),historical_leaf_input_changes=20,registered_sources_changed=False)))
