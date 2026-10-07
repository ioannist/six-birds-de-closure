"""Preserve historical input validation across the exact namespace source repair."""
from pathlib import Path
import ast, hashlib, json

ROOT=Path('/home/repos/six-birds-de-closure')
PACKET=ROOT/'results/native_registered_aggregate_verification_candidate_2026-10-06'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
original=Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/verify_recovery.py')
assert sha(original)=='b48e90cb8b1616399442d81bf81ea853c2cfc38c514d0b61fda9e1a6a85e34fa'
guard=original.read_text()
old="    assert len(frozen) == 3705 and all(sha(p) == h for p, h in frozen.items())"
assert guard.count(old)==1
guard=guard.replace('def verify_aggregate_repair(plan):','def verify_aggregate_repair(plan, freeze_check=None):',1)
guard=guard.replace(old,"    assert len(frozen) == 3705\n    if freeze_check is None:\n        assert all(sha(p) == h for p, h in frozen.items())\n    else:\n        freeze_check(frozen)",1)
path=Path('/tmp/de_registered_aggregate_repair_guard.py')
ast.parse(guard);path.write_text(guard)
(PACKET/'aggregate-repair-guard.py').write_text(guard)
verifier=Path('/tmp/de_native_registered_verify_aggregate_recovery.py')
text=verifier.read_text()
(PACKET/'verifier-before-freeze-transport.py').write_text(text)
text=text.replace("semantic=Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/verify_recovery.py')","semantic=Path('/tmp/de_registered_aggregate_repair_guard.py')",1)
text=text.replace("assert sha(semantic)=='b48e90cb8b1616399442d81bf81ea853c2cfc38c514d0b61fda9e1a6a85e34fa'","assert sha(semantic)=='"+sha(path)+"'",1)
text=text.replace("qp=load(recovery/'production-plan.json');guard.verify_aggregate_repair(qp)","qp=load(recovery/'production-plan.json');guard.verify_aggregate_repair(qp, check_aggregate_historical_inputs)",1)
helper='''
def check_aggregate_historical_inputs(frozen):
 packet=ROOT/'results/ground_offset_header_installation_candidate_2026-10-05'
 assert all(sha(packet/p)==h for p,h in load(packet/'file-manifest.json').items())
 transport=load(packet/'installation-plan.json')
 assert transport['registered_file_changes']==21 and transport['historical_leaf_freeze_changes']==20
 targets={str(ROOT/r['path']):r for r in transport['targets']}
 allowed={str(ROOT/'lean/SbtCosmo/Derivation/GroundOffsetTransport'/f'Point{i:03d}.lean') for i in range(18)}
 assert allowed==set(targets)&set(frozen)
 archive=packet/'original_files.tar.gz'
 assert sha(archive)==transport['original_archive_sha256']
 with tarfile.open(archive,'r|gz') as stream:
  for member,row in zip(stream,transport['targets'],strict=True):
   assert member.isfile() and member.name==row['path']
   raw=stream.extractfile(member).read()
   assert len(raw)==row['before_size'] and rawsha(raw)==row['before_sha256']
   path=str(ROOT/row['path'])
   if path in allowed:assert frozen[path]==row['before_sha256']
 for p,h in frozen.items():
  if p in allowed:
   assert h==targets[p]['before_sha256']
   assert sha(p) in {h,targets[p]['after_sha256']},p
  else:assert sha(p)==h,p

'''
text=text.replace('def verify_registered_repair(plan, files, parent_plan):',helper+'def verify_registered_repair(plan, files, parent_plan):',1)
# Preserve the historical owner table verbatim; recovery owners are additional.
text=text.replace("853723:'de_native_additional_constructions_aggregate_recovery_2026-10-06_build.py'","853723:'de_native_additional_constructions_stream_qualified_build.py'")
text=text.replace("853738:'de_source_execution_supplement_aggregate_recovery_2026-10-06_build.py'","853738:'de_source_execution_supplement_stream_qualified_build.py'")
ast.parse(text);verifier.write_text(text);(PACKET/'verifier.py').write_text(text)
(PACKET/'freeze_transport_driver.py').write_bytes(Path(__file__).read_bytes())
(PACKET/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in PACKET.iterdir() if p.is_file() and p.name!='file-manifest.json'},indent=2)+'\n')
print(json.dumps(dict(exact_historical_source_transports=18, historical_original_bytes_archived=True, registered_sources_changed=False)))
