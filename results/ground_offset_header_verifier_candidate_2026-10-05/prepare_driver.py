from pathlib import Path
import ast,datetime,hashlib,json
repo=Path('/home/repos/six-birds-de-closure');old=Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.repaired.py');new=Path('/tmp/de_offset_transport_namespace_recovery/de_ground_offset_transport_verify.header_repaired.py');out=repo/'results/ground_offset_header_verifier_candidate_2026-10-05'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
text=old.read_text()
text=text.replace("COMBINED='lean/manifests/axiom_audit_ground_offset_transport_2026-10-04.txt'","COMBINED='lean/manifests/axiom_audit_ground_offset_transport_2026-10-04.txt'\nFULL_AUDIT='results/ground_offset_transport_2026-10-04/cumulative-registered-receipts/axioms.log'")
text=text.replace('\ndef verify():','\ndef hoist(raw):\n    lines=raw.splitlines(keepends=True)\n    return b\'\'.join(l for l in lines if l.startswith(b\'import \'))+b\'\'.join(l for l in lines if not l.startswith(b\'import \'))\n\ndef verify():',1)
before="    assert read('lean/manifests/check_axioms.lean')==old_manifest+'\\n'+imports+'\\n'+''.join('#print axioms '+n+'\\n' for n in new)\n"
after="    expected_before=(old_manifest+'\\n'+imports+'\\n'+''.join('#print axioms '+n+'\\n' for n in new)).encode()\n    assert (ROOT/'lean/manifests/check_axioms.lean').read_bytes()==hoist(expected_before)\n"
assert text.count(before)==1;text=text.replace(before,after)
anchor='    changed=[]\n';assert text.count(anchor)==1
addition="""    header_packet=ROOT/'results/audit_manifest_header_repair_candidate_2026-10-05'
    header_manifest=json.loads((header_packet/'file-manifest.json').read_text())
    assert all(sha((header_packet/p).read_bytes())==h for p,h in header_manifest.items())
    header_plan=json.loads((header_packet/'repair-plan.json').read_text())
    manifest_path='lean/manifests/check_axioms.lean'
    before=(header_packet/'current_manifest.before.lean').read_bytes()
    repaired=(header_packet/'current_manifest.repaired.lean').read_bytes()
    assert before==expected_before and repaired==hoist(before)
    assert sha(before)==header_plan['manifests']['current']['before_sha256']
    assert (ROOT/manifest_path).read_bytes()==repaired
    assert sha(repaired)==header_plan['manifests']['current']['repaired_sha256']
    assert re.findall(rb'^#print axioms (\\S+)',before,re.M)==re.findall(rb'^#print axioms (\\S+)',repaired,re.M)
    assert hoist(repaired)==repaired
    allowed[manifest_path]=sha(before)
    assert len(allowed)==20
    full_root=ROOT/PACKET/'cumulative-registered-receipts'
    full_terminal=json.loads((full_root/'axioms-terminal.json').read_text())
    full_sources=json.loads((full_root/'source-snapshot.json').read_text())
    full_objects=json.loads((full_root/'objects-snapshot.json').read_text())
    expected_sources={str(p):sha(p.read_bytes()) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
    for name in ['lean-toolchain','lake-manifest.json']:p=ROOT/'lean'/name;expected_sources[str(p)]=sha(p.read_bytes())
    assert full_sources==expected_sources
    direct_imports=re.findall(r'^import (\\S+)',repaired.decode(),re.M)
    assert len(direct_imports)==len(set(direct_imports))==1965
    expected_objects={m:sha((ROOT/'lean/.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean')).read_bytes()) for m in direct_imports}
    assert full_objects==expected_objects
    assert full_terminal['terminal_exit_code']==0
    assert full_terminal['command']==['lake','env','lean','manifests/check_axioms.lean']
    assert full_terminal['cwd']==str(ROOT/'lean')
    assert full_terminal['environment_overrides']=={'LEAN_NUM_THREADS':'4'}
    assert full_terminal['manifest_sha256']==sha(repaired)
    assert full_terminal['source_snapshot_sha256']==sha((full_root/'source-snapshot.json').read_bytes())
    assert full_terminal['objects_snapshot_sha256']==sha((full_root/'objects-snapshot.json').read_bytes())
    assert full_terminal['log_sha256']==sha((ROOT/FULL_AUDIT).read_bytes())
    fullraw=read(FULL_AUDIT);assert not re.search(r'error:|warning:',fullraw)
    closures(fullraw,old+new)
"""
text=text.replace(anchor,addition+anchor)
text=text.replace('full_cumulative_command_rerun=False,preserved_raw_prefix=OLD_AUDIT,','full_cumulative_command_rerun=True,fresh_full_receipt=FULL_AUDIT,preserved_raw_prefix=OLD_AUDIT,',1)
anchor='      namespace_recovery=dict(verified=True,';assert text.count(anchor)==1
text=text.replace(anchor,"      manifest_header_repair=dict(verified=True,packet=str(header_packet.relative_to(ROOT)),import_occurrences_preserved=True,nonimport_bytes_preserved=True,ordered_queries_preserved=11776,raw_byte_prefix_preserved=False),\n"+anchor)
anchor="    files.update(str(p.relative_to(ROOT)) for p in repair_packet.rglob('*') if p.is_file())\n";assert text.count(anchor)==1
text=text.replace(anchor,anchor+"    files.update(str(p.relative_to(ROOT)) for p in header_packet.rglob('*') if p.is_file())\n    files.update(str(p.relative_to(ROOT)) for p in full_root.rglob('*') if p.is_file())\n")
new.write_text(text);ast.parse(text)
def fns(raw):return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef)}
a=fns(old.read_text());b=fns(text);assert set(b)==set(a)|{'hoist'};assert all(a[n]==b[n] for n in a if n!='verify')
# Exact proposal review: existing namespace/archive/leaf loop is byte identical;
# the added exception is exactly one manifest path with exact before/after bytes.
start=old.read_text().index('    repair_packet =');stop=old.read_text().index('    changed=[]')
assert old.read_text()[start:stop] in text
loop="""    changed=[]
    for p,h in recovery['source_sha256'].items():
        if sha((ROOT/p).read_bytes())==h:continue
        assert p in allowed and h==allowed[p],p
        changed.append(p)
    assert set(changed)==set(allowed)
"""
assert loop in old.read_text() and loop in text
out.mkdir(exist_ok=False)
(out/'verifier_candidate.py').write_bytes(new.read_bytes());(out/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(out/'review.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),prior_verifier_sha256=sha(old.read_bytes()),proposed_verifier_sha256=sha(new.read_bytes()),inherited_namespace_archive_checks_preserved=True,inherited_leaf_freeze_loop_preserved=True,permitted_frozen_input_changes=20,additional_change='exact import-header hoist of default11776 manifest',fresh_registered_11776_audit_required=True,actual_registered_commands_started=0,full_success_path_tested=False,goal_complete=False),indent=2)+'\n')
(out/'README.md').write_text('Prepared whole-offset verifier extension: exact existing19 namespace changes plus exact default-manifest import hoist, all20 bound to original historical source hashes. Every other frozen input remains identical. Original4867 historical and fresh6909 dedicated raw audits remain checked and preserved. An additional actual registered11776 cumulative command is mandatory, with full current source and direct-import object snapshots, exact command/environment/source/log receipts and standard-only closures. No registered success path was run.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in out.iterdir() if p.is_file()},indent=2)+'\n');print('Prepared exact20-change header-aware whole-offset verifier; registered11776 gate pending')
