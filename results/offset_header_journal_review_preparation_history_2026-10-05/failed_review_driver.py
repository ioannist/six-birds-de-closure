from pathlib import Path
import json,hashlib,importlib.util,subprocess,datetime,ast,shutil
REPO=Path('/home/repos/six-birds-de-closure')
OLD=Path('/tmp/de_offset_header_install_candidate.py')
SCRIPT=Path('/tmp/de_offset_header_install_journal_candidate.py')
OUT=REPO/'results/ground_offset_header_journal_installer_candidate_2026-10-05'
FIXTURE=Path('/tmp/de_offset_header_journal_fault_controls')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not OUT.exists() and not FIXTURE.exists();FIXTURE.mkdir()
spec=importlib.util.spec_from_file_location('corrected_journal_installer_fixture',SCRIPT);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
funcs=lambda s:{n.name:ast.dump(n,include_attributes=False) for n in ast.parse(s).body if isinstance(n,ast.FunctionDef)}
a=funcs(OLD.read_text());b=funcs(SCRIPT.read_text());unchanged=[n for n in a if n!='main'];assert all(a[n]==b[n] for n in unchanged)
native=Path('/tmp/de_native_registered_install_original_audit_journal_candidate.py');nf=funcs(native.read_text());assert all(b[n]==nf[n] for n in ['current_hash','atomically_install','install_target','observed_targets','record_installation_failure'])
results=[]
for label,old_exists,fail_call in [('replacement_directory_flush_failure',True,2),('new_file_directory_flush_failure',False,2),('before_replacement_file_flush_failure',True,1),('normal_replacement',True,None),('normal_new_file',False,None)]:
    root=FIXTURE/label;root.mkdir();v.ROOT=root
    receipt=root/'receipts';receipt.mkdir()
    p=root/'lean/target.lean';p.parent.mkdir()
    before=b'def sourceValue : Nat := 1\n';after=b'def sourceValue : Nat := 2\n'
    if old_exists:p.write_bytes(before)
    row=dict(path='lean/target.lean',existing_target_sha256=sha(p) if old_exists else None,sha256=hashlib.sha256(after).hexdigest())
    plan=dict(targets=[row]);installed=[];attempted=[];calls=[]
    fsync=v.os.fsync
    def inject(fd):
        calls.append(fd)
        if fail_call is not None and len(calls)==fail_call:raise OSError('Injected flush failure '+label)
        return fsync(fd)
    v.os.fsync=inject
    try:
        try:v.install_target(row,after,receipt,installed,attempted)
        except OSError as e:
            assert fail_call is not None
            v.record_installation_failure(receipt,plan,installed,attempted,e)
        else:assert fail_call is None
    finally:v.os.fsync=fsync
    journal=json.loads((receipt/'journal.json').read_text())
    assert attempted==journal['attempted']==['lean/target.lean']
    assert not list(root.rglob('*.native-install-*'))
    if fail_call is not None:
        terminal=json.loads((receipt/'terminal.json').read_text())
        assert terminal['terminal_exit_code']==1 and journal['phase']=='failed'
        assert terminal['attempted']==attempted and installed==terminal['installed']==[]
        assert terminal['pending_targets']==journal['pending_targets']==['lean/target.lean']
        obs=terminal['observed_targets']['lean/target.lean']
        if fail_call==2:
            assert p.read_bytes()==after and obs['matches_proposed'] and not obs['matches_original']
        else:
            assert p.read_bytes()==before and obs['matches_original'] and not obs['matches_proposed']
        assert journal['observed_targets']==terminal['observed_targets']
    else:
        assert p.read_bytes()==after and installed==['lean/target.lean']
        assert journal['installed']==installed and journal['pending_target'] is None and journal['phase']=='write_completed'
        assert not (receipt/'terminal.json').exists()
    results.append(dict(label=label,original_target_existed=old_exists,injected_fsync_call=fail_call,fsync_calls=len(calls),attempted=attempted,completed=installed,journal_correct=True,registered_installation_claimed=False))
preflights=[]
for mode,expected in [('candidate',0),('apply',2)]:
    cmd=['/usr/bin/python3',str(SCRIPT),'--mode',mode]
    r=subprocess.run(cmd,cwd=REPO,capture_output=True,text=True)
    assert r.returncode==expected,(mode,r.returncode,r.stdout,r.stderr)
    d=json.loads(r.stdout);assert not d['registered_sources_changed'] and d['proof_objects_installed']==0
    if mode=='apply':assert 'Source freeze owner remains active' in d['reason']
    preflights.append(dict(command=cmd,cwd=str(REPO),actual_exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,installer_sha256=sha(SCRIPT)))
assert not (REPO/'results/ground_offset_header_installation_receipts_2026-10-05').exists()
OUT.mkdir();shutil.copy2(SCRIPT,OUT/'installer_candidate.py');shutil.copy2(Path(__file__),OUT/'review_driver.py');shutil.copy2(Path('/tmp/de_native_installer_journal_functions.py'),OUT/'journal_functions.py')
fixture_out=OUT/'isolated-fault-controls';shutil.copytree(FIXTURE,fixture_out)
checks=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),unchanged_inherited_functions=unchanged,actual_file_operation_cases=results,preflights=preflights,registered_sources_changed=False,proof_objects_installed=0,registered_receipts_created=False,full_apply_success_path_tested=False,review='Adversarial self-review; no independent review',goal_complete=False)
(OUT/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'README.md').write_text('Journal-corrected preceding21-file whole-offset source installer. The source-candidate/private11776/release/frozen-input gates are unchanged. The native proof dependency now uses the checked original-audit-extended verifier. Shared journal/atomic-writer functions have identical ASTs to the checked corrected native installer. Each attempted target is recorded before writing; failures record pending writes and observed hashes for every target. Actual isolated fault controls cover post-replacement directory-flush failures for existing/new targets and a pre-replacement file-flush failure, plus normal existing/new writes. Both attempted writes and actual resulting bytes are correctly distinguished. These are file-operation controls, not a Lean build or full registered apply path. Actual candidate preflight exits0; actual apply preflight exits2 for live source-freeze owner before registered mutation or receipts. The prior installer remains preserved. Shared file-operation boundary controls are repeated for this actual stage entry point; all mathematical prerequisites are retained. Use this corrected21-file installer before the corrected1786-file native installer; actual full application and registered build/audits remain pending.\n')
(OUT/'file-manifest.json').write_text(json.dumps({str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file()},indent=2)+'\n')
assert all(sha(OUT/p)==h for p,h in json.loads((OUT/'file-manifest.json').read_text()).items())
print(json.dumps(checks),flush=True)
