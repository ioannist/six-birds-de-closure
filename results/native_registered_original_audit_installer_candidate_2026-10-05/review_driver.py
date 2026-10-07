from pathlib import Path
import json,hashlib,importlib.util,copy,subprocess,datetime,shutil
REPO=Path('/home/repos/six-birds-de-closure')
SCRIPT=Path('/tmp/de_native_registered_install_original_audit_candidate.py')
OUT=REPO/'results/native_registered_original_audit_installer_candidate_2026-10-05'
FIXTURE=Path('/tmp/de_native_registered_original_audit_installer_fixture')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not OUT.exists() and not FIXTURE.exists();FIXTURE.mkdir()
spec=importlib.util.spec_from_file_location('native_installer_fixture',SCRIPT);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
v.ROOT=FIXTURE
old=FIXTURE/'lean/existing.lean';old.parent.mkdir();old.write_text('def preserved : Nat := 3\n')
untouched=FIXTURE/'unrelated.txt';untouched.write_text('Unrelated fixture bytes remain unchanged.\n')
base=dict(targets=[dict(path='lean/existing.lean',existing_target_sha256=sha(old)),dict(path='lean/new/added.lean',existing_target_sha256=None)],input_sha256={})
before=old.read_bytes();unrelated_hash=sha(untouched);v.check_preimages(base)
controls=[]
def reject(label,plan):
 try:v.check_preimages(plan)
 except AssertionError:controls.append(label)
 else:raise AssertionError('Control accepted: '+label)
 assert old.read_bytes()==before and sha(untouched)==unrelated_hash
wrong=copy.deepcopy(base);wrong['targets'][0]['existing_target_sha256']='0'*64;reject('changed_existing_preimage',wrong)
unexpected=FIXTURE/'lean/unexpected.lean';unexpected.write_text('def unexpected : Nat := 7\n')
wrong=copy.deepcopy(base);wrong['targets'][1]['path']='lean/unexpected.lean';reject('unexpected_existing_target',wrong)
link=FIXTURE/'lean/linked.lean';link.symlink_to(old)
wrong=copy.deepcopy(base);wrong['targets'][0]['path']='lean/linked.lean';reject('symlink_target',wrong)
wrong=copy.deepcopy(base);wrong['targets'][1]['path']='../escaped.lean';reject('outside_root_target',wrong)
v.check_preimages(base)
v.atomically_install(old,b'def preserved : Nat := 4\n')
added=FIXTURE/'lean/new/added.lean';v.atomically_install(added,b'def added : Nat := 5\n')
assert old.read_bytes()==b'def preserved : Nat := 4\n' and added.read_bytes()==b'def added : Nat := 5\n'
assert sha(untouched)==unrelated_hash and not list(FIXTURE.rglob('*.native-install-*'))
assert not REPO.joinpath('results/native_registered_original_audit_installation_receipts_2026-10-05').exists()
preflights=[]
for mode,expected in [('candidate',0),('apply',2)]:
 cmd=['/usr/bin/python3',str(SCRIPT),'--mode',mode]
 r=subprocess.run(cmd,cwd=REPO,capture_output=True,text=True)
 assert r.returncode==expected,(mode,r.returncode,r.stdout,r.stderr)
 data=json.loads(r.stdout)
 assert not data['registered_sources_changed'] and data['proof_objects_installed']==0
 if mode=='apply':assert 'Source freeze owner remains active' in data['reason']
 assert not REPO.joinpath('results/native_registered_original_audit_installation_receipts_2026-10-05').exists()
 preflights.append(dict(command=cmd,cwd=str(REPO),actual_exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,installer_sha256=sha(SCRIPT)))
OUT.mkdir()
shutil.copy2(SCRIPT,OUT/'installer_candidate.py');shutil.copy2(Path(__file__),OUT/'review_driver.py')
fixture=OUT/'isolated-helper-fixture';fixture.mkdir()
for p in [old,added,untouched,unexpected]:
 dest=fixture/p.relative_to(FIXTURE);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
(fixture/'original-existing.lean').write_bytes(before)
checks=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),candidate_files=1786,rejected_preimage_controls=controls,atomic_helper_actual_replacement=True,atomic_helper_actual_new_nested_file=True,atomic_helper_unrelated_bytes_preserved=True,fixture_root=str(FIXTURE),symlink_control_target=str(link),symlink_points_to=str(old),preflights=preflights,registered_sources_changed=False,registered_receipts_created=False,proof_objects_installed=0,full_apply_success_path_tested=False,review='Adversarial self-review; no independent review',goal_complete=False)
(OUT/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'README.md').write_text('Prepared source-only native installer, gated by exact reviewed1786-file candidate, released source freezes, all private proof gates and verified fresh whole-offset11776/10003 phase. It requires every original target preimage and input binding, archives/readback-checks existing originals, records source/object snapshots and installation intent/journal, and uses atomic per-file replacement. It requires all prior non-target equations and all proof objects to remain unchanged. An isolated helper fixture exercises actual replacement/new-file operations and rejects changed preimages, unexpected existing files, symlink targets and root escape. These are file-operation controls, not a Lean build or the full apply path. Actual candidate preflight exits0; actual apply preflight exits2 for the live source-freeze owner before creating receipts or changing registered files. The complete source-installation success path and subsequent registered build/audits remain pending.\n')
(OUT/'file-manifest.json').write_text(json.dumps({str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file()},indent=2)+'\n')
assert all(sha(OUT/p)==h for p,h in json.loads((OUT/'file-manifest.json').read_text()).items())
print(json.dumps(checks),flush=True)
