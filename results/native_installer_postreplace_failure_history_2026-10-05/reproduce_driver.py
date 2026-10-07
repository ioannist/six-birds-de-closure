from pathlib import Path
import importlib.util,json,hashlib,datetime
REPO=Path('/home/repos/six-birds-de-closure')
SCRIPT=Path('/tmp/de_native_registered_install_original_audit_candidate.py')
OUT=REPO/'results/native_installer_postreplace_failure_history_2026-10-05'
FIXTURE=Path('/tmp/de_native_installer_postreplace_original_failure')
assert not OUT.exists() and not FIXTURE.exists();FIXTURE.mkdir()
spec=importlib.util.spec_from_file_location('original_installer_failure_fixture',SCRIPT);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
v.ROOT=FIXTURE
p=FIXTURE/'lean/changed.lean';p.parent.mkdir();before=b'def sourceValue : Nat := 1\n';after=b'def sourceValue : Nat := 2\n';p.write_bytes(before)
fsync=v.os.fsync;calls=[]
def fail_directory_flush(fd):
 calls.append(fd)
 if len(calls)==2:raise OSError('Injected directory flush failure after successful replacement')
 return fsync(fd)
v.os.fsync=fail_directory_flush
installed=[]
try:
 try:
  v.atomically_install(p,after)
  assert p.read_bytes()==after
  installed.append('lean/changed.lean')
 except OSError as e:failure=str(e)
 else:raise AssertionError('Injected post-replacement failure did not occur')
finally:v.os.fsync=fsync
assert p.read_bytes()==after and installed==[] and len(calls)==2
assert not list(FIXTURE.rglob('*.native-install-*'))
OUT.mkdir();(OUT/'executed_original_installer.py').write_bytes(SCRIPT.read_bytes());(OUT/'reproduce_driver.py').write_bytes(Path(__file__).read_bytes());(OUT/'before.lean').write_bytes(before);(OUT/'observed_after_failure.lean').write_bytes(p.read_bytes())
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),fixture=str(FIXTURE),injected_failure=failure,fsync_calls=len(calls),target_replaced_before_failure=True,original_completed_list=installed,original_completed_list_omits_attempted_write=True,registered_sources_changed=False,actual_registered_installation_claimed=False)
(OUT/'reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'README.md').write_text('Actual isolated file-operation fault reproduction. The historical installer helper replaces the target, then an injected directory-fsync failure raises before the caller appends the target to its completed list. This demonstrates a partial-write reporting gap, not a mathematical proof failure or a registered mutation. Original executed helper/source and exact before/observed-after bytes are preserved. The normal helper controls and historical source candidates remain valid at their recorded scopes.\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
assert all(sha(OUT/n)==h for n,h in json.loads((OUT/'file-manifest.json').read_text()).items())
print(json.dumps(result),flush=True)
