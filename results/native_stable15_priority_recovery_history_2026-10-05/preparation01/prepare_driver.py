"""Preserve an actually terminated build and resume only unchecked modules."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,tarfile,os

repo=Path('/home/repos/six-birds-de-closure')
old=Path('/tmp/de_native_stable15_priority')
base=Path('/tmp/de_native_stable15_priority_recovery')
out=repo/'results/native_stable15_priority_recovery_2026-10-05'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not Path('/proc/1255480').exists()
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode()
 except (FileNotFoundError,PermissionError,ProcessLookupError):continue
 if '/bin/lean ' in cmd:assert '/tmp/de_native_stable15_priority/' not in cmd,('Orphaned original compiler',p.name)
assert not (old/'terminal.json').exists() and not (old/'summary.json').exists()
freeze=json.loads((old/'source-freeze.json').read_text());assert all(sha(p)==h for p,h in freeze.items())
plan=json.loads((old/'build-plan.json').read_text());rows=plan['rows'];assert len(rows)==289
records=[];paths=[]
for p in sorted((old/'receipts').glob('*-terminal.json')):
 d=json.loads(p.read_text());m=d['module'];assert d['terminal_exit_code']==0
 row=rows[m];obj=old/'objects'/(m+'.olean');log=old/'receipts'/(m+'.log')
 assert d['source_sha256']==d['original_source_sha256']==row['source_sha256']==sha(row['source'])==sha(row['original_source'])
 assert d['object_sha256']==sha(obj) and d['log_sha256']==sha(log)
 assert not re.search(r'error:|warning:',log.read_text())
 records.append(d);paths += [p,obj,log]
done={d['module'] for d in records};assert len(done)==len(records)==73
assert all(set(plan['dependencies'][m])<=done for m in done)
assert set(plan['prerequisite_modules'])<=done
unfinished_logs=[p for p in (old/'receipts').glob('*.log') if p.stem not in done]
assert {p.stem for p in unfinished_logs}=={'NativeStableSeed009Step037','NativeStableSeed009Step038'}
assert not any(p.stem not in done for p in (old/'objects').glob('*.olean'))
assert not base.exists() and not out.exists()
base.mkdir();out.mkdir()
(base/'build-plan.json').write_bytes((old/'build-plan.json').read_bytes())
(base/'retained-receipts.json').write_text(json.dumps(records,indent=2)+'\n')
overlay=base/'overlay';overlay.mkdir()
for p in (old/'overlay').rglob('*.olean'):
 target=p.resolve(strict=True);q=overlay/p.relative_to(old/'overlay');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(target)
for d in records:assert sha(overlay/(d['module']+'.olean'))==d['object_sha256']
(base/'objects').mkdir()
source=(old/'build_priority.py').read_text()
def change(before,after):
 global source
 assert source.count(before)==1,(before,source.count(before));source=source.replace(before,after)
change("base=Path('/tmp/de_native_stable15_priority');", "base=Path('/tmp/de_native_stable15_priority_recovery');oldbase=Path('/tmp/de_native_stable15_priority');")
change("freeze={str(p):sha(p) for p in inputs};fp=base/'source-freeze.json';assert not fp.exists();fp.write_text(json.dumps(freeze,indent=2)+'\\n')", """oldfreeze=json.loads((oldbase/'source-freeze.json').read_text())
assert all(sha(p)==h for p,h in oldfreeze.items())
retained=json.loads((base/'retained-receipts.json').read_text());assert len(retained)==73
inputs += [oldbase/'source-freeze.json',base/'retained-receipts.json']
for d in retained:
 m=d['module'];obj=oldbase/'objects'/(m+'.olean');log=oldbase/'receipts'/(m+'.log');receipt=oldbase/'receipts'/(m+'-terminal.json')
 assert d['terminal_exit_code']==0 and sha(obj)==d['object_sha256'] and sha(log)==d['log_sha256']
 inputs += [obj,log,receipt]
freeze=dict(oldfreeze)
for p in inputs:
 h=sha(p);assert str(p) not in freeze or freeze[str(p)]==h;freeze[str(p)]=h
fp=base/'source-freeze.json';assert not fp.exists();fp.write_text(json.dumps(freeze,indent=2)+'\\n')""")
change("cmd=[raw,'-R',str(base/'lean'),'-o',str(obj),str(src)]", "cmd=[raw,'-R',str(oldbase/'lean'),'-o',str(obj),str(src)]")
change("pending=set(rows);done=set();running={};records=[];finite_done=False", "done={d['module'] for d in retained};pending=set(rows)-done;running={};records=list(retained);finite_done=False\n assert len(done)==73 and all(set(plan['dependencies'][m])<=done for m in done)\n print('Retained73 checked original terminal-zero modules; compiling216 unfinished modules; original interruption preserved',flush=True)")
change("fresh_modules=289,private_prerequisites=18", "fresh_modules=216,retained_terminal_zero_modules=73,total_modules=289,interrupted_original_session_exit_code=143,private_prerequisites=18")
change("'Original coupling15 exact complex seed converges with all guards/unit norms; every1..60-update verdict fails;27 standard-only audited declarations; production integration pending'", "'Original coupling15 recovery passed:73 preserved plus216 fresh modules; exact complex seed converges with all guards/unit norms; every1..60-update verdict fails;27 fresh standard-only audited declarations; production integration pending'")
driver=base/'build_recovery.py';driver.write_text(source)
compile(source,str(driver),'exec')
interruption=dict(utc=datetime.now(timezone.utc).isoformat(),old_pid=1255480,old_process_missing=True,old_session_id=9016,old_session_exit_code=143,
 original_terminal_receipt_missing=True,old_final_audits_complete=False,checked_terminal_zero_modules=73,
 remaining_modules=216,unfinished_modules=[p.stem for p in unfinished_logs],orphan_compilers_absent=True,
 signal_sender_or_reason='Not established; exit143 is interruption evidence, not a mathematical counterexample',
 historical_source_freeze_revalidated=len(freeze),old_sources_or_receipts_changed=False,goal_complete=False)
(base/'interruption.json').write_text(json.dumps(interruption,indent=2)+'\n')
paths += list(old/'lean'/Path(m+'.lean') for m in rows)
paths += unfinished_logs+[old/'build-plan.json',old/'source-freeze.json',old/'build_priority.py',Path('/tmp/de-native-stable15-priority-driver.log'),Path(__file__)]
paths += [base/'build-plan.json',base/'retained-receipts.json',base/'interruption.json',driver]
archive=out/'interrupted_build_and_recovery_inputs.tar.gz';entries=[]
with tarfile.open(archive,'w:gz') as saved:
 for p in sorted(set(paths)):
  member=str(p.relative_to('/tmp'));h=sha(p);saved.add(p,arcname=member,recursive=False);assert sha(p)==h
  entries.append(dict(name=member,sha256=h,size=p.stat().st_size))
with tarfile.open(archive,'r|gz') as saved:
 for member,row in zip(saved,entries,strict=True):
  assert member.name==row['name'] and member.isfile();raw=saved.extractfile(member).read()
  assert len(raw)==row['size'] and hashlib.sha256(raw).hexdigest()==row['sha256']
(out/'archive-manifest.json').write_text(json.dumps(dict(archive_sha256=sha(archive),entries=entries),indent=2)+'\n')
(out/'interruption.json').write_bytes((base/'interruption.json').read_bytes())
log=Path('/tmp/de-native-stable15-priority-recovery-driver.log')
assert not log.exists()
with log.open('w') as f:
 proc=subprocess.Popen(['/usr/bin/python3',str(driver)],cwd=repo/'lean',stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,close_fds=True)
launch=dict(utc=datetime.now(timezone.utc).isoformat(),pid=proc.pid,driver=str(driver),driver_sha256=sha(driver),log=str(log),
 start_new_session=True,completion_requires='terminal.json exit0, finite18 audit and combined27 fresh standard-only audit',retained_modules=73,remaining_fresh_modules=216,
 archive_members_verified=len(entries),old_source_freeze_sha256=sha(old/'source-freeze.json'),repository_registered=False,goal_complete=False)
(out/'launch.json').write_text(json.dumps(launch,indent=2)+'\n');(base/'launch.json').write_bytes((out/'launch.json').read_bytes())
(out/'README.md').write_text('The old isolated priority build actually stopped with session exit143 after73 successful modules; its PID and compilers are absent and it has no final terminal/audit summary. Its sources,73 objects/receipts/logs, incomplete logs and interruption history were archived and verified. The new separate recovery resumes216 unfinished modules from exact unchanged sources. It retains a visibly historical73-module cohort and requires fresh finite18/combined27 statement and standard-only axiom audits. Original private/qualified jobs, source plans and registered inputs are unchanged. This is an incomplete recovery launch, not proof completion. See launch.json and interruption.json.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in out.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(launch),flush=True)
