from pathlib import Path
import datetime,hashlib,json,re,sys
jobs={662901:'de_native_campaign_qualified_stream_build.py',760297:'de_native_seed_real_returns_qualified_stream_build.py',853725:'de_native_campaign_verification_stream_finish.py',853723:'de_native_additional_constructions_stream_qualified_build.py',853738:'de_source_execution_supplement_stream_qualified_build.py',4049651:'de_native_stable15_priority_recovery/build_recovery.py',2558747:'de_native_stable_seed_leaves_private_build.py',2637955:'de_native_stable_seed_pairs_private_build.py',2854622:'de_native_stable_seed_families_private_build.py',3948875:'de_native_stable_seed_sixty_private_build.py',940127:'de_native_stable_prefix_failures_private_build.py',2056100:'de_native_original_sample_results_private_build.py'}
live=[];missing=[];completed_jobs=[]
for pid,script in jobs.items():
 try:command=Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()
 except FileNotFoundError:command=None
 if command=='/usr/bin/python3 /tmp/'+script:live.append(pid)
 elif pid==4049651:
  base=Path('/tmp/de_native_stable15_priority_recovery')
  try:
   summary=json.loads((base/'summary.json').read_text());terminal=json.loads((base/'terminal.json').read_text())
   audit=json.loads((base/'CombinedReturnAudit-summary.json').read_text());at=json.loads((base/'CombinedReturnAudit-terminal.json').read_text())
   digest=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
   assert summary==terminal and summary['terminal_exit_code']==0 and summary['standard_only']
   assert summary['total_modules']==289 and summary['checked_declarations']==27
   assert summary['source_freeze_sha256']==digest(base/'source-freeze.json')
   assert audit['terminal_exit_code']==at['terminal_exit_code']==0 and audit['standard_only'] and audit['checked_declarations']==27
   assert audit['log_sha256']==at['log_sha256']==digest(base/'CombinedReturnAudit.log')
  except (FileNotFoundError,AssertionError,KeyError,json.JSONDecodeError):missing.append(dict(pid=pid,script=script,current_command=command))
  else:completed_jobs.append(dict(pid=pid,script=script,actual_terminal_exit_code=0,recorded_audited_declarations=27,terminal_sha256=digest(base/'terminal.json')))
 else:missing.append(dict(pid=pid,script=script,current_command=command))
progress={};failures=[]
for name,path,total in [('stable','de-native-stable-seed-leaves-driver.log',597),('priority15','de-native-stable15-priority-recovery-driver.log',289),('qualified','de-native-campaign-qualified-stream-driver.log',1734)]:
 text=(Path('/tmp')/path).read_text()
 if re.search(r'terminal [1-9]|Traceback \(most recent|^exception\s',text,re.M):failures.append(path)
 matches=re.findall(r'completed (\d+) /'+str(total),text);progress[name]=dict(passed=int(matches[-1]) if matches else None,planned=total)
family=Path('/tmp/de-native-stable-seed-families-driver.log').read_text();sixty=Path('/tmp/de-native-stable-seed-sixty-driver.log').read_text()
for path,text in [('families',family),('sixty',sixty)]:
 if re.search(r'terminal [1-9]|Traceback \(most recent|^exception\s',text,re.M):failures.append(path)
completed=[i for i in [1,3,4,5,6,7,8,9] if f'NativeStableSeed{i:03d}Audit terminal 0' in family and f'NativeStableSeed{i:03d}SixtyAudit terminal 0' in sixty]
evidence=[p for p in ['/tmp/de_native_stable15_priority_recovery/summary.json','/tmp/de-native-original-sample-results-audit-summary.json','/tmp/de-native-campaign-qualified-stream-summary.json','/tmp/de-native-campaign-verification-stream-finish-summary.json'] if Path(p).exists()]
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),live_jobs=len(live),verified_terminal_jobs=completed_jobs,missing_or_changed_processes=missing,progress=progress,regular_stable_sample_indices_with_both_audits=completed,recorded_failure_logs=failures,existing_final_summaries_to_inspect=evidence)))
raise SystemExit(1 if missing or failures else 0)
