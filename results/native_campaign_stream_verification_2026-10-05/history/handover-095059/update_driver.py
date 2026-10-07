from pathlib import Path
import datetime,hashlib,json,re
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_campaign_stream_verification_2026-10-05'
note=repo/'math/GROUND_NATIVE_RECOVERY_STATUS_2026-10-05.md';handover=out/'handover.md'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
fps=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]
fps += [Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]
protected={}
for p in fps:
 for f,h in json.loads(p.read_text()).items():
  assert f not in protected or protected[f]==h
  protected[f]=h
assert not set(map(str,[note,handover])).intersection(protected)
assert all(sha(p)==h for p,h in protected.items())
jobs={662901:'de_native_campaign_qualified_stream_build.py',760297:'de_native_seed_real_returns_qualified_stream_build.py',853725:'de_native_campaign_verification_stream_finish.py',853723:'de_native_additional_constructions_stream_qualified_build.py',853738:'de_source_execution_supplement_stream_qualified_build.py',4049651:'de_native_stable15_priority_recovery/build_recovery.py',2558747:'de_native_stable_seed_leaves_private_build.py',2637955:'de_native_stable_seed_pairs_private_build.py',2854622:'de_native_stable_seed_families_private_build.py',3948875:'de_native_stable_seed_sixty_private_build.py',940127:'de_native_stable_prefix_failures_private_build.py',2056100:'de_native_original_sample_results_private_build.py'}
for pid,p in jobs.items():assert Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0',b' ').decode().strip()=='/usr/bin/python3 /tmp/'+p,pid
counts={}
for key,p,denom in [('stable','/tmp/de-native-stable-seed-leaves-driver.log',597),('priority','/tmp/de-native-stable15-priority-recovery-driver.log',289),('qualified','/tmp/de-native-campaign-qualified-stream-driver.log',1734)]:
 text=Path(p).read_text();assert not re.search(r'terminal [1-9]|Traceback',text),p
 ms=re.findall(r'completed (\d+) /'+str(denom),text);assert ms;counts[key]=int(ms[-1])
packets={}
for name in ['source_normalization_failure_checked_2026-10-05','native_stable15_finite_checked_2026-10-05','source_normalization_failure_production_candidate_2026-10-05']:
 p=repo/'results'/name;mf=p/'file-manifest.json';m=json.loads(mf.read_text());assert all(sha(p/f)==h for f,h in m.items());packets[name]=sha(mf)
a=json.loads((repo/'results/source_normalization_failure_checked_2026-10-05/audit-summary.json').read_text());assert a['terminal_exit_code']==0 and a['standard_only'] and a['checked_declarations']==5
b=json.loads((repo/'results/native_stable15_finite_checked_2026-10-05/audit-summary.json').read_text());assert b['terminal_exit_code']==0 and b['standard_only'] and b['checked_declarations']==18
stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();s=note.read_text()
s=re.sub(r'Recorded [^\n]+',f'Recorded {stamp}. This is a recovery pointer; current sources, terminal',s,count=1)
s=re.sub(r'has \d+/597 scheduled',f'has {counts["stable"]}/597 scheduled',s)
s=re.sub(r'\d+/289 total terminal-zero',f'{counts["priority"]}/289 total terminal-zero',s)
s=re.sub(r'with \d+/1734 terminal-zero',f'with {counts["qualified"]}/1734 terminal-zero',s)
old='''leaves,89 pairs and4 aggregates. Its fresh finite18 and combined27 statement/
standard-only axiom audits remain pending.'''
new='''leaves,89 pairs and4 aggregates. Its finite18 statement/standard-only axiom
audit has now passed. The original seed has phase/normalization guards at inputs
0–59, unit states0–60 and failed four-test conjunctions at every update1–60,
witnessed by the actual last-update residual above the original tolerance.
The finite dependency closure has110 modules (72 retained,38 fresh), with60
leaves,30 pairs and3 aggregates. The durable finite packet has448 verified
archive members and786 source/object bindings:
`results/native_stable15_finite_checked_2026-10-05`;
`math/GROUND_NATIVE_STABLE15_FINITE_2026-10-05.md`.
The 178-update infinite entry and combined27 audit remain pending.'''
assert s.count(old)==1;s=s.replace(old,new)
marker='## Required registered integration order'
addition='''## New separate execution-failure supplement

Five exact mathematical source-execution failure declarations passed fresh
printed-statement and standard-only transitive-axiom checks. For every background
and coupling, earned real positive ground witnesses give unit imaginary starts
whose input/candidate normalizations pass but whose half update is zero and
whose execution fails at every positive count. A phase-related real/imaginary
pair has equal site densities and sourced potentials, but only the real member
completes its first update. These are supplied starts distinct from the original
experiment seed, with no IEEE or physical phase-dependence claim. The old
algebraic cancellation theorem is imported; execution and unconditional witness
returns are new. Checked packet:25 verified members/25 bindings,
`results/source_normalization_failure_checked_2026-10-05`;
note:`math/GROUND_SOURCE_NORMALIZATION_FAILURE_2026-10-05.md`.

Its separate production candidate has1 module/5 declarations. The fixed prior
1734+4,29,3 plans and prepared32560 installation/checker candidates remain
unchanged. Their future explicit extension must cover1771 native modules,
20789 fresh native declarations and a fresh cumulative32565-declaration audit.
This is an enumeration obligation, not a completed registered proof count.
The new module imports precisely the already checked normalization parent.

'''
assert s.count(marker)==1;s=s.replace(marker,addition+marker)
s=s.replace('''   is claimed by this source candidate. Its prerequisites remain mandatory.''','''   is claimed by this source candidate. Its prerequisites remain mandatory.
   Extend this archived installation candidate explicitly for the separate
   one-module/five-declaration execution-failure supplement before installing it;
   do not count that module under the old20784/32560 audit lists.''')
s=s.replace('''   adjustments remain pending; these preflights do not certify that success path.''','''   adjustments remain pending; these preflights do not certify that success path.
   Explicitly extend both candidates' exact source/object inventories, declaration
   lists and proof gates for the new checked1/5 supplement. Final native statement
   and cumulative axiom commands must then cover20789 and32565 respectively.''')
hist=out/'history'/('handover-'+datetime.datetime.now(datetime.timezone.utc).strftime('%H%M%S'));hist.mkdir()
(hist/note.name).write_bytes(note.read_bytes());mf=out/'snapshot-file-manifest.json'
(hist/'preceding-snapshot-file-manifest.json').write_bytes(mf.read_bytes())
note.write_text(s);handover.write_text(s)
(hist/'update_driver.py').write_bytes(Path(__file__).read_bytes())
(hist/'update-verification.json').write_text(json.dumps(dict(utc=stamp,live_jobs=jobs,progress=counts,source_freeze_inputs_revalidated=len(protected),packet_manifests=packets,old_handover_preserved=True,registered_inputs_unchanged=True,finite15_declarations_checked=18,execution_failure_declarations_checked=5,old_installation_candidate_unchanged=True,new_integration_obligation=dict(modules=1,declarations=5),goal_complete=False),indent=2)+'\n')
manifest={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p!=mf}
mf.write_text(json.dumps(manifest,indent=2)+'\n');assert all(sha(out/p)==h for p,h in manifest.items())
print(json.dumps(dict(utc=stamp,progress=counts,live_jobs=len(jobs),source_freeze_inputs_revalidated=len(protected),handover_sha256=sha(handover),finite15_checked=18,execution_failure_checked=5)))
