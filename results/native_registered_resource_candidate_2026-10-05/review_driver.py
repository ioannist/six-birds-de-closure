from pathlib import Path
import ast,copy,datetime,hashlib,importlib.util,json,subprocess,tarfile
repo=Path('/home/repos/six-birds-de-closure');out=repo/'results/native_registered_resource_candidate_2026-10-05';out.mkdir(exist_ok=False)
vp=Path('/tmp/de_native_registered_verify_resource_candidate.py');bp=Path('/tmp/de_native_registered_build_resource_candidate.py');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('resource_registered_review',vp);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
assert v.REQUIRED_ENV=={'LEAN_NUM_THREADS':'4'}
old=Path('/tmp/de_native_registered_verify_with_failure_candidate.py').read_text().replace('/tmp/de_native_registered_with_failure_receipts','/tmp/de_native_registered_resource_receipts');before={n.name:n for n in ast.parse(old).body if isinstance(n,ast.FunctionDef)};after={n.name:n for n in ast.parse(vp.read_text()).body if isinstance(n,ast.FunctionDef)}
unchanged=[]
for name,node in before.items():
 actual=copy.deepcopy(after[name])
 if name=='registered':
  loop=next(n for n in actual.body if isinstance(n,ast.For) and ast.unparse(n.target)=='(stage, command)')
  env=[i for i,n in enumerate(loop.body) if isinstance(n,ast.Assert) and ast.unparse(n.test)=="d['environment_overrides'] == REQUIRED_ENV"];assert len(env)==1;loop.body.pop(env[0])
 assert ast.dump(actual,include_attributes=False)==ast.dump(node,include_attributes=False),name;unchanged.append(name)
expected=Path('/tmp/de_native_registered_build_with_failure_candidate.py').read_text().replace('import hashlib,importlib.util,json,re,subprocess,traceback','import hashlib,importlib.util,json,os,re,subprocess,traceback').replace('/tmp/de_native_registered_verify_with_failure_candidate.py','/tmp/de_native_registered_verify_resource_candidate.py').replace('/tmp/de_native_registered_with_failure_receipts','/tmp/de_native_registered_resource_receipts')
expected=expected.replace(" helpers[str(source)]=sha(source)\n"," helpers[str(source)]=sha(source)\n runtime_env=dict(os.environ,**verify.REQUIRED_ENV)\n").replace("r=subprocess.run(command,cwd=ROOT/'lean',stdout=f,stderr=subprocess.STDOUT)","r=subprocess.run(command,cwd=ROOT/'lean',env=runtime_env,stdout=f,stderr=subprocess.STDOUT)").replace("installation_plan_sha256=sha(verify.CANDIDATE/'installation-plan.json'),source_snapshot_sha256=sha(out/'source-snapshot.json'),log_sha256=sha(log))","installation_plan_sha256=sha(verify.CANDIDATE/'installation-plan.json'),source_snapshot_sha256=sha(out/'source-snapshot.json'),log_sha256=sha(log),environment_overrides=verify.REQUIRED_ENV)")
assert bp.read_text()==expected
registered=after['registered'];loop=next(n for n in registered.body if isinstance(n,ast.For) and ast.unparse(n.target)=='(stage, command)');guard=next(n for n in loop.body if isinstance(n,ast.Assert) and ast.unparse(n.test)=="d['environment_overrides'] == REQUIRED_ENV")
check=compile(ast.Module(body=[guard],type_ignores=[]),'<actual verifier environment assertion>','exec');controls=[]
for value in [None,{}, {'LEAN_NUM_THREADS':'128'}, {'LEAN_NUM_THREADS':'0'}]:
 try:exec(check,dict(d={} if value is None else {'environment_overrides':value},REQUIRED_ENV=v.REQUIRED_ENV))
 except (AssertionError,KeyError):controls.append(dict(value=value,rejected=True))
 else:raise AssertionError('Wrong resource receipt accepted')
exec(check,dict(d={'environment_overrides':v.REQUIRED_ENV},REQUIRED_ENV=v.REQUIRED_ENV))
checks=[]
for name,args,code in [('candidate',[str(vp),'--mode','candidate'],0),('registered',[str(vp),'--mode','registered'],2),('runner',[str(bp)],2)]:
 cmd=['/usr/bin/python3']+args;r=subprocess.run(cmd,capture_output=True,text=True);(out/(name+'-stdout.log')).write_text(r.stdout);(out/(name+'-stderr.log')).write_text(r.stderr);assert r.returncode==code and not r.stderr,(name,r.stderr);checks.append(dict(command=cmd,terminal_exit_code=r.returncode,result=json.loads(r.stdout)))
assert not Path('/tmp/de_native_registered_resource_receipts').exists()
fixture=Path('/tmp/de_lake_concurrency_review_2026-10-05');summary=json.loads((fixture/'summary.json').read_text());assert [(r['limit'],r['peak_observed_lean_compilers'],r['terminal_exit_code']) for r in summary['results']]==[(2,2,0),(4,4,0)]
archive=out/'fixture_artifacts.tar.gz';entries=[]
paths=[p for p in fixture.rglob('*') if p.is_file()]+[Path('/tmp/de_test_lake_concurrency.py'),Path('/tmp/de_lean428_runtime_object.cpp')]
with tarfile.open(archive,'w:gz',dereference=True) as tar:
 for p in sorted(paths):
  name=str(p.relative_to('/tmp'));h=sha(p);tar.add(p,arcname=name,recursive=False);assert sha(p)==h;entries.append(dict(name=name,sha256=h,size=p.stat().st_size))
with tarfile.open(archive,'r|gz') as tar:
 for member,row in zip(tar,entries,strict=True):assert member.name==row['name'] and member.isfile() and hashlib.sha256(tar.extractfile(member).read()).hexdigest()==row['sha256']
(out/'fixture-archive-manifest.json').write_text(json.dumps(dict(archive_sha256=sha(archive),entries=entries),indent=2)+'\n')
for source,name in [(vp,'verifier_candidate.py'),(bp,'build_candidate.py'),(Path(__file__),'review_driver.py'),(Path('/tmp/de_prepare_registered_resource_candidates.py'),'prepare_driver.py')]: (out/name).write_bytes(source.read_bytes())
record=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),environment_overrides=v.REQUIRED_ENV,checks=checks,preserved_verifier_functions=unchanged,rejected_environment_receipt_controls=controls,isolated_fixture_builds=summary,fixture_archive_members=len(entries),runtime_source_url='https://raw.githubusercontent.com/leanprover/lean4/7e01a1bf5c70fc6167d49c345d3bf80596e9a79b/src/runtime/object.cpp',runtime_source_sha256=sha('/tmp/de_lean428_runtime_object.cpp'),actual_registered_commands_run=0,full_registered_success_path_tested=False,registered_sources_changed=False,hard_universal_process_cap_proved=False,review='adversarial self-review; actual isolated scheduler tests, not repository proof completion',goal_complete=False)
(out/'checks.json').write_text(json.dumps(record,indent=2)+'\n');(out/'README.md').write_text('Final registered verifier/runner candidates configureLEAN_NUM_THREADS=4 and require that explicit override in actual command receipts. Commands, proof gates, source/object inventories,1771 modules,20789 native declarations and32565 cumulative checks are unchanged. Two isolated twelve-module Lake builds passed with observed compiler peaks2 and4 for their requested thread settings. Four wrong/missing environment receipt controls are rejected. The actual pinned runtime/Lake sources were inspected; standard pool size is configurable, with dedicated/blocked-task replacement threads also possible, so this is no universal theorem on process counts or memory. Candidate mode passes; registered entry points refuse missing final qualified evidence before starting real registered commands. Existing candidates and protected proof inputs remain unchanged. Full registered success path, final publication and actual repository build/audits remain pending.\n')
(out/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in out.iterdir() if p.is_file()},indent=2)+'\n');print(json.dumps(dict(observed_fixture_peaks=[2,4],rejected_environment_controls=4,fixture_archive_members=len(entries),actual_registered_commands_run=0,output=str(out))))
