from pathlib import Path
import json,hashlib,subprocess,datetime,tarfile,ast
REPO=Path('/home/repos/six-birds-de-closure')
SCRIPT=Path('/tmp/de_checkpoint_stable10_return.py')
OLD=Path('/tmp/de_checkpoint_stable5_return.py')
PARENT=REPO/'results/native_original_stable5_return_2026-10-05'
OUT=REPO/'results/native_original_stable10_checkpoint_candidate_2026-10-05'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not OUT.exists()
assert all(sha(PARENT/p)==h for p,h in json.loads((PARENT/'file-manifest.json').read_text()).items())
archive=json.loads((PARENT/'archive-manifest.json').read_text());row=next(r for r in archive['entries'] if r['name']=='de_checkpoint_stable5_return.py')
assert row['sha256']==sha(OLD)
with tarfile.open(PARENT/'completed_artifacts.tar.gz','r|gz') as t:
    found=False
    for m in t:
        if m.name==row['name']:
            assert t.extractfile(m).read()==OLD.read_bytes();found=True;break
    assert found
old=ast.parse(OLD.read_text());new=ast.parse(SCRIPT.read_text())
functions=lambda tree:{n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,ast.FunctionDef)}
assert functions(old)==functions(new) # Dependency collector/archive behavior unchanged.
preflights=[]
for mode,expected in [('preflight',0),('checkpoint',2)]:
    cmd=['/usr/bin/python3',str(SCRIPT),'--mode',mode]
    r=subprocess.run(cmd,cwd=REPO,capture_output=True,text=True)
    assert r.returncode==expected,(mode,r.returncode,r.stdout,r.stderr)
    d=json.loads(r.stdout)
    assert d['coupling']=='10' and d['original_sample_index']==8 and d['entry_updates']==60 and d['paired_entry']==30
    assert not d['ready_for_checkpoint'] and not d['proof_success_claimed'] and not d['checkpoint_created']
    assert not (REPO/'results/native_original_stable10_return_2026-10-05').exists()
    preflights.append(dict(command=cmd,cwd=str(REPO),actual_exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,collector_sha256=sha(SCRIPT)))
OUT.mkdir();(OUT/'collector_candidate.py').write_bytes(SCRIPT.read_bytes());(OUT/'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
checks=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),coupling='10',original_sample_index=8,paired_entry=30,entry_updates=60,parent_executed_collector_sha256=sha(OLD),unchanged_dependency_collector_ast=True,preflights=preflights,checkpoint_created=False,math_proof_success_claimed=False,new_lean_command_started=False,registered_sources_changed=False,goal_complete=False)
(OUT/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
(OUT/'README.md').write_text('Prepared coupling10/sample8 checkpoint collector. Its parent collector was matched to the source actually archived in the completed coupling5 packet. Current sample/frame/entry source guards establish coupling10 and30 pairs/60 updates. Dependency collection and archive/readback behavior are unchanged. Explicit preflight mode reports readiness without success; checkpoint mode refuses missing actual family/sixty terminal0 audits with exit2 before creating a packet. Both real modes were exercised while those audits remain pending. After both finish, run /usr/bin/python3 /tmp/de_checkpoint_stable10_return.py --mode checkpoint. No new Lean command, mathematical success or registered integration is claimed.\n')
(OUT/'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
assert all(sha(OUT/p)==h for p,h in json.loads((OUT/'file-manifest.json').read_text()).items())
print(json.dumps(checks),flush=True)
