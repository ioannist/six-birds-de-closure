from pathlib import Path
import json, hashlib, subprocess, os, re, datetime, shutil
REPO=Path('/home/repos/six-birds-de-closure')
ROOT=Path('/tmp/de_original_audit_nonidentifiability_v3')
OUT=REPO/'results/original_audit_nonidentifiability_checked_2026-10-05'
MOD='SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability'
SRC=ROOT/'lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,d): p.write_text(json.dumps(d,indent=2)+'\n')
terminal=json.loads((ROOT/'compile-terminal.json').read_text())
assert terminal['terminal_exit_code']==0 and terminal['unchanged_inputs']
assert terminal['source_sha256']==sha(SRC) and terminal['object_sha256']==sha(ROOT/'GroundOriginalAuditNonidentifiability.olean')
assert terminal['log_sha256']==sha(ROOT/'compile.log')
assert not re.search(r'error:|warning:',(ROOT/'compile.log').read_text())
freeze=json.loads((ROOT/'compile-source-freeze.json').read_text())
assert all(sha(p)==h for p,h in freeze.items())
assert not re.search(r'\b(sorry|axiom|native_decide|admit)\b',SRC.read_text())
names=[MOD+'.'+n for n in re.findall(r'^theorem ([\w.]+)',SRC.read_text(),re.M)]
assert len(names)==len(set(names))==9

overlay=ROOT/'audit-overlay'
assert not overlay.exists()
# Merge registered modules; adding one isolated module never shadows an entire
# existing SbtCosmo directory or overwrites a registered object.
registered=REPO/'lean/.lake/build/lib/lean'
for p in registered.rglob('*'):
    if p.is_file():
        dest=overlay/p.relative_to(registered)
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(p.resolve())
own=[]
for p in ROOT.glob('GroundOriginalAuditNonidentifiability.*'):
    if p.suffix=='.lean': continue
    dest=overlay/'SbtCosmo/Derivation'/p.name
    assert not dest.exists()
    dest.symlink_to(p.resolve()); own.append(p)
    freeze[str(p)]=sha(p)
for p in list(freeze):
    if p.endswith('.olean'):
        for suffix in ['.private','.server']:
            companion=Path(p+suffix)
            if companion.is_file(): freeze[str(companion)]=sha(companion)

audit=ROOT/'Audit.lean'
assert not audit.exists()
audit.write_text('import '+MOD+'\nset_option warningAsError true\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names))
freeze[str(audit)]=sha(audit)
write(ROOT/'audit-source-object-freeze.json',freeze)
cwd=REPO/'lean'
raw=subprocess.check_output(['lake','env','which','lean'],cwd=cwd,text=True).strip()
lp=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=cwd,text=True).strip()
env=dict(os.environ,LEAN_PATH=str(overlay)+':'+lp,LEAN_NUM_THREADS='4')
command=[raw,str(audit)]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (ROOT/'audit.log').open('w') as f:
    result=subprocess.run(command,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
receipt=dict(terminal_exit_code=result.returncode,command=command,cwd=str(cwd),started_at=started,ended_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),environment_overrides={'LEAN_NUM_THREADS':'4','LEAN_PATH':env['LEAN_PATH']},audit_source_sha256=sha(audit),log_sha256=sha(ROOT/'audit.log'),freeze_sha256=sha(ROOT/'audit-source-object-freeze.json'))
write(ROOT/'audit-terminal.json',receipt)
assert result.returncode==0
log=(ROOT/'audit.log').read_text()
assert not re.search(r'error:|warning:',log)
found=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))",log,re.S)
assert [n for n,_,_ in found]==names
assert all(set(a.replace('\n',' ').replace(',',' ').split())<={'propext','Classical.choice','Quot.sound'} for _,a,_ in found)
assert all(sha(p)==h for p,h in freeze.items())
assert not OUT.exists(); OUT.mkdir()
files=[SRC,ROOT/'compile.log',ROOT/'compile-terminal.json',ROOT/'compile-source-freeze.json',audit,ROOT/'audit.log',ROOT/'audit-terminal.json',ROOT/'audit-source-object-freeze.json',Path(__file__),Path('/tmp/de_original_audit_nonidentifiability_v3_build.py')]+own
for p in files:
    dest=OUT/('lean/SbtCosmo/Derivation/'+p.name if p==SRC else p.name)
    dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(p,dest); assert sha(dest)==sha(p)
summary=dict(checked_modules=1,checked_declarations=9,names=names,standard_only=True,compile_terminal_exit_code=0,audit_terminal_exit_code=0,registered_integration=False,production_plans_changed=False,project_dependency_modules=terminal['project_dependency_modules'],bound_inputs=len(freeze),all_bound_inputs_unchanged=True,own_objects_archived=[p.name for p in own],dependency_objects_archived=False,source_sha256=sha(SRC),audit_log_sha256=sha(ROOT/'audit.log'),review='Adversarial self-review; no independent review',scope='Original eighteen rounded background controls at original fixed coupling/seed/mix/threshold. Only the Boolean sixty-update diagnostic or limit-existence predicate is used. No unrestricted value-law impossibility, physical Lambda theorem, background blindness or IEEE claim.')
write(OUT/'checkpoint-verification.json',summary)
(OUT/'README.md').write_text('Fresh isolated compilation and nine exact printed-statement/transitive-axiom checks passed. Source, own proof objects, actual commands, logs, terminal receipts and source/object freezes are preserved. Project dependencies are historical hash bindings, not copied archival objects. Paper/runtime/registered proof files remain unchanged. Earlier failed attempts are explicitly preserved in the separate history packets.\n')
write(OUT/'file-manifest.json',{str(p.relative_to(OUT)):sha(p) for p in sorted(OUT.rglob('*')) if p.is_file()})
assert all(sha(OUT/p)==h for p,h in json.loads((OUT/'file-manifest.json').read_text()).items())
assert all(sha(p)==h for p,h in freeze.items())
print(json.dumps(summary),flush=True)
