from pathlib import Path
import subprocess, os, json, hashlib, shutil, datetime, re

REPO = Path('/home/repos/six-birds-de-closure')
OLD = Path('/tmp/de_original_audit_nonidentifiability_corrected')
ROOT = Path('/tmp/de_original_audit_nonidentifiability_v3')
HISTORY = REPO / 'results/original_audit_nonidentifiability_proof_history_2026-10-05'
SOURCE_REL = Path('lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean')
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p, data):
    p.write_text(json.dumps(data, indent=2) + '\n')
def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

assert json.loads((OLD/'compile-terminal.json').read_text())['terminal_exit_code'] == 1
assert not ROOT.exists() and not HISTORY.exists()
HISTORY.mkdir(parents=True)
for rel in [SOURCE_REL, Path('compile.log'), Path('compile-terminal.json'), Path('compile-source-freeze.json')]:
    dest = HISTORY/rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(OLD/rel, dest)
(HISTORY/'README.md').write_text('Actual failed first attempt, preserved unchanged. Compiler exit 1: unused simp arguments, a finite-vector simplification and a return elaboration failed. No theorem success is claimed.\n')
write(HISTORY/'file-manifest.json', {str(p.relative_to(HISTORY)):sha(p) for p in HISTORY.rglob('*') if p.is_file()})

source = ROOT/SOURCE_REL
source.parent.mkdir(parents=True)
body = (OLD/SOURCE_REL).read_text()
body = body.replace('simp [finiteReadout, hn, hv]', 'simp [finiteReadout, hn]')
body = body.replace('simp [finiteReadout, hp, hv]', 'simp [finiteReadout, hp]')
body = body.replace('norm_num [GroundOriginalOffsets.offsets]', 'decide +kernel')
body = body.replace('  simpa [GroundOffsetSeedReturn.orbit, GroundOffsetSeedReturn.f,\n    GroundOffsetSeedReturn.κ] using\n      (GroundOriginalOffsetSeed.rounded_original_seed_return i).1', '  exact (GroundOriginalOffsetSeed.rounded_original_seed_return i).1')
source.write_text(body)

# Bind every project import in the actual source's transitive import closure.
bindings = {str(source):sha(source)}
pending = [source]
seen = set()
while pending:
    p = pending.pop()
    for module in re.findall(r'^import (SbtCosmo\.[A-Za-z0-9_.]+)\s*$', p.read_text(), re.M):
        if module in seen: continue
        seen.add(module)
        rel = Path(*module.split('.'))
        src = REPO/'lean'/rel.with_suffix('.lean')
        obj = REPO/'lean/.lake/build/lib/lean'/rel.with_suffix('.olean')
        assert src.is_file() and obj.is_file(), module
        bindings[str(src)] = sha(src)
        bindings[str(obj)] = sha(obj)
        pending.append(src)
for rel in ['lean/lean-toolchain', 'lean/lake-manifest.json', 'lean/lakefile.lean']:
    p=REPO/rel
    bindings[str(p)] = sha(p)
write(ROOT/'compile-source-freeze.json', bindings)
command=['lake','env','lean','-R',str(ROOT/'lean'),'-o',str(ROOT/'GroundOriginalAuditNonidentifiability.olean'),str(source)]
env=os.environ.copy(); env['LEAN_NUM_THREADS']='4'
started=now()
with (ROOT/'compile.log').open('w') as f:
    result=subprocess.run(command,cwd=REPO/'lean',env=env,stdout=f,stderr=subprocess.STDOUT)
changed=[p for p,h in bindings.items() if sha(Path(p)) != h]
terminal={'terminal_exit_code':result.returncode,'command':command,'cwd':str(REPO/'lean'),'started_at':started,'ended_at':now(),'source_sha256':sha(source),'log_sha256':sha(ROOT/'compile.log'),'environment_overrides':{'LEAN_NUM_THREADS':'4'},'freeze_sha256':sha(ROOT/'compile-source-freeze.json'),'unchanged_inputs':not changed,'changed_inputs':changed,'project_dependency_modules':len(seen)}
if result.returncode == 0:
    terminal['object_sha256']=sha(ROOT/'GroundOriginalAuditNonidentifiability.olean')
write(ROOT/'compile-terminal.json',terminal)
print(json.dumps(terminal),flush=True)
raise SystemExit(result.returncode or bool(changed))
