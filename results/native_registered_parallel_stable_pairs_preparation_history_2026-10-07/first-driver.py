"""Compile unchanged registered stable pair certificates beside the cycle branch."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, resource, subprocess, traceback
ROOT = Path('/home/repos/six-birds-de-closure')
LEAN = ROOT / 'lean'
LIB = LEAN / '.lake/build/lib/lean'
OUT = ROOT / 'results/native_registered_parallel_stable_pairs_2026-10-07'
FULL = Path('/tmp/de_native_registered_original_audit_receipts')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
load = lambda p: json.loads(Path(p).read_text())
def write(p, d):
    Path(p).write_text(json.dumps(d, indent=2) + '\n')
def main():
    assert not OUT.exists()
    assert 'lake build' in Path('/proc/2244141/cmdline').read_bytes().replace(b'\0', b' ').decode()
    assert not (FULL / 'build-terminal.json').exists()
    assert load(ROOT / 'results/native_registered_parallel_stable009_2026-10-07/actual-exec-result.json')['exit_code'] == 0
    plan_path = ROOT / 'results/native_registered_aggregate_installation_candidate_2026-10-06/installation-plan.json'
    plan = load(plan_path)
    snapshot = load(FULL / 'source-snapshot.json')
    def obj(n):
        return LIB / Path(*n.split('.')).with_suffix('.olean')
    def closure(roots):
        seen = set()
        todo = list(roots)
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            p = LEAN / Path(*n.split('.')).with_suffix('.lean')
            if not p.exists():
                continue
            assert sha(p) == snapshot[str(p)], n
            seen.add(n)
            for line in p.read_text().splitlines():
                m = re.match(r'^import\s+(.*)$', line)
                if m:
                    todo.extend(m.group(1).split())
        return seen
    roots = sorted(r['module'] for r in plan['modules'] if re.fullmatch(r'SbtCosmo\.Derivation\.NativeStableSeed\d{3}\.Pair\d{3}', r['module']) and not obj(r['module']).exists())
    assert len(roots) == 299
    deps = closure(roots)
    unbuilt = {n for n in deps if not obj(n).exists()}
    assert unbuilt == set(roots)
    cycle = closure([r['module'] for r in plan['modules'] if 'Cycle' in r['module'] and ('20' in r['module'] or '30' in r['module'])])
    assert not unbuilt & {n for n in cycle if not obj(n).exists()}
    children = set()
    for task in Path('/proc/2244141/task').iterdir():
        try:
            children.update((task / 'children').read_text().split())
        except FileNotFoundError:
            pass
    child_commands = []
    for pid in sorted(children):
        try:
            cmd = Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0', b' ').decode()
        except FileNotFoundError:
            continue
        if '/bin/lean ' in cmd:
            assert '/NativeCycle20/' in cmd or '/NativeCycle30/' in cmd, cmd
            child_commands.append(cmd)
    assert child_commands
    mem = next(int(l.split()[1]) for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:'))
    assert mem >= 60 * 1024 * 1024
    before = {str(LEAN / Path(*n.split('.')).with_suffix('.lean')): snapshot[str(LEAN / Path(*n.split('.')).with_suffix('.lean'))] for n in deps}
    source = Path(__file__)
    self_sha = sha(source)
    command = ['lake', 'build'] + ['+' + n for n in roots]
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    assert hard == resource.RLIM_INFINITY or hard >= 65536 * 1024
    resource.setrlimit(resource.RLIMIT_STACK, (65536 * 1024, hard))
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(source.read_bytes())
    write(OUT / 'intent.json', dict(utc=datetime.now(timezone.utc).isoformat(), command=command, cwd=str(LEAN), environment_overrides={'LEAN_NUM_THREADS': '4'}, main_driver_pid=2203106, main_lake_pid=2244141, main_active_compiler_commands=child_commands, registered_plan_sha256=sha(plan_path), full_source_snapshot_sha256=sha(FULL / 'source-snapshot.json'), local_dependencies=len(deps), planned_unbuilt=sorted(unbuilt), unbuilt_overlap_with_main_cycle20_and30=[], source_sha256=before, driver_sha256=self_sha, proof_objects_copied=0))
    try:
        print('Actual registered stable pair build starting: 299 targets', flush=True)
        log = OUT / 'build.log'
        with log.open('w') as f:
            r = subprocess.run(command, cwd=LEAN, env=env, stdout=f, stderr=subprocess.STDOUT)
        write(OUT / 'build-terminal.json', dict(utc=datetime.now(timezone.utc).isoformat(), terminal_exit_code=r.returncode, command=command, cwd=str(LEAN), environment_overrides={'LEAN_NUM_THREADS': '4'}, log_sha256=sha(log), intent_sha256=sha(OUT / 'intent.json')))
        assert r.returncode == 0
        assert 'Build completed successfully' in log.read_text()
        assert not re.search(r'error:|warning:|Traceback|build failed', log.read_text())
        assert sha(source) == self_sha and all(sha(p) == h for p, h in before.items())
        objects = {n: sha(obj(n)) for n in sorted(unbuilt)}
        write(OUT / 'objects-snapshot.json', objects)
        built = set(re.findall(r'Built (SbtCosmo\.Derivation\.\S+)', log.read_text()))
        assert unbuilt <= built
        write(OUT / 'terminal.json', dict(terminal_exit_code=0, selected_targets=299, selected_objects_checked=len(objects), genuinely_reported_built_selected_modules=len(built & unbuilt), proof_objects_copied=0, full_registered_build_still_required=True, full_axiom_and_statement_audits_still_required=True, goal_complete=False))
        print(json.dumps(load(OUT / 'terminal.json')), flush=True)
    except BaseException as e:
        write(OUT / 'terminal.json', dict(terminal_exit_code=1, error=repr(e), traceback=traceback.format_exc(), goal_complete=False))
        raise
if __name__ == '__main__':
    main()
