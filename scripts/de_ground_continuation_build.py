"""Run bounded batches of independent concrete Lean certificate builds.

The runner stops on a failed batch and records actual terminal results. Lake's
own source/dependency traces control reuse; no proof source is edited here.
"""
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'results/ground_continuation_2026-10-04'
OUT.mkdir(exist_ok=True)
leaves = sorted((ROOT/'lean/SbtCosmo/Derivation/GroundContinuation').glob('*.lean'))
assert len(leaves) == 572
rows = []
logpath = OUT/'leaf_build.txt'
with logpath.open('w') as log:
    for start in range(0, len(leaves), 24):
        batch = leaves[start:start+24]
        targets = ['SbtCosmo.Derivation.GroundContinuation.'+p.stem for p in batch]
        began = time.monotonic()
        command = ['lake', 'build', *targets]
        log.write('Batch targets: '+json.dumps(targets)+'\n')
        log.flush()
        result = subprocess.run(command, cwd=ROOT/'lean', stdout=log, stderr=subprocess.STDOUT)
        log.flush()
        row = dict(targets=targets, command=command, exit_code=result.returncode,
                   elapsed_seconds=round(time.monotonic()-began, 3))
        rows.append(row)
        status = dict(total_targets=572, batch_size=24,
                      terminal_batches=rows, successful_targets=sum(len(r['targets']) for r in rows if r['exit_code'] == 0),
                      all_success=all(r['exit_code'] == 0 for r in rows) and start+len(batch)==len(leaves))
        (OUT/'leaf_build_status.json').write_text(json.dumps(status, indent=2)+'\n')
        print(f"Terminal batch: {start+len(batch)}/572 targets; exit={result.returncode}; {row['elapsed_seconds']}s", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
print('All572 concrete continuation arithmetic modules built successfully', flush=True)
