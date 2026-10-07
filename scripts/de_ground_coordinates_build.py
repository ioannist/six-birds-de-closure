"""Build bounded pairs of independent kernel coordinate certificates."""
import json
from pathlib import Path
import subprocess
import time
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results/ground_coordinates_2026-10-04'
OUT.mkdir(exist_ok=True)
leaves=sorted((ROOT/'lean/SbtCosmo/Derivation/GroundCoordinates').glob('*.lean'))
assert len(leaves)==12
rows=[]
with (OUT/'leaf_build.txt').open('w') as log:
    for start in range(0,12,2):
        targets=['SbtCosmo.Derivation.GroundCoordinates.'+p.stem for p in leaves[start:start+2]]
        command=['lake','build',*targets]
        log.write('Batch targets: '+json.dumps(targets)+'\n');log.flush()
        began=time.monotonic()
        result=subprocess.run(command,cwd=ROOT/'lean',stdout=log,stderr=subprocess.STDOUT)
        log.write('Terminal exit: '+str(result.returncode)+'\n');log.flush()
        rows.append(dict(targets=targets,command=command,exit_code=result.returncode,
                         elapsed_seconds=round(time.monotonic()-began,3)))
        status=dict(total_targets=12,batch_size=2,terminal_batches=rows,
                    successful_targets=sum(len(r['targets']) for r in rows if r['exit_code']==0),
                    all_success=result.returncode==0 and start+2==12)
        (OUT/'leaf_build_status.json').write_text(json.dumps(status,indent=2)+'\n')
        print(f'Terminal batch:{start+2}/12;exit={result.returncode}',flush=True)
        if result.returncode:raise SystemExit(result.returncode)
print('All12 coordinate arithmetic modules built successfully',flush=True)
