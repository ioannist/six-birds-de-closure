"""Bounded builds of the seven original shifted-derivative certificates."""
from pathlib import Path
import json,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results/ground_spectral_2026-10-04';OUT.mkdir(exist_ok=True)
rows=[]
with (OUT/'leaf_build.txt').open('w') as log:
    for start in range(0,7,2):
        targets=[f'SbtCosmo.Derivation.GroundSpectralTests.Test{i:03d}' for i in range(start,min(start+2,7))]
        cmd=['lake','build',*targets];log.write('Batch targets: '+json.dumps(targets)+'\n');log.flush()
        t=time.monotonic();r=subprocess.run(cmd,cwd=ROOT/'lean',stdout=log,stderr=subprocess.STDOUT)
        log.write('Terminal exit: '+str(r.returncode)+'\n');log.flush()
        rows.append(dict(targets=targets,command=cmd,exit_code=r.returncode,elapsed_seconds=round(time.monotonic()-t,3)))
        (OUT/'leaf_build_status.json').write_text(json.dumps(dict(total_targets=7,batch_size=2,terminal_batches=rows,
            successful_targets=sum(len(x['targets']) for x in rows if x['exit_code']==0),all_success=r.returncode==0 and start+2>=7),indent=2)+'\n')
        print(f'Terminal batch:{min(start+2,7)}/7;exit={r.returncode}',flush=True)
        if r.returncode:raise SystemExit(r.returncode)
print('All seven spectral arithmetic modules built successfully',flush=True)
