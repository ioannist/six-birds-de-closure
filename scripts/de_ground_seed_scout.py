"""Read-only floating scout of the frozen initial seed; not a certificate.

State updates call the unchanged Step26 source with its real eigensolver sign,
phase fallback and normalizations. Diagnostic distances use a positive real
candidate. The unused unitary diagnostic does not enter the state update.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py'
PIN='391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd'


def scout():
    assert np.__version__=='1.26.4'
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==PIN
    spec=importlib.util.spec_from_file_location('step26_seed_scout',SOURCE)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    loaded,b,_=m.load_initial_field()
    initial=m.normalize(loaded.copy()) # Matches run_case's second initialization normalization.
    kinetic=m.kinetic_operator(len(initial));rows=[]
    for k in [0.,.3,15.,20.,30.]:
        z=initial.copy();checkpoints=[];min_overlap=float('inf');min_mixed_norm=float('inf')
        for n in range(1000):
            _,candidate=m.lowest_eigenvector(m.hamiltonian(kinetic,b+k*m.stress_energy_density(z,b)))
            overlap=abs(np.vdot(candidate,z));min_overlap=min(min_overlap,float(overlap))
            aligned=m.phase_align(candidate,z)
            mixed=.5*z+.5*aligned;min_mixed_norm=min(min_mixed_norm,float(np.linalg.norm(mixed)))
            z=m.normalize(mixed)
            positive=candidate if candidate.real.sum()>0 else -candidate
            if n+1 in [1,6,60,200,1000]:
                checkpoints.append(dict(iteration=n+1,real_sum=float(z.real.sum()),imaginary_norm=float(np.linalg.norm(z.imag)),
                    distance_to_positive_previous_candidate=float(np.linalg.norm(z-positive)),
                    distance_to_negative_previous_candidate=float(np.linalg.norm(z+positive))))
        rows.append(dict(coupling_hex=k.hex(),mix_hex=(.5).hex(),checkpoints=checkpoints,
                         observed_minimum_overlap=min_overlap,observed_minimum_mixed_norm=min_mixed_norm))
    return dict(kind='floating heuristic scout, not exact orbit/basin certificate',numpy_version=np.__version__,
                source_sha256=PIN,initial_data_sha256=hashlib.sha256(m.SOURCE_FIELDS.read_bytes()).hexdigest(),
                original_phase_bug_and_fallback_retained=True,source_eigensolver_sign_retained_in_updates=True,
                source_initialization_normalization_count=2,unused_unitary_diagnostic_omitted=True,
                source_updates_per_coupling=1000,couplings=rows,
                formal_initial_seed_basin_claimed=False,IEEE_per_operation_emulation_proved=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args();s=json.dumps(scout(),indent=2)+'\n'
    if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(s)
    else:print(s,end='')
