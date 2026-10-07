"""Empirical cross-check with the unchanged original sixty-update routine."""
import sys
sys.dont_write_bytecode = True
import hashlib
import importlib.util
import json
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py"
OUTPUT = Path(__file__).with_name("original_numeric_compare.json")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert np.__version__ == "1.26.4", np.__version__
    assert not OUTPUT.exists(), OUTPUT
    source_hash = sha(SOURCE)
    assert source_hash == "391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd"
    spec = importlib.util.spec_from_file_location("de_original_source_numeric_cross_check", SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    initial, background, _ = module.load_initial_field()
    assert len(initial) == len(background) == 8
    kinetic = module.kinetic_operator(8)
    rows = []
    for i, k in enumerate([0., .1, .3, .5, 1., 2., 3., 5., 10., 15., 20., 30.]):
        trace, summary, _ = module.run_case(f"original_sample_{i:03d}", initial,
                                          background, k, .5, kinetic, steps=60)
        assert len(trace) == summary["iterations"] == 60
        assert bool(summary["converged"]) == (i < 9), (i, summary)
        rows.append(summary)
        print("sample", i, "coupling", k, "sixty verdict", summary["converged"], flush=True)
    assert sha(SOURCE) == source_hash
    OUTPUT.write_text(json.dumps({
        "scope": "Observed execution of the unchanged NumPy1.26.4 routine at the twelve original sample inputs. All finite sixty-update verdicts agree with the mathematical classification. This is not an IEEE-operation certificate, infinite-trajectory proof or first-success-index theorem.",
        "original_runtime_sha256": source_hash,
        "source_field_sha256": sha(module.SOURCE_FIELDS),
        "numpy_version": np.__version__,
        "wrapper_sha256": sha(Path(__file__)),
        "steps": 60, "mix": .5, "all_twelve_verdicts_match": True,
        "samples": rows, "paper_edited": False, "original_runtime_edited": False,
        "goal_complete": False,
    }, indent=2)+"\n")
    print("All12 original numerical sixty-update verdicts agree with the exact native-source classification.")


if __name__ == "__main__":
    main()
