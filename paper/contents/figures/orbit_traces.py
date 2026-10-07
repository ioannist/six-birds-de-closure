#!/usr/bin/env python3
"""Floating-point traces of the frozen Step26 self-consistency iteration (illustration for Fig. 4).

Runs the unchanged sibling source `semiclassical_dynamics_step26.py` (its own `run_case`, including the
frozen phase convention) for n = 1..N_MAX updates and records, for every n, the largest of the four
convergence residuals that the sixty-update diagnostic compares with 1e-8. The diagnostic at n is
exactly the source's `converged` flag after n updates. These are IEEE traces; the exact statements
about the same orbits are the Lean results cited in the paper.
"""
from __future__ import annotations

import csv
import importlib.util
import os
from pathlib import Path

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

ROOT = Path(__file__).resolve().parents[3]
SRC = (ROOT.parent / "six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/"
       "step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py")
OUT = Path(__file__).resolve().parent / "data" / "orbit_traces.csv"
N_MAX = int(os.environ.get("N_MAX", "400"))

OFFSETS = [-8, -5, -3, -2, -1, -0.5, -0.2, -0.1, 0, 0.1, 0.2, 0.5, 1, 2, 3, 5, 8, 10]
KAPPAS = [0, 0.1, 0.3, 0.5, 1, 2, 3, 5, 10, 15, 20, 30]


def main() -> None:
    spec = importlib.util.spec_from_file_location("step26", SRC)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    psi, background, _ = m.load_initial_field()
    kin = m.kinetic_operator(len(psi))
    cases = [("offset", o, background + o, 0.3) for o in OFFSETS] + [("kappa", k, background, k) for k in KAPPAS]
    rows = []
    for family, value, bg, kappa in cases:
        for n in range(1, N_MAX + 1):
            _, s, _ = m.run_case("trace", psi, bg, kappa, 0.5, kin, n)
            res = max(s["final_update_residual"], s["fixed_point_residual"], s["final_eigen_residual"],
                      s["potential_sourcing_residual"])
            rows.append({"family": family, "value": value, "n": n, "max_residual": res,
                         "converged": bool(s["converged"])})
    OUT.parent.mkdir(exist_ok=True)
    with OUT.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


if __name__ == "__main__":
    main()
