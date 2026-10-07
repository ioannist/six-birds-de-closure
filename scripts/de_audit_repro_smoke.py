#!/usr/bin/env python3
"""Third-party DE-audit B1 smoke refit without requiring CLASS/classy."""

from __future__ import annotations

import argparse
import csv
import json
import os
from pathlib import Path

import numpy as np

from scripts import de_audit_run as audit


for _name in ["OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"]:
    os.environ.setdefault(_name, "1")


def read_frozen(results_dir: Path) -> dict[str, dict[str, str]]:
    with (results_dir / "B1_model_table.csv").open(newline="", encoding="utf-8") as handle:
        return {row["model"]: row for row in csv.DictReader(handle)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=Path("results/DE_audit_repro/b1_smoke_no_classy.json"))
    parser.add_argument("--frozen-results", type=Path, default=Path("results/DE_audit"))
    parser.add_argument("--tolerance-chi2", type=float, default=5.0)
    args = parser.parse_args()

    planck, bao, sn = audit.load_blocks()
    blocks = [planck, bao, sn]
    frozen = read_frozen(args.frozen_results)
    rows = []
    ok = True
    for model in ["lcdm", "rewrite_power"]:
        fit = audit.fit_model(model, "joint_smoke", blocks)
        frozen_chi2 = float(frozen[model]["chi2"])
        delta = float(fit.chi2 - frozen_chi2)
        within = bool(np.isfinite(delta) and abs(delta) <= args.tolerance_chi2)
        ok = ok and within
        rows.append(
            {
                "model": model,
                "smoke_chi2": fit.chi2,
                "frozen_chi2": frozen_chi2,
                "delta_chi2": delta,
                "tolerance_chi2": args.tolerance_chi2,
                "within_tolerance": within,
                "params": fit.params,
            }
        )
    payload = {
        "purpose": "Reduced optimizer smoke of B1 compressed likelihood without classy/class/clik imports",
        "backend": "scipy_compressed",
        "classy_required": False,
        "rows": rows,
        "passes": ok,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"passes": ok, "rows": rows}, sort_keys=True))
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
