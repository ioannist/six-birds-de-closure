#!/usr/bin/env python3
"""Exact local review of the imported finite graph and a scale-price repair.

The imported edge table supplies a declared carrier. This implementation does
not import its min-cut or max-flow routines. All arithmetic is Fraction; cuts
are exhaustively enumerated and flow witnesses are independently constructed.
This verifies a finite graph, not continuum RT or a physical Lambda bridge.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / "six-birds-sm-qm-gr/review_2026/repairs/q5_lp_duality"
LABELS = tuple(f"{side}{i}" for side in ("L", "R") for i in range(4))
INTERIOR = ("L", "R", "M0", "M1", "M2")
# These are new declared repair coordinates/constraints, fixed before cut evaluation.
THROUGHPUT_CEILING = Fraction(10)
SCALE_BUDGETS = (Fraction(0), Fraction(1, 2), Fraction(1), Fraction(3, 2))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def cut_rows(edges, capacities, mask):
    fixed_side = {label: bool(mask & (1 << i)) for i, label in enumerate(LABELS)}
    rows = []
    for values in itertools.product((False, True), repeat=len(INTERIOR)):
        side = fixed_side | dict(zip(INTERIOR, values))
        incidence = tuple(int(side[u] != side[v]) for u, v in edges)
        cost = sum((c * y for c, y in zip(capacities, incidence)), Fraction())
        rows.append((cost, side, incidence))
    return sorted(rows, key=lambda row: row[0])


def endpoints(edges, mask):
    def node(v):
        if v not in LABELS:
            return v
        return "source" if mask & (1 << LABELS.index(v)) else "sink"
    return [(node(u), node(v)) for u, v in edges]


def construct_flow(edges, capacities, mask):
    """Signed-edge residual augmentation using depth-first paths."""
    ends = endpoints(edges, mask)
    flow = [Fraction() for _ in edges]
    adjacency = {v: [] for v in ("source", "sink", *INTERIOR)}
    for i, (u, v) in enumerate(ends):
        if u != v:
            adjacency[u].append((v, i, 1))
            adjacency[v].append((u, i, -1))
    augmentations = 0
    while True:
        pending = [("source", ())]
        visited = {"source"}
        path = None
        while pending:
            vertex, route = pending.pop()
            if vertex == "sink":
                path = route
                break
            for neighbor, i, sign in adjacency[vertex]:
                if neighbor not in visited and capacities[i] - sign * flow[i] > 0:
                    visited.add(neighbor)
                    pending.append((neighbor, (*route, (i, sign))))
        if path is None:
            return flow, augmentations
        delta = min(capacities[i] - sign * flow[i] for i, sign in path)
        for i, sign in path:
            flow[i] += sign * delta
        augmentations += 1
        require(augmentations < 1000, "finite carrier augmentation guard exceeded")


def verify_flow(edges, capacities, mask, flow):
    require(len(flow) == len(edges) == len(capacities), "wrong flow dimensions")
    balance = {v: Fraction() for v in ("source", "sink", *INTERIOR)}
    for (u, v), c, f in zip(endpoints(edges, mask), capacities, flow):
        require(abs(f) <= c, "capacity violation")
        balance[u] += f
        balance[v] -= f
    require(all(balance[v] == 0 for v in INTERIOR), "interior conservation violation")
    require(balance["source"] == -balance["sink"] >= 0, "terminal conservation violation")
    return balance["source"]


def verify_controller(A, Q, B, x, r, price, coupling, ceiling):
    require(x >= 0 and r >= 0 and x <= B and r <= A*x and r <= Q, "controller infeasible")
    require(min(price, coupling, ceiling) >= 0, "negative multiplier")
    require(price == coupling*A and coupling+ceiling == 1, "stationarity violation")
    require(price*(B-x) == coupling*(A*x-r) == ceiling*(Q-r) == 0,
            "complementarity violation")
    require(r == min(A*B, Q), "not the constructed optimum")


def recompute(source: Path):
    edge_rows = load_csv(source / "q5_carrier_edges.csv")
    require([int(row["edge_index"]) for row in edge_rows] == list(range(14)), "edge order mismatch")
    edges = [tuple(row["edge"].split("--")) for row in edge_rows]
    capacities = [Fraction(row["capacity"]) for row in edge_rows]
    require(all(c > 0 for c in capacities), "nonpositive capacity")
    require(set(v for edge in edges for v in edge) == set(LABELS+INTERIOR), "vertex set mismatch")
    imported = {int(row["region_mask"]): row for row in load_csv(source / "q5_region_duality.csv")}
    require(set(imported) == set(range(1, 255)), "region table incomplete")
    imported_prices = {(int(row["region_mask"]), int(row["edge_index"])): row
                       for row in load_csv(source / "q5_edge_shadow_prices.csv")}
    require(set(imported_prices) == set(itertools.product(range(1, 255), range(14))),
            "price table incomplete")
    solutions = {m: cut_rows(edges, capacities, m) for m in range(1, 255)}
    margin = min(rows[1][0]-rows[0][0] for rows in solutions.values())
    require(margin > 0, "base cut not unique")
    epsilon = min(margin/4, min(capacities)/4)
    certificates = []
    sensitivity_checks = 0
    homogeneity_checks = 0
    weak_duality_checks = 0
    augmentation_count = 0
    for mask, cuts in solutions.items():
        A, side, incidence = cuts[0]
        reference = imported[mask]
        require(A == Fraction(reference["minimum_cut"]) == Fraction(reference["primal_max_flow"])
                == Fraction(reference["dual_optimum"]), "source scalar mismatch")
        require(cuts[1][0]-A == Fraction(reference["margin_to_second_cut"]), "source margin mismatch")
        flow, iterations = construct_flow(edges, capacities, mask)
        augmentation_count += iterations
        require(verify_flow(edges, capacities, mask, flow) == A, "primal/cut gap")
        for cost, candidate_side, _ in cuts:
            net = sum((f*(int(candidate_side[u])-int(candidate_side[v]))
                       for (u, v), f in zip(edges, flow)), Fraction())
            require(net == A <= cost, "weak-duality/cut bridge violation")
            weak_duality_checks += 1
        require(sum((c*y for c,y in zip(capacities, incidence)), Fraction()) == A,
                "dual/cut gap")
        for i, ((u,v), c, f, y) in enumerate(zip(edges, capacities, flow, incidence)):
            if y:
                require(f == c*(int(side[u])-int(side[v])), "cut edge not saturated")
            plus = min(cost+epsilon*inc[i] for cost, _, inc in cuts)
            minus = min(cost-epsilon*inc[i] for cost, _, inc in cuts)
            require(plus == A+epsilon*y and minus == A-epsilon*y, "cut sensitivity mismatch")
            row = imported_prices[mask, i]
            require(Fraction(row["y_e"]) == Fraction(row["central_difference_exact"]) == y,
                    "source edge price mismatch")
            sensitivity_checks += 1
        for B in SCALE_BUDGETS:
            scaled = cut_rows(edges, [B*c for c in capacities], mask)
            require(scaled[0][0] == B*A, "homogeneity violation")
            require(verify_flow(edges, [B*c for c in capacities], mask, [B*f for f in flow]) == B*A,
                    "scaled flow/cut bridge violation")
            homogeneity_checks += 1
        Q = THROUGHPUT_CEILING
        require(0 < A < Q, "declared ceiling does not give the requested active base regime")
        verify_controller(A, Q, Fraction(1), Fraction(1), A, A, Fraction(1), Fraction(0))
        # A separately added ceiling supplies an actual slack-budget regime.
        slack_budget = Q/A+1
        verify_controller(A, Q, slack_budget, Q/A, Q, Fraction(0), Fraction(0), Fraction(1))
        require(Q/A < slack_budget, "slack regime not strict")
        require(verify_flow(edges, [Q/A*c for c in capacities], mask, [Q/A*f for f in flow]) == Q,
                "ceiling throughput not realized by a graph flow")
        # At the kink, prices 0,A/2,A all certify the same optimizer.
        for price in (Fraction(0), A/2, A):
            verify_controller(A, Q, Q/A, Q/A, Q, price, price/A, 1-price/A)
        certificates.append({"region_mask": mask, "area": str(A),
                             "interior_source_side": [v for v in INTERIOR if side[v]],
                             "edge_prices": list(incidence), "oriented_flow": list(map(str, flow)),
                             "margin": str(cuts[1][0]-A), "active_unit_scale_price": str(A),
                             "slack_budget": str(slack_budget), "slack_price": "0"})
    # Controls challenge real certificate constraints, not a metadata field.
    broken = [Fraction() for _ in capacities]
    broken[0] = 2*capacities[0]
    try:
        verify_flow(edges, capacities, 1, broken)
    except ValueError as error:
        require(str(error) == "capacity violation", "capacity control failed for another reason")
        capacity_control_rejected = True
    else:
        raise ValueError("invalid flow unexpectedly accepted")
    flow, _ = construct_flow(edges, capacities, 1)
    flow[4] += min(capacities)/100
    try:
        verify_flow(edges, capacities, 1, flow)
    except ValueError as error:
        require(str(error) == "interior conservation violation", "conservation control failed for another reason")
        conservation_control_rejected = True
    else:
        raise ValueError("nonconserving flow unexpectedly accepted")
    # Explicit same-throughput/different-price coordinate control from Lean.
    verify_controller(Fraction(3), Fraction(10), Fraction(1), Fraction(1), Fraction(3),
                      Fraction(3), Fraction(1), Fraction(0))
    verify_controller(Fraction(3,2), Fraction(10), Fraction(2), Fraction(2), Fraction(3),
                      Fraction(3,2), Fraction(1), Fraction(0))
    inputs = [source / name for name in ("q5_carrier_edges.csv", "q5_region_duality.csv",
                                        "q5_edge_shadow_prices.csv", "q5_composition_probe.csv",
                                        "q5_lp_duality.py", "q5_results.json")]
    inputs += [Path(__file__), ROOT / "lean/SbtCosmo/Derivation/CapacityScale.lean",
               ROOT / "lean/SbtCosmo/Derivation/TensorComposition.lean"]
    return {
        "baseline_commit": "903d007",
        "scope": "exact finite graph LP/cut verification; explicit common-scale repair with an added ceiling",
        "no_continuum_or_physical_lambda_claim": True,
        "imported_carrier": {"labels": LABELS, "interior": INTERIOR,
                             "edges": [[u,v,str(c)] for (u,v),c in zip(edges, capacities)]},
        "declared_ceiling": str(THROUGHPUT_CEILING),
        "declared_scale_budgets": list(map(str, SCALE_BUDGETS)),
        "regions": len(certificates), "cuts_per_region": 32,
        "primal_dual_cut_certificates": certificates,
        "weak_duality_checks": weak_duality_checks,
        "edge_price_checks": sensitivity_checks,
        "homogeneity_checks": homogeneity_checks,
        "augmentations": augmentation_count,
        "capacity_control_rejected": capacity_control_rejected,
        "conservation_control_rejected": conservation_control_rejected,
        "global_unique_cut_margin": str(margin), "sensitivity_epsilon": str(epsilon),
        "area_bounds": [str(min(rows[0][0] for rows in solutions.values())),
             str(max(rows[0][0] for rows in solutions.values()))],
        "tensor_counterexample": {"input_squared_weights": ["3/4", "1/4"],
                                  "contraction_mass": "5/8", "output_squared_weights": ["9/10", "1/10"],
                                  "status": "strict entropy inequality proved in Lean, not a floating comparison"},
        "input_sha256": {str(p.relative_to(ROOT.parent)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in inputs},
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-dir", type=Path, default=SOURCE)
    parser.add_argument("--outdir", type=Path, default=ROOT / "results/imported_duality_2026-10-02")
    args = parser.parse_args()
    receipt = recompute(args.source_dir)
    args.outdir.mkdir(parents=True, exist_ok=True)
    (args.outdir / "receipt.json").write_text(json.dumps(receipt, indent=2, allow_nan=False)+"\n")
    print(json.dumps({k: receipt[k] for k in ("regions", "weak_duality_checks", "edge_price_checks",
                                             "homogeneity_checks", "area_bounds")}))


if __name__ == "__main__":
    main()
