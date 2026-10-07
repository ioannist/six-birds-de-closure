"""Static validator for the LOCKED R0 bridge-affinity manifest (data/manifests/r0_bridge_affinities.json).

Per the round-2 external review: the manifest's held-out cycles must be mechanically unambiguous and
anti-circular. This asserts:
  1. every test_cycle is a CLOSED graph cycle (heldout_edges + tree_path_edges form a closed loop);
  2. every DECISIVE-eligible held-out edge has eligible_for_test_cycle=true;
  3. no DECISIVE held-out edge shares a calibration anchor with any tree_path edge in its cycle;
  4. every DECISIVE R0-B held-out edge has edge_type == 'direct_cross_calibration';
  5. excluded cmb_bao / inverse_ladder never appear in routes, edges, or cycles;
plus structural sanity (edge endpoints are declared routes; spanning tree is acyclic; the declared
beta1_decisive_eligible equals the number of decisive_eligible cycles).
"""
import json
import os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MANIFEST = os.path.join(HERE, "data", "manifests", "r0_bridge_affinities.json")


def _load():
    with open(MANIFEST) as fh:
        return json.load(fh)


def _edges_by_id(m):
    return {e["edge_id"]: e for e in m["edges"]}


def _undirected(e):
    return frozenset((e["i"], e["j"]))


def test_valid_json_and_required_blocks():
    m = _load()
    for key in ("routes", "edges", "spanning_tree", "test_cycles", "cycle_availability", "excluded"):
        assert key in m, f"missing top-level block: {key}"


def test_edge_endpoints_are_declared_routes():
    m = _load()
    routes = {r["route_id"] for r in m["routes"]}
    for e in m["edges"]:
        assert e["i"] in routes, f"edge {e['edge_id']} endpoint {e['i']} not a declared route"
        assert e["j"] in routes, f"edge {e['edge_id']} endpoint {e['j']} not a declared route"
        assert e["i"] != e["j"], f"edge {e['edge_id']} is a self-loop"
        assert e["edge_type"] in {"direct_cross_calibration", "route_readout_difference", "TODO-on-fetch-classify"}, \
            f"edge {e['edge_id']} has illegal edge_type {e['edge_type']}"


def test_spanning_tree_is_acyclic_and_connects_its_nodes():
    m = _load()
    by_id = _edges_by_id(m)
    tree_ids = m["spanning_tree"]["edges"]
    nodes, parent = set(), {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    n_edges = 0
    for eid in tree_ids:
        assert eid in by_id, f"spanning_tree references unknown edge {eid}"
        e = by_id[eid]
        assert e.get("eligible_for_tree") is True, f"tree edge {eid} not eligible_for_tree"
        a, b = find(e["i"]), find(e["j"])
        assert a != b, f"spanning tree has a CYCLE at edge {eid}"  # union-find: same root => cycle
        parent[a] = b
        nodes.update((e["i"], e["j"]))
        n_edges += 1
    # a spanning tree over k nodes has exactly k-1 edges and is connected
    assert n_edges == len(nodes) - 1, "spanning tree edge count != nodes-1 (not a tree)"
    roots = {find(x) for x in nodes}
    assert len(roots) == 1, "spanning tree is not connected"


def test_every_test_cycle_is_a_closed_loop():
    m = _load()
    by_id = _edges_by_id(m)
    for c in m["test_cycles"]:
        cyc_edge_ids = list(c["heldout_edges"]) + list(c["tree_path_edges"])
        assert cyc_edge_ids, f"cycle {c['cycle_id']} has no edges"
        deg = {}
        for eid in cyc_edge_ids:
            assert eid in by_id, f"cycle {c['cycle_id']} references unknown edge {eid}"
            for node in _undirected(by_id[eid]):
                deg[node] = deg.get(node, 0) + 1
        # a closed loop (simple cycle or multigraph 2-cycle): every touched node has degree EXACTLY 2
        bad = {n: d for n, d in deg.items() if d != 2}
        assert not bad, f"cycle {c['cycle_id']} is NOT closed; nodes with degree!=2: {bad}"
        assert c.get("structurally_closed") is True, f"cycle {c['cycle_id']} structurally_closed flag wrong"


def test_decisive_eligible_cycles_obey_all_rules():
    m = _load()
    by_id = _edges_by_id(m)
    n_decisive = 0
    for c in m["test_cycles"]:
        if not c.get("decisive_eligible"):
            continue
        n_decisive += 1
        tree_anchor_families = set()
        for eid in c["tree_path_edges"]:
            tree_anchor_families.add(by_id[eid]["anchor_family"])
            tree_anchor_families.update(by_id[eid].get("shares_anchor_with", []))
        for eid in c["heldout_edges"]:
            e = by_id[eid]
            # rule 2: eligible_for_test_cycle
            assert e.get("eligible_for_test_cycle") is True, \
                f"decisive cycle {c['cycle_id']} held-out edge {eid} not eligible_for_test_cycle"
            # rule 4: must be a genuine direct cross-calibration
            assert e["edge_type"] == "direct_cross_calibration", \
                f"decisive cycle {c['cycle_id']} held-out edge {eid} edge_type={e['edge_type']} (must be direct_cross_calibration)"
            # rule 3: anchor-disjoint from every tree-path edge — checked SYMMETRICALLY (either edge
            # declaring the other / a shared family fails), so a one-sided manifest declaration cannot hide it.
            assert e["anchor_family"] not in tree_anchor_families, \
                f"decisive cycle {c['cycle_id']} held-out edge {eid} shares anchor with a tree edge (anti-circularity)"
            tree_edge_ids = set(c["tree_path_edges"])
            # forward: held-out edge declares a tree edge (by id) or a tree anchor_family
            for shared in e.get("shares_anchor_with", []):
                assert shared not in tree_edge_ids and shared not in tree_anchor_families, \
                    f"decisive cycle {c['cycle_id']} held-out edge {eid} shares_anchor_with a tree edge/family ({shared})"
            # symmetric: any tree edge declaring THIS held-out edge (by id) or its anchor_family
            for tid in tree_edge_ids:
                t = by_id[tid]
                shared_t = set(t.get("shares_anchor_with", []))
                assert eid not in shared_t and e["anchor_family"] != t["anchor_family"] \
                    and e["anchor_family"] not in shared_t, \
                    f"decisive cycle {c['cycle_id']} tree edge {tid} shares anchor with held-out edge {eid} (symmetric anti-circularity)"
    # rule: declared beta1_decisive_eligible must equal the count of decisive_eligible cycles
    assert m["cycle_availability"]["beta1_decisive_eligible"] == n_decisive, \
        f"beta1_decisive_eligible={m['cycle_availability']['beta1_decisive_eligible']} != actual {n_decisive}"


def test_excluded_routes_never_appear():
    m = _load()
    forbidden = {"cmb_bao", "inverse_ladder"}
    route_ids = {r["route_id"] for r in m["routes"]}
    assert forbidden.isdisjoint(route_ids), "excluded route present in routes"
    for e in m["edges"]:
        assert e["i"] not in forbidden and e["j"] not in forbidden, f"excluded route in edge {e['edge_id']}"
    # and they must be listed in the excluded block with a reason
    excluded_names = " ".join(str(x.get("route_or_edge", "")) for x in m["excluded"])
    for f in forbidden:
        assert f in excluded_names, f"{f} not documented in excluded block"
