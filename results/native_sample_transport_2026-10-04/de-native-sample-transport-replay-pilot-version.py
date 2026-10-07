"""Read-only exact replay of the ten additional original-seed transports.

This checks rational certificate arithmetic and source rendering. It does not
replace Lean checking, prove IEEE execution, or assert a completed seed return.
The data directory may be the private construction directory or its saved copy.
"""
import argparse
import concurrent.futures
import hashlib
import json
import re
from fractions import Fraction as F
from pathlib import Path

import de_ground_native_prefix_generate as g
import de_ground_basin_generate as jets
from de_ground_offset_basin_generate import source
from de_ground_offset_transport_render import render_step

ROOT = Path(__file__).resolve().parents[1]
J = g.J
SAMPLES = {"cycle20": (10, 320), "cycle30": (11, 152)} | {
    f"stable{i:03d}": (i, 178 if i == 9 else 60)
    for i in [1, 3, 4, 5, 6, 7, 8, 9]
}
COUPLINGS = [F.from_float(x) for x in [0., .1, .3, .5, 1., 2., 3., 5., 10., 15., 20., 30.]]
TAU = F.from_float(1e-10)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def literal_vector(text, name, size):
    body = text.split(f"def {name} : Fin {size} → ℚ := ![", 1)[1].split("]", 1)[0]
    result = [F(x.strip().strip("()")) for x in body.split(",")]
    assert len(result) == size
    return result


def literal_matrix(text, name):
    body = text.split(f"def {name} : QMatrix := ", 1)[1].split("]]", 1)[0] + "]]"
    result = [[F(x.strip().strip("()")) for x in row.split(",")]
              for row in re.findall(r"!\[([^\[\]]*)\]", body)]
    assert len(result) == 8 and all(len(row) == 8 for row in result)
    return result


def contains(cap, value):
    assert cap.lo <= value.lo and value.hi <= cap.hi


def rows(matrix):
    return max(sum(t.bound() for t in row) for row in matrix)


def bound_step(d, beta, k, x, y):
    assert d["input_re"] == [t.pair() for t in x]
    assert d["input_im"] == [t.pair() for t in y]
    z = list(map(F, d["center"])); r = F(d["radius"])
    c = [list(map(F, row)) for row in d["inverse"]]
    assert len(z) == len(c) == 9 and all(len(row) == 9 for row in c)
    q = F(d["rate"]); a = F(d["residual_budget"])
    g.root_checks(source(beta, k, x, y), z, r, c, q, a)
    ground = [J(t-r, t+r) for t in z[:8]]
    phase = J.read(d["overlap_inverse"]); norm = J.read(d["mixed_inverse"])
    overlap, mr, mi, mixed_norm = g.update(x, y, ground, phase)
    for value, inverse in [(overlap, phase), (mixed_norm, norm)]:
        assert value.lo > TAU*TAU and inverse.lo > 0
        assert inverse.lo**2 * value.hi <= 1 <= inverse.hi**2 * value.lo
    output = list(map(J.read, d["output_re"] + d["output_im"]))
    assert len(output) == 16
    for cap, raw in zip(output, mr+mi):
        contains(cap, norm*raw)
    return ground, c, q, phase, norm, output


def replay_one(tag, directory, lean_directory):
    sample, count = SAMPLES[tag]
    if tag.startswith("cycle"):
        klabel = tag[5:]
        path = directory / f"de_native_cycle_seed_transport_{klabel}.json"
        frame_path = lean_directory / f"NativeCycleFrame{klabel}.lean"
        frame_text = frame_path.read_text()
        prefix = f"NativeCycleSeed{klabel}"
        frame = f"NativeCycleFrame{klabel}"
        target_path = lean_directory / f"NativeCycle{klabel}Step000.lean"
        target_text = target_path.read_text()
        target_re = literal_vector(target_text, "u", 8)
        target_im = literal_vector(target_text, "v", 8)
        target_radius = F(target_text.split("def ρ : ℚ := ", 1)[1].splitlines()[0].strip().strip("()"))
    else:
        klabel = tag[6:]
        path = directory / f"de-native-stable-seed-{klabel}-transport.json"
        frame_path = ROOT / f"lean/SbtCosmo/Derivation/GroundCoordinates/Point{klabel}.lean"
        frame_text = frame_path.read_text()
        prefix = f"NativeStableSeed{klabel}"
        frame = f"NativeStableFrame{klabel}"
        target_path = ROOT / f"lean/SbtCosmo/Derivation/GroundSamples/Point{klabel}.lean"
        target_text = target_path.read_text()
        target_re = literal_vector(target_text, "z", 9)[:8]
        target_im = [F(0)]*8
        target_radius = F(1, 100000000)
    p = json.loads(path.read_text())
    if tag.startswith("stable"):
        assert p["sample_index"] == sample
        assert list(map(F, p["root_reference"][:8])) == target_re
        root_radius = F(target_text.split("def r : ℚ := ", 1)[1].splitlines()[0].strip().strip("()"))
        assert F(p["root_radius"]) == root_radius
    k = F(p["coupling"]); assert k == COUPLINGS[sample]
    assert len(p["steps"]) == count and len(p["references"]) == count+1
    assert len(p["pair_blocks"]) == count//2
    assert F(p["radius"]) == target_radius
    field_data = json.loads(g.DATA.read_text())
    background = list(map(F, p["background"]))
    assert background == [F.from_float(t) for t in field_data["potential"]]
    beta = list(map(J, background))
    s, inv_s, r, inv_r = [literal_matrix(frame_text, key) for key in ["S", "P", "R", "Q"]]
    for key, matrix in zip(["S", "P", "R", "Q"], [s, inv_s, r, inv_r]):
        assert [[F(t) for t in row] for row in p[key]] == matrix
    for a, b in [(s, inv_s), (inv_s, s), (r, inv_r), (inv_r, r)]:
        assert all(sum(a[i][l]*b[l][j] for l in range(8)) == int(i == j)
                   for i in range(8) for j in range(8))
    basis = F(p["basis_budget"])
    assert basis >= max(sum(abs(t) for t in row) for row in s+r)
    refs = [(list(map(F, t["re"])), list(map(F, t["im"]))) for t in p["references"]]
    assert all(len(x) == len(y) == 8 for x, y in refs)
    initial_path = ROOT / "results/ground_offset_prefix_2026-10-04/witnesses.json"
    initial = json.loads(initial_path.read_text())["points"][0]["steps"][0]
    x, y = refs[0]
    initial_error = jets.matvec(inv_s, [J.read(t)-v for t, v in zip(initial["input_re"], x)])
    initial_error += jets.matvec(inv_r, [J.read(t)-v for t, v in zip(initial["input_im"], y)])
    delta = F(p["initial_radius"])
    assert delta >= max(t.bound() for t in initial_error)
    matrices = []; source_hashes = {}
    for n, d in enumerate(p["steps"]):
        assert d["index"] == n and F(d["radius"]) == delta
        x, y = refs[n]; nx, ny = refs[n+1]
        *_, point_output = bound_step(d["point"], beta, k, list(map(J, x)), list(map(J, y)))
        defect = F(d["defect"]); assert defect >= 0
        difference = jets.matvec(inv_s, [t-v for t, v in zip(point_output[:8], nx)])
        difference += jets.matvec(inv_r, [t-v for t, v in zip(point_output[8:], ny)])
        assert max(t.bound() for t in difference) <= defect
        x_box = [J(t-basis*delta, t+basis*delta) for t in x]
        y_box = [J(t-basis*delta, t+basis*delta) for t in y]
        ground, c, q, phase, norm, _ = bound_step(d["whole"], beta, k, x_box, y_box)
        columns = []
        for j in range(16):
            dg = list(map(J.read, d["DG"][j]))
            fr = list(map(J.read, d["DF"][j][0])); fi = list(map(J.read, d["DF"][j][1]))
            yy = F(d["response_y"][j]); ee = F(d["response_error"][j])
            *_, raw_dg, _, _ = jets.derivative(beta, k, x_box, y_box, ground, c, q, phase, norm, j, s, r, yy, ee)
            for cap, raw in zip(dg, raw_dg): contains(cap, raw)
            *_, raw_fr, raw_fi = jets.derivative(beta, k, x_box, y_box, ground, c, q, phase, norm, j, s, r, yy, ee, dg)
            for cap, raw in zip(fr+fi, raw_fr+raw_fi): contains(cap, raw)
            columns.append(jets.matvec(inv_s, fr)+jets.matvec(inv_r, fi))
        cache = [[J.read(t) for t in row] for row in d["coordinate_DF"]]
        assert len(cache) == 16 and all(len(row) == 16 for row in cache)
        for i in range(16):
            for j in range(16): contains(cache[i][j], columns[j][i])
        matrices.append(cache)
        rate = F(d["rate"]); next_radius = F(d["next_radius"])
        assert max(sum(columns[j][i].bound() for j in range(16)) for i in range(16)) <= rate
        assert rows(cache) <= rate and rate*delta+defect <= next_radius
        if n % 2 == 0:
            delta = next_radius
        else:
            b = p["pair_blocks"][n//2]; first = p["steps"][n-1]
            assert b["start"] == n-1 and F(b["radius"]) == F(first["radius"])
            assert F(first["next_radius"]) <= F(d["radius"])
            assert F(first["defect"]) <= F(d["radius"])
            pair_cache = [[J.read(t) for t in row] for row in b["DF"]]
            assert len(pair_cache) == 16 and all(len(row) == 16 for row in pair_cache)
            for i in range(16):
                for j in range(16):
                    raw = sum((cache[i][l]*matrices[n-1][l][j] for l in range(16)), J(0))
                    contains(pair_cache[i][j], raw)
            pair_rate = F(b["rate"]); pair_defect = F(b["defect"])
            assert 0 <= pair_rate and rows(pair_cache) <= pair_rate
            assert rate*F(first["defect"])+defect <= pair_defect
            delta = F(b["next_radius"])
            assert pair_rate*F(first["radius"])+pair_defect <= delta
        assert F(d["following_radius"]) == delta
        rendered = render_step(0, p, n)
        rendered = rendered.replace(f"GroundOffsetTransport.Point000.Step{n:03d}", f"{prefix}.Step{n:03d}")
        rendered = rendered.replace("GroundOffsetStability.Point000", frame).replace("GroundOffsets.Point000", frame)
        rendered = rendered.replace("GroundOriginalOffsetBasins.T 0", frame+".T")
        rendered = rendered.replace("import SbtCosmo.Derivation.GroundOriginalOffsetBasins\n", "")
        rendered = rendered.replace("import SbtCosmo.Derivation."+frame+"\n", "import "+frame+"\n")
        seen = set(); lines = []
        for line in rendered.splitlines():
            if line.startswith("import "):
                if line in seen: continue
                seen.add(line)
            lines.append(line)
        rendered = "\n".join(lines)+"\n"
        lean_path = lean_directory / f"{prefix}Step{n:03d}.lean"
        assert lean_path.read_text() == rendered, lean_path
        source_hashes[str(lean_path)] = sha(lean_path)
        if (n+1) % 10 == 0: print(tag, "exact steps", n+1, "/", count, flush=True)
    assert F(p["entry_radius"]) == delta
    x, y = refs[-1]
    if tag.startswith("cycle"):
        endpoint = jets.matvec(inv_s, [J(a-b) for a, b in zip(x, target_re)])
        endpoint += jets.matvec(inv_r, [J(a-b) for a, b in zip(y, target_im)])
    else:
        endpoint = jets.matvec(inv_s, [J(a+b-root_radius, a+b+root_radius) for a, b in zip(x, target_re)])
        endpoint += jets.matvec(inv_r, list(map(J, y)))
    assert max(t.bound() for t in endpoint) <= F(p["center_distance"])
    assert delta+F(p["center_distance"]) <= F(p["entry_bound"]) < target_radius
    return {"sample": tag, "steps": count, "pairs": count//2, "coupling": str(k),
            "exact_arithmetic_replay": True, "read_only_leaf_render_match": True,
            "entry_bound": p["entry_bound"], "entry_radius": p["radius"],
            "payload_sha256": sha(path), "frame_source_sha256": sha(frame_path),
            "target_source_sha256": sha(target_path), "leaf_source_sha256": source_hashes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path, default=Path("/tmp"))
    parser.add_argument("--lean-root", type=Path, default=Path("/tmp/de_native_cycle_lean"))
    parser.add_argument("--only", choices=list(SAMPLES), nargs="+")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(); tags = args.only or list(SAMPLES)
    assert len(tags) == len(set(tags)) and 1 <= args.workers <= 4
    assert not args.output.exists(), args.output
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(replay_one, tag, args.data_root, args.lean_root) for tag in tags]
        results = [future.result() for future in futures]
    files = [Path(__file__), Path(g.__file__), Path(jets.__file__), g.DATA,
             ROOT / "scripts/de_ground_offset_basin_generate.py",
             ROOT / "scripts/de_ground_offset_transport_render.py",
             ROOT / "results/ground_offset_prefix_2026-10-04/witnesses.json"]
    receipt = {"scope": "Rational transport replay and read-only leaf rendering; Lean audits and full original-seed return checking remain separate. No IEEE trace.",
               "all_ten_samples": len(tags) == 10, "samples": results,
               "steps": sum(r["steps"] for r in results), "pairs": sum(r["pairs"] for r in results),
               "source_sha256": {str(p): sha(p) for p in files}, "goal_complete": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+"\n")
    print("Exact native transport replay passed:", len(tags), "samples;", receipt["steps"], "steps;", receipt["pairs"], "pairs.")


if __name__ == "__main__": main()
