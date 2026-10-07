#!/usr/bin/env python3
"""Exact finite access-fork review; no imported source solver is executed.

The universal mediator theorem is a Lean proof, not enumeration of a finite
competitor list. The numerical source's raw fields are separately reified as
rational complex coefficients and analytically normalized for exact mode tests.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction as F
import hashlib
import itertools
import json
import platform
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / "six-birds-sm-qm-gr"
REPAIR = SOURCE / "review_2026/repairs"
BITS = tuple(itertools.product((0, 1), repeat=4))
QM = (0, 1, 2)
GR = (0, 2, 3)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rows(path):
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def key(state, indices):
    return tuple(state[i] for i in indices)


def obstruction_pairs(source, target):
    return [(a,b) for a,b in itertools.combinations(range(len(source)), 2)
            if source[a] == source[b] and target[a] != target[b]]


def conditional_matrix(indices):
    result = []
    for state in BITS:
        selected = [key(t, indices) == key(state, indices) for t in BITS]
        result.append(tuple(F(1, sum(selected)) if yes else F(0) for yes in selected))
    return tuple(result)


def multiply(left, right):
    return tuple(tuple(sum((v*right[k][j] for k,v in enumerate(row) if v), F(0))
                       for j in range(len(right[0]))) for row in left)


def matrix_readout(matrix, encoding):
    return [tuple(sum((w*encoding(t[i]) for w,t in zip(row, BITS)), F(0))
                  for i in range(4)) for row in matrix]


def table_distance_squared(left, right, encoding):
    a = matrix_readout(left, encoding)
    b = matrix_readout(right, encoding)
    numerator = sum(((x-y)**2 for ar,br in zip(a,b) for x,y in zip(ar,br)), F(0))
    denominator = sum((F(encoding(bit))**2 for s in BITS for bit in s), F(0))
    return numerator/denominator


def parse_distribution(text):
    result = [F(0) for _ in BITS]
    for item in text.split("|"):
        index,value = item.split(":")
        result[int(index)] = F(value)
    return tuple(result)


def rational_mode(psi, background, coupling):
    # Reify raw IEEE values; analytic normalization cancels its square root in
    # density, current and gradient energy. No floating operations follow here.
    re = [F.from_float(float(x.real)) for x in psi]
    im = [F.from_float(float(x.imag)) for x in psi]
    bg = [F.from_float(float(x)) for x in background]
    norm2 = sum((a*a+b*b for a,b in zip(re,im)), F(0))
    require(norm2 > 0, "zero field")
    rho = [(a*a+b*b)/norm2 for a,b in zip(re,im)]
    gr = [(re[(i+1)%8]-re[(i-1)%8])/2 for i in range(8)]
    gi = [(im[(i+1)%8]-im[(i-1)%8])/2 for i in range(8)]
    current = [(re[i]*gi[i]-im[i]*gr[i])/norm2 for i in range(8)]
    effective = [bg[i]+coupling*((gr[i]**2+gi[i]**2)/norm2+bg[i]*rho[i]) for i in range(8)]
    require(sum(rho, F(0)) == 1, "normalization failed")
    peak = lambda values: max(range(8), key=lambda i: values[i])
    mode = (1, int(sum(current, F(0)) >= 0), peak(rho), peak(effective))
    return mode, rho, current, effective


def field_population():
    steps = SOURCE / "physics_atlas/thread_qm_gr/steps"
    field_path = steps / "step24_derived_physical_audits_artifacts/toy_field_samples_step24.json"
    history_path = steps / "step28_nonstationary_relational_histories_artifacts/nonstationary_history_step28.json"
    field_data = json.loads(field_path.read_text())
    history_data = json.loads(history_path.read_text())
    bg = np.asarray(field_data["potential"], dtype=float)
    population = []
    for r in field_data["fields"]:
        psi = np.asarray(r["psi_re"], dtype=float)+1j*np.asarray(r["psi_im"], dtype=float)
        population.append((f"step25_{int(r['sample']):03d}", psi, bg.copy()))
    for r in history_data["states"]:
        psi = np.asarray(r["psi_re"], dtype=float)+1j*np.asarray(r["psi_im"], dtype=float)
        population.append((f"step28_t{int(r['clock_t']):02d}", psi, bg.copy()))
    rng = np.random.default_rng(71017)
    for i in range(8):
        psi = rng.normal(size=8)+1j*rng.normal(size=8)
        population.append((f"fresh_seeded_{i:02d}", psi, bg.copy()))
    phase = rng.normal(size=8)+1j*rng.normal(size=8)
    population.extend([("control_phase_original",phase,bg.copy()),
                       ("control_phase_conjugate",np.conjugate(phase),bg.copy())])
    potential_field = rng.normal(size=8)+1j*rng.normal(size=8)
    base_mode,_,_,_ = rational_mode(potential_field, bg, F(3,10))
    target = (base_mode[3]+3)%8
    perturbed = bg.copy()
    perturbed[target] += 5.0
    population.extend([("control_potential_base",potential_field,bg.copy()),
                       ("control_potential_perturbed",potential_field,perturbed)])
    return population, [field_path, history_path]


def recompute():
    subsets = [tuple(i for i in range(4) if mask & (1<<i)) for mask in range(16)]
    name = lambda subset: "P_"+"_".join(f"d{i}" for i in subset) if subset else "P_empty"
    keys = {name(s):[key(x,s) for x in BITS] for s in subsets}
    catalog = {r["partition_id"]:r for r in rows(REPAIR / "q1_access_provenance/q1_partition_catalog.csv")}
    require(set(catalog) == set(keys), "partition catalog mismatch")
    for subset in subsets:
        r = catalog[name(subset)]
        require(int(r["block_count"]) == len(set(keys[name(subset)])) == 2**len(subset), "block count mismatch")
        require(int(r["fiber_size"]) == 2**(4-len(subset)), "fiber size mismatch")
    pair_rows = rows(REPAIR / "q1_access_provenance/q1_partition_pair_exhaustion.csv")
    require(len(pair_rows)==120, "pair table incomplete")
    require(len({frozenset((r["partition_A"],r["partition_B"])) for r in pair_rows}) == 120,
            "partition pair duplicates")
    incomparable = 0
    for r in pair_rows:
        a,b = keys[r["partition_A"]],keys[r["partition_B"]]
        forward,reverse = obstruction_pairs(a,b),obstruction_pairs(b,a)
        require(len(forward)==int(r["A_to_B_defect_pairs"]) and len(reverse)==int(r["B_to_A_defect_pairs"]), "partition defect mismatch")
        require((not forward)==(r["A_determines_B"]=="True") and (not reverse)==(r["B_determines_A"]=="True"), "factorization mismatch")
        incomparable += bool(forward and reverse)
    require(incomparable==55, "incomparable count mismatch")
    q,g = [key(s,QM) for s in BITS],[key(s,GR) for s in BITS]
    require(len(obstruction_pairs(q,g))==len(obstruction_pairs(g,q))==8, "endpoint defects mismatch")
    require(len(set(zip(q,g)))==16, "joint access not injective")
    matrices = {s:conditional_matrix(s) for s in subsets}
    completion_pairs = 0
    for a,b in itertools.product(subsets, repeat=2):
        expected = matrices[tuple(i for i in a if i in b)]
        require(multiply(matrices[a],matrices[b]) == expected, "coordinate mean composition mismatch")
        completion_pairs += 1
    qm,gr = matrices[QM], matrices[GR]
    matrix_rows = [r for r in rows(REPAIR / "q2_route_mismatch/q2_completion_matrices.csv")
                   if r["pair_id"] == "published_coordinate_pair"]
    expected_rows = set(itertools.product(("E_QM_visible_d0_d1_d2", "E_GR_visible_d0_d2_d3"),range(16)))
    require(len(matrix_rows) == 32 and
            {(r["completion"],int(r["row_index"])) for r in matrix_rows} == expected_rows,
            "published completion rows incomplete")
    for r in matrix_rows:
        actual = qm if r["completion"] == "E_QM_visible_d0_d1_d2" else gr
        require(actual[int(r["row_index"])] == parse_distribution(r["exact_distribution"]), "source matrix mismatch")
    unsigned_distance = table_distance_squared(qm,gr,lambda x:x)
    signed_distance = table_distance_squared(qm,gr,lambda x:2*x-1)
    require(unsigned_distance==F(1,4) and signed_distance==F(1,2), "recoding-distance control mismatch")
    # Encoding all sixteen records as one symbol preserves access. Dropping a
    # coordinate fails at least one endpoint. The Lean theorem covers all maps.
    candidate_rows = []
    for label,record in [("identity",BITS),
                         ("xor_memory",[s[:3]+(s[1]^s[3],) for s in BITS]),
                         ("single_symbol",list(range(16))),
                         ("qm_only",q),("gr_only",g)]:
        forward,reverse=obstruction_pairs(record,q),obstruction_pairs(record,g)
        candidate_rows.append({"mediator":label,"distinct_records":len(set(record)),
                               "determines_qm":not forward,"determines_gr":not reverse})
    population,inputs = field_population()
    imported = {r["state_id"]:r for r in rows(REPAIR / "q1_access_provenance/q1_field_modes.csv")}
    require(len(population)==len(imported)==54, "field population mismatch")
    exact_records = []
    exact_audits = {}
    for identity,psi,bg in population:
        mode,rho,current,potential = rational_mode(psi,bg,F(3,10))
        binary_mode,_,_,_ = rational_mode(psi,bg,F.from_float(0.3))
        columns=("d0_norm","d1_current_orientation","d2_density_peak","d3_geometry_peak")
        require(mode==tuple(int(imported[identity][c]) for c in columns)==binary_mode, "exact/source mode mismatch: "+identity)
        exact_records.append({"state_id":identity,"mode":list(mode),"current_total":str(sum(current,F(0))),
                              "raw_field_hex":{"real":[float(x.real).hex() for x in psi],
                                               "imag":[float(x.imag).hex() for x in psi],
                                               "background":[float(x).hex() for x in bg]}})
        exact_audits[identity]=(rho,current,potential,mode)
    pa,pb = exact_audits["control_phase_original"],exact_audits["control_phase_conjugate"]
    require(pa[0]==pb[0] and pa[2]==pb[2] and pa[1]==[-x for x in pb[1]] and pa[3][1]!=pb[3][1], "conjugate witness invalid")
    va,vb = exact_audits["control_potential_base"],exact_audits["control_potential_perturbed"]
    require(va[0]==vb[0] and va[1]==vb[1] and va[3][3]!=vb[3][3], "potential witness invalid")
    field_modes = [tuple(r["mode"]) for r in exact_records]
    fq,fg = [key(s,QM) for s in field_modes],[key(s,GR) for s in field_modes]
    require(len(set(field_modes))==15 and len(set(fq))==14 and len(set(fg))==10, "realized image mismatch")
    require(len(obstruction_pairs(fq,fg))==5 and len(obstruction_pairs(fg,fq))==32, "field factorization mismatch")
    # Actual field-cell multiplicities induce a nonproduct conditional-mean block.
    mode_cells = sorted(set(field_modes))
    multiplicity = [field_modes.count(s) for s in mode_cells]
    def cell_matrix(indices, cells=mode_cells, weights=multiplicity):
        return tuple(tuple(F(w,sum(weights[k] for k,t in enumerate(cells)
                                  if key(s,indices)==key(t,indices)))
                           if key(s,indices)==key(t,indices) else F(0)
                           for t,w in zip(cells,weights)) for s in cells)
    field_qm,field_gr = cell_matrix(QM),cell_matrix(GR)
    require(multiply(field_qm,field_qm)==field_qm and multiply(field_gr,field_gr)==field_gr,
            "field conditionals not idempotent")
    field_forward,field_reverse = multiply(field_qm,field_gr),multiply(field_gr,field_qm)
    block = [i for i,s in enumerate(mode_cells) if s[2]==4]
    require([mode_cells[i] for i in block] == [(1,0,4,0),(1,0,4,3),(1,1,4,0)] and
            [multiplicity[i] for i in block] == [5,1,3], "field block bridge mismatch")
    i,j = block[:2]
    require(field_forward[i][j]==F(1,6) and field_reverse[i][j]==F(5,48), "block commutator mismatch")
    require(field_forward[i][j]-field_reverse[i][j]==F(1,16), "commutator not the checked Lean value")
    field_defect_indices = [i for i in range(len(mode_cells)) if field_forward[i]!=field_reverse[i]]
    require(field_defect_indices == block, "field defect support mismatch")
    full_qm = cell_matrix(QM,field_modes,[1]*54)
    full_gr = cell_matrix(GR,field_modes,[1]*54)
    raw_forward,raw_reverse = multiply(full_qm,full_gr),multiply(full_gr,full_qm)
    indicator = [int(s==mode_cells[j]) for s in field_modes]
    def readout(row):
        return sum((a*b for a,b in zip(row,indicator)),F(0))
    for n,s in enumerate(field_modes):
        row = mode_cells.index(s)
        require(readout(raw_forward[n])==field_forward[row][j] and
                readout(raw_reverse[n])==field_reverse[row][j], "record/cell completion bridge mismatch")
    raw_defect_rows = [n for n in range(54) if raw_forward[n]!=raw_reverse[n]]
    require(len(raw_defect_rows)==9 and all(field_modes[n][2]==4 for n in raw_defect_rows),
            "record-level defect support mismatch")
    # Remove the potential-only perturbation, rather than changing an output flag.
    reduced_modes = [tuple(r["mode"]) for r in exact_records
                     if r["state_id"] != "control_potential_perturbed"]
    reduced_cells = sorted(set(reduced_modes))
    reduced_weights = [reduced_modes.count(s) for s in reduced_cells]
    reduced_qm = cell_matrix(QM,reduced_cells,reduced_weights)
    reduced_gr = cell_matrix(GR,reduced_cells,reduced_weights)
    require(multiply(reduced_qm,reduced_gr)==multiply(reduced_gr,reduced_qm),
            "potential-control ablation did not restore commutation")
    field_block = {"mode_cells":[list(s) for s in mode_cells],"multiplicities":multiplicity,
                   "density4_block_indices":block,"weights":[5,1,3],
                   "field_operators_idempotent":True,"defect_mode_cell_count":len(block),
                   "defect_raw_record_count":sum(multiplicity[i] for i in block),
                   "full_54_record_operator_bridge_checked":True,
                   "potential_control_ablation_commutes":True,
                   "requires_the_potential_only_control":True,
                   "forward_indicator_value":"1/6","reverse_indicator_value":"5/48","commutator_value":"1/16"}
    inputs += [REPAIR / relative for relative in [
        "q1_access_provenance/q1_field_modes.csv", "q1_access_provenance/q1_provenance_checks.csv",
        "q1_access_provenance/q1_partition_catalog.csv", "q1_access_provenance/q1_partition_pair_exhaustion.csv",
        "q1_access_provenance/q1_access_provenance.py", "q2_route_mismatch/q2_completion_matrices.csv",
        "q2_route_mismatch/q2_route_mismatch.py"]]
    inputs += [Path(__file__),ROOT / "lean/SbtCosmo/Derivation/AccessFork.lean",
               ROOT / "lean/SbtCosmo/Derivation/FieldAccessBlock.lean"]
    return {"baseline_commit":"4430aea","environment":{"python":platform.python_version(),"numpy":np.__version__},"scope":"declared finite access maps; no physical QM/GR or vacuum-discrepancy bridge",
            "universal_mediator_theorem":"kernel-checked full-state recovery and injectivity; not inferred from tested candidates",
            "boolean_carrier_states":16,"coordinate_partitions":16,"unordered_partition_pairs":120,
            "incomparable_pairs":55,"directed_endpoint_defect_counts":[8,8],
            "exact_coordinate_completion_pair_checks":completion_pairs,
            "original_commutator_zero":True,"table_distance_squared":{
                "zero_one":str(unsigned_distance),"plus_minus_one":str(signed_distance)},
            "encoding_controls":candidate_rows,
            "field_reification":{"method":"raw IEEE complex inputs reified rationally, analytic normalization; both exact 3/10 and reified machine coupling agree on every label",
                "records":54,"distinct_full_mode_tuples":15,"mode_marginal_sizes":[1,2,8,3],
                "qm_fibers":14,"gr_fibers":10,"directed_defect_counts":[5,32],
                "phase_and_potential_controls_exact":True,"exact_records":exact_records},
            "new_field_carrier_noncommuting_block":field_block,
            "input_sha256":{str(p.relative_to(ROOT.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--outdir",type=Path,default=ROOT / "results/access_fork_2026-10-02")
    args=parser.parse_args();receipt=recompute()
    args.outdir.mkdir(parents=True,exist_ok=True)
    (args.outdir / "receipt.json").write_text(json.dumps(receipt,indent=2,allow_nan=False)+"\n")
    summary = {k:receipt[k] for k in ["boolean_carrier_states","incomparable_pairs",
                                     "exact_coordinate_completion_pair_checks","original_commutator_zero"]}
    summary["field_block_commutator"] = receipt["new_field_carrier_noncommuting_block"]["commutator_value"]
    summary["potential_control_ablation_commutes"] = receipt["new_field_carrier_noncommuting_block"]["potential_control_ablation_commutes"]
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
