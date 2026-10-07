"""Reify original coupling sample and crossing-root boxes as kernel proofs.

The old witnesses supply rational data only. Fresh kernel arithmetic earns each
actual tube. No source or receipt from the earlier packets is modified.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import de_ground_continuation_generate as cg

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'lean/SbtCosmo/Derivation/GroundSamples'


def proposals():
    old = json.loads((ROOT/'results/ground_interval_2026-10-03/witnesses.json').read_text())
    branch = json.loads((ROOT/'results/ground_branch_2026-10-03/witnesses.json').read_text())
    beta = [F.from_float(float.fromhex(t)) for t in branch['background_hex']]
    points = [w for w in old['witnesses'] if w['sweep'] == 'kappa']
    assert len(points) == 12
    result = []
    for w in points:
        assert [F.from_float(float.fromhex(t)) for t in w['background_hex']] == beta
        w = dict(w, coupling=str(F.from_float(float.fromhex(w['coupling_hex']))))
        result.append(cg.propose(w, beta))
    for w in branch['crossing_anchors']:
        result.append(cg.propose(w, beta))
    assert len(result) == 14
    return result


def render(i, d):
    return cg.render_leaf('Point', i, d).replace('GroundContinuation.Point', 'GroundSamples.Point')


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    ds = proposals()
    for i, d in enumerate(ds):
        (OUT/f'Point{i:03d}.lean').write_text(render(i, d))
    print('Reified14 original thin-root boxes; actual certificates require fresh Lean kernel checks')
