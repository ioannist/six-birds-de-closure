"""Propose and reify bordered derivative-response bounds for14 original roots.

Exact Fraction intervals choose data. Fresh kernel comparisons and the actual
border response equation are the proof route; saved Jacobian verdicts are not
theorem premises or a numeric oracle.
"""
from fractions import Fraction as F
import json
from pathlib import Path

from de_ground_kernel_tube_generate import rational, vector
import de_ground_samples_generate as roots
from de_ground_continuation_generate import Interval as I, upper_dyadic

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'lean/SbtCosmo/Derivation/GroundResponses'


def proposals():
    old = json.loads((ROOT/'results/ground_interval_2026-10-03/witnesses.json').read_text())
    branch = json.loads((ROOT/'results/ground_branch_2026-10-03/witnesses.json').read_text())
    ws = [w for w in old['witnesses'] if w['sweep'] == 'kappa']+branch['crossing_anchors']
    beta = [F.from_float(float.fromhex(t)) for t in branch['background_hex']]
    result = []
    for d, w in zip(roots.proposals(), ws):
        u = [I(t-d['r'], t+d['r']) for t in d['z'][:8]]
        e = I(d['z'][8]-d['r'], d['z'][8]+d['r'])
        k = I(d['a'])
        g = [(u[(i+1)%8]-u[(i-1)%8])*F(1,2) for i in range(8)]
        src = [beta[i]+k*(g[i]*g[i]+beta[i]*u[i]*u[i]) for i in range(8)]
        B = [[(1+src[i]-e)*int(i == j)-I(F(int((i-1)%8 == j)+int((i+1)%8 == j),2))-int(j == 8)*u[i]
              for j in range(9)] for i in range(8)]
        B.append(u+[I(0)])
        C = [[F(int(t),2**80) for t in row] for row in w['border_inverse']]
        Q = [[I(int(i == j))-sum((C[i][t]*B[t][j] for t in range(9)),I(0)) for j in range(9)] for i in range(9)]
        q = upper_dyadic(max(sum(v.bound() for v in row) for row in Q),50)
        assert 0 <= q < 1
        rhs = [[-(2*k*(g[i]*F(int((i+1)%8 == j)-int((i-1)%8 == j),2)+beta[i]*u[i]*int(i == j)))*u[i]
                for j in range(8)] for i in range(8)]+[[I(0)]*8]
        Cr = [[sum((C[i][t]*rhs[t][j] for t in range(9)),I(0)) for j in range(8)] for i in range(9)]
        y = [upper_dyadic(max(Cr[i][j].bound() for i in range(9)),60) for j in range(8)]
        error = [upper_dyadic(q*t/(1-q),60) for t in y]
        assert all(q*y[j] <= error[j]*(1-q) for j in range(8))
        H = [[(I(int(i == j))-u[i]*u[j]+Cr[i][j])*F(1,2)+I(-error[j]/2,error[j]/2)
              for j in range(8)] for i in range(8)]
        result.append(dict(C=C,q=q,y=y,error=error,half=H))
    assert len(result) == 14
    return result


def render(i, d):
    name = f'Point{i:03d}'
    s = 'import SbtCosmo.Derivation.GroundBorderResponse\n'
    s += 'import SbtCosmo.Derivation.GroundSamples.'+name+'\n\n'
    s += '''/-! Actual bordered-selector response bounds, closed kernel arithmetic. -/
namespace SbtCosmo.Derivation.GroundResponses.'''+name+'''
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundBorderResponse GroundOriginalFirstTube

'''
    s += 'def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vector(row) for row in d['C'])+']\n\n'
    s += 'def q : ℚ := '+rational(d['q'])+'\n'
    s += 'def y : Fin 8 → ℚ := '+vector(d['y'])+'\n'
    s += 'def error : Fin 8 → ℚ := '+vector(d['error'])+'\n\n'
    s += 'theorem arithmetic : Arithmetic originalBackground GroundSamples.'+name+'.a GroundSamples.'+name+'.z GroundSamples.'+name+'.r C q y error := by\n'
    s += '  constructor\n'+'  · decide +kernel\n'*7
    s += '\nend\nend SbtCosmo.Derivation.GroundResponses.'+name+'\n'
    return s


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    ds = proposals()
    for i,d in enumerate(ds):
        (OUT/f'Point{i:03d}.lean').write_text(render(i,d))
    print('Reified14 response certificates; max proposed derivative-column error',float(max(max(d['error']) for d in ds)))
