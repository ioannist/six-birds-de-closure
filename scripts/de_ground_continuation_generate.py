"""Propose rational bounds and reify immutable continuation witnesses for Lean.

The exact Python interval calculations choose data only. Every actual certificate
is subsequently proved by Lean kernel reduction through the existing sound route.
"""
from fractions import Fraction as F
import json
from pathlib import Path

from de_ground_kernel_tube_generate import rational, vector

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'results/ground_branch_2026-10-03/witnesses.json'
OUT = ROOT/'lean/SbtCosmo/Derivation/GroundContinuation'


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        assert self.lo <= self.hi

    @staticmethod
    def of(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, x):
        x = self.of(x)
        return Interval(self.lo+x.lo, self.hi+x.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, x):
        return self + -self.of(x)

    def __rsub__(self, x):
        return self.of(x) + -self

    def __mul__(self, x):
        x = self.of(x)
        ends = [a*b for a in (self.lo, self.hi) for b in (x.lo, x.hi)]
        return Interval(min(ends), max(ends))

    __rmul__ = __mul__

    def bound(self):
        return max(abs(self.lo), abs(self.hi))


def equations(beta, coupling, state):
    u, e = state[:8], state[8]
    grad = [(u[(i+1)%8]-u[(i-1)%8])*F(1, 2) for i in range(8)]
    src = [beta[i]+coupling*(grad[i]*grad[i]+beta[i]*u[i]*u[i]) for i in range(8)]
    residual = [(1+src[i]-e)*u[i]-(u[(i-1)%8]+u[(i+1)%8])*F(1, 2) for i in range(8)]
    residual += [(sum((x*x for x in u), Interval(0))-1)*F(1, 2)]
    derivative = []
    for i in range(8):
        row = []
        for j in range(9):
            delta = F(int(i == j))
            dp, dn = F(int((i-1)%8 == j)), F(int((i+1)%8 == j))
            sourced = 2*coupling*(grad[i]*((dn-dp)/2)+beta[i]*u[i]*delta)
            row.append(sourced*u[i]+(1+src[i]-e)*delta-(dp+dn)/2-F(int(j == 8))*u[i])
        derivative.append(row)
    derivative.append(u+[Interval(0)])
    return residual, derivative


def upper_dyadic(x, bits):
    scale = 2**bits
    t = x*scale
    return F(-((-t.numerator)//t.denominator), scale)


def propose(w, beta):
    a, c = map(F, w['coupling_interval']) if 'coupling_interval' in w else (F(w['coupling']),)*2
    z = [F(int(t), 2**80) for t in w['center']]
    r = F(int(w['radius']), 2**80)
    C = [[F(int(t), 2**80) for t in row] for row in w['newton_inverse']]
    assert len(z) == len(C) == 9 and all(len(row) == 9 for row in C)
    k = Interval(a, c)
    res = equations(beta, k, list(map(Interval, z)))[0]
    df = equations(beta, k, [Interval(t-r, t+r) for t in z])[1]
    qraw = max(sum((Interval(int(i == j))-sum((C[i][t]*df[t][j] for t in range(9)), Interval(0))).bound()
                   for j in range(9)) for i in range(9))
    yraw = max(sum((C[i][t]*res[t] for t in range(9)), Interval(0)).bound() for i in range(9))
    q, y = upper_dyadic(qraw, 20), upper_dyadic(yraw, 60)
    assert r > 0 and 0 <= q < 1 and y >= 0 and y+q*r < r, (w.get('coupling_interval', w.get('coupling')), float(q), float(y), float(r-y-q*r))
    assert all(t-r > 0 for t in z[:8])
    return dict(a=a, c=c, z=z, r=r, C=C, q=q, y=y)


def render_leaf(kind, index, d):
    name = f'{kind}{index:03d}'
    text = '''import SbtCosmo.Derivation.GroundKernelChain

/-! Concrete immutable continuation witness, certified by kernel arithmetic. -/
namespace SbtCosmo.Derivation.GroundContinuation.'''+name+'''
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundKernelTube GroundKernelChain GroundOriginalFirstTube

'''
    for key in ['a', 'c', 'r', 'q', 'y']:
        text += f'def {key} : ℚ := {rational(d[key])}\n'
    text += f'\ndef z : Fin 9 → ℚ := {vector(d["z"])}\n\n'
    text += 'def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(map(vector, d['C']))+']\n\n'
    text += '''theorem arithmetic : Arithmetic originalBackground a c z r q y C := by
  constructor
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def datum : Data originalBackground := ⟨a, c, z, r, q, y, C, arithmetic⟩

end
end SbtCosmo.Derivation.GroundContinuation.'''+name+'\n'
    return text


def proposals():
    data = json.loads(SOURCE.read_text())
    assert data['scale'] == str(2**80) and len(data['tubes']) == 286 and len(data['anchors']) == 287
    beta = [F.from_float(float.fromhex(t)) for t in data['background_hex']]
    result = {}
    for kind, witnesses in [('Tube', data['tubes']), ('Anchor', data['anchors'])]:
        for i, w in enumerate(witnesses):
            if kind == 'Tube' and i == 0:
                continue  # Existing immutable GroundOriginalFirstTube kernel proof.
            result[f'{kind}{i:03d}'] = propose(w, beta)
    return result


if __name__ == '__main__':
    ds = proposals()
    OUT.mkdir(exist_ok=True)
    for name, d in ds.items():
        kind = 'Tube' if name.startswith('Tube') else 'Anchor'
        i = int(name[len(kind):])
        (OUT/(name+'.lean')).write_text(render_leaf(kind, i, d))
    print(f'Reified {len(ds)} proposals; each arithmetic proof must be checked by Lean')
