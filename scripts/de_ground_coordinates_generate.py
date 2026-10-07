"""Propose exact rational bases, entry boxes and row budgets for12 couplings.

Fraction inversion and arithmetic propose data only. Both inverse identities,
box equalities and induced row tests are reified as fresh Lean kernel checks.
"""
from fractions import Fraction as F
import json
from pathlib import Path
from de_ground_kernel_tube_generate import rational, vector
from de_ground_continuation_generate import Interval as I, upper_dyadic
import de_ground_samples_generate as roots
import de_ground_response_generate as responses

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'lean/SbtCosmo/Derivation/GroundCoordinates'


def inverse(a):
    n = len(a)
    q = [row[:]+[F(int(i == j)) for j in range(n)] for i,row in enumerate(a)]
    for i in range(n):
        p = next(k for k in range(i,n) if q[k][i])
        q[i],q[p] = q[p],q[i]
        d = q[i][i];q[i] = [t/d for t in q[i]]
        for k in range(n):
            if k != i:
                d = q[k][i];q[k] = [x-d*y for x,y in zip(q[k],q[i])]
    return [row[n:] for row in q]


def row_bound(s,p,b):
    return max(sum(sum((sum((p[i][a]*b[a][t]*s[t][j] for t in range(8)),I(0)) for a in range(8)),I(0)).bound()
                   for j in range(8)) for i in range(8))


def proposals():
    old = json.loads((ROOT/'results/ground_interval_2026-10-03/witnesses.json').read_text())
    ws = [w for w in old['witnesses'] if w['sweep'] == 'kappa']
    im = json.loads((ROOT/'results/ground_native_2026-10-03/imaginary_witnesses.json').read_text())
    ims = [w for w in im['imaginary_bases'] if w['sweep'] == 'kappa']
    result = []
    for i,(w,v,d,response) in enumerate(zip(ws,ims,roots.proposals()[:12],responses.proposals()[:12])):
        assert w['parameter_hex'] == v['parameter_hex']
        # Coordinate bases may be chosen freely. Simpler dyadic proposals keep
        # exact inverse comparisons tractable; their validity and all bounds
        # are checked again rather than assuming a rounded basis is adequate.
        S = [[F(round(F(int(t),2**80)*2**24),2**24) for t in row] for row in w['spectral_basis']]
        R = [[F(round(F(int(t),2**80)*2**24),2**24) for t in row] for row in v['basis']]
        P,Q = inverse(S),inverse(R)
        for a,b in [(S,P),(P,S),(R,Q),(Q,R)]:
            assert all(sum(a[j][k]*b[k][l] for k in range(8)) == int(j == l) for j in range(8) for l in range(8))
        u = [I(t-d['r'],t+d['r']) for t in d['z'][:8]]
        realBox = response['half']
        imagBox = [[F(1,2)*(I(int(j == k))-u[j]*u[k]) for k in range(8)] for j in range(8)]
        realBound,imagBound = row_bound(S,P,realBox),row_bound(R,Q,imagBox)
        rate = upper_dyadic(realBound,20) if i < 10 else F(3,2) if i == 10 else F(3)
        assert realBound <= rate and (rate < 1 if i < 10 else True)
        assert imagBound <= F(501,1000)
        result.append(dict(S=S,P=P,R=R,Q=Q,realBox=realBox,imagBox=imagBox,rate=rate,
                           realBound=realBound,imagBound=imagBound))
    assert len(result) == 12
    return result


def matrix(a, interval=False):
    def cell(x):
        return '⟨'+rational(x.lo)+', '+rational(x.hi)+'⟩' if interval else rational(x)
    return '![\n  '+',\n  '.join('!['+', '.join(cell(x) for x in row)+']' for row in a)+']'


def render(i,d):
    name=f'Point{i:03d}'
    s='import SbtCosmo.Derivation.GroundMatrixCoordinates\n\n'
    s+='''/-! Closed kernel coordinate arithmetic for an original coupling sample. -/
namespace SbtCosmo.Derivation.GroundCoordinates.'''+name+'''
noncomputable section
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000
open GroundMatrixCoordinates GroundOriginalFirstTube

'''
    for k in ['S','P','R','Q']:
        s+='def '+k+' : QMatrix := '+matrix(d[k])+'\n\n'
    for k in ['realBox','imagBox']:
        s+='def '+k+' : Matrix (Fin 8) (Fin 8) GroundRationalInterval.Interval := '+matrix(d[k],True)+'\n\n'
    s+='def rate : ℚ := '+rational(d['rate'])+'\n\n'
    for k,a,b in [('real_inverse','S','P'),('imag_inverse','R','Q')]:
        s+='theorem '+k+' : InverseArithmetic '+a+' '+b+' := by\n  constructor\n  all_goals\n    ext i j\n    fin_cases i <;> fin_cases j <;>\n      norm_num ['+a+', '+b+', Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]\n\n'
    s+='theorem realBox_return : realBox = GroundOriginalResponses.enclosures '+str(i)+' := by\n  funext a b\n  fin_cases a <;> fin_cases b <;> decide +kernel\n\n'
    s+='theorem imagBox_return : imagBox = imaginaryIntervals originalBackground GroundSamples.'+name+'.a GroundSamples.'+name+'.z GroundSamples.'+name+'.r := by\n  funext a b\n  fin_cases a <;> fin_cases b <;> decide +kernel\n\n'
    s+='theorem real_rows : RowArithmetic S P realBox rate := by\n  constructor\n  · decide +kernel\n  · intro i\n    fin_cases i <;> decide +kernel\n\n'
    s+='theorem imag_rows : RowArithmetic R Q imagBox (501/1000) := by\n  constructor\n  · decide +kernel\n  · intro i\n    fin_cases i <;> decide +kernel\n\n'
    return s+'end\nend SbtCosmo.Derivation.GroundCoordinates.'+name+'\n'


if __name__ == '__main__':
    OUT.mkdir(exist_ok=True)
    ds=proposals()
    for i,d in enumerate(ds):
        (OUT/f'Point{i:03d}.lean').write_text(render(i,d))
        print(i,float(d['realBound']),float(d['rate']),float(d['imagBound']))
