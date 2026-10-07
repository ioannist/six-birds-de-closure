"""Propose seven exact dyadic determinant-sign certificates, reified in Lean.

Midpoint inversion and LU choose data only. Positive denominators, cleared
integer product identities, triangularity and defect rows are kernel obligations.
"""
from fractions import Fraction as F
from math import lcm, prod
from pathlib import Path
import de_ground_response_generate as responses
import de_ground_coordinates_generate as coords
from de_ground_continuation_generate import Interval as I
from de_ground_kernel_tube_generate import rational
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'lean/SbtCosmo/Derivation/GroundSpectralTests'
TESTS=[(12,F(-1),1),(13,F(-1),-1),(10,F(-1),1),(10,F(-36,25),1),
       (10,F(-71,50),-1),(11,F(-249,100),1),(11,F(-247,100),-1)]


def integral(a,d=None):
    if d is None:d=lcm(*(x.denominator for row in a for x in row))
    assert d>0
    z=[[int(x*d) for x in row] for row in a]
    assert all(F(z[i][j],d)==a[i][j] for i in range(8) for j in range(8))
    return z,d


def proposals():
    roots=responses.proposals();out=[]
    for sample,ell,sign in TESTS:
        box=roots[sample]['half']
        B=[[x-I(ell*int(i==j)) for j,x in enumerate(row)] for i,row in enumerate(box)]
        mid=[[(x.lo+x.hi)/2 for x in row] for row in B]
        C=[[F(round(x*2**24),2**24) for x in row] for row in coords.inverse(mid)]
        E=[[I(int(i==j))-sum((C[i][t]*B[t][j] for t in range(8)),I(0)) for j in range(8)] for i in range(8)]
        q=max(sum(x.bound() for x in row) for row in E)
        assert q<F(1,1000)
        U=[row[:] for row in C];L=[[F(int(i==j)) for j in range(8)] for i in range(8)]
        for i in range(8):
            assert U[i][i], 'Candidate requires an unrepresented row swap'
            for k in range(i+1,8):
                f=U[k][i]/U[i][i];L[k][i]=f
                U[k]=[x-f*y for x,y in zip(U[k],U[i])]
        ci,dc=integral(C,2**24);li,dl=integral(L);ui,du=integral(U)
        assert all(dc*sum(li[i][t]*ui[t][j] for t in range(8))==dl*du*ci[i][j] for i in range(8) for j in range(8))
        assert all(li[i][i]==dl for i in range(8))
        assert sign*prod(ui[i][i] for i in range(8))>0
        out.append(dict(sample=sample,ell=ell,sign=sign,CI=ci,LI=li,UI=ui,dc=dc,dl=dl,du=du,box=box,defect_bound=q))
    return out


def zmatrix(a):return '![\n  '+',\n  '.join('!['+', '.join('('+str(x)+')' if x<0 else str(x) for x in row)+']' for row in a)+']'


def render(i,d):
    n=f'Test{i:03d}';sample=d['sample']
    s='import SbtCosmo.Derivation.GroundSpectralEnclosure\n'
    if sample<12:s+=f'import SbtCosmo.Derivation.GroundCoordinates.Point{sample:03d}\n'
    s+='\n/-! Closed arithmetic for an actual original shifted derivative matrix. -/\n'
    s+='namespace SbtCosmo.Derivation.GroundSpectralTests.'+n+'\nnoncomputable section\n'
    s+='set_option maxHeartbeats 20000000\nset_option maxRecDepth 20000\n'
    s+='open GroundMatrixCoordinates GroundSpectralEnclosure GroundTriangularArithmetic\n\n'
    for k in ['CI','LI','UI']:s+='def '+k+' : ZMatrix := '+zmatrix(d[k])+'\n\n'
    for k in ['dc','dl','du','sign']:s+='def '+k+' : ℤ := '+str(d[k] if k!='sign' else d['sign'])+'\n'
    s+='def ell : ℚ := '+rational(d['ell'])+'\n'
    s+='def C : QMatrix := scaled CI dc\n'
    if sample<12:s+=f'def B : Box := GroundCoordinates.Point{sample:03d}.realBox\n\n'
    else:s+='def B : Box := '+coords.matrix(d['box'],True)+'\n\n'
    s+='theorem factor_arithmetic : GroundTriangularArithmetic.Arithmetic CI LI UI dc dl du sign := by\n  constructor\n'
    s+='  · decide +kernel\n'*3
    s+='  · funext i j\n    fin_cases i <;> fin_cases j <;> decide +kernel\n'
    s+='  · decide +kernel\n'*4+'\n'
    s+=f'theorem box_return : B = GroundOriginalResponses.enclosures {sample} := by\n'
    if sample<12:s+=f'  exact GroundCoordinates.Point{sample:03d}.realBox_return\n\n'
    else:s+='  funext i j\n  fin_cases i <;> fin_cases j <;> decide +kernel\n\n'
    s+='theorem defect_arithmetic : GroundSpectralEnclosure.Arithmetic C (shifted B ell) (1/1000) := by\n  constructor\n  · decide +kernel\n  · decide +kernel\n  · intro i\n    fin_cases i <;> decide +kernel\n\n'
    return s+'end\nend SbtCosmo.Derivation.GroundSpectralTests.'+n+'\n'


if __name__=='__main__':
    OUT.mkdir(exist_ok=True)
    for i,d in enumerate(proposals()):
        (OUT/f'Test{i:03d}.lean').write_text(render(i,d))
        print(i,d['sample'],str(d['ell']),d['sign'],float(d['defect_bound']),d['dl'].bit_length(),d['du'].bit_length())
