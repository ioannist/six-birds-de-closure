"""Exact proposals for actual native attraction at eighteen background offsets.

The selector border inverse is distinct from the nonlinear Newton inverse.
Both source input models and every background between them share the boxes.
Saved bases and matrices propose data; Lean earns inverses and derivative bounds.
"""
from fractions import Fraction as F
from pathlib import Path
import json, hashlib
from de_ground_continuation_generate import Interval as I, upper_dyadic
from de_ground_kernel_tube_generate import rational, vector
from de_ground_coordinates_generate import inverse, row_bound, matrix

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_offset_stability_2026-10-04'
OUT=ROOT/'lean/SbtCosmo/Derivation/GroundOffsetStability'

def enclosure(x, bits=48):
    return I(-upper_dyadic(-x.lo,bits),upper_dyadic(x.hi,bits))

def proposals():
    roots=json.loads((ROOT/'results/ground_offsets_2026-10-04/witnesses.json').read_text())['points']
    source=ROOT/'results/ground_interval_2026-10-03/witnesses.json'
    imag=ROOT/'results/ground_native_2026-10-03/imaginary_witnesses.json'
    ws=[w for w in json.loads(source.read_text())['witnesses'] if w['sweep']=='background']
    ims=[w for w in json.loads(imag.read_text())['imaginary_bases'] if w['sweep']=='background']
    assert len(roots)==len(ws)==len(ims)==18
    out=[]
    for d,w,v in zip(roots,ws,ims):
        assert w['parameter_hex']==v['parameter_hex'] and F.from_float(float.fromhex(w['parameter_hex']))==F(d['offset'])
        z=list(map(F,d['z']));r=F(d['r']);k=I(F(d['coupling']))
        beta=[I(F(a),F(b)) for a,b in d['background_box']]
        u=[I(t-r,t+r) for t in z[:8]];e=I(z[8]-r,z[8]+r)
        g=[(u[(i+1)%8]-u[(i-1)%8])*F(1,2) for i in range(8)]
        src=[beta[i]+k*(g[i]*g[i]+beta[i]*u[i]*u[i]) for i in range(8)]
        border=[[(1+src[i]-e)*int(i==j)-I(F(int((i-1)%8==j)+int((i+1)%8==j),2))-int(j==8)*u[i]
                 for j in range(9)] for i in range(8)]+[u+[I(0)]]
        C=[[F(int(t),2**80) for t in row] for row in w['border_inverse']]
        defect=[[I(int(i==j))-sum((C[i][t]*border[t][j] for t in range(9)),I(0)) for j in range(9)] for i in range(9)]
        q=upper_dyadic(max(sum(t.bound() for t in row) for row in defect),50)
        assert 0<=q<1
        rhs=[[-(2*k*(g[i]*F(int((i+1)%8==j)-int((i-1)%8==j),2)+beta[i]*u[i]*int(i==j)))*u[i]
              for j in range(8)] for i in range(8)]+[[I(0)]*8]
        Cr=[[sum((C[i][t]*rhs[t][j] for t in range(9)),I(0)) for j in range(8)] for i in range(9)]
        y=[upper_dyadic(max(Cr[i][j].bound() for i in range(9)),60) for j in range(8)]
        error=[upper_dyadic(q*t/(1-q),60) for t in y]
        assert all(q*y[j]<=error[j]*(1-q) for j in range(8))
        H=[[(I(int(i==j))-u[i]*u[j]+Cr[i][j])*F(1,2)+I(-error[j]/2,error[j]/2) for j in range(8)] for i in range(8)]
        J=[[F(1,2)*(I(int(i==j))-u[i]*u[j]) for j in range(8)] for i in range(8)]
        S=[[F(round(F(int(t),2**80)*2**24),2**24) for t in row] for row in w['spectral_basis']]
        R=[[F(round(F(int(t),2**80)*2**24),2**24) for t in row] for row in v['basis']]
        P,Q=inverse(S),inverse(R)
        for a,b in [(S,P),(P,S),(R,Q),(Q,R)]:
            assert all(sum(a[i][t]*b[t][j] for t in range(8))==int(i==j) for i in range(8) for j in range(8))
        realBox=[[enclosure(t) for t in row] for row in H]
        imagBox=[[enclosure(t) for t in row] for row in J]
        for a,b in [(H,realBox),(J,imagBox)]:
            assert all(b[i][j].lo<=a[i][j].lo<=a[i][j].hi<=b[i][j].hi for i in range(8) for j in range(8))
        realBound,imagBound=row_bound(S,P,realBox),row_bound(R,Q,imagBox)
        rate=upper_dyadic(realBound,20)
        assert realBound<=rate<1 and imagBound<=F(501,1000)
        point=dict(offset=d['offset'],C=[[str(t) for t in row] for row in C],q=str(q),y=list(map(str,y)),error=list(map(str,error)),rate=str(rate),realBound=str(realBound),imagBound=str(imagBound))
        point.update({key:[[str(t) for t in row] for row in a] for key,a in [('S',S),('P',P),('R',R),('Q',Q)]})
        point.update({key:[[[str(t.lo),str(t.hi)] for t in row] for row in a] for key,a in [('realBox',realBox),('imagBox',imagBox)]})
        out.append(point)
    return dict(kind='Whole-background-box selector responses and sixteen-real-coordinate native stability',saved_border_source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),saved_imag_basis_source_sha256=hashlib.sha256(imag.read_bytes()).hexdigest(),points=out)

def render(w):
    out={}
    for i,d in enumerate(w['points']):
        name=f'Point{i:03d}';base='GroundOffsets.'+name
        s='import SbtCosmo.Derivation.GroundUncertainBorderResponse\nimport SbtCosmo.Derivation.'+base+'\n\n'
        s+='''/-! Kernel obligations for the actual native derivative at an offset root.
The real and imaginary blocks both use the unchanged source phase rule. -/
namespace SbtCosmo.Derivation.GroundOffsetStability.'''+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundMatrixCoordinates

'''
        s+='def C : Matrix (Fin 9) (Fin 9) ℚ := '+matrix([list(map(F,row)) for row in d['C']])+'\n\n'
        s+='def q : ℚ := '+rational(F(d['q']))+'\n'
        for key in ['y','error']:s+='def '+key+' : Fin 8 → ℚ := '+vector(list(map(F,d[key])))+'\n'
        for key in ['S','P','R','Q']:s+='def '+key+' : QMatrix := '+matrix([list(map(F,row)) for row in d[key]])+'\n\n'
        for key in ['realBox','imagBox']:s+='def '+key+' : Matrix (Fin 8) (Fin 8) GroundRationalInterval.Interval := '+matrix([[I(F(a),F(b)) for a,b in row] for row in d[key]],True)+'\n\n'
        s+='def rate : ℚ := '+rational(F(d['rate']))+'\n\n'
        args=' '.join(base+'.'+t for t in ['B','κ','z','r'])
        s+='theorem response_arithmetic : GroundUncertainBorderResponse.Arithmetic '+args+' C q y error := by\n  constructor <;> decide +kernel\n\n'
        for key,a,b in [('real_inverse','S','P'),('imag_inverse','R','Q')]:
            s+='theorem '+key+' : InverseArithmetic '+a+' '+b+' := by\n  constructor\n  all_goals\n    ext i j\n    fin_cases i <;> fin_cases j <;>\n      norm_num ['+a+', '+b+', Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]\n\n'
        s+='theorem realBox_included : GroundUncertainBorderResponse.Included\n    (GroundUncertainBorderResponse.halfInterval '+args+' C error) realBox := by\n  intro i j\n  fin_cases i <;> fin_cases j <;> decide +kernel\n\n'
        s+='theorem imagBox_included : GroundUncertainBorderResponse.Included\n    (GroundUncertainBorderResponse.imaginaryIntervals '+args+') imagBox := by\n  intro i j\n  fin_cases i <;> fin_cases j <;> decide +kernel\n\n'
        for key,a,b,box,rate in [('real_rows','S','P','realBox','rate'),('imag_rows','R','Q','imagBox','(501/1000)')]:
            s+='theorem '+key+' : RowArithmetic '+a+' '+b+' '+box+' '+rate+' := by\n  constructor\n  · decide +kernel\n  · intro i\n    fin_cases i <;> decide +kernel\n\n'
        s+='theorem stable_rate : rate < 1 := by decide +kernel\n\nend\nend SbtCosmo.Derivation.GroundOffsetStability.'+name+'\n'
        out['lean/SbtCosmo/Derivation/GroundOffsetStability/'+name+'.lean']=s
    return out

if __name__=='__main__':
    PACKET.mkdir(exist_ok=True);OUT.mkdir(exist_ok=True)
    w=proposals();(PACKET/'witnesses.json').write_text(json.dumps(w,indent=2)+'\n')
    for p,s in render(w).items():(ROOT/p).write_text(s)
    for i,d in enumerate(w['points']):print(i,d['offset'],float(F(d['rate'])),float(F(d['imagBound'])))
