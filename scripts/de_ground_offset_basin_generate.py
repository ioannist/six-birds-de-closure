"""Propose explicit whole-background-box native basins for all18 offsets.

NumPy proposes linear selector roots and preconditioners only. Fraction replay
earns all interval comparisons; the generated modules require kernel proofs.
"""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
import de_ground_native_prefix_generate as g
import de_ground_basin_generate as jets
from de_ground_kernel_tube_generate import rational,vector
from de_ground_coordinates_generate import matrix
from de_ground_continuation_generate import Interval as I

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_offset_basin_2026-10-04'
OUT=ROOT/'lean/SbtCosmo/Derivation/GroundOffsetBasins'
J=g.J

def source(beta,k,X,Y):
    grad=lambda U,i:(U[(i+1)%8]-U[(i+7)%8])*F(1,2)
    return [beta[i]+k*(grad(X,i)*grad(X,i)+grad(Y,i)*grad(Y,i)+beta[i]*(X[i]*X[i]+Y[i]*Y[i])) for i in range(8)]

def linear_ground_proposal(beta):
    import numpy as np
    assert np.__version__=='1.26.4'
    midpoint=[t.mid() for t in beta];H=np.diag(1+np.array(list(map(float,midpoint))))
    for i in range(8):H[i,(i+1)%8]=H[i,(i+7)%8]=-.5
    vals,vecs=np.linalg.eigh(H);u=vecs[:,0]
    if u.sum()<0:u=-u
    border=np.block([[H-vals[0]*np.eye(8),-u[:,None]],[u[None,:],np.zeros((1,1))]])
    C=[[g.nearq(F.from_float(float(t)),1<<80) for t in row] for row in np.linalg.inv(border)]
    z=[F.from_float(float(t)) for t in u]+[F.from_float(float(vals[0]))]
    for _ in range(8):
        correction=g.mv(C,g.residual([J(t) for t in midpoint],[J(t) for t in z]))
        z=[g.nearq(t-d.lo,1<<120) for t,d in zip(z,correction)]
    err=max(t.bound() for t in g.mv(C,g.residual(beta,[J(t) for t in z])))
    a=g.ceilq(err,1<<110)+F(1,1<<120);r=F(1,1<<120)
    while r<=2*a:r*=2
    D=g.derivative(beta,[J(t-r,t+r) for t in z])
    rows=[sum((J(int(i==j))-sum((C[i][k]*D[k][j] for k in range(9)),J(0))).bound() for j in range(9)) for i in range(9)]
    q=g.ceilq(max(rows),1<<48);assert 0<=q<F(1,2)
    g.root_checks(beta,z,r,C,q,a)
    return z,r,C,q,a

def inputs(i,w,c):
    beta=[J(F(a),F(b)) for a,b in w['background_box']];k=F(w['coupling'])
    rho=F(1,400000 if i==17 else 40000)
    S,P,R,Q=[[[F(t) for t in row] for row in c[key]] for key in ['S','P','R','Q']]
    s=g.ceilq(max(sum(abs(t) for t in row) for row in S+R),1<<24)
    z0=list(map(F,w['z']));r0=F(w['r'])
    X=[J(z0[j]-r0-rho*s,z0[j]+r0+rho*s) for j in range(8)]
    Y=[J(-rho*s,rho*s) for _ in range(8)]
    return beta,k,rho,s,X,Y,S,P,R,Q

def replay_point(i,w,c,d):
    beta,k,rho,s,X,Y,S,P,R,Q=inputs(i,w,c)
    assert d['rho']==str(rho) and d['basis_budget']==str(s)
    z=list(map(F,d['z']));r=F(d['r']);q=F(d['q']);a=F(d['a']);C=[[F(t) for t in row] for row in d['C']]
    g.root_checks(source(beta,k,X,Y),z,r,C,q,a)
    G=[J(t-r,t+r) for t in z[:8]];K=J.read(d['K']);L=J.read(d['L'])
    rad,mr,mi,N=g.update(X,Y,G,K);tau=F.from_float(1e-10)
    for A,H in [(rad,K),(N,L)]:
        assert A.lo>tau*tau and H.lo>0 and H.hi>0 and H.lo**2*A.hi<=1<=H.hi**2*A.lo
    columns=[]
    for j in range(16):
        DG=list(map(J.read,d['DG'][j]));FR=list(map(J.read,d['DF'][j][0]));FI=list(map(J.read,d['DF'][j][1]))
        y,e=F(d['y'][j]),F(d['error'][j])
        _,_,raw,_,_=jets.derivative(beta,k,X,Y,G,C,q,K,L,j,S,R,y,e)
        assert all(B.lo<=A.lo and A.hi<=B.hi for A,B in zip(raw,DG))
        _,_,_,fr,fi=jets.derivative(beta,k,X,Y,G,C,q,K,L,j,S,R,y,e,DG)
        assert all(B.lo<=A.lo and A.hi<=B.hi for A,B in zip(fr+fi,FR+FI))
        columns.append(jets.matvec(P,FR)+jets.matvec(Q,FI))
    bound=max(sum(columns[j][i].bound() for j in range(16)) for i in range(16))
    assert 0<=bound<=F(d['rate'])<1
    return bound

def propose():
    rootsfile=ROOT/'results/ground_offsets_2026-10-04/witnesses.json'
    coordsfile=ROOT/'results/ground_offset_stability_2026-10-04/witnesses.json'
    ws=json.loads(rootsfile.read_text())['points'];cs=json.loads(coordsfile.read_text())['points'];out=[]
    rounding=lambda t:J(g.floorq(t.lo,1<<60),g.ceilq(t.hi,1<<60))
    for i,(w,c) in enumerate(zip(ws,cs)):
        beta,k,rho,s,X,Y,S,P,R,Q=inputs(i,w,c)
        z,r,C,q,a=linear_ground_proposal(source(beta,k,X,Y));G=[J(t-r,t+r) for t in z[:8]]
        K=g.invsqrt(jets.dot(G,X)*jets.dot(G,X)+jets.dot(G,Y)*jets.dot(G,Y));_,mr,mi,N=g.update(X,Y,G,K);L=g.invsqrt(N)
        ys=[];es=[];DS=[];FS=[];cols=[]
        for j in range(16):
            y,e,D,_,_=jets.derivative(beta,k,X,Y,G,C,q,K,L,j,S,R)
            D=list(map(rounding,D));_,_,_,fr,fi=jets.derivative(beta,k,X,Y,G,C,q,K,L,j,S,R,y,e,D)
            FR=list(map(rounding,fr));FI=list(map(rounding,fi));ys.append(str(y));es.append(str(e))
            DS.append([t.pair() for t in D]);FS.append([[t.pair() for t in FR],[t.pair() for t in FI]])
            cols.append(jets.matvec(P,FR)+jets.matvec(Q,FI))
        bound=max(sum(cols[j][i].bound() for j in range(16)) for i in range(16))
        rate=g.ceilq(bound,1<<20);assert rate<1
        d=dict(rho=str(rho),basis_budget=str(s),z=list(map(str,z)),r=str(r),q=str(q),a=str(a),C=[[str(t) for t in row] for row in C],
            K=K.pair(),L=L.pair(),y=ys,error=es,DG=DS,DF=FS,rate=str(rate))
        actual=replay_point(i,w,c,d);out.append(d)
        print(i,'rho',rho,'whole native DF',float(actual),'rate',float(rate),flush=True)
    assert len(out)==18
    return dict(kind='Explicit basins: NumPy proposes linear grounds only; Fraction replay and Lean kernel proofs required',
        root_source_sha256=hashlib.sha256(rootsfile.read_bytes()).hexdigest(),basis_source_sha256=hashlib.sha256(coordsfile.read_bytes()).hexdigest(),points=out)

def interval(t):return '⟨'+rational(F(t[0]))+', '+rational(F(t[1]))+'⟩'
def intervals(row):return '!['+', '.join(interval(t) for t in row)+']'

def render(w):
    out={}
    for i,d in enumerate(w['points']):
        name=f'Point{i:03d}';base='GroundOffsets.'+name;basis='GroundOffsetStability.'+name
        s='import SbtCosmo.Derivation.GroundUncertainNativeBasin\nimport SbtCosmo.Derivation.'+base+'\nimport SbtCosmo.Derivation.'+basis+'\nimport SbtCosmo.Derivation.GroundNativePrefixInitial\n\n'
        s+='''/-! Closed kernel comparisons for an explicit native basin at an offset.
The input hull includes exact and rounded source backgrounds. -/
namespace SbtCosmo.Derivation.GroundOffsetBasins.'''+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundRationalInterval GroundNativeBox
open GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open scoped BigOperators

'''
        for key,src in [('ρ','rho'),('s','basis_budget'),('r','r'),('q','q'),('a','a'),('rate','rate')]:s+='def '+key+' : ℚ := '+rational(F(d[src]))+'\n'
        s+='def input : StateBox := aroundBox '+base+'.z '+base+'.r ρ s\n'
        s+='def z : Fin 9 → ℚ := '+vector(list(map(F,d['z'])))+'\n'
        s+='def C : Matrix (Fin 9) (Fin 9) ℚ := '+matrix([list(map(F,row)) for row in d['C']])+'\n'
        for key in ['K','L']:s+='def '+key+' : Interval := '+interval(d[key])+'\n'
        for key,src in [('y','y'),('e','error')]:s+='def '+key+' : Fin 16 → ℚ := '+vector(list(map(F,d[src])))+'\n'
        s+='def DG : Fin 16 → Fin 8 → Interval := ![\n  '+',\n  '.join(intervals(row) for row in d['DG'])+']\n'
        s+='def DF : Fin 16 → StateBox := ![\n  '+',\n  '.join('⟨'+intervals(R)+', '+intervals(I)+'⟩' for R,I in d['DF'])+']\n\n'
        s+='theorem ground_arithmetic : GroundBackgroundKernel.Arithmetic\n    (GroundUncertainNativeBox.sourceBox '+base+'.B '+base+'.κ input) z r q a C := by\n  constructor <;> decide +kernel\n\n'
        s+='theorem phase_arithmetic : GroundIntervalReciprocal.Arithmetic (overlapBox input (GroundBackgroundKernel.fieldBox z r)) K := by\n  constructor <;> decide +kernel\n\n'
        s+='theorem mixed_arithmetic : GroundIntervalReciprocal.Arithmetic (normBox (mixedBox input (GroundBackgroundKernel.fieldBox z r) K)) L := by\n  constructor <;> decide +kernel\n\n'
        s+='theorem threshold_nonneg : 0 ≤ GroundNativePrefixInitial.τ := by decide +kernel\n'
        s+='theorem phase_margin : GroundNativePrefixInitial.τ^2 < (overlapBox input (GroundBackgroundKernel.fieldBox z r)).lo := by decide +kernel\n'
        s+='theorem mixed_margin : GroundNativePrefixInitial.τ^2 < (normBox (mixedBox input (GroundBackgroundKernel.fieldBox z r) K)).lo := by decide +kernel\n\n'
        s+='def certificate : Certificate where\n  β := '+base+'.B\n  κ := '+base+'.κ\n  τ := GroundNativePrefixInitial.τ\n  input := input\n  z := z\n  r := r\n  q := q\n  a := a\n  C := C\n  K := K\n  L := L\n'
        for key in ['S','P','R','Q']:s+='  '+key+' := '+basis+'.'+key+'\n'
        for key in ['real_inverse','imag_inverse']:s+='  '+key+' := '+basis+'.'+key+'\n'
        s+='  DG := DG\n  DF := DF\n  y := y\n  e := e\n  rate := rate\n  ground := ground_arithmetic\n  phase_inverse := phase_arithmetic\n  mixed_inverse := mixed_arithmetic\n  threshold_nonneg := threshold_nonneg\n  phase_margin := phase_margin\n  normalization_margin := mixed_margin\n\n'
        s+='theorem responses : certificate.ResponseArithmetic := by\n  intro j\n  fin_cases j <;> constructor <;> decide +kernel\n\n'
        s+='theorem response_included : certificate.ResponseIncluded := by\n  intro j\n  fin_cases j <;> unfold included <;> decide +kernel\n\n'
        s+='theorem derivative_included : certificate.DerivativeIncluded := by\n  intro j\n  fin_cases j <;> unfold StateBox.Included included <;> decide +kernel\n\n'
        s+='theorem rows : certificate.RowArithmetic := by\n  constructor\n  · decide +kernel\n  · decide +kernel\n  · intro i; fin_cases i <;> decide +kernel\n  · intro i; fin_cases i <;> decide +kernel\n\n'
        s+='theorem basis_rows : ∀ i : Fin 8, (∑ j, |certificate.S i j|) ≤ s ∧ (∑ j, |certificate.R i j|) ≤ s := by decide +kernel\n'
        s+='theorem radius_pos : 0 < ρ := by decide +kernel\n'
        s+='theorem basis_nonneg : 0 ≤ s := by decide +kernel\n\nend\nend SbtCosmo.Derivation.GroundOffsetBasins.'+name+'\n'
        out['lean/SbtCosmo/Derivation/GroundOffsetBasins/'+name+'.lean']=s
    return out

if __name__=='__main__':
    PACKET.mkdir(exist_ok=True);OUT.mkdir(exist_ok=True)
    w=propose();(PACKET/'witnesses.json').write_text(json.dumps(w,indent=2)+'\n')
    for p,s in render(w).items():(ROOT/p).write_text(s)
