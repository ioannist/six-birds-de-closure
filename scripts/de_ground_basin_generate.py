"""Propose and exactly replay an explicit .3 native attraction neighborhood.

The floating solver proposes a uniform-potential ground certificate only.
All budgets, response error,16 derivative columns and endpoint entry are exact
Fraction replay here and must be returned separately by Lean kernel proofs.
"""
from pathlib import Path
from fractions import Fraction as F
import json,re,hashlib
from de_ground_native_prefix_generate import J,ROOT,DATA,source,propose_root,root_checks,invsqrt,update,mv,ceilq,floorq
PACKET=ROOT/'results/ground_basin_2026-10-04'

def read_matrix(k):
 s=(ROOT/'lean/SbtCosmo/Derivation/GroundCoordinates/Point002.lean').read_text()
 t=s.split('def '+k+' : QMatrix := ')[1].split('\n\ndef ')[0]
 rows=[[F(x.strip(' ()')) for x in row.split(',')] for row in re.findall(r'!\[([^\[\]]*)\]',t)]
 assert len(rows)==8 and all(len(row)==8 for row in rows)
 return rows

def initial_root():
 s=(ROOT/'lean/SbtCosmo/Derivation/GroundSamples/Point002.lean').read_text()
 return [F(x.strip(' ()')) for x in s.split('def z : Fin 9 → ℚ := ![')[1].split(']')[0].split(',')]

def data():
 d=json.loads(DATA.read_text());β=list(map(F.from_float,d['potential']));κ=F.from_float(.3);ρ=F(1,40000);s=F(177,50);r0=F(1,2**32);z0=initial_root()
 S,P,R,Q=[read_matrix(k) for k in ['S','P','R','Q']]
 assert max(sum(abs(x) for x in row) for row in S+R)<=s
 X=[J(z0[i]-ρ*s-r0,z0[i]+ρ*s+r0) for i in range(8)];Y=[J(-ρ*s,ρ*s) for _ in range(8)]
 return β,κ,ρ,s,X,Y,S,P,R,Q

def dot(a,b):return sum((x*y for x,y in zip(a,b)),J(0))
def negcube(k):return -(k*k*k)
def matvec(A,x):return [dot(row,x) for row in A]
def gradient(X,i):return (X[(i+1)%8]-X[(i+7)%8])*F(1,2)

def derivative(β,κ,X,Y,G,C,q,K,L,j,S,R,y=None,e=None,dg_cache=None):
 HR=[J(S[i][j]) if j<8 else J(0) for i in range(8)]
 HI=[J(0) if j<8 else J(R[i][j-8]) for i in range(8)]
 V=[2*κ*((gradient(X,i)*gradient(HR,i)+β[i]*X[i]*HR[i])+
          (gradient(Y,i)*gradient(HI,i)+β[i]*Y[i]*HI[i])) for i in range(8)]
 corrected=mv(C,[-V[i]*G[i] for i in range(8)]+[J(0)])
 if y is None:y=ceilq(max(x.bound() for x in corrected),1<<48)
 if e is None:e=ceilq(q*y/(1-q),1<<48)
 assert y>=0 and e>=0 and q*y<=e*(1-q) and max(x.bound() for x in corrected)<=y
 DG=[x+J(-e,e) for x in corrected[:8]]
 if dg_cache is not None:
  assert all(B.lo<=A.lo and A.hi<=B.hi for A,B in zip(DG,dg_cache))
  DG=dg_cache
 a,h=dot(G,X),dot(G,Y);da,dh=dot(X,DG)+dot(G,HR),dot(Y,DG)+dot(G,HI)
 dk=negcube(K)*(a*da+h*dh)
 ar=[(da*K+a*dk)*G[i]+a*K*DG[i] for i in range(8)]
 ai=[(-dh*K-h*dk)*G[i]-h*K*DG[i] for i in range(8)]
 dr=[F(1,2)*HR[i]+F(1,2)*ar[i] for i in range(8)]
 di=[F(1,2)*HI[i]+F(1,2)*ai[i] for i in range(8)]
 _,mR,mI,_=update(X,Y,G,K)
 dl=negcube(L)*(dot(mR,dr)+dot(mI,di))
 fr=[L*dr[i]+dl*mR[i] for i in range(8)]
 fi=[L*di[i]+dl*mI[i] for i in range(8)]
 return y,e,DG,fr,fi

def replay(w):
 assert len(w['ground_center'])==9 and len(w['preconditioner'])==9
 assert all(len(row)==9 for row in w['preconditioner'])
 for key in ['dg_cache','jet_re_cache','jet_im_cache']:
  assert len(w[key])==16 and all(len(row)==8 for row in w[key]),key
 assert len(w['phase_inverse'])==len(w['normalization_inverse'])==2
 β,κ,ρ,s,X,Y,S,P,R,Q=data();assert w['coupling']==str(κ) and w['radius']==str(ρ) and w['basis_budget']==str(s)
 assert w['data_sha256']==hashlib.sha256(DATA.read_bytes()).hexdigest()
 z=list(map(F,w['ground_center']));r=F(w['ground_radius']);q=F(w['ground_rate']);a=F(w['ground_residual']);C=[[F(x) for x in row] for row in w['preconditioner']]
 root_checks(source(β,κ,X,Y),z,r,C,q,a);G=[J(t-r,t+r) for t in z[:8]]
 K=J.read(w['phase_inverse']);L=J.read(w['normalization_inverse']);rad,mR,mI,norm=update(X,Y,G,K)
 τ=F.from_float(1e-10)
 for N,A in [(rad,K),(norm,L)]:
  assert N.lo>τ**2 and A.lo>0 and A.hi>0 and A.lo**2*N.hi<=1<=A.hi**2*N.lo
 cols=[];Dcols=[]
 assert len(w['response_y'])==len(w['response_e'])==16
 for j in range(16):
  cache=list(map(J.read,w['dg_cache'][j]))
  _,_,DG,fr,fi=derivative(β,κ,X,Y,G,C,q,K,L,j,S,R,F(w['response_y'][j]),F(w['response_e'][j]),cache)
  FR=list(map(J.read,w['jet_re_cache'][j]));FI=list(map(J.read,w['jet_im_cache'][j]))
  assert all(B.lo<=A.lo and A.hi<=B.hi for A,B in zip(fr+fi,FR+FI))
  cols.append(matvec(P,FR)+matvec(Q,FI));Dcols.append(DG)
 rows=[sum(cols[j][i].bound() for j in range(16)) for i in range(16)]
 selector_rows=[sum(Dcols[j][i].bound() for j in range(16)) for i in range(8)]
 assert max(rows)<=F(3,5) and max(selector_rows)<=1
 seed=json.loads((ROOT/'results/ground_native_prefix_2026-10-04/witnesses.json').read_text())['steps'][-1]
 z0=initial_root();r0=F(1,2**32)
 dR=[-J.read(t)-J(z0[i]-r0,z0[i]+r0) for i,t in enumerate(seed['output_re'])];dI=[-J.read(t) for t in seed['output_im']]
 error=max(x.bound() for x in matvec(P,dR)+matvec(Q,dI));assert error<=F(1,48000)<ρ
 return max(rows),max(selector_rows),error

def add_caches(w):
 β,κ,ρ,s,X,Y,S,P,R,Q=data();z=list(map(F,w['ground_center']));r=F(w['ground_radius']);q=F(w['ground_rate']);C=[[F(x) for x in row] for row in w['preconditioner']]
 G=[J(t-r,t+r) for t in z[:8]];K=J.read(w['phase_inverse']);L=J.read(w['normalization_inverse'])
 rounding=lambda A:J(floorq(A.lo,1<<60),ceilq(A.hi,1<<60))
 DC=[];FC=[];IC=[]
 for j in range(16):
  y,e,D,_,_=derivative(β,κ,X,Y,G,C,q,K,L,j,S,R,F(w['response_y'][j]),F(w['response_e'][j]))
  D=list(map(rounding,D));_,_,_,fr,fi=derivative(β,κ,X,Y,G,C,q,K,L,j,S,R,y,e,D)
  DC.append([t.pair() for t in D]);FC.append([rounding(t).pair() for t in fr]);IC.append([rounding(t).pair() for t in fi])
 w.update(cache_dyadic_bits=60,dg_cache=DC,jet_re_cache=FC,jet_im_cache=IC)
 return w

def propose():
 β,κ,ρ,s,X,Y,S,P,R,Q=data();z,r,C,_,a=propose_root(source(β,κ,X,Y));q=F(1,2500)
 root_checks(source(β,κ,X,Y),z,r,C,q,a);G=[J(t-r,t+r) for t in z[:8]]
 K=invsqrt(dot(G,X)*dot(G,X)+dot(G,Y)*dot(G,Y));_,mR,mI,N=update(X,Y,G,K);L=invsqrt(N)
 ys=[];es=[]
 for j in range(16):
  y,e,_,_,_=derivative(β,κ,X,Y,G,C,q,K,L,j,S,R);ys.append(str(y));es.append(str(e))
 w=dict(kind='Explicit native basin proposals;Fraction replay;Lean kernel return required',coupling=str(κ),radius=str(ρ),basis_budget=str(s),
  data_sha256=hashlib.sha256(DATA.read_bytes()).hexdigest(),ground_center=list(map(str,z)),ground_radius=str(r),ground_rate=str(q),ground_residual=str(a),
  preconditioner=[[str(x) for x in row] for row in C],phase_inverse=K.pair(),normalization_inverse=L.pair(),response_y=ys,response_e=es)
 add_caches(w)
 row,sel,entry=replay(w);print('exact proposed derivative bound',float(row),'selector bound',float(sel),'entry bound',float(entry),flush=True)
 return w

if __name__=='__main__':
 PACKET.mkdir(exist_ok=True);w=propose();(PACKET/'witnesses.json').write_text(json.dumps(w,indent=2)+'\n')
