"""Propose and exactly replay a native complex orbit prefix at original coupling.3.

NumPy supplies root/preconditioner proposals only. Fraction replay and Lean
kernel certificates keep every potential box and both inverse square roots.
"""
from fractions import Fraction as F
from pathlib import Path
import json,math,hashlib
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step24_derived_physical_audits_artifacts/toy_field_samples_step24.json'
BITS=100
SCALE=1<<BITS

class J:
    def __init__(self,a,b=None):self.lo=F(a);self.hi=F(a if b is None else b);assert self.lo<=self.hi
    def __add__(self,b):b=toJ(b);return J(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return J(-self.hi,-self.lo)
    def __sub__(self,b):return self+-toJ(b)
    def __rsub__(self,b):return toJ(b)+-self
    def __mul__(self,b):
        b=toJ(b);ends=[x*y for x in [self.lo,self.hi] for y in [b.lo,b.hi]];return J(min(ends),max(ends))
    __rmul__=__mul__
    def bound(self):return max(abs(self.lo),abs(self.hi))
    def mid(self):return (self.lo+self.hi)/2
    def pair(self):return [str(self.lo),str(self.hi)]
    @staticmethod
    def read(x):return J(F(x[0]),F(x[1]))

def toJ(x):return x if isinstance(x,J) else J(x)
def floorq(x,scale=SCALE):return F(x.numerator*scale//x.denominator,scale)
def ceilq(x,scale=SCALE):return -floorq(-x,scale)
def nearq(x,scale):return floorq(F(x)+F(1,2*scale),scale)
def rounded(x):return J(floorq(x.lo),ceilq(x.hi))
def invsqrt(x):
    assert x.lo>0
    def floorinv(a):q=F(SCALE*SCALE,a);return math.isqrt(q.numerator//q.denominator)
    k=J(F(floorinv(x.hi),SCALE),F(floorinv(x.lo)+1,SCALE))
    assert k.lo>0 and k.hi>0 and k.lo*k.lo*x.hi<=1<=k.hi*k.hi*x.lo
    return k

def source(beta,k,R,I):
    G=lambda u,i:(u[(i+1)%8]-u[(i+7)%8])*F(1,2)
    return [J(beta[i])+k*(G(R,i)*G(R,i)+G(I,i)*G(I,i)+beta[i]*(R[i]*R[i]+I[i]*I[i])) for i in range(8)]

def residual(beta,u):
    return [(1+beta[i]-u[8])*u[i]-(u[(i+7)%8]+u[(i+1)%8])*F(1,2) for i in range(8)]+[(sum((u[i]*u[i] for i in range(8)),J(0))-1)*F(1,2)]

def derivative(beta,u):
    return [[(1+beta[i]-u[8])*(i==j)-F(1,2)*(j in [(i+7)%8,(i+1)%8])-u[i]*(j==8) for j in range(9)] for i in range(8)]+[[u[j] if j<8 else J(0) for j in range(9)]]

def mv(C,v):return [sum((C[i][j]*v[j] for j in range(9)),J(0)) for i in range(9)]
def root_checks(beta,z,r,C,q,y):
    D=derivative(beta,[J(x-r,x+r) for x in z])
    rows=[sum((J(i==j)-sum((C[i][k]*D[k][j] for k in range(9)),J(0))).bound() for j in range(9)) for i in range(9)]
    res=mv(C,residual(beta,[J(x) for x in z]))
    assert r>0 and 0<=q<1 and y>=0 and y+q*r<r and all(z[i]-r>0 for i in range(8))
    assert max(rows)<=q and max(x.bound() for x in res)<=y,(float(max(rows)),float(q),float(max(x.bound() for x in res)),float(y))
    return rows,res

def propose_root(beta):
    import numpy as np
    assert np.__version__=='1.26.4'
    midpoint=[x.mid() for x in beta];v=np.array([float(x) for x in midpoint]);H=np.diag(1+v)
    for i in range(8):H[i,(i+7)%8]=H[i,(i+1)%8]=-.5
    vals,vecs=np.linalg.eigh(H);u=vecs[:,0]
    if u.sum()<0:u=-u
    matrix=np.block([[H-vals[0]*np.eye(8),-u[:,None]],[u[None,:],np.zeros((1,1))]])
    C=[[nearq(F.from_float(float(t)),1<<80) for t in row] for row in np.linalg.inv(matrix)]
    z=[F.from_float(float(t)) for t in u]+[F.from_float(float(vals[0]))]
    for _ in range(4):
        correction=mv(C,residual([J(t) for t in midpoint],[J(t) for t in z]))
        z=[nearq(t-d.lo,1<<120) for t,d in zip(z,correction)]
    err=max(x.bound() for x in mv(C,residual(beta,[J(t) for t in z])))
    y=ceilq(err,1<<110)+F(1,1<<120)
    r=F(1,1<<120)
    while r<=2*y:r*=2
    q=F(1,100)
    root_checks(beta,z,r,C,q,y)
    return z,r,C,q,y

def update(R,I,G,K):
    a=sum((G[i]*R[i] for i in range(8)),J(0));h=sum((G[i]*I[i] for i in range(8)),J(0))
    rad=a*a+h*h
    assert K.lo*K.lo*rad.hi<=1<=K.hi*K.hi*rad.lo
    mR=[F(1,2)*R[i]+F(1,2)*(a*K*G[i]) for i in range(8)]
    mI=[F(1,2)*I[i]+F(1,2)*(-h*K*G[i]) for i in range(8)]
    norm=sum((mR[i]*mR[i]+mI[i]*mI[i] for i in range(8)),J(0))
    return rad,mR,mI,norm

def propose(count=16):
    data=json.loads(DATA.read_text());seed=data['fields'][0]
    beta=list(map(F.from_float,data['potential']));Rraw=list(map(F.from_float,seed['psi_re']));Iraw=list(map(F.from_float,seed['psi_im']))
    N=sum(x*x for x in Rraw+Iraw);initial_inverse=invsqrt(J(N))
    R=[rounded(J(x)*initial_inverse) for x in Rraw];I=[rounded(J(x)*initial_inverse) for x in Iraw]
    k=F.from_float(.3);tau=F.from_float(1e-10);steps=[]
    for n in range(count):
        pot=source(beta,k,R,I);z,r,C,q,y=propose_root(pot);G=[J(z[i]-r,z[i]+r) for i in range(8)]
        a=sum((G[i]*R[i] for i in range(8)),J(0));h=sum((G[i]*I[i] for i in range(8)),J(0));rad=a*a+h*h
        K=invsqrt(rad);rad,mR,mI,norm=update(R,I,G,K);L=invsqrt(norm)
        assert tau*tau<rad.lo and tau*tau<norm.lo
        outR=[rounded(L*x) for x in mR];outI=[rounded(L*x) for x in mI]
        steps.append(dict(input_re=[x.pair() for x in R],input_im=[x.pair() for x in I],
                          center=list(map(str,z)),radius=str(r),rate=str(q),residual_budget=str(y),
                          inverse=[[str(x) for x in row] for row in C],overlap_inverse=K.pair(),mixed_inverse=L.pair(),
                          output_re=[x.pair() for x in outR],output_im=[x.pair() for x in outI]))
        R,I=outR,outI
        print(n+1,'width',float(max(x.hi-x.lo for x in R+I)),'imag',float(max(x.bound() for x in I)),flush=True)
    return dict(kind='Exact rational witnesses;NumPy proposals only;Lean kernel return required',dyadic_bits=BITS,
                data_sha256=hashlib.sha256(DATA.read_bytes()).hexdigest(),coupling=str(k),tolerance=str(tau),
                initial_inverse=initial_inverse.pair(),initial_re=steps[0]['input_re'],initial_im=steps[0]['input_im'],steps=steps)

def replay(w):
    d=json.loads(DATA.read_text());beta=list(map(F.from_float,d['potential']));k=F(w['coupling']);tau=F(w['tolerance'])
    assert k==F.from_float(.3) and tau==F.from_float(1e-10) and w['data_sha256']==hashlib.sha256(DATA.read_bytes()).hexdigest()
    raw=[F.from_float(t) for key in ['psi_re','psi_im'] for t in d['fields'][0][key]];N=sum(t*t for t in raw)
    initial=J.read(w['initial_inverse']);assert initial.lo>0 and initial.hi>0 and initial.lo**2*N<=1<=initial.hi**2*N
    R=list(map(J.read,w['initial_re']));I=list(map(J.read,w['initial_im']))
    for vals,rr in [(R,raw[:8]),(I,raw[8:])]:
        for A,t in zip(vals,rr):a=J(t)*initial;assert A.lo<=a.lo and a.hi<=A.hi
    for p in w['steps']:
        assert p['input_re']==[x.pair() for x in R] and p['input_im']==[x.pair() for x in I]
        z=list(map(F,p['center']));r=F(p['radius']);C=[[F(x) for x in row] for row in p['inverse']]
        root_checks(source(beta,k,R,I),z,r,C,F(p['rate']),F(p['residual_budget']))
        G=[J(z[i]-r,z[i]+r) for i in range(8)];K=J.read(p['overlap_inverse']);rad,mR,mI,norm=update(R,I,G,K)
        L=J.read(p['mixed_inverse']);assert K.lo>0 and K.hi>0 and rad.lo>0 and L.lo>0 and L.hi>0 and norm.lo>0
        assert L.lo**2*norm.hi<=1<=L.hi**2*norm.lo and tau*tau<rad.lo and tau*tau<norm.lo
        R,I=list(map(J.read,p['output_re'])),list(map(J.read,p['output_im']))
        for vals,rr in [(R,mR),(I,mI)]:
            for A,t in zip(vals,rr):a=L*t;assert A.lo<=a.lo and a.hi<=A.hi
    return True

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--count',type=int,default=16)
    a=p.parse_args();w=propose(a.count);replay(w);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(w,indent=2)+'\n')
