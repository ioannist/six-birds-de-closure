"""Exact proposals for eighteen whole-background-box Newton certificates.

Each box covers both the exact uniform shift and the saved rounded source input.
Saved numerical roots/preconditioners are proposals; Lean must certify all rows.
"""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib
import de_ground_continuation_generate as cg
from de_ground_kernel_tube_generate import rational,vector
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'results/ground_interval_2026-10-03/witnesses.json'
BRANCH=ROOT/'results/ground_branch_2026-10-03/witnesses.json'
OUT=ROOT/'lean/SbtCosmo/Derivation/GroundOffsets'
PACKET=ROOT/'results/ground_offsets_2026-10-04'
PARAMETERS=[-8,-5,-3,-2,-1,-.5,-.2,-.1,0,.1,.2,.5,1,2,3,5,8,10]

def proposals():
 old=json.loads(SOURCE.read_text());branch=json.loads(BRANCH.read_text())
 assert old['scale']==str(2**80)
 base=[F.from_float(float.fromhex(t)) for t in branch['background_hex']]
 ws=[w for w in old['witnesses'] if w['sweep']=='background']
 assert len(ws)==18 and len(base)==8
 out=[]
 for w,p in zip(ws,PARAMETERS):
  offset=F.from_float(float.fromhex(w['parameter_hex']));κ=F.from_float(float.fromhex(w['coupling_hex']))
  assert offset==F.from_float(float(p)) and κ==F.from_float(.3)
  rounded=[F.from_float(float.fromhex(t)) for t in w['background_hex']]
  assert rounded==[F.from_float(float(t)+float(offset)) for t in base]
  exact=[b+offset for b in base]
  assert len(rounded)==8
  B=[cg.Interval(min(a,b),max(a,b)) for a,b in zip(exact,rounded)]
  d=cg.propose(dict(w,coupling=str(κ)),B)
  out.append(dict(offset=str(offset),coupling=str(κ),background_box=[[str(t.lo),str(t.hi)] for t in B],
   exact_background=list(map(str,exact)),rounded_background=list(map(str,rounded)),
   z=list(map(str,d['z'])),r=str(d['r']),q=str(d['q']),y=str(d['y']),C=[[str(t) for t in row] for row in d['C']]))
 return dict(kind='Whole background boxes; exact Fraction proposals; Lean kernel checks required',
  witness_source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),base_source_sha256=hashlib.sha256(BRANCH.read_bytes()).hexdigest(),points=out)

def render(w):
 out={}
 assert len(w['points'])==18
 for n,d in enumerate(w['points']):
  name=f'Point{n:03d}'
  s='''import SbtCosmo.Derivation.GroundUncertainBackgroundTube
import SbtCosmo.Derivation.GroundOriginalFirstTube

/-! A complete whole-background-box root certificate at an original offset.
Both exact uniform shifts and saved rounded input vectors lie in this box. -/
namespace SbtCosmo.Derivation.GroundOffsets.'''+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundOriginalFirstTube GroundRationalInterval

'''
  s+='def offset : ℚ := '+rational(F(d['offset']))+'\n'
  s+='def κ : ℚ := '+rational(F(d['coupling']))+'\n'
  s+='def exactBackground : Fin 8 → ℚ := fun i => originalBackground i+offset\n'
  s+='def roundedBackground : Fin 8 → ℚ := '+vector(list(map(F,d['rounded_background'])))+'\n'
  s+='def B : Fin 8 → Interval := !['+', '.join('⟨'+rational(F(a))+', '+rational(F(b))+'⟩' for a,b in d['background_box'])+']\n'
  for k in ['r','q','y']:s+='def '+k+' : ℚ := '+rational(F(d[k]))+'\n'
  s+='def z : Fin 9 → ℚ := '+vector(list(map(F,d['z'])))+'\n'
  s+='def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vector(list(map(F,row))) for row in d['C'])+']\n'
  s+='''
theorem backgrounds_arithmetic : ∀ i : Fin 8,
    (B i).lo ≤ exactBackground i ∧ exactBackground i ≤ (B i).hi ∧
    (B i).lo ≤ roundedBackground i ∧ roundedBackground i ≤ (B i).hi := by decide +kernel

theorem arithmetic : GroundUncertainBackgroundTube.Arithmetic B κ κ z r q y C := by
  constructor <;> decide +kernel

end
end SbtCosmo.Derivation.GroundOffsets.'''+name+'\n'
  out['lean/SbtCosmo/Derivation/GroundOffsets/'+name+'.lean']=s
 return out

if __name__=='__main__':
 PACKET.mkdir(exist_ok=True);OUT.mkdir(exist_ok=True)
 w=proposals();(PACKET/'witnesses.json').write_text(json.dumps(w,indent=2)+'\n')
 for p,s in render(w).items():(ROOT/p).write_text(s)
 print('Proposed eighteen whole-background-box root certificates, covering exact and rounded inputs')
