"""Render populated rounded-offset original-seed prefix proposals as kernel proofs.

This renderer never runs a floating solver. All step inequalities remain kernel
obligations. Prefixes stop at the proposed entry; later source verdicts are separate.
"""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
from de_ground_native_prefix_render import q,vec,iv,box
ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_offset_prefix_2026-10-04'

def proposal_packet(directory):
    points=[]
    for i in range(18):
        w=json.loads((directory/f'point{i:03d}.json').read_text())
        assert w['offset_index']==i and w['model']=='rounded_background' and w['entry']['sign']==-1
        n=w['entry']['step'];assert 0<n<=len(w['steps'])
        w=dict(w,steps=w['steps'][:n])
        # Outward dyadic bound for the proposed coordinate entry distance.
        d=F(w['entry']['distance']);scale=1<<100
        w['entry_bound']=str(F(-(-d.numerator*scale//d.denominator),scale))
        points.append(w)
    assert all(p[k]==points[0][k] for p in points for k in ['initial_inverse','initial_re','initial_im'])
    src=['results/ground_offsets_2026-10-04/witnesses.json','results/ground_offset_stability_2026-10-04/witnesses.json','results/ground_offset_basin_2026-10-04/witnesses.json']
    return dict(kind='Rounded input original-seed basin-entry proposals; kernel proofs required',points=points,source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in src})

def render_steps(w):
    files={}
    for i,p in enumerate(w['points']):
        prefix=f'GroundOffsetPrefix.Point{i:03d}'
        old=f'GroundOffsets.Point{i:03d}'
        for n,d in enumerate(p['steps']):
            name=prefix+f'.Step{n:03d}'
            s=f'import SbtCosmo.Derivation.GroundCertifiedNativePrefix\nimport SbtCosmo.Derivation.{old}\nimport SbtCosmo.Derivation.GroundNativePrefixInitial\n\n'
            s+='''/-! Whole-step kernel obligations for the exact mathematical original seed.
The rounded background is a fixed exact rational input; IEEE operations are not emulated. -/
namespace SbtCosmo.Derivation.'''+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundNativeBox GroundRationalInterval

'''
            s+=f'def β : Fin 8 → Interval := fun i => Interval.point ({old}.roundedBackground i)\n'
            s+=f'def input : StateBox := {box(d["input_re"],d["input_im"])}\ndef output : StateBox := {box(d["output_re"],d["output_im"])}\n'
            s+=f'def z : Fin 9 → ℚ := {vec(d["center"])}\ndef r : ℚ := {q(d["radius"])}\ndef q : ℚ := {q(d["rate"])}\ndef y : ℚ := {q(d["residual_budget"])}\n'
            s+='def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vec(row) for row in d['inverse'])+']\n'
            s+=f'def K : Interval := {iv(d["overlap_inverse"])}\ndef L : Interval := {iv(d["mixed_inverse"])}\n\n'
            s+=f'''theorem ground_arithmetic : GroundBackgroundKernel.Arithmetic
    (GroundUncertainNativeBox.sourceBox β {old}.κ input) z r q y C := by
  constructor <;> decide +kernel

theorem arithmetic : GroundUncertainNativeBox.Arithmetic β {old}.κ GroundNativePrefixInitial.τ
    input output z r q y C K L := by
  constructor
  · exact ground_arithmetic
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold StateBox.Included included
    decide +kernel

def step : GroundCertifiedNativePrefix.Step β {old}.κ GroundNativePrefixInitial.τ :=
  ⟨input,output,z,r,q,y,C,K,L,arithmetic⟩

end
end SbtCosmo.Derivation.{name}
'''
            files['lean/SbtCosmo/Derivation/'+name.replace('.','/')+'.lean']=s
    return files

if __name__=='__main__':
    import argparse
    a=argparse.ArgumentParser();a.add_argument('--proposal-dir',type=Path,required=True);opts=a.parse_args()
    w=proposal_packet(opts.proposal_dir);PACKET.mkdir(exist_ok=True)
    (PACKET/'witnesses.json').write_text(json.dumps(w,indent=2)+'\n')
    for p,s in render_steps(w).items():
        out=ROOT/p;out.parent.mkdir(parents=True,exist_ok=True);out.write_text(s)
    print('Rendered prefix lengths:',[len(p['steps']) for p in w['points']])
    print('Arithmetic leaves:',sum(len(p['steps']) for p in w['points']))


def replay_point(w,root,basis,basin):
    """Exact replay of every original-seed normalization, step and entry row."""
    import de_ground_native_prefix_generate as g
    J=g.J
    assert w['model']=='rounded_background' and w['entry']['sign']==-1
    assert len(w['steps'])==w['entry']['step']
    assert len(w['initial_re'])==len(w['initial_im'])==8 and len(w['initial_inverse'])==2
    d=json.loads(g.DATA.read_text());raw=[F.from_float(t) for k in ['psi_re','psi_im'] for t in d['fields'][0][k]]
    norm=sum(t*t for t in raw);K=J.read(w['initial_inverse'])
    assert K.lo>0 and K.hi>0 and K.lo**2*norm<=1<=K.hi**2*norm
    R=list(map(J.read,w['initial_re']));I=list(map(J.read,w['initial_im']))
    for A,t in zip(R+I,raw):
        v=J(t)*K;assert A.lo<=v.lo and v.hi<=A.hi
    beta=list(map(F,root['rounded_background']));k=F(root['coupling']);tau=F.from_float(1e-10)
    for p in w['steps']:
        assert p['input_re']==[t.pair() for t in R] and p['input_im']==[t.pair() for t in I]
        assert len(p['center'])==9 and len(p['inverse'])==9 and all(len(row)==9 for row in p['inverse'])
        assert len(p['output_re'])==len(p['output_im'])==8
        z=list(map(F,p['center']));r=F(p['radius']);C=[[F(t) for t in row] for row in p['inverse']]
        g.root_checks(g.source(beta,k,R,I),z,r,C,F(p['rate']),F(p['residual_budget']))
        G=[J(t-r,t+r) for t in z[:8]];K=J.read(p['overlap_inverse']);L=J.read(p['mixed_inverse'])
        rad,mR,mI,norm=g.update(R,I,G,K)
        assert K.lo>0 and K.hi>0 and L.lo>0 and L.hi>0 and tau**2<rad.lo and tau**2<norm.lo
        assert L.lo**2*norm.hi<=1<=L.hi**2*norm.lo
        R=list(map(J.read,p['output_re']));I=list(map(J.read,p['output_im']))
        for A,t in zip(R+I,mR+mI):
            v=L*t;assert A.lo<=v.lo and v.hi<=A.hi
    center=list(map(F,root['z']));r0=F(root['r'])
    # Original seed approaches the negative representative: compare -z to +u.
    dR=[-R[i]-J(center[i]-r0,center[i]+r0) for i in range(8)];dI=[-t for t in I]
    cols=[sum((F(row[j])*v[j] for j in range(8)),J(0)) for A,v in [(basis['P'],dR),(basis['Q'],dI)] for row in A]
    distance=max(t.bound() for t in cols)
    assert distance==F(w['entry']['distance']) and distance<=F(w['entry_bound'])<F(basin['rho'])
    return distance


def render_families(w):
    files={}
    for i,p in enumerate(w['points']):
        N=len(p['steps']);name=f'GroundOffsetPrefix.Point{i:03d}';old=f'GroundOffsets.Point{i:03d}'
        modules=[name+f'.Step{n:03d}' for n in range(N)]
        s=''.join('import SbtCosmo.Derivation.'+m+'\n' for m in modules)
        s+='import SbtCosmo.Derivation.GroundOffsetSeedReturn\n\n'
        s+='''/-! Populated rounded-offset original-seed entry into the actual negative basin.
Every finite seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.'''+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundCertifiedNativeEntry GroundOffsetSeedReturn GroundUncertainNativeBasin.Certificate
open Metric

'''
        s+=f'def N : ℕ := {N}\ndef δ : ℚ := {q(p["entry_bound"])}\n'
        s+=f'def steps : Fin N → GroundCertifiedNativePrefix.Step (β {i}) (κ {i}) GroundNativePrefixInitial.τ :=\n  '
        s+=''.join('Fin.cases '+m+'.step (\n  ' for m in modules[:-1])+'fun _ => '+modules[-1]+'.step'+')'*(N-1)+'\n\n'
        s+='''theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel

'''
        s+=f'''def certificate : Prefix {i} N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundNativePrefix.Step000.arithmetic.threshold_nonneg
  seams := seams

'''
        # Use the directly certified threshold fact, rather than an unrelated step.
        s=s.replace('GroundNativePrefix.Step000.arithmetic.threshold_nonneg','GroundOffsetBasins.Point000.threshold_nonneg')
        s+=f'def targetBox : StateBox := negativeTargetBox {old}.z {old}.r\n'
        s+=f'def entryBox : StateBox := {modules[-1]}.output\n\n'
        s+=f'''theorem entry_arithmetic : ∀ j : Fin 8,
    ((((GroundOriginalOffsetBasins.data {i}).c).coordinateBox (differenceBox entryBox targetBox)).R j).bound ≤ δ ∧
    ((((GroundOriginalOffsetBasins.data {i}).c).coordinateBox (differenceBox entryBox targetBox)).I j).bound ≤ δ := by
  decide +kernel

theorem entry_margin : 0 ≤ δ ∧ δ < (GroundOriginalOffsetBasins.data {i}).ρ := by decide +kernel

theorem distance : dist ((GroundOriginalOffsetBasins.T {i}).symm (unpack (orbit {i} N)))
    ((GroundOriginalOffsetBasins.T {i}).symm (-(GroundOriginalOffsets.roundedRoot {i}).1,0)) ≤ (δ : ℝ) := by
  have hx : entryBox.Contains (unpack (orbit {i} N)) := by
    have h := certificate.enclosed (background_sound {i}) (Fin.last N)
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using h
  have ht : targetBox.Contains (-(GroundOriginalOffsets.roundedRoot {i}).1,0) :=
    negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box {i}
      (GroundOriginalOffsets.rounded_inputs_sound {i}))
  exact coordinate_distance (GroundOriginalOffsetBasins.data {i}).c entry_margin.1 hx ht entry_arithmetic

theorem entry : (GroundOriginalOffsetBasins.T {i}).symm (unpack (orbit {i} N)) ∈ closedBall
    ((GroundOriginalOffsetBasins.T {i}).symm (-(GroundOriginalOffsets.roundedRoot {i}).1,0))
    ((GroundOriginalOffsetBasins.data {i}).ρ : ℝ) := by
  rw [mem_closedBall]
  exact distance.trans (Rat.cast_le.mpr entry_margin.2.le)

end
end SbtCosmo.Derivation.{name}
'''
        files['lean/SbtCosmo/Derivation/'+name.replace('.','/')+'.lean']=s
    return files
