"""Render populated whole-background-box finite transport certificates.

All numeric inputs are proposals until exact replay and closed Lean arithmetic
have passed. No floating solver is invoked by this renderer.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
from de_ground_native_prefix_render import q,vec,iv,box
from de_ground_offset_basin_generate import render as basin_render
ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_offset_transport_2026-10-04'

def proposal_packet(directory):
    points=[json.loads((directory/f'point{i:03d}.json').read_text()) for i in range(18)]
    assert [p['index'] for p in points]==list(range(18))
    assert sum(len(p['steps']) for p in points)==421
    sources=['results/ground_offsets_2026-10-04/witnesses.json',
      'results/ground_offset_stability_2026-10-04/witnesses.json',
      'results/ground_offset_basin_2026-10-04/witnesses.json',
      'results/ground_offset_prefix_2026-10-04/witnesses.json',
      'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py']
    return dict(kind='Whole input-hull original-seed finite transport proposals; closed Lean certificates required',
      points=points,source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources})

def sourcepath(name):return 'lean/SbtCosmo/Derivation/'+name.replace('.','/')+'.lean'

def render_step(i,p,n):
    d=p['steps'][n];g=d['whole'];point=d['point'];ref=p['references'][n];nextref=p['references'][n+1]
    old=dict(rho=d['radius'],basis_budget=p['basis_budget'],r=g['radius'],q=g['rate'],a=g['residual_budget'],rate=d['rate'],
      z=g['center'],C=g['inverse'],K=g['overlap_inverse'],L=g['mixed_inverse'],
      y=d['response_y'],error=d['response_error'],DG=d['DG'],DF=d['DF'])
    s=basin_render(dict(points=[old]))['lean/SbtCosmo/Derivation/GroundOffsetBasins/Point000.lean']
    s=s.replace('GroundOffsetBasins.Point000',f'GroundOffsetTransport.Point{i:03d}.Step{n:03d}')
    s=s.replace('GroundOffsets.Point000',f'GroundOffsets.Point{i:03d}').replace('GroundOffsetStability.Point000',f'GroundOffsetStability.Point{i:03d}')
    s=s.replace('/-! Closed kernel comparisons for an explicit native basin at an offset.\nThe input hull includes exact and rounded source backgrounds. -/',
      '/-! Closed finite transport comparisons, uniform over the input hull.\nThis step may expand: its native derivative bound need not be below one. -/')
    s='import SbtCosmo.Derivation.GroundCertifiedNativeTransportStep\nimport SbtCosmo.Derivation.GroundOriginalOffsetBasins\n'+s
    s=s.replace('open GroundRationalInterval GroundNativeBox','open GroundRationalInterval GroundNativeBox\nopen GroundNativeTransportGeometry GroundCertifiedNativeEntry')
    line=f'def input : StateBox := aroundBox GroundOffsets.Point{i:03d}.z GroundOffsets.Point{i:03d}.r ρ s\n'
    s=s.replace(line,f'def u : Fin 8 → ℚ := {vec(ref["re"])}\ndef v : Fin 8 → ℚ := {vec(ref["im"])}\n'+
      f'def next_u : Fin 8 → ℚ := {vec(nextref["re"])}\ndef next_v : Fin 8 → ℚ := {vec(nextref["im"])}\n'+
      f'def next_radius : ℚ := {q(d["next_radius"])}\ndef defect : ℚ := {q(d["defect"])}\n'+
      'def input : StateBox := around u v ρ s\n')
    s=s.replace('theorem rows : certificate.RowArithmetic := by\n  constructor\n  · decide +kernel\n  · decide +kernel\n',
      'theorem rows : GroundNativeTransportJets.RowBounds certificate := by\n  constructor\n  · decide +kernel\n')
    s=s.replace('theorem radius_pos : 0 < ρ','theorem radius_nonneg : 0 ≤ ρ')
    end='\nend\nend SbtCosmo.Derivation.'+f'GroundOffsetTransport.Point{i:03d}.Step{n:03d}'+'\n'
    assert s.endswith(end);s=s[:-len(end)]
    s+='\n-- Independent narrow reference-step enclosure for the centre defect.\n'
    s+='def pointInput : StateBox := around u v 0 s\n'
    s+=f'def pointOutput : StateBox := {box(point["output_re"],point["output_im"])}\n'
    for name,key in [('point_z','center'),('point_r','radius'),('point_q','rate'),('point_y','residual_budget')]:
      s+=f'def {name} : '+('Fin 9 → ℚ := '+vec(point[key]) if name=='point_z' else 'ℚ := '+q(point[key]))+'\n'
    s+='def point_C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vec(row) for row in point['inverse'])+']\n'
    s+=f'def point_K : Interval := {iv(point["overlap_inverse"])}\ndef point_L : Interval := {iv(point["mixed_inverse"])}\n'
    base=f'GroundOffsets.Point{i:03d}'
    s+=f'''
theorem point_ground : GroundBackgroundKernel.Arithmetic
    (GroundUncertainNativeBox.sourceBox {base}.B {base}.κ pointInput)
      point_z point_r point_q point_y point_C := by
  constructor <;> decide +kernel

theorem point_arithmetic : GroundUncertainNativeBox.Arithmetic {base}.B {base}.κ GroundNativePrefixInitial.τ
    pointInput pointOutput point_z point_r point_q point_y point_C point_K point_L := by
  constructor
  · exact point_ground
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · exact threshold_nonneg
  · decide +kernel
  · decide +kernel
  · unfold StateBox.Included included
    decide +kernel

def pointStep : GroundCertifiedNativePrefix.Step {base}.B {base}.κ GroundNativePrefixInitial.τ :=
  ⟨pointInput,pointOutput,point_z,point_r,point_q,point_y,point_C,point_K,point_L,point_arithmetic⟩

theorem defect_arithmetic : 0 ≤ defect ∧ 0 ≤ next_radius ∧
    certificate.rate*ρ+defect ≤ next_radius ∧ ∀ j : Fin 8,
      ((certificate.coordinateBox (differenceBox pointOutput (around next_u next_v 0 s))).R j).bound ≤ defect ∧
      ((certificate.coordinateBox (differenceBox pointOutput (around next_u next_v 0 s))).I j).bound ≤ defect := by
  decide +kernel

def transport : GroundCertifiedNativeTransportStep.Data {base}.B {base}.κ GroundNativePrefixInitial.τ
    (GroundOriginalOffsetBasins.T {i}) where
  u := u
  v := v
  next_u := next_u
  next_v := next_v
  radius := ρ
  next_radius := next_radius
  defect := defect
  s := s
  jet := certificate
  inputs := rfl
  coupling := rfl
  threshold := rfl
  frame := rfl
  input := rfl
  pointStep := pointStep
  point_input := rfl
  responses := responses
  response_included := response_included
  derivative_included := derivative_included
  rows := rows
  basis_nonneg := basis_nonneg
  basis_rows := basis_rows
  radius_nonneg := radius_nonneg
  next_radius_nonneg := defect_arithmetic.2.1
  defect_nonneg := defect_arithmetic.1
  defect_rows := defect_arithmetic.2.2.2
  budget := defect_arithmetic.2.2.1
'''
    return s+end

def render_steps(w):
    return {sourcepath(f'GroundOffsetTransport.Point{i:03d}.Step{n:03d}'):render_step(i,p,n)
      for i,p in enumerate(w['points']) for n in range(len(p['steps']))}

def cases(items):
    assert items
    return ''.join(f'Fin.cases {t} (\n  ' for t in items[:-1])+f'fun _ => {items[-1]}'+')'*(len(items)-1)

def render_family(i,p):
    N=len(p['steps']);ns=f'GroundOffsetTransport.Point{i:03d}'
    gamma=str(F(p['entry_bound'])-F(p['entry_radius']))
    imports=''.join(f'import SbtCosmo.Derivation.{ns}.Step{n:03d}\n' for n in range(N))
    refs=p['references'];radii=[p['initial_radius']]+[d['next_radius'] for d in p['steps']]
    return imports+f'''import SbtCosmo.Derivation.GroundOffsetTransportReturn

/-! Populated original-seed entry, uniform over this entire background box.
Every reference/radius seam and the distance to the actual root are earned. -/
namespace SbtCosmo.Derivation.{ns}
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundNativeTransportGeometry GroundCertifiedNativeEntry GroundOffsetTransportReturn
open Metric Filter
open scoped Topology

def N : ℕ := {N}
def u : Fin (N+1) → Fin 8 → ℚ := ![{', '.join(vec(t['re']) for t in refs)}]
def v : Fin (N+1) → Fin 8 → ℚ := ![{', '.join(vec(t['im']) for t in refs)}]
def radius : Fin (N+1) → ℚ := {vec(radii)}
def steps : Fin N → GroundCertifiedNativeTransportStep.Data (β {i}) (κ {i})
    GroundNativePrefixInitial.τ (GroundOriginalOffsetBasins.T {i}) :=
  {cases([f'{ns}.Step{n:03d}.transport' for n in range(N)])}

theorem source_seams : ∀ j : Fin N,
    (steps j).u = u j.castSucc ∧ (steps j).v = v j.castSucc ∧ (steps j).radius = radius j.castSucc := by
  intro j
  fin_cases j <;> exact ⟨rfl,rfl,rfl⟩

theorem target_seams : ∀ j : Fin N,
    (steps j).next_u = u j.succ ∧ (steps j).next_v = v j.succ ∧ (steps j).next_radius = radius j.succ := by
  intro j
  fin_cases j <;> exact ⟨rfl,rfl,rfl⟩

theorem initial_arithmetic : 0 ≤ radius 0 ∧ ∀ j : Fin 8,
    (((GroundOriginalOffsetBasins.data {i}).c.coordinateBox
      (differenceBox GroundOffsetPrefixInitial.initialBox (around (u 0) (v 0) 0 0))).R j).bound ≤ radius 0 ∧
    (((GroundOriginalOffsetBasins.data {i}).c.coordinateBox
      (differenceBox GroundOffsetPrefixInitial.initialBox (around (u 0) (v 0) 0 0))).I j).bound ≤ radius 0 := by
  decide +kernel

def certificate : Prefix {i} N where
  u := u
  v := v
  radius := radius
  steps := steps
  source_seams := source_seams
  target_seams := target_seams
  threshold_nonneg := {ns}.Step000.threshold_nonneg
  initial := by
    rw [mem_closedBall]
    exact coordinate_distance (GroundOriginalOffsetBasins.data {i}).c initial_arithmetic.1
      GroundOffsetPrefixInitial.original_seed_enclosed
      (point_enclosed (u 0) (v 0) (by norm_num : (0 : ℚ) ≤ 0) (by norm_num : (0 : ℚ) ≤ 0))
      initial_arithmetic.2

def γ : ℚ := {q(gamma)}
def δ : ℚ := {q(p['entry_bound'])}

theorem center_arithmetic : 0 ≤ γ ∧ ∀ j : Fin 8,
    (((GroundOriginalOffsetBasins.data {i}).c.coordinateBox (differenceBox
      (around (certificate.u (Fin.last N)) (certificate.v (Fin.last N)) 0 0)
      (negativeTargetBox (GroundOriginalOffsets.certificates {i}).z
        (GroundOriginalOffsets.certificates {i}).r))).R j).bound ≤ γ ∧
    (((GroundOriginalOffsetBasins.data {i}).c.coordinateBox (differenceBox
      (around (certificate.u (Fin.last N)) (certificate.v (Fin.last N)) 0 0)
      (negativeTargetBox (GroundOriginalOffsets.certificates {i}).z
        (GroundOriginalOffsets.certificates {i}).r))).I j).bound ≤ γ := by
  decide +kernel

theorem entry_arithmetic : 0 ≤ δ ∧ certificate.radius (Fin.last N)+γ ≤ δ ∧
    δ < (GroundOriginalOffsetBasins.data {i}).ρ := by decide +kernel

theorem distance {{b : Field}} (hb : ∀ j, (β {i} j).Contains (b j)) :
    dist ((GroundOriginalOffsetBasins.T {i}).symm (unpack (orbit {i} b N)))
      ((GroundOriginalOffsetBasins.T {i}).symm (-(GroundOriginalOffsetStability.wholeRoot {i} hb).1,0)) ≤ (δ : ℝ) := by
  have hc := center_distance {i} certificate hb center_arithmetic.1 center_arithmetic.2
  have hd := endpoint_distance {i} certificate hb hc
  have hbudget : (certificate.radius (Fin.last N) : ℝ)+(γ : ℝ) ≤ (δ : ℝ) := by
    exact_mod_cast entry_arithmetic.2.1
  exact hd.trans hbudget

theorem entry {{b : Field}} (hb : ∀ j, (β {i} j).Contains (b j)) :
    (GroundOriginalOffsetBasins.T {i}).symm (unpack (orbit {i} b N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T {i}).symm (-(GroundOriginalOffsetStability.wholeRoot {i} hb).1,0))
      ((GroundOriginalOffsetBasins.data {i}).ρ : ℝ) := by
  rw [mem_closedBall]
  exact (distance hb).trans (Rat.cast_le.mpr entry_arithmetic.2.2.le)

theorem seed_return {{b : Field}} (hb : ∀ j, (β {i} j).Contains (b j)) :
    Tendsto (orbit {i} b) atTop (nhds (realEmbed (-(GroundOriginalOffsetStability.wholeRoot {i} hb).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ {i} : ℝ) (orbit {i} b n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ {i} : ℝ) (1/2) (orbit {i} b n) ∧
      complexNormSq (orbit {i} b n) = 1 :=
  whole_seed_return {i} certificate hb (entry hb)
end
end SbtCosmo.Derivation.{ns}
'''

def render_families(w):
    return {sourcepath(f'GroundOffsetTransport.Point{i:03d}'):render_family(i,p) for i,p in enumerate(w['points'])}

def render_return(w):
    imports=''.join(f'import SbtCosmo.Derivation.GroundOffsetTransport.Point{i:03d}\n' for i in range(18))
    items=[f'⟨GroundOffsetTransport.Point{i:03d}.N, GroundOffsetTransport.Point{i:03d}.δ, '
      f'GroundOffsetTransport.Point{i:03d}.certificate, GroundOffsetTransport.Point{i:03d}.entry_arithmetic.1, '
      f'GroundOffsetTransport.Point{i:03d}.distance, GroundOffsetTransport.Point{i:03d}.entry⟩' for i in range(18)]
    return {sourcepath('GroundOriginalOffsetHullSeed'):imports+'''\n/-! Original-seed returns for every fixed background in all eighteen certified
boxes. This includes the exact uniform-offset and saved rounded-input models. -/
namespace SbtCosmo.Derivation.GroundOriginalOffsetHullSeed
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundOffsetTransportReturn
open Filter Metric
open scoped Topology

structure Data (i : Fin 18) where
  N : ℕ
  δ : ℚ
  c : Prefix i N
  nonneg : 0 ≤ δ
  distance : ∀ {b : Field} (hb : ∀ j, (β i j).Contains (b j)),
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤ (δ : ℝ)
  entry : ∀ {b : Field} (hb : ∀ j, (β i j).Contains (b j)),
    (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)

def data : (i : Fin 18) → Data i :=
  '''+cases(items)+'''

theorem entry_times : ∀ i : Fin 18, 15 ≤ (data i).N ∧ (data i).N ≤ 65 := by decide +kernel

theorem whole_background_box_original_seed_return (i : Fin 18) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) :
    Tendsto (orbit i b) atTop (nhds (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hb).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) (orbit i b n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) (orbit i b n) ∧
      complexNormSq (orbit i b n) = 1 :=
  whole_seed_return i (data i).c hb ((data i).entry hb)

theorem whole_background_box_original_geometric_tail (i : Fin 18) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) (n : ℕ) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b (n+(data i).N))))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤
      (GroundOriginalOffsetBasins.rate i : ℝ)^n * ((data i).δ : ℝ) := by
  exact (whole_seed_geometric_tail i hb ((data i).entry hb) n).trans
    (mul_le_mul_of_nonneg_left ((data i).distance hb) (pow_nonneg (GroundOriginalOffsetBasins.rate i).property n))

theorem exact_root_identity (i : Fin 18) :
    GroundOriginalOffsetStability.wholeRoot i (GroundOriginalOffsets.exact_inputs_sound i) =
      GroundOriginalOffsets.root i := rfl

theorem rounded_root_identity (i : Fin 18) :
    GroundOriginalOffsetStability.wholeRoot i (GroundOriginalOffsets.rounded_inputs_sound i) =
      GroundOriginalOffsets.roundedRoot i := rfl

theorem exact_uniform_offset_original_seed_return (i : Fin 18) :
    Tendsto (orbit i (GroundOriginalOffsets.b i)) atTop
      (nhds (realEmbed (-(GroundOriginalOffsets.root i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i) (κ i : ℝ)
        (orbit i (GroundOriginalOffsets.b i) n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.b i) (κ i : ℝ) (1/2)
        (orbit i (GroundOriginalOffsets.b i) n) ∧
      complexNormSq (orbit i (GroundOriginalOffsets.b i) n) = 1 := by
  simpa only [exact_root_identity] using
    whole_background_box_original_seed_return i (GroundOriginalOffsets.exact_inputs_sound i)

theorem rounded_original_seed_return (i : Fin 18) :
    Tendsto (orbit i (GroundOriginalOffsets.rounded_b i)) atTop
      (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ)
        (orbit i (GroundOriginalOffsets.rounded_b i) n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2)
        (orbit i (GroundOriginalOffsets.rounded_b i) n) ∧
      complexNormSq (orbit i (GroundOriginalOffsets.rounded_b i) n) = 1 := by
  simpa only [rounded_root_identity] using
    whole_background_box_original_seed_return i (GroundOriginalOffsets.rounded_inputs_sound i)

theorem whole_background_box_original_density_limit (i : Fin 18) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) (j : Fin 8) :
    Tendsto (fun n : ℕ => Complex.normSq (orbit i b n j)) atTop
      (nhds (Complex.normSq (realEmbed (GroundOriginalOffsetStability.wholeRoot i hb).1 j))) := by
  have hc : Continuous (fun x : ComplexField => Complex.normSq (x j)) := by fun_prop
  have ht := (hc.tendsto (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hb).1))).comp
    (whole_background_box_original_seed_return i hb).1
  simpa only [realEmbed,Pi.neg_apply,Complex.normSq_ofReal,mul_neg,neg_mul,neg_neg] using ht

theorem whole_background_box_eventual_density_separation {b₀ b₁ : Field}
    (h₀ : ∀ j, (β 0 j).Contains (b₀ j)) (h₁ : ∀ j, (β 17 j).Contains (b₁ j)) :
    ∀ᶠ n : ℕ in atTop, Complex.normSq (orbit 0 b₀ n 0)+9/100 < Complex.normSq (orbit 17 b₁ n 0) := by
  have h0 := whole_background_box_original_density_limit 0 h₀ 0
  have h17 := whole_background_box_original_density_limit 17 h₁ 0
  have hp : 0 < (GroundOriginalOffsetStability.wholeRoot 0 h₀).1 0 :=
    (GroundOriginalOffsetStability.tube 0 h₀).field_positive _
      (GroundOriginalOffsetStability.whole_root_return 0 h₀).1 0
  have hf := GroundOriginalOffsets.field_coordinate_separation
    (GroundOriginalOffsetBasins.root_field_box 0 h₀ 0) (GroundOriginalOffsetBasins.root_field_box 17 h₁ 0)
  have hg : Complex.normSq (realEmbed (GroundOriginalOffsetStability.wholeRoot 0 h₀).1 0)+9/100 <
      Complex.normSq (realEmbed (GroundOriginalOffsetStability.wholeRoot 17 h₁).1 0) := by
    simp only [realEmbed,Complex.normSq_ofReal,← pow_two]
    exact GroundOriginalOffsets.density_separation_of_positive hp hf
  have he := (tendsto_order.mp (h17.sub h0)).1 (9/100) (by linarith)
  filter_upwards [he] with n hn
  linarith
end
end SbtCosmo.Derivation.GroundOriginalOffsetHullSeed
'''}

def render(w):return render_steps(w)|render_families(w)|render_return(w)


def replay(w):
    """Exact checks for every reference, guard, point defect and whole-state jet."""
    import de_ground_native_prefix_generate as g
    import de_ground_basin_generate as jets
    from de_ground_offset_basin_generate import source
    J=g.J
    roots=json.loads((ROOT/'results/ground_offsets_2026-10-04/witnesses.json').read_text())['points']
    frames=json.loads((ROOT/'results/ground_offset_stability_2026-10-04/witnesses.json').read_text())['points']
    old=json.loads((ROOT/'results/ground_offset_prefix_2026-10-04/witnesses.json').read_text())['points']
    basins=json.loads((ROOT/'results/ground_offset_basin_2026-10-04/witnesses.json').read_text())['points']
    assert len(w['points'])==18 and sum(len(p['steps']) for p in w['points'])==421
    for path,h in w['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==h,path
    tau=F.from_float(1e-10)
    def bound_step(d,beta,k,X,Y):
        assert d['input_re']==[t.pair() for t in X] and d['input_im']==[t.pair() for t in Y]
        z=list(map(F,d['center']));r=F(d['radius']);C=[list(map(F,row)) for row in d['inverse']]
        q0=F(d['rate']);a=F(d['residual_budget'])
        g.root_checks(source(beta,k,X,Y),z,r,C,q0,a)
        G=[J(t-r,t+r) for t in z[:8]];K=J.read(d['overlap_inverse']);L=J.read(d['mixed_inverse'])
        rad,mR,mI,N=g.update(X,Y,G,K)
        for A,H in [(rad,K),(N,L)]:
            assert A.lo>tau*tau and H.lo>0 and H.hi>0 and H.lo**2*A.hi<=1<=H.hi**2*A.lo
        output=list(map(J.read,d['output_re']+d['output_im']))
        for cap,raw in zip(output,mR+mI):
            actual=L*raw;assert cap.lo<=actual.lo and actual.hi<=cap.hi
        return G,C,q0,K,L,output
    for i,p in enumerate(w['points']):
        r,c,o,b=roots[i],frames[i],old[i],basins[i]
        assert p['index']==i and p['background']==r['background_box'] and p['coupling']==r['coupling']
        assert p['reference_dyadic_bits']==100 and p['derivative_cache_bits']==80
        assert len(p['steps'])==len(o['steps']) and len(p['references'])==len(o['steps'])+1
        beta=list(map(J.read,p['background']));k=F(p['coupling'])
        S,P,R,Q=[[[F(t) for t in row] for row in c[key]] for key in ['S','P','R','Q']]
        s=F(p['basis_budget']);assert 0<=s and s==F(b['basis_budget'])
        assert max(sum(abs(t) for t in row) for row in S+R)<=s
        expected=[dict(re=[str(g.nearq(J.read(t).mid(),1<<100)) for t in o['steps'][0]['input_re']],
          im=[str(g.nearq(J.read(t).mid(),1<<100)) for t in o['steps'][0]['input_im']])]
        expected += [dict(re=[str(g.nearq(J.read(t).mid(),1<<100)) for t in d['output_re']],
          im=[str(g.nearq(J.read(t).mid(),1<<100)) for t in d['output_im']]) for d in o['steps']]
        assert p['references']==expected
        refs=[(list(map(F,t['re'])),list(map(F,t['im']))) for t in p['references']]
        x,y=refs[0]
        initR=[J.read(t)-J(v) for t,v in zip(o['steps'][0]['input_re'],x)]
        initI=[J.read(t)-J(v) for t,v in zip(o['steps'][0]['input_im'],y)]
        delta=F(p['initial_radius']);assert 0<=delta
        assert max(t.bound() for t in jets.matvec(P,initR)+jets.matvec(Q,initI))<=delta
        maximum=delta
        for n,d in enumerate(p['steps']):
            x,y=refs[n];nx,ny=refs[n+1];assert d['index']==n and F(d['radius'])==delta
            _,_,_,_,_,pointout=bound_step(d['point'],beta,k,list(map(J,x)),list(map(J,y)))
            a=F(d['defect']);assert 0<=a
            pointdiff=jets.matvec(P,[t-J(v) for t,v in zip(pointout[:8],nx)])+jets.matvec(Q,[t-J(v) for t,v in zip(pointout[8:],ny)])
            assert max(t.bound() for t in pointdiff)<=a
            X=[J(t-s*delta,t+s*delta) for t in x];Y=[J(t-s*delta,t+s*delta) for t in y]
            G,C,q0,K,L,_=bound_step(d['whole'],beta,k,X,Y)
            columns=[]
            for j in range(16):
                DG=list(map(J.read,d['DG'][j]));FR=list(map(J.read,d['DF'][j][0]));FI=list(map(J.read,d['DF'][j][1]))
                yy,ee=F(d['response_y'][j]),F(d['response_error'][j])
                _,_,raw,_,_=jets.derivative(beta,k,X,Y,G,C,q0,K,L,j,S,R,yy,ee)
                assert all(cap.lo<=val.lo and val.hi<=cap.hi for cap,val in zip(DG,raw))
                _,_,_,fr,fi=jets.derivative(beta,k,X,Y,G,C,q0,K,L,j,S,R,yy,ee,DG)
                assert all(cap.lo<=val.lo and val.hi<=cap.hi for cap,val in zip(FR+FI,fr+fi))
                columns.append(jets.matvec(P,FR)+jets.matvec(Q,FI))
            M=F(d['rate']);assert 0<=M
            assert max(sum(columns[j][l].bound() for j in range(16)) for l in range(16))<=M
            nd=F(d['next_radius']);assert 0<=nd and M*delta+a<=nd
            delta=nd;maximum=max(maximum,delta)
        x,y=refs[-1];z=list(map(F,r['z']));rootradius=F(r['r']);rho=F(b['rho'])
        target=jets.matvec(P,[J(x[j])+J(z[j]-rootradius,z[j]+rootradius) for j in range(8)])+jets.matvec(Q,list(map(J,y)))
        assert F(p['entry_radius'])==delta and F(p['maximum_transport_radius'])==maximum
        assert max(t.bound() for t in target)+delta<=F(p['entry_bound'])<rho==F(p['rho'])
    return True


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--proposal-dir',type=Path)
    parser.add_argument('--check',action='store_true',help='Compare generated sources without writing')
    parser.add_argument('--replay',action='store_true',help='Replay every certificate with exact Fraction arithmetic')
    args=parser.parse_args()
    witness=PACKET/'witnesses.json'
    if witness.exists():
        w=json.loads(witness.read_text())
        if args.proposal_dir:assert w==proposal_packet(args.proposal_dir)
    else:
        assert args.proposal_dir and not args.check,'Initial generation requires a proposal directory'
        w=proposal_packet(args.proposal_dir)
    if args.replay:
        assert replay(w)
        print('Exact replay passed for all18 input hulls and421 transport steps',flush=True)
    generated=render(w)
    if args.check:
        for path,text in generated.items():assert (ROOT/path).read_text()==text,path
        print('Read-only generation comparison passed for',len(generated),'populated transport modules')
    else:
        for path,text in generated.items():
            out=ROOT/path
            if out.exists():assert out.read_text()==text,path
        PACKET.mkdir(exist_ok=True)
        if not witness.exists():witness.write_text(json.dumps(w,indent=2)+'\n')
        created=0
        for path,text in generated.items():
            out=ROOT/path
            if not out.exists():
                out.parent.mkdir(parents=True,exist_ok=True);out.write_text(text);created+=1
        print('Rendered',created,'new modules;',len(generated),'total populated modules; closed Lean verification required')
