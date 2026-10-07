"""Render certificates for the original eighteen rounded-offset 60-update verdicts.

Proposals are external inputs until exact replay and closed Lean arithmetic pass.
This renderer never invokes a floating solver and preserves every earlier source.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
from de_ground_offset_prefix_render import render_steps as old_render_steps
from de_ground_native_prefix_render import q,vec,iv,box

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_offset_sixty_2026-10-04'
OLD='results/ground_offset_prefix_2026-10-04/witnesses.json'
ROOTS='results/ground_offsets_2026-10-04/witnesses.json'
BASINS='results/ground_offset_basin_2026-10-04/witnesses.json'
EXTENSIONS=[0,2,3,16,17]
DIRECT_PASSES=[0,3,16]
FAILURES=[(1,4,-1),(2,5,1),(17,6,1)]

def proposal_packet(directory,sixty,fast):
    old=json.loads((ROOT/OLD).read_text())['points']
    full=[json.loads((directory/f'point{i:03d}.json').read_text()) for i in range(18)]
    for i,p in enumerate(full):
        assert p['offset_index']==i and p['model']=='rounded_background'
        assert p['steps'][:len(old[i]['steps'])]==old[i]['steps']
    candidates=json.loads(sixty.read_text())
    assert [p['index'] for p in candidates if not p['four_tests_sufficient']]==[1,2,17]
    fast_rows=json.loads(fast.read_text());assert [p['index'] for p in fast_rows]==list(range(4,16))
    extensions=[dict(index=i,start=len(old[i]['steps']),steps=full[i]['steps'][len(old[i]['steps']):60]) for i in EXTENSIONS]
    assert sum(len(p['steps']) for p in extensions)==132
    sources=[OLD,ROOTS,BASINS,
      'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py']
    return dict(kind='Original rounded offset fixed60 verdict proposals; closed Lean certificates required',
      extensions=extensions,direct_passes=[candidates[i] for i in DIRECT_PASSES],fast_passes=fast_rows,
      failures=[dict(index=i,coordinate=j,sign=s) for i,j,s in FAILURES],
      source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources})

def sourcepath(name):return 'lean/SbtCosmo/Derivation/'+name.replace('.','/')+'.lean'

def render_extensions(w):
    old=json.loads((ROOT/OLD).read_text())['points']
    points=[dict(steps=[]) for _ in range(18)]
    for p in w['extensions']:
        i=p['index'];assert p['start']==len(old[i]['steps'])
        points[i]['steps']=old[i]['steps']+p['steps'];assert len(points[i]['steps'])==60
    generated=old_render_steps(dict(points=points));out={}
    for p in w['extensions']:
        i=p['index']
        for n in range(p['start'],60):
            name=f'GroundOffsetPrefix.Point{i:03d}.Step{n:03d}'
            s=generated[sourcepath(name)].replace('GroundOffsetPrefix','GroundOffsetSixtyPrefix')
            out[sourcepath(name.replace('GroundOffsetPrefix','GroundOffsetSixtyPrefix'))]=s
    assert len(out)==132
    return out

def render_prefixes(w):
    out={}
    for p in w['extensions']:
        i=p['index'];name=f'GroundOffsetSixtyPrefix.Point{i:03d}'
        modules=[f'GroundOffsetPrefix.Point{i:03d}.Step{n:03d}' if n<p['start'] else name+f'.Step{n:03d}' for n in range(60)]
        s='import SbtCosmo.Derivation.'+f'GroundOffsetPrefix.Point{i:03d}'+'\n'
        s+=''.join('import SbtCosmo.Derivation.'+m+'\n' for m in modules[p['start']:])
        s+='\n/-! Earned original rounded-input enclosures at iterations59 and60. -/\nnamespace SbtCosmo.Derivation.'+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval GroundOffsetSeedReturn

def N : ℕ := 60
'''
        s+=f'def steps : Fin N → GroundCertifiedNativePrefix.Step (β {i}) (κ {i}) GroundNativePrefixInitial.τ :=\n  '
        s+=''.join('Fin.cases '+m+'.step (\n  ' for m in modules[:-1])+f'fun _ => {modules[-1]}.step'+')'*59+'\n\n'
        s+='''theorem seams : ∀ j : Fin N,
    (Fin.cases GroundOffsetPrefixInitial.initialBox (fun k => (steps k).output) j.castSucc) =
      (steps j).input := by decide +kernel
'''
        s+=f'''
def certificate : Prefix {i} N where
  first := GroundOffsetPrefixInitial.initialBox
  steps := steps
  initial := GroundOffsetPrefixInitial.original_seed_enclosed
  threshold_nonneg := GroundOffsetBasins.Point000.threshold_nonneg
  seams := seams

def previousBox : StateBox := {modules[58]}.output
def currentBox : StateBox := {modules[59]}.output

theorem previous_enclosed : previousBox.Contains (unpack (orbit {i} 59)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound {i}) ⟨59,by decide⟩

theorem current_enclosed : currentBox.Contains (unpack (orbit {i} 60)) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      certificate.enclosed (background_sound {i}) (Fin.last N)

end
end SbtCosmo.Derivation.{name}
'''
        out[sourcepath(name)]=s
    return out

def write_sources(generated):
    for p,s in generated.items():
        out=ROOT/p;assert not out.exists(),p
        out.parent.mkdir(parents=True,exist_ok=True);out.write_text(s)

def replay(w):
    """Exact replay of new steps, sourced candidates and finite verdict budgets."""
    import de_ground_native_prefix_generate as g
    from de_ground_offset_basin_generate import source
    J=g.J
    old=json.loads((ROOT/OLD).read_text())['points']
    roots=json.loads((ROOT/ROOTS).read_text())['points']
    basins=json.loads((ROOT/BASINS).read_text())['points']
    final={}
    assert [p['index'] for p in w['extensions']]==EXTENSIONS
    for p in w['extensions']:
        i=p['index'];r=roots[i];assert p['start']==len(old[i]['steps'])
        assert p['start']+len(p['steps'])==60
        beta=list(map(F,r['rounded_background']));k=F(r['coupling']);tau=F.from_float(1e-10)
        R=list(map(J.read,old[i]['steps'][-1]['output_re']));I=list(map(J.read,old[i]['steps'][-1]['output_im']))
        for d in p['steps']:
            assert d['input_re']==[t.pair() for t in R] and d['input_im']==[t.pair() for t in I]
            z=list(map(F,d['center']));radius=F(d['radius']);C=[list(map(F,row)) for row in d['inverse']]
            g.root_checks(g.source(beta,k,R,I),z,radius,C,F(d['rate']),F(d['residual_budget']))
            G=[J(t-radius,t+radius) for t in z[:8]];K=J.read(d['overlap_inverse']);L=J.read(d['mixed_inverse'])
            rad,mr,mi,norm=g.update(R,I,G,K)
            for A,H in [(rad,K),(norm,L)]:
                assert H.lo>0 and H.hi>0 and A.lo>tau*tau and H.lo**2*A.hi<=1<=H.hi**2*A.lo
            R=list(map(J.read,d['output_re']));I=list(map(J.read,d['output_im']))
            for B,t in zip(R+I,mr+mi):
                a=L*t;assert B.lo<=a.lo and a.hi<=B.hi
        final[i]=d
    final[1]=old[1]['steps'][59]
    assert [p['index'] for p in w['direct_passes']]==DIRECT_PASSES
    epsilon=F.from_float(1e-8)
    for p in w['direct_passes']:
        i=p['index'];d=final[i];r=roots[i]
        R=list(map(J.read,d['output_re']));I=list(map(J.read,d['output_im']))
        beta=list(map(F,r['rounded_background']));k=F(r['coupling']);V=g.source(beta,k,R,I)
        z=list(map(F,p['linear_center']));radius=F(p['linear_radius']);C=[list(map(F,row)) for row in p['linear_inverse']]
        g.root_checks(V,z,radius,C,F(p['linear_rate']),F(p['linear_residual']))
        G=[J(t-radius,t+radius) for t in z[:8]]
        difference=[R[j]+G[j] for j in range(8)]+I
        assert sum(t.bound()**2 for t in difference)<=F(p['candidate_distance'])**2
        delta=[J.read(a)-J.read(b) for part in ['re','im'] for a,b in zip(d['output_'+part],d['input_'+part])]
        assert sum(t.bound()**2 for t in delta)<=F(p['update_distance'])**2
        A=F(min(t.lo for t in V).__floor__());B=F(max(t.hi for t in V).__ceil__())
        assert F(p['potential_lower'])==min(t.lo for t in V) and F(p['potential_upper'])==max(t.hi for t in V)
        distance=F(p['candidate_distance']);update=F(p['update_distance'])
        assert update<epsilon and 4*distance<epsilon and (2+B-A)*(distance+distance**2)<epsilon
    assert [p['index'] for p in w['fast_passes']]==list(range(4,16))
    for p in w['fast_passes']:
        i=p['index'];r=roots[i];b=basins[i];N=len(old[i]['steps']);delta=F(old[i]['entry_bound']);rate=F(b['rate']);s=F(b['basis_budget'])
        a=F(p['selector_budget']);d=F(p['d']);A=F(p['potential_lower']);B=F(p['potential_upper'])
        assert a>=0 and max(sum(J.read(b['DG'][j][l]).bound() for j in range(16)) for l in range(8))<=a
        z=list(map(F,r['z']));radius=F(r['r']);rho=F(b['rho'])
        X=[J(t-radius-rho*s,t+radius+rho*s) for t in z[:8]];Y=[J(-rho*s,rho*s) for _ in range(8)]
        V=source(list(map(J.read,r['background_box'])),F(r['coupling']),X,Y)
        assert all(A<=t.lo and t.hi<=B for t in V)
        candidate=4*(s+a)*rate**(60-N)*delta;update=4*s*(rate**(59-N)+rate**(60-N))*delta
        assert candidate==F(p['candidate_tail_bound']) and update==F(p['update_tail_bound'])
        assert candidate<=d and update<=d and 4*d<epsilon and (2+B-A)*(d+d*d)<epsilon
    assert [(p['index'],p['coordinate'],p['sign']) for p in w['failures']]==FAILURES
    for p in w['failures']:
        d=final[p['index']];j=p['coordinate'];delta=J.read(d['output_re'][j])-J.read(d['input_re'][j])
        assert (p['sign']>0 and epsilon<delta.lo) or (p['sign']<0 and epsilon<-delta.hi)
    return True

def render_failures(w):
    out={}
    for p in w['failures']:
        i=p['index'];j=p['coordinate'];name=f'GroundOffsetSixtyTests.Point{i:03d}'
        prefix=f'GroundOffsetPrefix.Point{i:03d}' if i==1 else f'GroundOffsetSixtyPrefix.Point{i:03d}'
        s=f'import SbtCosmo.Derivation.{prefix}\n'
        s+='import SbtCosmo.Derivation.GroundComplexCoordinateBudget\nimport SbtCosmo.Derivation.GroundOriginalResiduals\n'
        s+='\n/-! Failure of the actual source conjunction from a strict last-update lower bound. -/\nnamespace SbtCosmo.Derivation.'+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundOffsetSeedReturn GroundSourceDiagnostics GroundComplexEuclidean
open GroundComplexCoordinateBudget

'''
        if i==1:
            s+=f'def previousBox : StateBox := {prefix}.Step058.output\ndef currentBox : StateBox := {prefix}.Step059.output\n'
        else:
            s+=f'def previousBox : StateBox := {prefix}.previousBox\ndef currentBox : StateBox := {prefix}.currentBox\n'
        for n,label in [(59,'previous'),(60,'current')]:
            s+=f'\ntheorem {label}_enclosed : {label}Box.Contains (unpack (orbit {i} {n})) := by\n'
            if i==1:
                s+=f'''  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using
      {prefix}.certificate.enclosed (background_sound {i}) ⟨{n},by decide⟩
'''
            else:s+=f'  exact {prefix}.{label}_enclosed\n'
        s+='''
def difference : StateBox := GroundCertifiedNativeEntry.differenceBox currentBox previousBox
def εRat : ℚ := 3022314549036573/302231454903657293676544
'''
        bound=f'(difference.R {j}).lo' if p['sign']>0 else f'-(difference.R {j}).hi'
        s+=f'''
theorem gap_arithmetic : εRat < {bound} := by decide +kernel

theorem difference_enclosed : difference.Contains (unpack (orbit {i} 60-orbit {i} 59)) := by
  simpa only [← packCLE_symm_apply,map_sub] using
    GroundCertifiedNativeEntry.differenceBox_sound current_enclosed previous_enclosed

theorem last_update_fail : GroundOriginalResiduals.ε < lastUpdateResidual
    GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ)
      (1/2) (orbit {i} 59) := by
  have he : GroundOriginalResiduals.ε = (εRat : ℝ) := by norm_num [GroundOriginalResiduals.ε,εRat]
  have hc : GroundOriginalResiduals.ε < (({bound} : ℚ) : ℝ) := by
    rw [he];exact_mod_cast gap_arithmetic
  have hj : (difference.R {j}).Contains ((orbit {i} 60-orbit {i} 59) {j}).re := (difference_enclosed {j}).1
  have hb : (({bound} : ℚ) : ℝ) ≤ |((orbit {i} 60-orbit {i} 59) {j}).re| := by
'''
        if p['sign']>0:s+='    exact hj.1.trans (le_abs_self _)\n'
        else:s+='    simpa only [Rat.cast_neg] using (neg_le_neg hj.2).trans (neg_le_abs _)\n'
        s+=f'''  have hgap := hc.trans_le (hb.trans (real_component_le_l2 (orbit {i} 60-orbit {i} 59) {j}))
  have hstep : nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (1/2) (orbit {i} 59) = orbit {i} 60 :=
    (Function.iterate_succ_apply' (f {i}) 59 GroundOriginalSeed.initial).symm
  rw [lastUpdateResidual,hstep]
  exact hgap

theorem actual_four_source_tests_fail : ¬ MeetsConvergence GroundNativeControls.originalTolerance
    GroundOriginalResiduals.ε (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (1/2)
      (orbit {i} 59) (orbit {i} 60) := by
  intro h
  exact (not_lt_of_ge h.1) last_update_fail

end
end SbtCosmo.Derivation.{name}
'''
        out[sourcepath(name)]=s
    return out

def render_direct(w):
    out={}
    for p in w['direct_passes']:
        i=p['index'];name=f'GroundOffsetSixtyTests.Point{i:03d}';prefix=f'GroundOffsetSixtyPrefix.Point{i:03d}'
        s=f'import SbtCosmo.Derivation.{prefix}\n'
        s+='import SbtCosmo.Derivation.GroundComplexFiniteBudget\nimport SbtCosmo.Derivation.GroundOriginalOffsetSeed\nimport SbtCosmo.Derivation.GroundOriginalResiduals\n'
        s+='\n/-! Four source tests using the actual sourced candidate at the actual60th iterate. -/\nnamespace SbtCosmo.Derivation.'+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundOffsetSeedReturn GroundSourceDiagnostics GroundComplexEuclidean GroundComplexFiniteBudget
open GroundCertifiedNativeEntry

'''
        s+=f'def currentBox : StateBox := {prefix}.currentBox\ndef previousBox : StateBox := {prefix}.previousBox\n'
        s+=f'def z : Fin 9 → ℚ := {vec(p["linear_center"])}\n'
        for namekey,sourcekey in [('r','linear_radius'),('q','linear_rate'),('y','linear_residual'),('d','candidate_distance'),('update','update_distance')]:
            s+=f'def {namekey} : ℚ := {q(p[sourcekey])}\n'
        s+='def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vec(row) for row in p['linear_inverse'])+']\n'
        A=F(F(p['potential_lower']).__floor__());B=F(F(p['potential_upper']).__ceil__())
        s+=f'def A : ℚ := {q(A)}\ndef B : ℚ := {q(B)}\n'
        s+='def candidateBox : StateBox := negativeTargetBox z r\n'
        s+=f'''
theorem ground_arithmetic : GroundBackgroundKernel.Arithmetic
    (GroundUncertainNativeBox.sourceBox (β {i}) (κ {i}) currentBox) z r q y C := by
  constructor <;> decide +kernel

theorem distance_arithmetic :
    squaredBudget (differenceBox currentBox candidateBox) ≤ d^2 ∧
      squaredBudget (differenceBox currentBox previousBox) ≤ update^2 := by decide +kernel

theorem source_bounds_arithmetic : ∀ j : Fin 8,
    A ≤ (GroundUncertainNativeBox.sourceBox (β {i}) (κ {i}) currentBox j).lo ∧
      (GroundUncertainNativeBox.sourceBox (β {i}) (κ {i}) currentBox j).hi ≤ B := by decide +kernel

theorem actual_candidate_enclosed : candidateBox.Contains
    (unpack (-nativeCandidate (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (orbit {i} 60))) := by
  have hx := {prefix}.current_enclosed
  have hg := GroundBackgroundKernel.actual_selected_enclosed ground_arithmetic
    (GroundUncertainNativeBox.sourceBox_sound (β {i}) (κ {i}) (background_sound {i}) hx)
  have he := nativeCandidate_pack (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (unpack (orbit {i} 60))
  rw [show pack (unpack (orbit {i} 60)) = orbit {i} 60 from packCLE.apply_symm_apply _] at he
  rw [he, ← GroundNativeReflection.realEmbed_neg]
  exact negativeTargetBox_sound hg

theorem actual_candidate_distance :
    l2 (orbit {i} 60-(-nativeCandidate (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (orbit {i} 60))) ≤ (d : ℝ) := by
  have hx : (differenceBox currentBox candidateBox).Contains
      (unpack (orbit {i} 60-(-nativeCandidate (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (orbit {i} 60)))) := by
    simpa only [← packCLE_symm_apply,map_sub] using
      differenceBox_sound {prefix}.current_enclosed actual_candidate_enclosed
  exact box_l2_bound hx (by decide +kernel) distance_arithmetic.1

theorem actual_update_distance : l2 (orbit {i} 60-orbit {i} 59) ≤ (update : ℝ) := by
  have hx : (differenceBox currentBox previousBox).Contains (unpack (orbit {i} 60-orbit {i} 59)) := by
    simpa only [← packCLE_symm_apply,map_sub] using
      differenceBox_sound {prefix}.current_enclosed {prefix}.previous_enclosed
  exact box_l2_bound hx (by decide +kernel) distance_arithmetic.2

theorem actual_potential_bounds : ∀ j,
    (A : ℝ) ≤ complexSourcePotential (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (orbit {i} 60) j ∧
      complexSourcePotential (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (orbit {i} 60) j ≤ (B : ℝ) := by
  have hp := source_pack (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (unpack (orbit {i} 60))
  rw [show pack (unpack (orbit {i} 60)) = orbit {i} 60 from packCLE.apply_symm_apply _] at hp
  intro j
  have hs := GroundUncertainNativeBox.sourceBox_sound (β {i}) (κ {i}) (background_sound {i}) {prefix}.current_enclosed j
  rw [← hp] at hs
  exact ⟨(Rat.cast_le.mpr (source_bounds_arithmetic j).1).trans hs.1,
    hs.2.trans (Rat.cast_le.mpr (source_bounds_arithmetic j).2)⟩

theorem actual_four_source_tests : MeetsConvergence GroundNativeControls.originalTolerance
    GroundOriginalResiduals.ε (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (1/2)
      (orbit {i} 59) (orbit {i} 60) := by
  have hstep : nativeUpdate GroundNativeControls.originalTolerance
      (GroundOriginalOffsets.rounded_b {i}) (κ {i} : ℝ) (1/2) (orbit {i} 59) = orbit {i} 60 :=
    (Function.iterate_succ_apply' (f {i}) 59 GroundOriginalSeed.initial).symm
  apply tests_of_budgets GroundNativeControls.originalTolerance_guard.1
    (by norm_num [GroundOriginalResiduals.ε]) (by norm_num [d])
    ((GroundOriginalOffsetSeed.rounded_original_seed_return {i}).2 60).2.2
    actual_candidate_distance actual_update_distance hstep actual_potential_bounds
  · norm_num [d]
  · norm_num [d,GroundNativeControls.originalTolerance]
  · norm_num [d,update,A,B,GroundOriginalResiduals.ε]

end
end SbtCosmo.Derivation.{name}
'''
        out[sourcepath(name)]=s
    return out

# Verified populated prototype, instantiated by exact point/rational substitution.
FAST_TEMPLATE="import SbtCosmo.Derivation.GroundOffsetPrefix.Point004\nimport SbtCosmo.Derivation.GroundOffsetSelectorBudget\nimport SbtCosmo.Derivation.GroundComplexFiniteBudget\nimport SbtCosmo.Derivation.GroundOriginalOffsetSeed\nnamespace SbtCosmo.Derivation.OffsetSixtyFastPilot\nnoncomputable section\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\nset_option warningAsError true\nset_option maxHeartbeats 100000000\nset_option maxRecDepth 100000\nopen GroundState GroundNativePhase GroundOffsetSeedReturn GroundRationalInterval GroundNativeBox\nopen GroundOffsetSelectorBudget\nopen scoped BigOperators\ndef a : ℚ := (3637741/16777216)\ndef d : ℚ := 1/100000000000\ntheorem selector_rows : 0 ≤ a ∧ ∀ j : Fin 8, (∑ k : Fin 8,\n      (((GroundOriginalOffsetBasins.data 4).c.DG (k.castAdd 8) j).bound+\n       ((GroundOriginalOffsetBasins.data 4).c.DG (Fin.natAdd 8 k) j).bound)) ≤ a := by decide +kernel\n\ntheorem candidate_arithmetic :\n    (4*(GroundOriginalOffsetBasins.data 4).s+4*a)*\n      ((GroundOriginalOffsetBasins.data 4).c.rate^42*GroundOffsetPrefix.Point004.δ) ≤ d := by decide +kernel\n\ntheorem actual_candidate_distance :\n    GroundComplexEuclidean.l2 (orbit 4 60-(-GroundNativeIteration.nativeCandidate\n      (GroundOriginalOffsets.rounded_b 4) (κ 4 : ℝ) (orbit 4 60))) ≤ (d : ℝ) := by\n  have h := candidate_distance 4 GroundOffsetPrefix.Point004.entry GroundOffsetPrefix.Point004.distance\n    selector_rows.1 selector_rows.2 42\n  have hc : (4*((GroundOriginalOffsetBasins.data 4).s : ℝ)+4*(a : ℝ))*\n      ((GroundOriginalOffsetBasins.rate 4 : ℝ)^42*(GroundOffsetPrefix.Point004.δ : ℝ)) ≤ (d : ℝ) := by\n    change (4*((GroundOriginalOffsetBasins.data 4).s : ℝ)+4*(a : ℝ))*\n      (((GroundOriginalOffsetBasins.data 4).c.rate : ℝ)^42*(GroundOffsetPrefix.Point004.δ : ℝ)) ≤ (d : ℝ)\n    exact_mod_cast candidate_arithmetic\n  exact h.trans hc\n\ntheorem update_arithmetic :\n    4*(GroundOriginalOffsetBasins.data 4).s*\n      (((GroundOriginalOffsetBasins.data 4).c.rate^41+\n        (GroundOriginalOffsetBasins.data 4).c.rate^42)*GroundOffsetPrefix.Point004.δ) ≤ d := by decide +kernel\n\ntheorem source_bounds_arithmetic : ∀ j : Fin 8,\n    -1 ≤ (GroundUncertainNativeBox.sourceBox (GroundOriginalOffsetBasins.data 4).c.β\n      (GroundOriginalOffsetBasins.data 4).c.κ (GroundOriginalOffsetBasins.data 4).c.input j).lo ∧\n    (GroundUncertainNativeBox.sourceBox (GroundOriginalOffsetBasins.data 4).c.β\n      (GroundOriginalOffsetBasins.data 4).c.κ (GroundOriginalOffsetBasins.data 4).c.input j).hi ≤ 0 := by decide +kernel\n\ntheorem actual_update_distance : GroundComplexEuclidean.l2 (orbit 4 60-orbit 4 59) ≤ (d : ℝ) := by\n  have h59 := euclidean_tail_bound 4 GroundOffsetPrefix.Point004.entry GroundOffsetPrefix.Point004.distance 41\n  have h60 := euclidean_tail_bound 4 GroundOffsetPrefix.Point004.entry GroundOffsetPrefix.Point004.distance 42\n  have h := GroundComplexEuclidean.l2_sub_triangle (orbit 4 60)\n    (realEmbed (-(GroundOriginalOffsets.roundedRoot 4).1)) (orbit 4 59)\n  have hn : realEmbed (-(GroundOriginalOffsets.roundedRoot 4).1)-orbit 4 59 =\n      -(orbit 4 59-realEmbed (-(GroundOriginalOffsets.roundedRoot 4).1)) := by abel\n  rw [hn,GroundComplexEuclidean.l2_neg] at h\n  have hc : 4*((GroundOriginalOffsetBasins.data 4).s : ℝ)*\n      (((GroundOriginalOffsetBasins.rate 4 : ℝ)^41+\n        (GroundOriginalOffsetBasins.rate 4 : ℝ)^42)*(GroundOffsetPrefix.Point004.δ : ℝ)) ≤ (d : ℝ) := by\n    change 4*((GroundOriginalOffsetBasins.data 4).s : ℝ)*\n      ((((GroundOriginalOffsetBasins.data 4).c.rate : ℝ)^41+\n        ((GroundOriginalOffsetBasins.data 4).c.rate : ℝ)^42)*(GroundOffsetPrefix.Point004.δ : ℝ)) ≤ (d : ℝ)\n    exact_mod_cast update_arithmetic\n  simp only [GroundOffsetPrefix.Point004.N,Nat.reduceAdd] at h59 h60\n  nlinarith\n\ndef ε : ℝ := 3022314549036573/302231454903657293676544\n\ntheorem actual_four_source_tests : GroundSourceDiagnostics.MeetsConvergence\n    GroundNativeControls.originalTolerance ε (GroundOriginalOffsets.rounded_b 4) (κ 4 : ℝ)\n      (1/2) (orbit 4 59) (orbit 4 60) := by\n  have hstep : GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance\n    (GroundOriginalOffsets.rounded_b 4) (κ 4 : ℝ) (1/2) (orbit 4 59) = orbit 4 60 := by\n    exact (Function.iterate_succ_apply' (f 4) 59 GroundOriginalSeed.initial).symm\n  have hpot := sourced_potential_bounds 4 GroundOffsetPrefix.Point004.entry source_bounds_arithmetic 42\n  apply GroundComplexFiniteBudget.tests_of_budgets\n    GroundNativeControls.originalTolerance_guard.1 (by norm_num [ε]) (by norm_num [d])\n    ((GroundOriginalOffsetSeed.rounded_original_seed_return 4).2 60).2.2\n    actual_candidate_distance actual_update_distance hstep (by simpa only [Rat.cast_neg,Rat.cast_one,Rat.cast_zero] using hpot)\n  · norm_num [d]\n  · norm_num [d,GroundNativeControls.originalTolerance]\n  · norm_num [d,ε]\nend\nend SbtCosmo.Derivation.OffsetSixtyFastPilot\n"

def render_fast(w):
    old=json.loads((ROOT/OLD).read_text())['points'];out={}
    for p in w['fast_passes']:
        i=p['index'];n59=59-len(old[i]['steps']);n60=60-len(old[i]['steps'])
        s=FAST_TEMPLATE.replace('OffsetSixtyFastPilot',f'GroundOffsetSixtyTests.Point{i:03d}')
        s=s.replace('GroundOffsetPrefix.Point004',f'GroundOffsetPrefix.Point{i:03d}')
        for token in ['data','rate','orbit','rounded_b','roundedRoot','κ','f','candidate_distance','euclidean_tail_bound','sourced_potential_bounds','rounded_original_seed_return']:
            s=s.replace(token+' 4',token+' '+str(i))
        s=s.replace('^41','^__N59__').replace('^42','^__N60__').replace('__N59__',str(n59)).replace('__N60__',str(n60))
        s=s.replace('distance 41','distance __N59__').replace('distance 42','distance __N60__').replace('__N59__',str(n59)).replace('__N60__',str(n60))
        s=s.replace('source_bounds_arithmetic 42','source_bounds_arithmetic '+str(n60))
        s=s.replace('selector_rows.2 42','selector_rows.2 '+str(n60))
        begin=s.index('def a : ℚ := ');end=s.index('\n',begin)
        s=s[:begin]+'def a : ℚ := '+q(p['selector_budget'])+s[end:]
        s=s.replace('-1 ≤ (GroundUncertainNativeBox.sourceBox',q(p['potential_lower'])+' ≤ (GroundUncertainNativeBox.sourceBox')
        s=s.replace('.c.input j).hi ≤ 0 := by decide +kernel','.c.input j).hi ≤ '+q(p['potential_upper'])+' := by decide +kernel')
        s=s.replace('simpa only [Rat.cast_neg,Rat.cast_one,Rat.cast_zero] using hpot','norm_num at hpot; exact hpot')
        out[sourcepath(f'GroundOffsetSixtyTests.Point{i:03d}')]=s
    return out


def generated_sources(w):
    return render_extensions(w)|render_prefixes(w)|render_fast(w)|render_direct(w)|render_failures(w)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument('--check',action='store_true',help='Read-only replay and populated source comparison')
    p.add_argument('--proposal-dir',type=Path)
    p.add_argument('--sixty',type=Path);p.add_argument('--fast',type=Path)
    a=p.parse_args()
    if a.check:
        if any(x is not None for x in [a.proposal_dir,a.sixty,a.fast]):
            p.error('--check uses the saved witness packet and accepts no proposal inputs')
        w=json.loads((PACKET/'witnesses.json').read_text());assert replay(w)
        generated=generated_sources(w);assert len(generated)==155
        for path,text in generated.items():assert (ROOT/path).read_text()==text,path
        print('Exact replay and read-only comparison of155 populated sources passed')
    else:
        if any(x is None for x in [a.proposal_dir,a.sixty,a.fast]):
            p.error('--proposal-dir, --sixty and --fast are required when generating')
        w=proposal_packet(a.proposal_dir,a.sixty,a.fast);assert replay(w)
        generated=generated_sources(w);assert len(generated)==155
        assert not (PACKET/'witnesses.json').exists(),'Refusing to overwrite witness packet'
        assert all(not (ROOT/path).exists() for path in generated),'Refusing to overwrite existing source'
        PACKET.mkdir(exist_ok=True)
        (PACKET/'witnesses.json').write_text(json.dumps(w,indent=2)+'\n')
        write_sources(generated)
        print('Rendered155 populated extension/prefix/verdict modules; closed Lean verification required')
