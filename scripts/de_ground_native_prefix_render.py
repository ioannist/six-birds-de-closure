"""Render rational native-prefix witnesses as Lean declarations and kernel proofs."""
from pathlib import Path
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'results/ground_native_prefix_2026-10-04'
def q(x):
    t=F(x);return str(t.numerator) if t.denominator==1 else '('+str(t.numerator)+'/'+str(t.denominator)+')'
def vec(xs):return '!['+', '.join(map(q,xs))+']'
def iv(p):return '⟨'+q(p[0])+', '+q(p[1])+'⟩'
def box(R,I):return '⟨!['+', '.join(map(iv,R))+'], !['+', '.join(map(iv,I))+']⟩'
def render(w):
    assert len(w['steps'])==16
    initial='''import SbtCosmo.Derivation.GroundNativeBox
import SbtCosmo.Derivation.GroundOriginalSeed
import SbtCosmo.Derivation.GroundSamples.Point002

/-! Tight initial box for the original seed, preserving both exact mathematical
normalizations. Coupling and threshold are the actual original IEEE rationals. -/
namespace SbtCosmo.Derivation.GroundNativePrefixInitial
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval
open GroundNativeBox GroundOriginalSeed

def κ : ℚ := GroundSamples.Point002.a
'''+f'def τ : ℚ := {q(w["tolerance"])}\ndef K : Interval := {iv(w["initial_inverse"])}\ndef initialBox : StateBox := {box(w["initial_re"],w["initial_im"])}\n'+'''
def rawBox : StateBox := ⟨fun i => Interval.point (R i), fun i => Interval.point (I i)⟩

theorem inverse_arithmetic : GroundIntervalReciprocal.Arithmetic (Interval.point rawNorm) K := by
  constructor <;> decide +kernel

theorem initial_inclusion : (normalizedBox rawBox K).Included initialBox := by
  unfold StateBox.Included included
  decide +kernel

theorem raw_box_sound : rawBox.Contains rawState := fun i => ⟨Interval.point_sound (R i), Interval.point_sound (I i)⟩

theorem original_seed_enclosed : initialBox.Contains (unpack initial) := by
  have hn : (Interval.point rawNorm).Contains (stateNormSq rawState) := by
    rw [raw_norm_return]; exact Interval.point_sound rawNorm
  have hk := (GroundIntervalReciprocal.inverse_sqrt_sound inverse_arithmetic hn).2
  have hx := StateBox.included_sound initial_inclusion (normalizedBox_sound raw_box_sound hk)
  rw [double_normalization]
  exact hx

theorem tolerance_return : (τ : ℝ) = GroundNativeControls.originalTolerance := by
  norm_num [τ, GroundNativeControls.originalTolerance]

theorem coupling_return : κ = GroundOriginalSamples.couplings 2 := by
  decide +kernel

theorem zero_inverse_rejected : ¬ GroundIntervalReciprocal.Arithmetic (Interval.point rawNorm) (Interval.point 0) := by
  intro h
  have hp := h.lower_pos
  norm_num [Interval.point] at hp

end
end SbtCosmo.Derivation.GroundNativePrefixInitial
'''
    files={'lean/SbtCosmo/Derivation/GroundNativePrefixInitial.lean':initial}
    for n,p in enumerate(w['steps']):
        name=f'GroundNativePrefix.Step{n:03d}'
        s='''import SbtCosmo.Derivation.GroundNativePrefixInitial

/-! Exact rational native orbit step at original coupling.3. NumPy proposals
supply data only; whole-box selector and reciprocal budgets are kernel proofs. -/
namespace SbtCosmo.Derivation.'''+name+'''
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundNativeBox GroundRationalInterval GroundNativePrefixInitial GroundOriginalFirstTube

'''
        s+=f'def input : StateBox := {box(p["input_re"],p["input_im"])}\ndef output : StateBox := {box(p["output_re"],p["output_im"])}\n'
        s+=f'def z : Fin 9 → ℚ := {vec(p["center"])}\ndef r : ℚ := {q(p["radius"])}\ndef q : ℚ := {q(p["rate"])}\ndef y : ℚ := {q(p["residual_budget"])}\n'
        s+='def C : Matrix (Fin 9) (Fin 9) ℚ := ![\n  '+',\n  '.join(vec(row) for row in p['inverse'])+']\n'
        s+=f'def K : Interval := {iv(p["overlap_inverse"])}\ndef L : Interval := {iv(p["mixed_inverse"])}\n\n'
        s+='''theorem ground_arithmetic : GroundBackgroundKernel.Arithmetic
    (sourceBox originalBackground κ input) z r q y C := by
  constructor <;> decide +kernel

theorem arithmetic : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q y C K L := by
  constructor
  · exact ground_arithmetic
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold StateBox.Included included
    decide +kernel

end
end SbtCosmo.Derivation.'''+name+'\n'
        files['lean/SbtCosmo/Derivation/'+name.replace('.','/')+'.lean']=s
    imports=''.join('import SbtCosmo.Derivation.GroundNativePrefix.Step'+f'{n:03d}'+'\n' for n in range(16))
    family=imports+'''import SbtCosmo.Derivation.GroundOriginalSamples

/-! The fully populated16-step original-seed native prefix at original coupling.3.
It earns finite legality and nearness to the actual branch root; no unknown
attracting radius or basin entry is inferred from nearness alone. -/
namespace SbtCosmo.Derivation.GroundOriginalNativePrefix
noncomputable section
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundNativePrefixInitial GroundOriginalFirstTube GroundKernelTube GroundOriginalSeed GroundOriginalSamples
open scoped BigOperators

'''
    family_body="structure Certificate where\n  input : StateBox\n  output : StateBox\n  z : Fin 9 → ℚ\n  r : ℚ\n  q : ℚ\n  y : ℚ\n  C : Matrix (Fin 9) (Fin 9) ℚ\n  K : Interval\n  L : Interval\n  proof : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q y C K L\n\n__CERTIFICATES__\n\ndef boxes : Fin 17 → StateBox := Fin.cases initialBox (fun i => (certificates i).output)\n\ntheorem seams : ∀ i : Fin 16, boxes i.castSucc = (certificates i).input ∧ boxes i.succ = (certificates i).output := by\n  decide +kernel\n\ndef f : ComplexField → ComplexField := nativeUpdate GroundNativeControls.originalTolerance\n  (background originalBackground) (κ : ℝ) (1/2)\ndef orbit (n : ℕ) : ComplexField := f^[n] initial\n\ntheorem certificate_step (i : Fin 16) {x : State} (hx : (certificates i).input.Contains x) :\n    ActivePhase GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (pack x) ∧\n    NativeLegal GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (1/2) (pack x) ∧\n    (certificates i).output.Contains (unpack (f (pack x))) := by\n  simpa only [tolerance_return] using arithmetic_native_step (certificates i).proof hx\n\ntheorem native_prefix_enclosed (i : Fin 17) : (boxes i).Contains (unpack (orbit i.val)) := by\n  refine Fin.induction ?_ (fun j ih => ?_) i\n  · exact original_seed_enclosed\n  · have hx : (certificates j).input.Contains (unpack (orbit j.val)) := by\n      rw [← (seams j).1]; exact ih\n    have h := (certificate_step j hx).2.2\n    have he : pack (unpack (orbit j.val)) = orbit j.val := packCLE.apply_symm_apply _\n    rw [he] at h\n    rw [(seams j).2]\n    change (certificates j).output.Contains (unpack (orbit (j.val+1)))\n    rw [orbit, Function.iterate_succ_apply']\n    exact h\n\ntheorem native_prefix_guards (i : Fin 16) :\n    ActivePhase GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (orbit i.val) ∧\n    NativeLegal GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (1/2) (orbit i.val) := by\n  have hx : (certificates i).input.Contains (unpack (orbit i.val)) := by\n    rw [← (seams i).1]; exact native_prefix_enclosed i.castSucc\n  have h := certificate_step i hx\n  have he : pack (unpack (orbit i.val)) = orbit i.val := packCLE.apply_symm_apply _\n  rw [he] at h\n  exact ⟨h.1, h.2.1⟩\n\ntheorem native_prefix_unit (i : Fin 17) : complexNormSq (orbit i.val) = 1 := by\n  refine Fin.induction ?_ (fun j _ => ?_) i\n  · exact initial_unit\n  · change complexNormSq (orbit (j.val+1)) = 1\n    rw [orbit, Function.iterate_succ_apply']\n    exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 (native_prefix_guards j).2\n\ndef targetBox : StateBox := ⟨fun i => (GroundBackgroundKernel.fieldBox GroundSamples.Point002.z GroundSamples.Point002.r i).neg,\n  fun _ => Interval.point 0⟩\n\ntheorem target_box_sound : targetBox.Contains (-(GroundOriginalContinuation.branch (κ : ℝ)).1, 0) := by\n  have hx := branch_in_sample_ball 2\n  rw [← coupling_return] at hx\n  change GroundOriginalContinuation.branch (κ : ℝ) ∈ Metric.closedBall (center GroundSamples.Point002.z) (GroundSamples.Point002.r : ℝ) at hx\n  have hb := GroundKernelTube.box_sound originalBackground GroundSamples.Point002.a GroundSamples.Point002.c\n    GroundSamples.Point002.z GroundSamples.Point002.r (κ := (κ : ℝ)) (by simp [κ, GroundSamples.Point002.a, GroundSamples.Point002.c]) hx\n  intro i\n  have h := hb (.state i.castSucc)\n  have hh : (GroundBackgroundKernel.fieldBox GroundSamples.Point002.z GroundSamples.Point002.r i).Contains\n      ((GroundOriginalContinuation.branch (κ : ℝ)).1 i) := by\n    simpa only [GroundBackgroundKernel.fieldBox, GroundKernelTube.box, GroundResidualEnclosure.valuation,\n      GroundPointCoordinates.coord, Fin.lastCases_castSucc] using h\n  refine ⟨Interval.neg_sound hh, ?_⟩\n  change (Interval.point 0).Contains (0 : ℝ)\n  simpa only [Rat.cast_zero] using Interval.point_sound 0\n\ndef differenceBox (B A : StateBox) : StateBox := ⟨fun i => (B.R i).add (A.R i).neg, fun i => (B.I i).add (A.I i).neg⟩\n\ntheorem distance_arithmetic : ∀ i : Fin 8,\n    ((differenceBox (boxes 16) targetBox).R i).bound ≤ 1/125000 ∧\n    ((differenceBox (boxes 16) targetBox).I i).bound ≤ 1/125000 := by decide +kernel\n\ntheorem actual_seed_sixteen_near_negative_ground :\n    complexNormSq (orbit 16) = 1 ∧\n    ‖unpack (orbit 16)-(-(GroundOriginalContinuation.branch (κ : ℝ)).1, 0)‖ < 1/100000 := by\n  refine ⟨native_prefix_unit 16, ?_⟩\n  have hx := native_prefix_enclosed (16 : Fin 17)\n  have ht := target_box_sound\n  have hδ : ‖unpack (orbit 16)-(-(GroundOriginalContinuation.branch (κ : ℝ)).1, 0)‖ ≤ (1/125000 : ℝ) := by\n    rw [Prod.norm_def]\n    apply max_le\n    all_goals apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/125000)).mpr\n    all_goals intro i\n    · have h := Interval.add_sound (hx i).1 (Interval.neg_sound (ht i).1)\n      have hd := (distance_arithmetic i).1\n      have hd' : (((differenceBox (boxes 16) targetBox).R i).bound : ℝ) ≤ ((1/125000 : ℚ) : ℝ) := Rat.cast_le.mpr hd\n      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hd'\n      simpa only [Real.norm_eq_abs, Prod.fst_sub, Pi.sub_apply, sub_eq_add_neg] using (Interval.abs_le_bound h).trans hd'\n    · have h := Interval.add_sound (hx i).2 (Interval.neg_sound (ht i).2)\n      have hd := (distance_arithmetic i).2\n      have hd' : (((differenceBox (boxes 16) targetBox).I i).bound : ℝ) ≤ ((1/125000 : ℚ) : ℝ) := Rat.cast_le.mpr hd\n      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hd'\n      simpa only [Real.norm_eq_abs, Prod.snd_sub, Pi.sub_apply, sub_eq_add_neg] using (Interval.abs_le_bound h).trans hd'\n  exact hδ.trans_lt (by norm_num)\n\ntheorem zero_selector_preconditioner_rejected : ¬ GroundBackgroundKernel.Arithmetic\n    (sourceBox originalBackground κ GroundNativePrefix.Step000.input) GroundNativePrefix.Step000.z GroundNativePrefix.Step000.r\n    GroundNativePrefix.Step000.q GroundNativePrefix.Step000.y (fun _ _ => 0) := by\n  intro h\n  have hn : ¬ (∑ j : Fin 9, ((GroundResidualEnclosure.defectExpr (fun _ _ => 0) 0 j).enclose\n    (GroundBackgroundKernel.box (sourceBox originalBackground κ GroundNativePrefix.Step000.input) GroundNativePrefix.Step000.z GroundNativePrefix.Step000.r)).bound) ≤\n      GroundNativePrefix.Step000.q := by decide +kernel\n  exact hn (h.defect_rows 0)\n"
    records=[]
    for n in range(16):
        m='GroundNativePrefix.Step'+f'{n:03d}'
        records.append('⟨'+', '.join(m+'.'+k for k in ['input','output','z','r','q','y','C','K','L','arithmetic'])+'⟩')
    certificates='def certificates : Fin 16 → Certificate :=\n  '+''.join('Fin.cases '+t+' (\n  ' for t in records[:-1])+'fun _ => '+records[-1]+')'*15+'\n'
    family+=family_body.replace('__CERTIFICATES__',certificates)+'\nend\nend SbtCosmo.Derivation.GroundOriginalNativePrefix\n'
    files['lean/SbtCosmo/Derivation/GroundOriginalNativePrefix.lean']=family
    return files

if __name__=='__main__':
    w=json.loads((PACKET/'witnesses.json').read_text())
    for p,s in render(w).items():
        t=ROOT/p;t.parent.mkdir(parents=True,exist_ok=True);t.write_text(s)
