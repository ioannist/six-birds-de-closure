import SbtCosmo.Derivation.GroundNativePrefix.Step000
import SbtCosmo.Derivation.GroundNativePrefix.Step001
import SbtCosmo.Derivation.GroundNativePrefix.Step002
import SbtCosmo.Derivation.GroundNativePrefix.Step003
import SbtCosmo.Derivation.GroundNativePrefix.Step004
import SbtCosmo.Derivation.GroundNativePrefix.Step005
import SbtCosmo.Derivation.GroundNativePrefix.Step006
import SbtCosmo.Derivation.GroundNativePrefix.Step007
import SbtCosmo.Derivation.GroundNativePrefix.Step008
import SbtCosmo.Derivation.GroundNativePrefix.Step009
import SbtCosmo.Derivation.GroundNativePrefix.Step010
import SbtCosmo.Derivation.GroundNativePrefix.Step011
import SbtCosmo.Derivation.GroundNativePrefix.Step012
import SbtCosmo.Derivation.GroundNativePrefix.Step013
import SbtCosmo.Derivation.GroundNativePrefix.Step014
import SbtCosmo.Derivation.GroundNativePrefix.Step015
import SbtCosmo.Derivation.GroundOriginalSamples

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

structure Certificate where
  input : StateBox
  output : StateBox
  z : Fin 9 → ℚ
  r : ℚ
  q : ℚ
  y : ℚ
  C : Matrix (Fin 9) (Fin 9) ℚ
  K : Interval
  L : Interval
  proof : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q y C K L

def certificates : Fin 16 → Certificate :=
  Fin.cases ⟨GroundNativePrefix.Step000.input, GroundNativePrefix.Step000.output, GroundNativePrefix.Step000.z, GroundNativePrefix.Step000.r, GroundNativePrefix.Step000.q, GroundNativePrefix.Step000.y, GroundNativePrefix.Step000.C, GroundNativePrefix.Step000.K, GroundNativePrefix.Step000.L, GroundNativePrefix.Step000.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step001.input, GroundNativePrefix.Step001.output, GroundNativePrefix.Step001.z, GroundNativePrefix.Step001.r, GroundNativePrefix.Step001.q, GroundNativePrefix.Step001.y, GroundNativePrefix.Step001.C, GroundNativePrefix.Step001.K, GroundNativePrefix.Step001.L, GroundNativePrefix.Step001.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step002.input, GroundNativePrefix.Step002.output, GroundNativePrefix.Step002.z, GroundNativePrefix.Step002.r, GroundNativePrefix.Step002.q, GroundNativePrefix.Step002.y, GroundNativePrefix.Step002.C, GroundNativePrefix.Step002.K, GroundNativePrefix.Step002.L, GroundNativePrefix.Step002.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step003.input, GroundNativePrefix.Step003.output, GroundNativePrefix.Step003.z, GroundNativePrefix.Step003.r, GroundNativePrefix.Step003.q, GroundNativePrefix.Step003.y, GroundNativePrefix.Step003.C, GroundNativePrefix.Step003.K, GroundNativePrefix.Step003.L, GroundNativePrefix.Step003.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step004.input, GroundNativePrefix.Step004.output, GroundNativePrefix.Step004.z, GroundNativePrefix.Step004.r, GroundNativePrefix.Step004.q, GroundNativePrefix.Step004.y, GroundNativePrefix.Step004.C, GroundNativePrefix.Step004.K, GroundNativePrefix.Step004.L, GroundNativePrefix.Step004.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step005.input, GroundNativePrefix.Step005.output, GroundNativePrefix.Step005.z, GroundNativePrefix.Step005.r, GroundNativePrefix.Step005.q, GroundNativePrefix.Step005.y, GroundNativePrefix.Step005.C, GroundNativePrefix.Step005.K, GroundNativePrefix.Step005.L, GroundNativePrefix.Step005.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step006.input, GroundNativePrefix.Step006.output, GroundNativePrefix.Step006.z, GroundNativePrefix.Step006.r, GroundNativePrefix.Step006.q, GroundNativePrefix.Step006.y, GroundNativePrefix.Step006.C, GroundNativePrefix.Step006.K, GroundNativePrefix.Step006.L, GroundNativePrefix.Step006.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step007.input, GroundNativePrefix.Step007.output, GroundNativePrefix.Step007.z, GroundNativePrefix.Step007.r, GroundNativePrefix.Step007.q, GroundNativePrefix.Step007.y, GroundNativePrefix.Step007.C, GroundNativePrefix.Step007.K, GroundNativePrefix.Step007.L, GroundNativePrefix.Step007.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step008.input, GroundNativePrefix.Step008.output, GroundNativePrefix.Step008.z, GroundNativePrefix.Step008.r, GroundNativePrefix.Step008.q, GroundNativePrefix.Step008.y, GroundNativePrefix.Step008.C, GroundNativePrefix.Step008.K, GroundNativePrefix.Step008.L, GroundNativePrefix.Step008.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step009.input, GroundNativePrefix.Step009.output, GroundNativePrefix.Step009.z, GroundNativePrefix.Step009.r, GroundNativePrefix.Step009.q, GroundNativePrefix.Step009.y, GroundNativePrefix.Step009.C, GroundNativePrefix.Step009.K, GroundNativePrefix.Step009.L, GroundNativePrefix.Step009.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step010.input, GroundNativePrefix.Step010.output, GroundNativePrefix.Step010.z, GroundNativePrefix.Step010.r, GroundNativePrefix.Step010.q, GroundNativePrefix.Step010.y, GroundNativePrefix.Step010.C, GroundNativePrefix.Step010.K, GroundNativePrefix.Step010.L, GroundNativePrefix.Step010.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step011.input, GroundNativePrefix.Step011.output, GroundNativePrefix.Step011.z, GroundNativePrefix.Step011.r, GroundNativePrefix.Step011.q, GroundNativePrefix.Step011.y, GroundNativePrefix.Step011.C, GroundNativePrefix.Step011.K, GroundNativePrefix.Step011.L, GroundNativePrefix.Step011.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step012.input, GroundNativePrefix.Step012.output, GroundNativePrefix.Step012.z, GroundNativePrefix.Step012.r, GroundNativePrefix.Step012.q, GroundNativePrefix.Step012.y, GroundNativePrefix.Step012.C, GroundNativePrefix.Step012.K, GroundNativePrefix.Step012.L, GroundNativePrefix.Step012.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step013.input, GroundNativePrefix.Step013.output, GroundNativePrefix.Step013.z, GroundNativePrefix.Step013.r, GroundNativePrefix.Step013.q, GroundNativePrefix.Step013.y, GroundNativePrefix.Step013.C, GroundNativePrefix.Step013.K, GroundNativePrefix.Step013.L, GroundNativePrefix.Step013.arithmetic⟩ (
  Fin.cases ⟨GroundNativePrefix.Step014.input, GroundNativePrefix.Step014.output, GroundNativePrefix.Step014.z, GroundNativePrefix.Step014.r, GroundNativePrefix.Step014.q, GroundNativePrefix.Step014.y, GroundNativePrefix.Step014.C, GroundNativePrefix.Step014.K, GroundNativePrefix.Step014.L, GroundNativePrefix.Step014.arithmetic⟩ (
  fun _ => ⟨GroundNativePrefix.Step015.input, GroundNativePrefix.Step015.output, GroundNativePrefix.Step015.z, GroundNativePrefix.Step015.r, GroundNativePrefix.Step015.q, GroundNativePrefix.Step015.y, GroundNativePrefix.Step015.C, GroundNativePrefix.Step015.K, GroundNativePrefix.Step015.L, GroundNativePrefix.Step015.arithmetic⟩)))))))))))))))


def boxes : Fin 17 → StateBox := Fin.cases initialBox (fun i => (certificates i).output)

theorem seams : ∀ i : Fin 16, boxes i.castSucc = (certificates i).input ∧ boxes i.succ = (certificates i).output := by
  decide +kernel

def f : ComplexField → ComplexField := nativeUpdate GroundNativeControls.originalTolerance
  (background originalBackground) (κ : ℝ) (1/2)
def orbit (n : ℕ) : ComplexField := f^[n] initial

theorem certificate_step (i : Fin 16) {x : State} (hx : (certificates i).input.Contains x) :
    ActivePhase GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (pack x) ∧
    NativeLegal GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (1/2) (pack x) ∧
    (certificates i).output.Contains (unpack (f (pack x))) := by
  simpa only [tolerance_return] using arithmetic_native_step (certificates i).proof hx

theorem native_prefix_enclosed (i : Fin 17) : (boxes i).Contains (unpack (orbit i.val)) := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · exact original_seed_enclosed
  · have hx : (certificates j).input.Contains (unpack (orbit j.val)) := by
      rw [← (seams j).1]; exact ih
    have h := (certificate_step j hx).2.2
    have he : pack (unpack (orbit j.val)) = orbit j.val := packCLE.apply_symm_apply _
    rw [he] at h
    rw [(seams j).2]
    change (certificates j).output.Contains (unpack (orbit (j.val+1)))
    rw [orbit, Function.iterate_succ_apply']
    exact h

theorem native_prefix_guards (i : Fin 16) :
    ActivePhase GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (orbit i.val) ∧
    NativeLegal GroundNativeControls.originalTolerance (background originalBackground) (κ : ℝ) (1/2) (orbit i.val) := by
  have hx : (certificates i).input.Contains (unpack (orbit i.val)) := by
    rw [← (seams i).1]; exact native_prefix_enclosed i.castSucc
  have h := certificate_step i hx
  have he : pack (unpack (orbit i.val)) = orbit i.val := packCLE.apply_symm_apply _
  rw [he] at h
  exact ⟨h.1, h.2.1⟩

theorem native_prefix_unit (i : Fin 17) : complexNormSq (orbit i.val) = 1 := by
  refine Fin.induction ?_ (fun j _ => ?_) i
  · exact initial_unit
  · change complexNormSq (orbit (j.val+1)) = 1
    rw [orbit, Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 (native_prefix_guards j).2

def targetBox : StateBox := ⟨fun i => (GroundBackgroundKernel.fieldBox GroundSamples.Point002.z GroundSamples.Point002.r i).neg,
  fun _ => Interval.point 0⟩

theorem target_box_sound : targetBox.Contains (-(GroundOriginalContinuation.branch (κ : ℝ)).1, 0) := by
  have hx := branch_in_sample_ball 2
  rw [← coupling_return] at hx
  change GroundOriginalContinuation.branch (κ : ℝ) ∈ Metric.closedBall (center GroundSamples.Point002.z) (GroundSamples.Point002.r : ℝ) at hx
  have hb := GroundKernelTube.box_sound originalBackground GroundSamples.Point002.a GroundSamples.Point002.c
    GroundSamples.Point002.z GroundSamples.Point002.r (κ := (κ : ℝ)) (by simp [κ, GroundSamples.Point002.a, GroundSamples.Point002.c]) hx
  intro i
  have h := hb (.state i.castSucc)
  have hh : (GroundBackgroundKernel.fieldBox GroundSamples.Point002.z GroundSamples.Point002.r i).Contains
      ((GroundOriginalContinuation.branch (κ : ℝ)).1 i) := by
    simpa only [GroundBackgroundKernel.fieldBox, GroundKernelTube.box, GroundResidualEnclosure.valuation,
      GroundPointCoordinates.coord, Fin.lastCases_castSucc] using h
  refine ⟨Interval.neg_sound hh, ?_⟩
  change (Interval.point 0).Contains (0 : ℝ)
  simpa only [Rat.cast_zero] using Interval.point_sound 0

def differenceBox (B A : StateBox) : StateBox := ⟨fun i => (B.R i).add (A.R i).neg, fun i => (B.I i).add (A.I i).neg⟩

theorem distance_arithmetic : ∀ i : Fin 8,
    ((differenceBox (boxes 16) targetBox).R i).bound ≤ 1/125000 ∧
    ((differenceBox (boxes 16) targetBox).I i).bound ≤ 1/125000 := by decide +kernel

theorem actual_seed_sixteen_near_negative_ground :
    complexNormSq (orbit 16) = 1 ∧
    ‖unpack (orbit 16)-(-(GroundOriginalContinuation.branch (κ : ℝ)).1, 0)‖ < 1/100000 := by
  refine ⟨native_prefix_unit 16, ?_⟩
  have hx := native_prefix_enclosed (16 : Fin 17)
  have ht := target_box_sound
  have hδ : ‖unpack (orbit 16)-(-(GroundOriginalContinuation.branch (κ : ℝ)).1, 0)‖ ≤ (1/125000 : ℝ) := by
    rw [Prod.norm_def]
    apply max_le
    all_goals apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/125000)).mpr
    all_goals intro i
    · have h := Interval.add_sound (hx i).1 (Interval.neg_sound (ht i).1)
      have hd := (distance_arithmetic i).1
      have hd' : (((differenceBox (boxes 16) targetBox).R i).bound : ℝ) ≤ ((1/125000 : ℚ) : ℝ) := Rat.cast_le.mpr hd
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hd'
      simpa only [Real.norm_eq_abs, Prod.fst_sub, Pi.sub_apply, sub_eq_add_neg] using (Interval.abs_le_bound h).trans hd'
    · have h := Interval.add_sound (hx i).2 (Interval.neg_sound (ht i).2)
      have hd := (distance_arithmetic i).2
      have hd' : (((differenceBox (boxes 16) targetBox).I i).bound : ℝ) ≤ ((1/125000 : ℚ) : ℝ) := Rat.cast_le.mpr hd
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hd'
      simpa only [Real.norm_eq_abs, Prod.snd_sub, Pi.sub_apply, sub_eq_add_neg] using (Interval.abs_le_bound h).trans hd'
  exact hδ.trans_lt (by norm_num)

theorem zero_selector_preconditioner_rejected : ¬ GroundBackgroundKernel.Arithmetic
    (sourceBox originalBackground κ GroundNativePrefix.Step000.input) GroundNativePrefix.Step000.z GroundNativePrefix.Step000.r
    GroundNativePrefix.Step000.q GroundNativePrefix.Step000.y (fun _ _ => 0) := by
  intro h
  have hn : ¬ (∑ j : Fin 9, ((GroundResidualEnclosure.defectExpr (fun _ _ => 0) 0 j).enclose
    (GroundBackgroundKernel.box (sourceBox originalBackground κ GroundNativePrefix.Step000.input) GroundNativePrefix.Step000.z GroundNativePrefix.Step000.r)).bound) ≤
      GroundNativePrefix.Step000.q := by decide +kernel
  exact hn (h.defect_rows 0)

end
end SbtCosmo.Derivation.GroundOriginalNativePrefix
