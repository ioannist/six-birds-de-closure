import SbtCosmo.Derivation.GroundBasin.Point002Data
import SbtCosmo.Derivation.GroundNativeQuantitativeBall
import SbtCosmo.Derivation.GroundStateRows
import SbtCosmo.Derivation.GroundNativeReflection

/-! Semantic bridges for the explicit .3 native basin. Uniform numerical
premises remain explicit here and are discharged in GroundOriginalBasin. -/
namespace SbtCosmo.Derivation.GroundOriginalBasin
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open Filter Metric NNReal GroundState GroundBorder GroundSourceJacobian GroundNativePhase
open GroundNativeIteration GroundNativeDerivative GroundNativeBox GroundNativeDerivativeBox GroundRationalInterval
open GroundBasin.Point002Data GroundOriginalFirstTube
open GroundNativePrefixInitial (κ τ coupling_return tolerance_return)
open scoped BigOperators Topology

def b : Field := GroundKernelTube.background originalBackground
def u : Field := (GroundOriginalContinuation.branch (κ : ℝ)).1
def realBasis : Field ≃L[ℝ] Field := GroundMatrixCoordinates.basis GroundCoordinates.Point002.real_inverse
def imagBasis : Field ≃L[ℝ] Field := GroundMatrixCoordinates.basis GroundCoordinates.Point002.imag_inverse
def T : State ≃L[ℝ] State := realBasis.prodCongr imagBasis

theorem ground_data : normSq u = 1 ∧ groundMap b (κ : ℝ) u = u := by
  have hk := GroundOriginalSamples.coupling_range 2
  rw [← coupling_return] at hk
  have h := GroundOriginalContinuation.whole_ground (κ : ℝ) hk
  exact ⟨h.2.2.1, h.2.2.2.2⟩

theorem old_positive_sound : oldPositive.Contains (u, 0) := by
  intro i
  constructor
  · have h := Interval.neg_sound (GroundOriginalNativePrefix.target_box_sound i).1
    simpa only [oldPositive, GroundOriginalNativePrefix.targetBox, Interval.neg, Pi.neg_apply, u, neg_neg] using h
  · change (Interval.point 0).Contains (0 : ℝ)
    simpa only [Rat.cast_zero] using Interval.point_sound 0

theorem coordinateBox_sound {B : StateBox} {x : State} (hx : B.Contains x) :
    (coordinateBox B).Contains (T.symm x) := by
  intro i
  constructor
  · change (sumBox (fun j => (Interval.point (GroundCoordinates.Point002.P i j)).mul (B.R j))).Contains
      ((GroundMatrixCoordinates.basis GroundCoordinates.Point002.real_inverse).symm x.1 i)
    rw [GroundMatrixCoordinates.basis_symm_apply]
    exact sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound _) (hx j).1)
  · change (sumBox (fun j => (Interval.point (GroundCoordinates.Point002.Q i j)).mul (B.I j))).Contains
      ((GroundMatrixCoordinates.basis GroundCoordinates.Point002.imag_inverse).symm x.2 i)
    rw [GroundMatrixCoordinates.basis_symm_apply]
    exact sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound _) (hx j).2)

theorem basis_rows : ∀ i : Fin 8,
    (∑ j, |GroundCoordinates.Point002.S i j|) ≤ basisBudget ∧
    (∑ j, |GroundCoordinates.Point002.R i j|) ≤ basisBudget := by decide +kernel

theorem basis_norm : ‖T.toContinuousLinearMap‖ ≤ (basisBudget : ℝ) := by
  have hs : ‖realBasis.toContinuousLinearMap‖ ≤ (basisBudget : ℝ) := by
    apply GroundLocalDynamics.operator_norm_le_rows _ (by norm_num [basisBudget])
    intro i
    have hcol (j : Fin 8) : realBasis (GroundLocalDynamics.column j) i = (GroundCoordinates.Point002.S i j : ℝ) := by
      change GroundMatrixCoordinates.basis GroundCoordinates.Point002.real_inverse (GroundLocalDynamics.column j) i = _
      rw [GroundMatrixCoordinates.basis_apply]
      simp [GroundLocalDynamics.column, Pi.single_apply]
    simp only [ContinuousLinearEquiv.coe_coe, hcol]
    exact_mod_cast (basis_rows i).1
  have hr : ‖imagBasis.toContinuousLinearMap‖ ≤ (basisBudget : ℝ) := by
    apply GroundLocalDynamics.operator_norm_le_rows _ (by norm_num [basisBudget])
    intro i
    have hcol (j : Fin 8) : imagBasis (GroundLocalDynamics.column j) i = (GroundCoordinates.Point002.R i j : ℝ) := by
      change GroundMatrixCoordinates.basis GroundCoordinates.Point002.imag_inverse (GroundLocalDynamics.column j) i = _
      rw [GroundMatrixCoordinates.basis_apply]
      simp [GroundLocalDynamics.column, Pi.single_apply]
    simp only [ContinuousLinearEquiv.coe_coe, hcol]
    exact_mod_cast (basis_rows i).2
  change ‖realBasis.toContinuousLinearMap.prodMap imagBasis.toContinuousLinearMap‖ ≤ (basisBudget : ℝ)
  exact (GroundNativeLocal.product_operator_norm_bound _ _).trans (max_le hs hr)

theorem input_box_on_ball {x : State} (hx : x ∈ closedBall (T.symm (u, 0)) (ρ : ℝ)) : input.Contains (T x) := by
  have hdist : ‖x-T.symm (u, 0)‖ ≤ (ρ : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hx
  have hfield : ‖T x-(u, 0)‖ ≤ (basisBudget : ℝ)*(ρ : ℝ) := by
    rw [← T.apply_symm_apply (u, (0 : Field)), ← map_sub]
    exact (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul basis_norm hdist (norm_nonneg _) (by norm_num [basisBudget]))
  have hR (i : Fin 8) : |(T x).1 i-u i| ≤ (basisBudget : ℝ)*(ρ : ℝ) := by
    have hp : |(T x).1 i-u i| ≤ ‖(T x-(u, 0)).1‖ := by
      simpa only [Real.norm_eq_abs, Prod.fst_sub, Pi.sub_apply] using norm_le_pi_norm (T x-(u, 0)).1 i
    exact hp.trans ((by rw [Prod.norm_def]; exact le_max_left _ _ : ‖(T x-(u, 0)).1‖ ≤ ‖T x-(u, 0)‖).trans hfield)
  have hI (i : Fin 8) : |(T x).2 i| ≤ (basisBudget : ℝ)*(ρ : ℝ) := by
    have he : (T x-(u, 0)).2 = (T x).2 := by change (T x).2-0 = (T x).2; exact sub_zero _
    have hp : |(T x).2 i| ≤ ‖(T x-(u, 0)).2‖ := by
      rw [he]
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (T x).2 i
    exact hp.trans ((by rw [Prod.norm_def]; exact le_max_right _ _ : ‖(T x-(u, 0)).2‖ ≤ ‖T x-(u, 0)‖).trans hfield)
  intro i
  have hz := (old_positive_sound i).1
  have hr := abs_le.mp (hR i)
  have hi := abs_le.mp (hI i)
  simp only [oldPositive, GroundBackgroundKernel.fieldBox, Interval.Contains, Rat.cast_sub, Rat.cast_add] at hz
  simp only [input, Interval.Contains, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
  constructor <;> constructor <;> linarith


theorem real_direction_sound (j : Fin 8) : (realDirection j).Contains (T (GroundLocalDynamics.column j, 0)) := by
  intro i
  constructor
  · change (Interval.point (GroundCoordinates.Point002.S i j)).Contains (realBasis (GroundLocalDynamics.column j) i)
    have he : realBasis (GroundLocalDynamics.column j) i = (GroundCoordinates.Point002.S i j : ℝ) := by
      change GroundMatrixCoordinates.basis GroundCoordinates.Point002.real_inverse (GroundLocalDynamics.column j) i = _
      rw [GroundMatrixCoordinates.basis_apply]
      simp [GroundLocalDynamics.column, Pi.single_apply]
    rw [he]; exact Interval.point_sound _
  · change (Interval.point 0).Contains (imagBasis 0 i)
    rw [map_zero]
    simpa only [Rat.cast_zero, Pi.zero_apply] using Interval.point_sound 0

theorem imag_direction_sound (j : Fin 8) : (imagDirection j).Contains (T (0, GroundLocalDynamics.column j)) := by
  intro i
  constructor
  · change (Interval.point 0).Contains (realBasis 0 i)
    rw [map_zero]
    simpa only [Rat.cast_zero, Pi.zero_apply] using Interval.point_sound 0
  · change (Interval.point (GroundCoordinates.Point002.R i j)).Contains (imagBasis (GroundLocalDynamics.column j) i)
    have he : imagBasis (GroundLocalDynamics.column j) i = (GroundCoordinates.Point002.R i j : ℝ) := by
      change GroundMatrixCoordinates.basis GroundCoordinates.Point002.imag_inverse (GroundLocalDynamics.column j) i = _
      rw [GroundMatrixCoordinates.basis_apply]
      simp [GroundLocalDynamics.column, Pi.single_apply]
    rw [he]; exact Interval.point_sound _

theorem core_real_jet_enclosed
    (hA : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q a C K L)
    (hR : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
      (sourceDerivativeBox originalBackground κ input (realDirection j)) q (yR j) (eR j))
    (hD : ∀ j i : Fin 8, included (computedDR j i) (DR j i))
    (hJ : ∀ j : Fin 8, (computedJR j).Included (JR j))
    {x : State} (hx : input.Contains x) (j : Fin 8) :
    (CR j).Contains (T.symm (GroundNativeGeneralDerivative.fullDerivative b (κ : ℝ) (1/2) x
      (T (GroundLocalDynamics.column j, 0)))) := by
  have hg := GroundBackgroundKernel.actual_selected_enclosed hA.ground (sourceBox_sound originalBackground κ hx)
  have hd := selectedDerivative_enclosed hA.ground (hR j) hx (real_direction_sound j)
  have hdCached := fun i => GroundNativeBox.included_sound (hD j i) (hd i)
  have hk := (GroundIntervalReciprocal.inverse_sqrt_sound hA.overlap_inverse (overlapBox_sound hx hg)).2
  have hm := mixedBox_sound hx hg hk
  have hl := (GroundIntervalReciprocal.inverse_sqrt_sound hA.mixed_inverse (normBox_sound hm)).2
  exact coordinateBox_sound (StateBox.included_sound (hJ j)
    (fullDerivativeBox_sound hx (real_direction_sound j) hg hdCached hk hl))

theorem core_imag_jet_enclosed
    (hA : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q a C K L)
    (hR : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
      (sourceDerivativeBox originalBackground κ input (imagDirection j)) q (yI j) (eI j))
    (hD : ∀ j i : Fin 8, included (computedDI j i) (DI j i))
    (hJ : ∀ j : Fin 8, (computedJI j).Included (JI j))
    {x : State} (hx : input.Contains x) (j : Fin 8) :
    (CI j).Contains (T.symm (GroundNativeGeneralDerivative.fullDerivative b (κ : ℝ) (1/2) x
      (T (0, GroundLocalDynamics.column j)))) := by
  have hg := GroundBackgroundKernel.actual_selected_enclosed hA.ground (sourceBox_sound originalBackground κ hx)
  have hd := selectedDerivative_enclosed hA.ground (hR j) hx (imag_direction_sound j)
  have hdCached := fun i => GroundNativeBox.included_sound (hD j i) (hd i)
  have hk := (GroundIntervalReciprocal.inverse_sqrt_sound hA.overlap_inverse (overlapBox_sound hx hg)).2
  have hm := mixedBox_sound hx hg hk
  have hl := (GroundIntervalReciprocal.inverse_sqrt_sound hA.mixed_inverse (normBox_sound hm)).2
  exact coordinateBox_sound (StateBox.included_sound (hJ j)
    (fullDerivativeBox_sound hx (imag_direction_sound j) hg hdCached hk hl))

theorem core_guards
    (hA : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q a C K L)
    {x : State} (hx : input.Contains x) :
    GroundNativeControls.originalTolerance < overlapNorm b (κ : ℝ) x ∧
    GroundNativeControls.originalTolerance < Real.sqrt (stateNormSq (mixed b (κ : ℝ) (1/2) x)) := by
  have hn := arithmetic_native_step hA hx
  have ho : (τ : ℝ) < overlapNorm b (κ : ℝ) x := by
    simpa only [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using hn.1
  have hlegal := hn.2.1
  change NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack x) at hlegal
  rw [NativeLegal, ← pack_mixed_native (by exact_mod_cast hA.threshold_nonneg) b (κ : ℝ) (1/2) x ho, norm_pack] at hlegal
  simpa only [tolerance_return] using And.intro ho hlegal

theorem core_derivative_norm
    (hA : GroundNativeBox.Arithmetic originalBackground κ τ input output z r q a C K L)
    (hR : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
      (sourceDerivativeBox originalBackground κ input (realDirection j)) q (yR j) (eR j))
    (hI : ∀ j : Fin 8, GroundBackgroundResponse.ResponseArithmetic C G
      (sourceDerivativeBox originalBackground κ input (imagDirection j)) q (yI j) (eI j))
    (hDR : ∀ j i : Fin 8, included (computedDR j i) (DR j i))
    (hDI : ∀ j i : Fin 8, included (computedDI j i) (DI j i))
    (hJR : ∀ j : Fin 8, (computedJR j).Included (JR j))
    (hJI : ∀ j : Fin 8, (computedJI j).Included (JI j))
    (hr : ∀ i : Fin 8, (∑ j : Fin 8, (((CR j).R i).bound + ((CI j).R i).bound)) ≤ rate)
    (hi : ∀ i : Fin 8, (∑ j : Fin 8, (((CR j).I i).bound + ((CI j).I i).bound)) ≤ rate)
    {x : State} (hx : input.Contains (T x)) :
    ‖GroundNativeQuantitativeBall.derivative T b (κ : ℝ) (1/2) x‖ ≤ (rate : ℝ) := by
  apply GroundStateRows.operator_norm_le_rows _ (by norm_num [rate])
  · intro i
    calc
      (∑ j, (|(GroundNativeQuantitativeBall.derivative T b (κ : ℝ) (1/2) x (GroundLocalDynamics.column j, 0)).1 i|+
        |(GroundNativeQuantitativeBall.derivative T b (κ : ℝ) (1/2) x (0, GroundLocalDynamics.column j)).1 i|)) ≤
          ∑ j, ((((CR j).R i).bound : ℝ)+(((CI j).R i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((core_real_jet_enclosed hA hR hDR hJR hx j) i).1)
          (Interval.abs_le_bound ((core_imag_jet_enclosed hA hI hDI hJI hx j) i).1)
      _ ≤ (rate : ℝ) := by
        have hc : ((∑ j : Fin 8, (((CR j).R i).bound + ((CI j).R i).bound) : ℚ) : ℝ) ≤ (rate : ℝ) := Rat.cast_le.mpr (hr i)
        simpa only [Rat.cast_sum, Rat.cast_add] using hc
  · intro i
    calc
      (∑ j, (|(GroundNativeQuantitativeBall.derivative T b (κ : ℝ) (1/2) x (GroundLocalDynamics.column j, 0)).2 i|+
        |(GroundNativeQuantitativeBall.derivative T b (κ : ℝ) (1/2) x (0, GroundLocalDynamics.column j)).2 i|)) ≤
          ∑ j, ((((CR j).I i).bound : ℝ)+(((CI j).I i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((core_real_jet_enclosed hA hR hDR hJR hx j) i).2)
          (Interval.abs_le_bound ((core_imag_jet_enclosed hA hI hDI hJI hx j) i).2)
      _ ≤ (rate : ℝ) := by
        have hc : ((∑ j : Fin 8, (((CR j).I i).bound + ((CI j).I i).bound) : ℚ) : ℝ) ≤ (rate : ℝ) := Rat.cast_le.mpr (hi i)
        simpa only [Rat.cast_sum, Rat.cast_add] using hc

theorem core_endpoint_entry
    (he : ∀ i : Fin 8, (entryBox.R i).bound ≤ 1/48000 ∧ (entryBox.I i).bound ≤ 1/48000) :
    dist (T.symm (unpack (-GroundOriginalNativePrefix.orbit 16))) (T.symm (u, 0)) ≤ (1/48000 : ℝ) := by
  have hp := GroundOriginalNativePrefix.native_prefix_enclosed (16 : Fin 17)
  have hn : reflectedEndpoint.Contains (unpack (-GroundOriginalNativePrefix.orbit 16)) := by
    intro i
    simpa only [reflectedEndpoint, GroundNativeReflection.unpack_neg, Prod.fst_neg,
      Prod.snd_neg, Pi.neg_apply] using And.intro (Interval.neg_sound (hp i).1) (Interval.neg_sound (hp i).2)
  have hd : (GroundOriginalNativePrefix.differenceBox reflectedEndpoint oldPositive).Contains
      (unpack (-GroundOriginalNativePrefix.orbit 16)-(u, 0)) := by
    intro i
    simpa only [GroundOriginalNativePrefix.differenceBox, Prod.fst_sub, Prod.snd_sub,
      Pi.sub_apply, sub_eq_add_neg] using And.intro
      (Interval.add_sound (hn i).1 (Interval.neg_sound (old_positive_sound i).1))
      (Interval.add_sound (hn i).2 (Interval.neg_sound (old_positive_sound i).2))
  have hc := coordinateBox_sound hd
  rw [dist_eq_norm, ← map_sub]
  rw [Prod.norm_def]
  apply max_le
  all_goals apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/48000)).mpr
  all_goals intro i
  · have h : ((entryBox.R i).bound : ℝ) ≤ ((1/48000 : ℚ) : ℝ) := Rat.cast_le.mpr (he i).1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    simpa only [Real.norm_eq_abs] using (Interval.abs_le_bound (hc i).1).trans h
  · have h : ((entryBox.I i).bound : ℝ) ≤ ((1/48000 : ℚ) : ℝ) := Rat.cast_le.mpr (he i).2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    simpa only [Real.norm_eq_abs] using (Interval.abs_le_bound (hc i).2).trans h


end
end SbtCosmo.Derivation.GroundOriginalBasin
