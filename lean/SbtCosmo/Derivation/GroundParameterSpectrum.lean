import SbtCosmo.Derivation.GroundParameterEquations
import SbtCosmo.Derivation.GroundNativeControls
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Continuity of the actual full normalized Jacobian in the original
parameters/state, and a determinant IVT return to actual minus-one modes. -/
namespace SbtCosmo.Derivation.GroundParameterSpectrum
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
open GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian GroundLocalDynamics
open GroundParameterEquations
open scoped ContDiff BigOperators

def jointGround (z : Parameter × Field) : Field := groundMap z.1.1 z.1.2 z.2

theorem jointGround_smooth : ContDiff ℝ ∞ jointGround := by
  have hs : ContDiff ℝ ∞ (fun z : Parameter × Field => sourcePotential z.1.1 z.1.2 z.2) := by
    unfold sourcePotential BackgroundSelection.potential GroundState.gradient
    fun_prop
  exact GroundSmooth.positiveGround_smooth.comp hs

theorem jointGround_partial (z : Parameter × Field) :
    (fderiv ℝ jointGround z).comp (ContinuousLinearMap.inr ℝ Parameter Field) =
      jacobian z.1.1 z.1.2 z.2 := by
  have hh0 : HasFDerivAt jointGround (fderiv ℝ jointGround z) z :=
    (jointGround_smooth.differentiable (by norm_num) z).hasFDerivAt
  have hp : HasFDerivAt (fun x : Field => (z.1, x)) (ContinuousLinearMap.inr ℝ Parameter Field) z.2 :=
    (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) z.2)
  have hh := hh0.comp z.2 hp
  change HasFDerivAt (groundMap z.1.1 z.1.2)
    ((fderiv ℝ jointGround z).comp (ContinuousLinearMap.inr ℝ Parameter Field)) z.2 at hh
  exact hh.unique (groundMap_hasFDerivAt z.1.1 z.1.2 z.2)

theorem jacobian_column_continuous (j : Fin 8) :
    Continuous (fun z : Parameter × Field => jacobian z.1.1 z.1.2 z.2 (column j)) := by
  have hc := jointGround_smooth.continuous_fderiv (by norm_num)
  have hh := hc.clm_apply (continuous_const (y := ((0 : Parameter), column j)))
  convert hh using 1
  funext z
  exact congrArg (fun L : Field →L[ℝ] Field => L (column j)) (jointGround_partial z).symm

def entries (L : Field →L[ℝ] Field) : Matrix (Fin 8) (Fin 8) ℝ := fun i j => L (column j) i
def halfMatrix (z : Parameter × Field) : Matrix (Fin 8) (Fin 8) ℝ :=
  entries (normalizedJacobian z.1.1 z.1.2 (1/2) z.2)

theorem halfMatrix_continuous : Continuous halfMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hj := jacobian_column_continuous j
  change Continuous (fun z : Parameter × Field => normalizedJacobian z.1.1 z.1.2 (1/2) z.2 (column j) i)
  simp only [normalizedJacobian, ContinuousLinearMap.comp_apply, projection_apply,
    affineJacobian, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dot]
  fun_prop

def crossingDet (z : Parameter × Field) : ℝ := (halfMatrix z + 1).det

theorem crossingDet_continuous : Continuous crossingDet :=
  (halfMatrix_continuous.add continuous_const).matrix_det

theorem determinant_zero_mode {L : Field →L[ℝ] Field}
    (hd : (entries L + 1).det = 0) : ∃ h : Field, h ≠ 0 ∧ L h = -h := by
  obtain ⟨h, hn, hh⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨h, hn, ?_⟩
  have he : L h + h = 0 := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hh
    convert hh using 1
    congr 1
    funext i
    rw [linear_action_entries]
    rfl
  exact eq_neg_of_add_eq_zero_left he

theorem projection_tangent {u : Field} (hu : normSq u = 1) (h : Field) : dot u (projection u h) = 0 := by
  simp only [dot, projection_apply, mul_sub, Finset.sum_sub_distrib]
  change dot u h - (∑ i, u i * (dot u h * u i)) = 0
  have he : (∑ i, u i * (dot u h * u i)) = dot u h * normSq u := by
    rw [normSq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hu, mul_one]
  exact sub_self _

theorem strict_sign_crossing {f : ℝ → ℝ} {a c : ℝ}
    (hac : a < c) (hf : ContinuousOn f (Set.Icc a c)) (hs : f a * f c < 0) :
    ∃ k ∈ Set.Ioo a c, f k = 0 := by
  have ha : f a ≠ 0 := by intro he; rw [he, zero_mul] at hs; linarith
  have hc : f c ≠ 0 := by intro he; rw [he, mul_zero] at hs; linarith
  have himage : (0 : ℝ) ∈ f '' Set.Icc a c := by
    by_cases hp : 0 < f a
    · have hn : f c < 0 := by nlinarith
      exact intermediate_value_Icc' hac.le hf ⟨hn.le, hp.le⟩
    · have hn : f a < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
      have hpos : 0 < f c := by nlinarith
      exact intermediate_value_Icc hac.le hf ⟨hn.le, hpos.le⟩
  obtain ⟨k, hk, hz⟩ := himage
  refine ⟨k, ⟨lt_of_le_of_ne hk.1 ?_, lt_of_le_of_ne hk.2 ?_⟩, hz⟩
  · intro he; subst k; exact ha hz
  · intro he; subst k; exact hc hz

/-- A determinant sign change on an actual continuous fixed-point branch
earns an interior minus-one multiplier, tangent to the unit sphere, and
returns it to the derivative of the unchanged native complex iteration. -/
theorem actual_minus_one_crossing {b : Field} {u : ℝ → Field} {a c τ : ℝ}
    (hac : a < c) (hu : ContinuousOn u (Set.Icc a c))
    (hfixed : ∀ k ∈ Set.Icc a c, normSq (u k) = 1 ∧ groundMap b k (u k) = u k)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hsign : crossingDet ((b, a), u a) * crossingDet ((b, c), u c) < 0) :
    ∃ k ∈ Set.Ioo a c, ∃ h : Field, h ≠ 0 ∧ dot (u k) h = 0 ∧
      normalizedJacobian b k (1/2) (u k) h = -h ∧
      GroundNativeJacobian.fullDerivative b k (1/2) (u k) (h, 0) = -(h, 0) ∧
      HasFDerivAt (GroundNativeJacobian.nativePairMap τ b k (1/2))
        (GroundNativeJacobian.fullDerivative b k (1/2) (u k)) (u k, 0) := by
  have hp : Continuous (fun k : ℝ => ((b, k) : Parameter)) := continuous_const.prodMk continuous_id
  have hgraph : ContinuousOn (fun k : ℝ => ((b, k), u k)) (Set.Icc a c) := hp.continuousOn.prodMk hu
  have hd : ContinuousOn (fun k => crossingDet ((b, k), u k)) (Set.Icc a c) :=
    crossingDet_continuous.comp_continuousOn' hgraph
  obtain ⟨k, hk, hz⟩ := strict_sign_crossing hac hd hsign
  obtain ⟨h, hn, he⟩ := determinant_zero_mode hz
  obtain ⟨hnorm, hfix⟩ := hfixed k ⟨hk.1.le, hk.2.le⟩
  have ht := projection_tangent hnorm (affineJacobian b k (1/2) (u k) h)
  change dot (u k) (normalizedJacobian b k (1/2) (u k) h) = 0 at ht
  rw [he] at ht
  have hdot : dot (u k) h = 0 := by
    simpa only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] using ht
  refine ⟨k, hk, h, hn, hdot, he, ?_, ?_⟩
  · have hm := GroundNativeControls.real_mode_full_return (ℓ := -1) (by simpa using he)
    simpa using hm
  · exact GroundNativeJacobian.nativePairMap_hasFDerivAt hnorm hfix hτ0 hτ1

end
end SbtCosmo.Derivation.GroundParameterSpectrum
