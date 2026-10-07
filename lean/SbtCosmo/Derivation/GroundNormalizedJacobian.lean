import SbtCosmo.Derivation.GroundSourceJacobian
import SbtCosmo.Derivation.GroundFixedPoint
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Actual normalization derivative and the normalized Step26 tangent Jacobian.
All-background existence supplies realizable fixed points; no stability claim
or certified numerical branch is inferred from existence. -/
namespace SbtCosmo.Derivation.GroundNormalizedJacobian
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSmooth GroundSourceJacobian
open scoped BigOperators ContDiff

def dotMap (u : Field) : Field →L[ℝ] ℝ :=
  ∑ i, u i • ContinuousLinearMap.proj i
def projection (u : Field) : Field →L[ℝ] Field :=
  ContinuousLinearMap.id ℝ Field - (dotMap u).smulRight u
def normalize (u : Field) : Field := fun i => u i / Real.sqrt (normSq u)

theorem dotMap_apply (u h : Field) : dotMap u h = dot u h := by simp [dotMap, dot]

theorem projection_apply (u h : Field) (i : Fin 8) :
    projection u h i = h i - dot u h * u i := by simp [projection, dotMap_apply]

theorem normSq_hasFDerivAt (u : Field) : HasFDerivAt normSq ((2 : ℝ) • dotMap u) u := by
  have hv (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt (x := u)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hv i).pow 2)
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [dotMap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sqrt_normSq_hasFDerivAt {u : Field} (hu : normSq u = 1) :
    HasFDerivAt (fun w => Real.sqrt (normSq w)) (dotMap u) u := by
  have hh := (normSq_hasFDerivAt u).sqrt (by rw [hu]; norm_num)
  convert hh using 1
  norm_num [hu, smul_smul]

theorem inv_sqrt_normSq_hasFDerivAt {u : Field} (hu : normSq u = 1) :
    HasFDerivAt (fun w => (Real.sqrt (normSq w))⁻¹) (-dotMap u) u := by
  have hh := (hasDerivAt_inv (by rw [hu]; norm_num : Real.sqrt (normSq u) ≠ 0)).comp_hasFDerivAt u
    (sqrt_normSq_hasFDerivAt hu)
  simpa only [hu, Real.sqrt_one, one_pow, inv_one, neg_smul, one_smul] using hh

theorem normalize_hasFDerivAt {u : Field} (hu : normSq u = 1) :
    HasFDerivAt normalize (projection u) u := by
  have hh := (inv_sqrt_normSq_hasFDerivAt hu).smul (hasFDerivAt_id u)
  convert hh using 1
  · funext w i
    simp [normalize, div_eq_mul_inv, mul_comm]
  · apply ContinuousLinearMap.ext
    intro h
    funext i
    simp [projection, hu, sub_eq_add_neg]

def affineJacobian (b : Field) (κ m : ℝ) (u : Field) : Field →L[ℝ] Field :=
  (1 - m) • ContinuousLinearMap.id ℝ Field + m • jacobian b κ u
def normalizedJacobian (b : Field) (κ m : ℝ) (u : Field) : Field →L[ℝ] Field :=
  (projection u).comp (affineJacobian b κ m u)

theorem affine_hasFDerivAt (b : Field) (κ m : ℝ) (u : Field) :
    HasFDerivAt (relaxed (groundMap b κ) m) (affineJacobian b κ m u) u := by
  have hh := ((hasFDerivAt_id u).const_smul (1 - m)).add
    ((groundMap_hasFDerivAt b κ u).const_smul m)
  exact hh

theorem normalized_hasFDerivAt {b : Field} {κ m : ℝ} {u : Field}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (normalizedRelaxed (groundMap b κ) m) (normalizedJacobian b κ m u) u := by
  have hr : relaxed (groundMap b κ) m u = u := by
    funext i
    simp only [relaxed, hf]
    ring
  have hn : HasFDerivAt normalize (projection u) (relaxed (groundMap b κ) m u) := by
    rw [hr]
    exact normalize_hasFDerivAt hu
  exact hn.comp u (affine_hasFDerivAt b κ m u)

theorem normalized_tangent_return {b : Field} {κ m : ℝ} {u h : Field}
    (hf : groundMap b κ u = u) (ht : dot u h = 0) :
    normalizedJacobian b κ m u h = (1 - m) • h + m • jacobian b κ u h := by
  have hj := jacobian_tangent b κ u h
  rw [hf] at hj
  have hdot : dot u (affineJacobian b κ m u h) = 0 := by
    calc
      dot u (affineJacobian b κ m u h) = (1 - m) * dot u h + m * dot u (jacobian b κ u h) := by
        simp [affineJacobian, dot, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      _ = 0 := by rw [ht, hj]; ring
  funext i
  change projection u (affineJacobian b κ m u h) i = _
  rw [projection_apply, hdot]
  simp [affineJacobian]

theorem positive_ground_fixed {b u : Field} {κ : ℝ}
    (hp : ∀ i, 0 < u i) (hg : IsSelfConsistentGround b κ u) : groundMap b κ u = u := by
  obtain ⟨e, he⟩ := hg
  exact positive_ground_unique (positiveGround_spec _).2 he (positiveGround_spec _).1 hp

/-- Actual fixed points and their derivatives are supplied for every native parameter. -/
theorem exists_actual_normalized_jacobian (b : Field) (κ m : ℝ) :
    ∃ u : Field, (∀ i, 0 < u i) ∧ normSq u = 1 ∧ groundMap b κ u = u ∧
      HasFDerivAt (normalizedRelaxed (groundMap b κ) m) (normalizedJacobian b κ m u) u := by
  obtain ⟨u, hp, hg⟩ := exists_selfConsistent_ground b κ
  have hn := hg.choose_spec.1
  have hf := positive_ground_fixed hp hg
  exact ⟨u, hp, hn, hf, normalized_hasFDerivAt hn hf⟩

/-- The scalar damping law now applies to an earned actual native Jacobian. -/
theorem actual_real_eigenmode_return {b : Field} {κ m t : ℝ} {u h : Field}
    (hf : groundMap b κ u = u) (ht : dot u h = 0) (he : jacobian b κ u h = t • h) :
    normalizedJacobian b κ m u h = (1 - m + m * t) • h := by
  rw [normalized_tangent_return hf ht, he]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Deleting the actual source coupling makes the original ground map constant. -/
theorem zero_coupling_groundMap (b u : Field) : groundMap b 0 u = positiveGround b := by
  have hs : GroundState.sourcePotential b 0 u = b := by
    funext i
    simp [GroundState.sourcePotential, BackgroundSelection.potential]
  change positiveGround (GroundState.sourcePotential b 0 u) = positiveGround b
  rw [hs]

theorem zero_coupling_jacobian (b u : Field) : jacobian b 0 u = 0 := by
  have hs : sourceDerivative b 0 u = 0 := by
    apply ContinuousLinearMap.ext
    intro h
    funext i
    simp [sourceDerivative_apply]
  simp [jacobian, hs]

theorem zero_coupling_tangent_return (b : Field) (m : ℝ) {h : Field}
    (ht : dot (positiveGround b) h = 0) :
    normalizedJacobian b 0 m (positiveGround b) h = (1 - m) • h := by
  rw [normalized_tangent_return (zero_coupling_groundMap b _) ht, zero_coupling_jacobian]
  simp

end
end SbtCosmo.Derivation.GroundNormalizedJacobian
