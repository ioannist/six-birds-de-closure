import SbtCosmo.Derivation.GroundEquations

/-! Smoothness and earned inverse-border derivative of the existing positive
ground selector for every real potential, including nonconstant potentials. -/
namespace SbtCosmo.Derivation.GroundSmooth
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundEquations Filter
open scoped Topology ContDiff BigOperators

theorem actual_selector_local_return (v : Field) :
    groundPair =ᶠ[nhds v] (actual_implicit_data v).implicitFunction := by
  have ht : Tendsto (fun z => (z, groundPair z)) (nhds v) (nhds (v, groundPair v)) :=
    (continuous_id.prodMk continuous_groundPair).continuousAt.tendsto
  have he := ht.eventually ((actual_implicit_data v).eventually_implicitFunction_apply_eq)
  filter_upwards [he] with z hz
  exact (hz (by rw [ground_equations, ground_equations])).symm

theorem groundPair_smooth : ContDiff ℝ ∞ groundPair := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  exact (actual_implicit_data v).contDiffAt_implicitFunction.congr_of_eventuallyEq
    (actual_selector_local_return v)

theorem positiveGround_smooth : ContDiff ℝ ∞ positiveGround := groundPair_smooth.fst
theorem groundEnergy_smooth : ContDiff ℝ ∞ (fun v => energy v (positiveGround v)) := groundPair_smooth.snd

def influenceLM (u : Field) : Field →ₗ[ℝ] Point where
  toFun h := (fun i => h i * u i, 0)
  map_add' a b := by
    apply Prod.ext
    · funext i
      dsimp
      ring
    · simp
  map_smul' c h := by
    apply Prod.ext
    · funext i
      simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_fst, RingHom.id_apply]
      ring
    · simp

def influence (u : Field) : Field →L[ℝ] Point := (influenceLM u).toContinuousLinearMap
def pairDerivative (v : Field) : Field →L[ℝ] Point :=
  (groundBorder v).symm.toContinuousLinearMap.comp (-influence (positiveGround v))
def selectorDerivative (v : Field) : Field →L[ℝ] Field :=
  (ContinuousLinearMap.fst ℝ Field ℝ).comp (pairDerivative v)

theorem pairDerivative_equation (v h : Field) :
    border v (groundPair v).1 (groundPair v).2 (pairDerivative v h) =
      (fun i => -h i * positiveGround v i, 0) := by
  change groundBorder v ((groundBorder v).symm (-influence (positiveGround v) h)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    simp [influence, influenceLM]
  · simp [influence, influenceLM]

theorem pairDerivative_unique (v h : Field) {y : Point}
    (hy : border v (groundPair v).1 (groundPair v).2 y =
      (fun i => -h i * positiveGround v i, 0)) : y = pairDerivative v h :=
  border_injective (positiveGround_spec v).2 (hy.trans (pairDerivative_equation v h).symm)

theorem groundPair_hasFDerivAt_fderiv (v : Field) :
    HasFDerivAt groundPair (fderiv ℝ groundPair v) v :=
  (groundPair_smooth.differentiable (by norm_num) v).hasFDerivAt

theorem actual_pair_fderiv (v : Field) : fderiv ℝ groundPair v = pairDerivative v := by
  have hg := groundPair_hasFDerivAt_fderiv v
  have hh := (equations_hasFDerivAt (v, groundPair v)).comp v ((hasFDerivAt_id v).prodMk hg)
  have heq : (fun z => equations (z, groundPair z)) = fun _ : Field => (0 : Point) := by
    funext z
    exact ground_equations z
  change HasFDerivAt (fun z => equations (z, groundPair z))
    ((derivative (v, groundPair v)).comp
      ((ContinuousLinearMap.id ℝ Field).prod (fderiv ℝ groundPair v))) v at hh
  rw [heq] at hh
  have hz := hh.unique (hasFDerivAt_const (0 : Point) v)
  apply ContinuousLinearMap.ext
  intro h
  apply pairDerivative_unique
  have h0 := congrArg (fun L : Field →L[ℝ] Point => L h) hz
  change derivative (v, groundPair v) (h, fderiv ℝ groundPair v h) = 0 at h0
  apply Prod.ext
  · funext i
    have hi := congrArg (fun y : Point => y.1 i) h0
    change h i * positiveGround v i + shifted v (groundPair v).2
      (fderiv ℝ groundPair v h).1 i - (fderiv ℝ groundPair v h).2 * positiveGround v i = 0 at hi
    change shifted v (groundPair v).2 (fderiv ℝ groundPair v h).1 i -
      (fderiv ℝ groundPair v h).2 * positiveGround v i = -h i * positiveGround v i
    linarith
  · have hd := congrArg (fun y : Point => y.2) h0
    exact hd

theorem actual_pair_hasFDerivAt (v : Field) : HasFDerivAt groundPair (pairDerivative v) v := by
  rw [← actual_pair_fderiv]
  exact groundPair_hasFDerivAt_fderiv v

/-- Actual selector derivative, constructed from the earned invertible border. -/
theorem positiveGround_hasFDerivAt (v : Field) :
    HasFDerivAt positiveGround (selectorDerivative v) v :=
  (ContinuousLinearMap.fst ℝ Field ℝ).hasFDerivAt.comp v (actual_pair_hasFDerivAt v)

theorem selector_derivative_tangent (v h : Field) : dot (positiveGround v) (selectorDerivative v h) = 0 :=
  congrArg Prod.snd (pairDerivative_equation v h)

theorem selector_derivative_eigen_equation (v h : Field) (i : Fin 8) :
    shifted v (groundPair v).2 (selectorDerivative v h) i -
      (pairDerivative v h).2 * positiveGround v i = -h i * positiveGround v i :=
  congrArg (fun y : Point => y.1 i) (pairDerivative_equation v h)

end
end SbtCosmo.Derivation.GroundSmooth
