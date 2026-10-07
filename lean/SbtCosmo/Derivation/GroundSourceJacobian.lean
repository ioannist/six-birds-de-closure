import SbtCosmo.Derivation.GroundSmooth

/-! Earned derivative of the unchanged Step26 nonlinear real ground map for
every background and field, including the original nonconstant template. -/
namespace SbtCosmo.Derivation.GroundSourceJacobian
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSmooth
open scoped BigOperators ContDiff

def gradientLM : Field →ₗ[ℝ] Field where
  toFun := gradient
  map_add' a b := by
    funext i
    dsimp [gradient]
    ring
  map_smul' c u := by
    funext i
    simp [gradient, smul_eq_mul]
    ring
def gradientMap : Field →L[ℝ] Field := gradientLM.toContinuousLinearMap

def sourceDerivativeLM (b : Field) (κ : ℝ) (u : Field) : Field →ₗ[ℝ] Field where
  toFun h := fun i => 2 * κ * (gradient u i * gradient h i + b i * u i * h i)
  map_add' h k := by
    funext i
    dsimp [gradient]
    ring
  map_smul' c h := by
    funext i
    simp [gradient, smul_eq_mul]
    ring
def sourceDerivative (b : Field) (κ : ℝ) (u : Field) : Field →L[ℝ] Field :=
  (sourceDerivativeLM b κ u).toContinuousLinearMap

theorem sourceDerivative_apply (b : Field) (κ : ℝ) (u h : Field) (i : Fin 8) :
    sourceDerivative b κ u h i = 2 * κ * (gradient u i * gradient h i + b i * u i * h i) := rfl

theorem sourcePotential_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (sourcePotential b κ) := by
  unfold sourcePotential BackgroundSelection.potential gradient
  fun_prop

theorem sourcePotential_hasFDerivAt (b : Field) (κ : ℝ) (u : Field) :
    HasFDerivAt (sourcePotential b κ) (sourceDerivative b κ u) u := by
  have hv (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt (x := u)
  have hg (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp u
    (gradientMap.hasFDerivAt (x := u))
  have hh (i : Fin 8) := (((hg i).pow 2).add ((hv i).pow 2 |>.const_mul (b i))).const_mul κ |>.const_add (b i)
  convert hasFDerivAt_pi.mpr hh using 1
  apply ContinuousLinearMap.ext
  intro h
  funext i
  simp [sourceDerivative, sourceDerivativeLM, gradientMap, gradientLM]
  ring

def groundMap (b : Field) (κ : ℝ) (u : Field) : Field := positiveGround (sourcePotential b κ u)
def jacobian (b : Field) (κ : ℝ) (u : Field) : Field →L[ℝ] Field :=
  (selectorDerivative (sourcePotential b κ u)).comp (sourceDerivative b κ u)

theorem groundMap_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (groundMap b κ) :=
  positiveGround_smooth.comp (sourcePotential_smooth b κ)

/-- The full actual real map derivative is constructed, rather than supplied. -/
theorem groundMap_hasFDerivAt (b : Field) (κ : ℝ) (u : Field) :
    HasFDerivAt (groundMap b κ) (jacobian b κ u) u :=
  (positiveGround_hasFDerivAt (sourcePotential b κ u)).comp u (sourcePotential_hasFDerivAt b κ u)

theorem jacobian_tangent (b : Field) (κ : ℝ) (u h : Field) :
    dot (groundMap b κ u) (jacobian b κ u h) = 0 :=
  selector_derivative_tangent _ _

theorem jacobian_eigen_equation (b : Field) (κ : ℝ) (u h : Field) (i : Fin 8) :
    shifted (sourcePotential b κ u) (groundPair (sourcePotential b κ u)).2 (jacobian b κ u h) i -
      (pairDerivative (sourcePotential b κ u) (sourceDerivative b κ u h)).2 * groundMap b κ u i =
      -(sourceDerivative b κ u h i) * groundMap b κ u i :=
  selector_derivative_eigen_equation _ _ _

end
end SbtCosmo.Derivation.GroundSourceJacobian
