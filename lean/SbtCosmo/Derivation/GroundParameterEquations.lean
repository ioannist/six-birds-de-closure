import SbtCosmo.Derivation.GroundNativeLocal

/-! Joint background/coupling nonlinear equations. A strict Newton defect
earns the partial derivative's invertibility, not an inverse oracle. -/
namespace SbtCosmo.Derivation.GroundParameterEquations
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSourceJacobian GroundRootCertificate
open scoped ContDiff

abbrev Parameter := Field × ℝ
abbrev Domain := Parameter × Point
def jointSource (z : Domain) : Field := sourcePotential z.1.1 z.1.2 z.2.1
def jointResidual (z : Domain) : Point := residual z.1.1 z.1.2 z.2

theorem jointSource_smooth : ContDiff ℝ ∞ jointSource := by
  unfold jointSource sourcePotential BackgroundSelection.potential GroundState.gradient
  fun_prop

theorem jointResidual_smooth : ContDiff ℝ ∞ jointResidual :=
  GroundEquations.equations_smooth.comp (jointSource_smooth.prodMk contDiff_snd)

theorem jointResidual_hasFDerivAt (z : Domain) :
    HasFDerivAt jointResidual (fderiv ℝ jointResidual z) z :=
  (jointResidual_smooth.differentiable (by norm_num) z).hasFDerivAt

theorem jointResidual_partial (p : Parameter) (x : Point) :
    (fderiv ℝ jointResidual (p, x)).comp (ContinuousLinearMap.inr ℝ Parameter Point) =
      residualDerivative p.1 p.2 x := by
  have hh := (jointResidual_hasFDerivAt (p, x)).comp x
    ((hasFDerivAt_const p x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (residual p.1 p.2)
    ((fderiv ℝ jointResidual (p, x)).comp (ContinuousLinearMap.inr ℝ Parameter Point)) x at hh
  exact hh.unique (residual_hasFDerivAt p.1 p.2 x)

theorem defect_kernel_trivial (C D : Point →L[ℝ] Point)
    (hd : ‖ContinuousLinearMap.id ℝ Point - C.comp D‖ < 1)
    {h : Point} (hh : D h = 0) : h = 0 := by
  have he : (ContinuousLinearMap.id ℝ Point - C.comp D) h = h := by simp [hh]
  have hn := (ContinuousLinearMap.id ℝ Point - C.comp D).le_opNorm h
  rw [he] at hn
  have hz : ‖h‖ = 0 := by nlinarith [norm_nonneg h]
  exact norm_eq_zero.mp hz

/-- A strict Newton defect makes the actual partial derivative bijective.
The proposed preconditioner need not be given an inverse or injectivity proof. -/
theorem defect_bijective (C D : Point →L[ℝ] Point)
    (hd : ‖ContinuousLinearMap.id ℝ Point - C.comp D‖ < 1) : Function.Bijective D := by
  have hi : Function.Injective D := by
    intro a b hab
    apply sub_eq_zero.mp
    apply defect_kernel_trivial C D hd
    rw [map_sub, hab, sub_self]
  exact ⟨hi, LinearMap.surjective_of_injective (f := D.toLinearMap) hi⟩

theorem defect_preconditioner_bijective (C D : Point →L[ℝ] Point)
    (hd : ‖ContinuousLinearMap.id ℝ Point - C.comp D‖ < 1) : Function.Bijective C := by
  have hD := defect_bijective C D hd
  have hCD := defect_bijective (ContinuousLinearMap.id ℝ Point) (C.comp D) (by simpa using hd)
  have hi : Function.Injective C := by
    intro a b hab
    obtain ⟨u, hu⟩ := hD.2 a
    obtain ⟨v, hv⟩ := hD.2 b
    have huv : (C.comp D) u = (C.comp D) v := by simp [hu, hv, hab]
    have he := hCD.1 huv
    rw [he] at hu
    exact hu.symm.trans hv
  exact ⟨hi, LinearMap.surjective_of_injective (f := C.toLinearMap) hi⟩

def actualImplicitData (p : Parameter) (x : Point) (C : Point →L[ℝ] Point)
    (hd : ‖correctionDerivative p.1 p.2 C x‖ < 1) :
    IsContDiffImplicitAt ∞ jointResidual (fderiv ℝ jointResidual (p, x)) (p, x) := by
  refine ⟨jointResidual_hasFDerivAt _, jointResidual_smooth.contDiffAt, ?_, by norm_num⟩
  rw [jointResidual_partial]
  exact defect_bijective C _ hd

end
end SbtCosmo.Derivation.GroundParameterEquations
