import SbtCosmo.Derivation.SchurDifferential
import SbtCosmo.Derivation.RelativeSchurStationarity

/-! Original extended qualified Schur stationarity in the literal trace-dual
adjoint form, with its explicit directional formula. -/
namespace SbtCosmo.Derivation.SchurAdjointStationarity
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice ConvexSubgradient ExtendedClosurePrice SchurDifferential
open scoped Matrix Matrix.Norms.Elementwise
variable {n m e E : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Full original objective/normal split with the actual residual derivative's
trace-dual adjoint and an explicit two-term directional evaluation. -/
theorem matrix_stationarity (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef) :
    ∃ (P : Matrix m m ℝ) (q η : E →L[ℝ] ℝ), P.PosSemidef ∧
      Subgradient J star q ∧ NormalCone A star η ∧
      q+traceAdjoint (fderiv ℝ (fun x => SbtCosmo.Adequacy.Support.residual L (D x)) star) P+η=0 ∧
      (∀ h : E, q h+2*trace (P*D star*complement L*(D.linear h).transpose)+η h=0) ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := by
  obtain ⟨P,q,η,hP,hq,hη,hs,hcomp⟩ := RelativeSchurStationarity.matrix_stationarity L D
    hbottom hJ hA hC hAr hstar hx₀ hfinite₀ hslater
  change q+fderiv ℝ (fun x => trace (P*(SbtCosmo.Adequacy.Support.residual L (D x)-(B : Matrix m m ℝ)))) star+η=0 at hs
  rw [fderiv_trace_gap] at hs
  refine ⟨P,q,η,hP,hq,hη,?_,?_,hcomp⟩
  · rwa [pricePullback_eq_adjoint_fderiv] at hs
  · intro h
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f h) hs
    simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,pricePullback_psd hP] using hh

/-- Strict actual PSD-direction value decrease earns a nonzero price in the
literal adjoint stationarity theorem, without a derivative or adjoint premise. -/
theorem matrix_stationarity_nonzero (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef)
    (hsensitive : ∃ H : Symmetric m, positive H ∧
      ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive (B+H) <
        ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive B) :
    ∃ (P : Matrix m m ℝ) (q η : E →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      Subgradient J star q ∧ NormalCone A star η ∧
      q+traceAdjoint (fderiv ℝ (fun x => SbtCosmo.Adequacy.Support.residual L (D x)) star) P+η=0 ∧
      (∀ h : E, q h+2*trace (P*D star*complement L*(D.linear h).transpose)+η h=0) ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := by
  obtain ⟨P,q,η,hP,hne,hq,hη,hs,hcomp⟩ := RelativeSchurStationarity.matrix_stationarity_nonzero L D
    hbottom hJ hA hC hAr hstar hx₀ hfinite₀ hslater hsensitive
  change q+fderiv ℝ (fun x => trace (P*(SbtCosmo.Adequacy.Support.residual L (D x)-(B : Matrix m m ℝ)))) star+η=0 at hs
  rw [fderiv_trace_gap] at hs
  refine ⟨P,q,η,hP,hne,hq,hη,?_,?_,hcomp⟩
  · rwa [pricePullback_eq_adjoint_fderiv] at hs
  · intro h
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f h) hs
    simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,pricePullback_psd hP] using hh

end
end SbtCosmo.Derivation.SchurAdjointStationarity
