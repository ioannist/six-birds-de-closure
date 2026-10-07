import SbtCosmo.Derivation.ScalarPriceStationarity
import SbtCosmo.Derivation.SchurDifferential
import SbtCosmo.Derivation.SchurClosurePrice

/-! Canonical scalar sensitivity price and stationarity returned to the actual
Schur energy, matrix derivative and trace-dual adjoint. -/
namespace SbtCosmo.Derivation.ScalarSchurStationarity
noncomputable section
open Set Matrix ExtendedClosurePrice ConvexSubgradient SchurClosurePrice SchurDifferential
open scoped Matrix Matrix.Norms.Elementwise
variable {n m e E : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq e]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual Schur energy differentiability, earned even for singular native Gram
blocks. No derivative of the residual is supplied. -/
theorem hasFDerivAt_energy (W : Matrix m m ℝ) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) (x : E) :
    HasFDerivAt (fun z => schurEnergy W L (D z)) (pricePullback L D x W) x := by
  simpa only [sub_zero,schurEnergy] using hasFDerivAt_trace_gap L D x W 0

/-- Scaling the scalar price scales the original audit weight in the actual
matrix trace-dual pullback. This is not an unrelated matrix-budget price. -/
theorem scaled_adjoint (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    (x : E) (W : Matrix m m ℝ) (p : ℝ) :
    p • pricePullback L D x W=
      traceAdjoint (fderiv ℝ (fun z => SbtCosmo.Adequacy.Support.residual L (D z)) x) (p • W) := by
  rw [pricePullback_eq_adjoint_fderiv,map_smul]

/-- A single p=-V'(B)>0 supplies scalar duality and full qualified original
Schur stationarity, with literal adjoint of the actual residual derivative and
explicit evaluation on every primal direction. -/
theorem positive_price_stationarity {W : Matrix m m ℝ} (hW : W.PosSemidef)
    (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B d lo hi : ℝ} {star xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : PrimalOptimum A J (fun x => schurEnergy W L (D x)) B star)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, value A J (fun x => schurEnergy W L (D x)) T ≠ ⊤ ∧
      value A J (fun x => schurEnergy W L (D x)) T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J (fun x => schurEnergy W L (D x)) T).toReal) d B)
    (hs : d < 0) :
    ∃ (p : ℝ) (q η : E →L[ℝ] ℝ), p = -d ∧ 0 < p ∧ schurEnergy W L (D star)=B ∧
      DualCertificate A J (fun x => schurEnergy W L (D x)) B p star ∧
      dualValue A J (fun x => schurEnergy W L (D x)) B p=
        value A J (fun x => schurEnergy W L (D x)) B ∧
      Subgradient J star q ∧ NormalCone A star η ∧
      q+traceAdjoint (fderiv ℝ (fun x => SbtCosmo.Adequacy.Support.residual L (D x)) star) (p • W)+η=0 ∧
      (∀ h : E, q h+2*p*trace (W*D star*complement L*(D.linear h).transpose)+η h=0) := by
  obtain ⟨p,q,η,hp,hpos,hact,hc,hdual,hq,hη,hstation⟩ :=
    ScalarPriceStationarity.positive_price_smooth_stationarity hbottom hJ hA
      (affine_schur_energy_convex hW L D convex_univ) hC hAr hstar hB hfinite hd hs
      (hasFDerivAt_energy W L D star)
  refine ⟨p,q,η,hp,hpos,hact,hc,hdual,hq,hη,?_,?_⟩
  · rwa [scaled_adjoint] at hstation
  · intro h
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f h) hstation
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply,smul_eq_mul,pricePullback_psd hW] at hh
    nlinarith only [hh]

end
end SbtCosmo.Derivation.ScalarSchurStationarity
