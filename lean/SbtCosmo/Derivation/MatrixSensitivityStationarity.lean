import SbtCosmo.Derivation.MatrixPriceSensitivity
import SbtCosmo.Derivation.GeneralMatrixStationarity

/-! One earned matrix price supplies full budget sensitivity, actual stationarity
and original finite strong duality. Slater earns all local value guards. -/
namespace SbtCosmo.Derivation.MatrixSensitivityStationarity
noncomputable section
open Set Filter Matrix MatrixPriceRepresentation MatrixClosurePrice GeneralMatrixPrice
open MatrixPriceSensitivity ExtendedClosurePrice ConvexSubgradient SchurDifferential
open scoped Matrix Topology Matrix.Norms.Elementwise
variable {m E : Type*} [Fintype m] [DecidableEq m]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Full value derivative and strict PSD-direction sensitivity identify the
same nonzero matrix price used by general smooth qualified stationarity.
No local finite-value guard or final output is supplied. -/
theorem matrix_stationarity {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ xr : E} {Xi' : E →L[ℝ] Matrix m m ℝ} {d : Symmetric m →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hXi : LoewnerConvexOn A Xi)
    (hderiv : HasFDerivAt (fun x => (Xi x : Matrix m m ℝ)) Xi' star)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J Xi positive T).toReal) d B)
    (hsensitive : ∃ H : Symmetric m, positive H ∧ d H < 0) :
    ∃ (P : Matrix m m ℝ) (q η : E →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      tracePrice P=-d ∧ P=priceMatrix (-d).toLinearMap ∧
      (∀ H : Symmetric m, trace (P*(H : Matrix m m ℝ)) = -d H) ∧
      Subgradient J star q ∧ NormalCone A star η ∧ q+traceAdjoint Xi' P+η=0 ∧
      trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊤ ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊥ := by
  obtain ⟨P,q,η,hP,hq,hη,hstation,hcomp,hc,hdual,hfinite⟩ := GeneralMatrixStationarity.matrix_stationarity
    hbottom hJ hA hC hAr hXi hderiv hstar hx₀ hfinite₀ hslater
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  have heq := slater_price_identification (fun x _ => hbottom x) hrestricted hXi hc hx₀ hfinite₀ hslater hd
  have hrepr (H : Symmetric m) : trace (P*(H : Matrix m m ℝ)) = -d H :=
    congrArg (fun p : Symmetric m →L[ℝ] ℝ => p H) heq
  have hne : P ≠ 0 := by
    intro hz
    obtain ⟨H,_,hH⟩ := hsensitive
    have hh := hrepr H
    rw [hz,zero_mul,trace_zero] at hh
    linarith
  have hmatrix : P=priceMatrix (-d).toLinearMap := by rw [← heq,priceMatrix_tracePrice hP.1]
  exact ⟨P,q,η,hP,hne,heq,hmatrix,hrepr,hq,hη,hstation,hcomp,hc,hdual,hfinite⟩

/-- The same full value derivative also identifies the price in the genuinely
nonsmooth matrix-map endpoint. Its trace-energy support is earned; no matrix
derivative or local finite-value guard is supplied. -/
theorem matrix_nonsmooth_stationarity {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ xr : E} {d : Symmetric m →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hXi : LoewnerConvexOn univ Xi)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J Xi positive T).toReal) d B)
    (hsensitive : ∃ H : Symmetric m, positive H ∧ d H < 0) :
    ∃ (P : Matrix m m ℝ) (q k η : E →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      tracePrice P=-d ∧ P=priceMatrix (-d).toLinearMap ∧
      (∀ H : Symmetric m, trace (P*(H : Matrix m m ℝ)) = -d H) ∧
      Subgradient J star q ∧ RealSubgradient (fun x => trace (P*(Xi x : Matrix m m ℝ))) star k ∧
      NormalCone A star η ∧ q+k+η=0 ∧
      trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B := by
  obtain ⟨P,q,k,η,hP,hq,hk,hη,hstation,hcomp,hc,hdual⟩ := GeneralMatrixStationarity.matrix_nonsmooth_stationarity
    hbottom hJ hA hC hAr hXi hstar hx₀ hfinite₀ hslater
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  have heq := slater_price_identification (fun x _ => hbottom x) hrestricted
    (fun x _ y _ => hXi x (mem_univ _) y (mem_univ _)) hc hx₀ hfinite₀ hslater hd
  have hrepr (H : Symmetric m) : trace (P*(H : Matrix m m ℝ)) = -d H :=
    congrArg (fun p : Symmetric m →L[ℝ] ℝ => p H) heq
  have hne : P ≠ 0 := by
    intro hz
    obtain ⟨H,_,hH⟩ := hsensitive
    have hh := hrepr H
    rw [hz,zero_mul,trace_zero] at hh
    linarith
  have hmatrix : P=priceMatrix (-d).toLinearMap := by rw [← heq,priceMatrix_tracePrice hP.1]
  exact ⟨P,q,k,η,hP,hne,heq,hmatrix,hrepr,hq,hk,hη,hstation,hcomp,hc,hdual⟩

end
end SbtCosmo.Derivation.MatrixSensitivityStationarity
