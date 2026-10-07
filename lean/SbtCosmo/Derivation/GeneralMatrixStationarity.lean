import SbtCosmo.Derivation.GeneralMatrixPrice
import SbtCosmo.Derivation.ExtendedSmoothStationarity
import SbtCosmo.Derivation.SchurDifferential
import SbtCosmo.Derivation.ConvexSumSplit

/-! Qualified original extended stationarity for general Loewner-convex matrix
maps, with local actual differentiability or a finite convex ambient extension. -/
namespace SbtCosmo.Derivation.GeneralMatrixStationarity
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice GeneralMatrixPrice
open ExtendedClosurePrice ConvexSubgradient SchurDifferential
open scoped Matrix Topology Matrix.Norms.Elementwise
variable {m E : Type*} [Fintype m] [DecidableEq m]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq m] in
/-- The actual matrix derivative composes with its trace price, and the fixed
budget contributes zero. No derivative of a Lagrangian is supplied. -/
theorem hasFDerivAt_trace_gap {Xi : E → Symmetric m} {Xi' : E →L[ℝ] Matrix m m ℝ}
    {star : E} (hXi : HasFDerivAt (fun x => (Xi x : Matrix m m ℝ)) Xi' star)
    (P : Matrix m m ℝ) (B : Symmetric m) :
    HasFDerivAt (fun x => trace (P*((Xi x : Matrix m m ℝ)-(B : Matrix m m ℝ))))
      (traceAdjoint Xi' P) star := by
  have hh := (MatrixDifferential.hasFDerivAt_tracePair P hXi).sub_const (trace (P*(B : Matrix m m ℝ)))
  simpa only [Matrix.mul_sub,Matrix.trace_sub] using hh

variable [FiniteDimensional ℝ E]

omit [DecidableEq m] in
/-- Any earned certificate and actual local matrix derivative supply the
qualified split. Matrix convexity away from A is not needed for this return. -/
theorem certificate_stationarity {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {P : Matrix m m ℝ} {star xr : E} {Xi' : E →L[ℝ] Matrix m m ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hc : ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star)
    (hXi : HasFDerivAt (fun x => (Xi x : Matrix m m ℝ)) Xi' star) :
    ∃ q η : E →L[ℝ] ℝ, Subgradient J star q ∧ NormalCone A star η ∧ q+traceAdjoint Xi' P+η=0 := by
  have hcomp : trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := hc.complementarity
  have hmin : ∀ x ∈ A,
      J star+(trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ) ≤
        J x+(trace (P*((Xi x : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ) := by
    simpa only [hcomp,EReal.coe_zero,add_zero] using hc.global_minimum
  exact ExtendedSmoothStationarity.qualified_stationarity hbottom hJ hA hC hAr hc.member hc.finite hmin
    (hasFDerivAt_trace_gap hXi P B)

/-- General smooth matrix/Loewner Theorem S: arbitrary matrix map, ordinary
attainment, PD Slater, genuine matrix derivative at the optimizer and common RI.
All price, support, normal, stationarity and dual outputs are constructed. -/
theorem matrix_stationarity {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ xr : E} {Xi' : E →L[ℝ] Matrix m m ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hXi : LoewnerConvexOn A Xi)
    (hderiv : HasFDerivAt (fun x => (Xi x : Matrix m m ℝ)) Xi' star)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef) :
    ∃ (P : Matrix m m ℝ) (q η : E →L[ℝ] ℝ), P.PosSemidef ∧ Subgradient J star q ∧
      NormalCone A star η ∧ q+traceAdjoint Xi' P+η=0 ∧
      trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊤ ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊥ := by
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  obtain ⟨P,hP,hc,hdual,hfinite⟩ := matrix_price (fun x _ => hbottom x) hrestricted hXi hstar hx₀ hfinite₀ hslater
  obtain ⟨q,η,hq,hη,hstation⟩ := certificate_stationarity hbottom hJ hA hC hAr hc hderiv
  exact ⟨P,q,η,hP,hq,hη,hstation,hc.complementarity,hc,hdual,hfinite⟩

/-- Strict actual value decrease in a PSD budget direction retains nonzero P
in the same general full-stationarity/duality construction. -/
theorem matrix_stationarity_nonzero {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ xr : E} {Xi' : E →L[ℝ] Matrix m m ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hXi : LoewnerConvexOn A Xi)
    (hderiv : HasFDerivAt (fun x => (Xi x : Matrix m m ℝ)) Xi' star)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef)
    (hsensitive : ∃ H : Symmetric m, positive H ∧
      ExtendedConeClosurePrice.value A J Xi positive (B+H) <
        ExtendedConeClosurePrice.value A J Xi positive B) :
    ∃ (P : Matrix m m ℝ) (q η : E →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧ Subgradient J star q ∧
      NormalCone A star η ∧ q+traceAdjoint Xi' P+η=0 ∧
      trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊤ ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊥ := by
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  obtain ⟨P,hP,hne,hc,hdual,hfinite⟩ := matrix_price_nonzero (fun x _ => hbottom x)
    hrestricted hXi hstar hx₀ hfinite₀ hslater hsensitive
  obtain ⟨q,η,hq,hη,hstation⟩ := certificate_stationarity hbottom hJ hA hC hAr hc hderiv
  exact ⟨P,q,η,hP,hne,hq,hη,hstation,hc.complementarity,hc,hdual,hfinite⟩

/-- Literal fderiv form, after actual differentiability is established. -/
theorem matrix_stationarity_fderiv {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hXi : LoewnerConvexOn A Xi)
    (hderiv : DifferentiableAt ℝ (fun x => (Xi x : Matrix m m ℝ)) star)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef) :
    ∃ (P : Matrix m m ℝ) (q η : E →L[ℝ] ℝ), P.PosSemidef ∧ Subgradient J star q ∧
      NormalCone A star η ∧
      q+traceAdjoint (fderiv ℝ (fun x => (Xi x : Matrix m m ℝ)) star) P+η=0 ∧
      trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊤ ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P) ≠ ⊥ :=
  matrix_stationarity hbottom hJ hA hC hAr hXi hderiv.hasFDerivAt hstar hx₀ hfinite₀ hslater

/-- Nonsmooth matrix maps with finite ambient Loewner-convex extension earn an
actual scalar trace-energy support, instead of a fictitious matrix derivative. -/
theorem matrix_nonsmooth_stationarity {A : Set E} {J : E → EReal} {Xi : E → Symmetric m}
    {B : Symmetric m} {star x₀ xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hXi : LoewnerConvexOn univ Xi)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J Xi positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(Xi x₀ : Matrix m m ℝ)).PosDef) :
    ∃ (P : Matrix m m ℝ) (q k η : E →L[ℝ] ℝ), P.PosSemidef ∧ Subgradient J star q ∧
      RealSubgradient (fun x => trace (P*(Xi x : Matrix m m ℝ))) star k ∧
      NormalCone A star η ∧ q+k+η=0 ∧
      trace (P*((Xi star : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      ExtendedConeClosurePrice.DualCertificate A J Xi positive B (tracePrice P) star ∧
      ExtendedConeClosurePrice.dualValue A J Xi B (tracePrice P)=
        ExtendedConeClosurePrice.value A J Xi positive B := by
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  obtain ⟨P,hP,hc,hdual,_⟩ := matrix_price (fun x _ => hbottom x) hrestricted
    (fun x _ y _ => hXi x (mem_univ _) y (mem_univ _)) hstar hx₀ hfinite₀ hslater
  let g : E → ℝ := fun x => trace (P*((Xi x : Matrix m m ℝ)-(B : Matrix m m ℝ)))
  have hcomp : g star=0 := hc.complementarity
  have hmin : ∀ x ∈ A, J star+(g star : ℝ) ≤ J x+(g x : ℝ) := by
    simpa only [g,hcomp,EReal.coe_zero,add_zero] using hc.global_minimum
  have hg : ConvexOn ℝ univ g := by
    simp only [g,Matrix.mul_sub,Matrix.trace_sub]
    simpa only [Pi.add_apply,sub_eq_add_neg] using
      (certificate_trace_energy_convex hXi hc).add_const (-trace (P*(B : Matrix m m ℝ)))
  obtain ⟨k,hk,hgk⟩ := ConvexSumSplit.split_extended (fun x _ => hbottom x)
    hrestricted hg hc.member hc.finite hmin
  have henergySub : RealSubgradient (fun x => trace (P*(Xi x : Matrix m m ℝ))) star k := by
    intro x
    have hh := hgk x
    simp only [g,Matrix.mul_sub,Matrix.trace_sub] at hh
    linarith
  obtain ⟨q,η,hq,hη,heq⟩ := RelativeSumSplit.split_subgradient hbottom hJ hA hC hAr hk
  refine ⟨P,q,k,η,hP,hq,henergySub,hη,?_,hc.complementarity,hc,hdual⟩
  calc
    q+k+η=(q+η)+k := by abel
    _ = 0 := by rw [heq,neg_add_cancel]

end
end SbtCosmo.Derivation.GeneralMatrixStationarity
