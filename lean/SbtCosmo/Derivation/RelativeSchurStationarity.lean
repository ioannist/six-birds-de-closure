import SbtCosmo.Derivation.RelativeSumSplit
import SbtCosmo.Derivation.SchurStationarity

/-! Original extended Schur stationarity with an earned ambient objective/normal
split under the actual relative-interior qualification. -/
namespace SbtCosmo.Derivation.RelativeSchurStationarity
noncomputable section
open Set Matrix MatrixPriceRepresentation MatrixClosurePrice ConvexSubgradient ExtendedClosurePrice
open scoped Matrix Matrix.Norms.Elementwise
variable {n m e E : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [Fintype n] [Fintype m] [Fintype e] [DecidableEq n] [DecidableEq m] [DecidableEq e]
  [FiniteDimensional ℝ E] in
theorem restricted_epigraph_convex {A : Set E} {J : E → EReal}
    (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A) : Convex ℝ (epigraph A J) := by
  intro x hx y hy a b ha hb hab
  have hh := hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab
  exact ⟨hA hx.1 hy.1 ha hb hab,hh.2⟩

/-- Slater earns the matrix price and actual Schur derivative; relative interiors
earn the extended objective/normal split. None of these outputs is a premise. -/
theorem matrix_stationarity (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J))
    (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef) :
    ∃ (P : Matrix m m ℝ) (q n : E →L[ℝ] ℝ), P.PosSemidef ∧
      Subgradient J star q ∧ NormalCone A star n ∧
      q+fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star+n=0 ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := by
  obtain ⟨P,hP,hsub,hcomp⟩ := SchurStationarity.matrix_restricted_stationarity L D
    (fun x _ => hbottom x) (restricted_epigraph_convex hJ hA) hstar hx₀ hfinite₀ hslater
  obtain ⟨q,n,hq,hn,heq⟩ := RelativeSumSplit.split_subgradient hbottom hJ hA hC hAr hsub
  refine ⟨P,q,n,hP,hq,hn,?_,hcomp⟩
  calc
    q+fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star+n
      = (q+n)+fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star := by abel
    _ = 0 := by rw [heq,neg_add_cancel]

/-- Actual strict decrease of the complete-lattice value earns a nonzero matrix
price in the fully split, genuinely extended stationarity theorem. -/
theorem matrix_stationarity_nonzero (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ xr : E}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J))
    (hAr : xr ∈ intrinsicInterior ℝ A)
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef)
    (hs : ∃ H : Symmetric m, positive H ∧
      ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive (B+H) <
        ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive B) :
    ∃ (P : Matrix m m ℝ) (q n : E →L[ℝ] ℝ), P.PosSemidef ∧ P ≠ 0 ∧
      Subgradient J star q ∧ NormalCone A star n ∧
      q+fderiv ℝ (fun x => trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) star+n=0 ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 := by
  obtain ⟨P,q,n,hP,hq,hn,hstation,hcomp⟩ := matrix_stationarity L D hbottom hJ hA hC hAr hstar hx₀ hfinite₀ hslater
  refine ⟨P,q,n,hP,?_,hq,hn,hstation,hcomp⟩
  intro hz
  have hzero : q+n=0 := by simpa only [hz,zero_mul,trace_zero,fderiv_const_apply,add_zero] using hstation
  have hrestricted := RelativeSumSplit.join_subgradient hq hn hzero
  obtain ⟨H,_,hdec⟩ := hs
  rw [ExtendedConeClosurePrice.optimum_value hstar] at hdec
  obtain ⟨_,⟨x,hx,_,rfl⟩,hcost⟩ := sInf_lt_iff.mp hdec
  have hh := hrestricted.2.2.2 x hx
  simp only [ContinuousLinearMap.zero_apply,EReal.coe_zero,add_zero] at hh
  exact hcost.not_ge hh

end
end SbtCosmo.Derivation.RelativeSchurStationarity
