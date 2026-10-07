import SbtCosmo.Derivation.ExtendedNonsmoothConePrice
import SbtCosmo.Derivation.MatrixSlaterTopology

/-! Nonsmooth Slater duality for the actual Schur matrix budget and extended objective. -/
namespace SbtCosmo.Derivation.NonsmoothMatrixPrice
noncomputable section
open Set Filter Matrix MatrixPriceRepresentation MatrixClosurePrice
open scoped Matrix Topology Matrix.Norms.Elementwise
variable {n m e E : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e] [AddCommGroup E] [Module ℝ E]

/-- Ordinary attainment and a finite positive-definite Slater slack suffice. Neither
value differentiability nor local finiteness nor a dual certificate is supplied. -/
theorem matrix_price (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (ExtendedClosurePrice.epigraph A J))
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      (∀ x ∈ A, J star ≤ J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) =
        ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive B ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) ≠ ⊤ ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) ≠ ⊥ := by
  have hs : B-residual L (D x₀) ∈ interior {H : Symmetric m | positive H} :=
    MatrixSlaterTopology.posdef_mem_interior_positive hslater
  obtain ⟨price,hp,hdual,hfinite⟩ := ExtendedNonsmoothConePrice.slater_strong_duality cone_laws hbottom hJ
    (fun x _ y _ a b ha hb hab => affine_residual_loewner_convex L D x y ha hb hab)
    hstar hx₀ hfinite₀ hs
  let p : Symmetric m →ₗ[ℝ] ℝ := price.toLinearMap
  have hrepr (H : Symmetric m) : trace (priceMatrix p*(H : Matrix m m ℝ))=price H :=
    trace_representation p H
  have hgap (x : E) : trace (priceMatrix p*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) =
      price (residual L (D x)-B) := hrepr (residual L (D x)-B)
  have hfun : (fun x => J x+(trace (priceMatrix p*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) =
      ExtendedConeClosurePrice.lagrangian J (fun x => residual L (D x)) B price := by
    funext x
    rw [hgap x]
    rfl
  refine ⟨priceMatrix p,price_matrix_positive p hp.nonnegative,?_,?_,?_,?_,?_⟩
  · exact (hgap star).trans hp.complementarity
  · intro x hx
    rw [hgap x]
    exact hp.global_minimum x hx
  · rw [hfun]
    exact hdual
  · rw [hfun]
    exact hfinite.1
  · rw [hfun]
    exact hfinite.2

/-- A strict actual decrease in a PSD budget direction earns a nonzero PSD matrix price.
A decrease is tested on the original complete-lattice value, not a supplied derivative. -/
theorem matrix_price_nonzero (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star x₀ : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (ExtendedClosurePrice.epigraph A J))
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : ((B : Matrix m m ℝ)-(residual L (D x₀) : Matrix m m ℝ)).PosDef)
    (hs : ∃ H : Symmetric m, positive H ∧
      ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive (B+H) <
        ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive B) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      (∀ x ∈ A, J star ≤ J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) =
        ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive B := by
  obtain ⟨P,hP,hcomp,hglob,hdual,_⟩ := matrix_price L D hbottom hJ hstar hx₀ hfinite₀ hslater
  refine ⟨P,hP,?_,hcomp,hglob,hdual⟩
  intro hz
  obtain ⟨H,_,hdec⟩ := hs
  have hopt := ExtendedConeClosurePrice.optimum_value hstar
  rw [hopt] at hdec
  obtain ⟨_,⟨x,hx,_,rfl⟩,hcost⟩ := sInf_lt_iff.mp hdec
  have hh := hglob x hx
  rw [hz,zero_mul,trace_zero] at hh
  simp only [EReal.coe_zero,add_zero] at hh
  exact hcost.not_ge hh

end
end SbtCosmo.Derivation.NonsmoothMatrixPrice
