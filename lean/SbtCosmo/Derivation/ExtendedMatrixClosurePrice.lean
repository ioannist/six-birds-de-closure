import SbtCosmo.Derivation.ExtendedConeClosurePrice
import SbtCosmo.Derivation.MatrixClosurePrice

/-! Actual symmetric Schur budgets with a genuinely extended-real objective. -/
namespace SbtCosmo.Derivation.ExtendedMatrixClosurePrice
noncomputable section
open Matrix Set MatrixPriceRepresentation MatrixClosurePrice
open ExtendedClosurePrice (epigraph)
open scoped Matrix Topology Matrix.Norms.Elementwise

variable {n m e : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e]
  {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual finite extended infimum derivative constructs the original matrix trace dual.
Objective-domain and Loewner-convexity bridges are proved, not supplied. -/
theorem matrix_price (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → EReal} {B : Symmetric m} {star : E} {d : Symmetric m →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B,
      ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive T).toReal) d B)
    (hs : ∃ H : Symmetric m, positive H ∧ d H < 0) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      (∀ H : Symmetric m, trace (P*(H : Matrix m m ℝ)) = -d H) ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      (∀ x ∈ A, J star ≤ J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) =
        ExtendedConeClosurePrice.value A J (fun x => residual L (D x)) positive B ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) ≠ ⊤ ∧
      sInf ((fun x => J x+(trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) '' A) ≠ ⊥ := by
  have hc := ExtendedConeClosurePrice.price_certificate cone_laws hbottom hJ
    (fun x _ y _ a b ha hb hab => affine_residual_loewner_convex L D x y ha hb hab) hstar hfinite hd
  let p : Symmetric m →ₗ[ℝ] ℝ := (-d).toLinearMap
  have hrepr (H : Symmetric m) : trace (priceMatrix p*(H : Matrix m m ℝ)) = -d H :=
    trace_representation p H
  have hgap (x : E) : trace (priceMatrix p*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) =
      -d (residual L (D x)-B) := hrepr (residual L (D x)-B)
  have hfun : (fun x => J x+(trace (priceMatrix p*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) : ℝ)) =
      ExtendedConeClosurePrice.lagrangian J (fun x => residual L (D x)) B (-d) := by
    funext x
    rw [hgap x]
    rfl
  refine ⟨priceMatrix p,price_matrix_positive p hc.nonnegative,?_,hrepr,?_,?_,?_,?_,?_⟩
  · obtain ⟨H,_,hH⟩ := hs
    exact price_matrix_nonzero p (by simpa [p] using neg_pos.mpr hH)
  · exact (hrepr (residual L (D star)-B)).trans hc.complementarity
  · intro x hx
    rw [hgap x]
    exact hc.global_minimum x hx
  · rw [hfun]
    exact ExtendedConeClosurePrice.certificate_strong_duality hc
  · rw [hfun]
    exact (ExtendedConeClosurePrice.certificate_dual_finite hbottom hc).1
  · rw [hfun]
    exact (ExtendedConeClosurePrice.certificate_dual_finite hbottom hc).2

end
end SbtCosmo.Derivation.ExtendedMatrixClosurePrice
