import SbtCosmo.Derivation.ConeClosurePrice
import SbtCosmo.Derivation.MatrixPriceRepresentation
import SbtCosmo.Derivation.SchurClosurePrice
import Mathlib.Analysis.Matrix.Normed

/-! Actual Loewner Schur-budget price, constructed from an actual differentiable value. -/
namespace SbtCosmo.Derivation.MatrixClosurePrice
noncomputable section
open Matrix Set MatrixPriceRepresentation
open scoped Matrix Topology Matrix.Norms.Elementwise

variable {n m e : Type*} [Fintype n] [Fintype m] [Fintype e] [DecidableEq n] [DecidableEq e]

def residual (L : Matrix n e ℝ) (D : Matrix m e ℝ) : Symmetric m :=
  ⟨SbtCosmo.Adequacy.Support.residual L D, by
    have h := (SbtCosmo.Adequacy.Support.residual_psd L D).1
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h⟩

omit [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e] in
def positive (M : Symmetric m) : Prop := (M : Matrix m m ℝ).PosSemidef

omit [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e] in
theorem cone_laws : ConeClosurePrice.ConeLaws (positive (m := m)) := by
  refine ⟨Matrix.PosSemidef.zero,?_,?_⟩
  · intro A B hA hB
    exact Matrix.PosSemidef.add hA hB
  · intro a A ha hA
    exact hA.smul ha

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq e] in
theorem gram_mix_gap (X Y : Matrix m e ℝ) {a b : ℝ} (hab : a+b=1) :
    a • (X*Xᴴ)+b • (Y*Yᴴ)-(a • X+b • Y)*(a • X+b • Y)ᴴ =
      (a*b) • ((X-Y)*(X-Y)ᴴ) := by
  have hbval : b=1-a := by linarith
  subst b
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
  module

theorem residual_mix_gap (L : Matrix n e ℝ) (X Y : Matrix m e ℝ) {a b : ℝ} (hab : a+b=1) :
    a • (residual L X : Matrix m m ℝ)+b • (residual L Y : Matrix m m ℝ)-
      (residual L (a • X+b • Y) : Matrix m m ℝ) =
      (a*b) • (residual L (X-Y) : Matrix m m ℝ) := by
  simp only [residual, SbtCosmo.Adequacy.Support.residual_gram,
    Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul]
  simpa only [Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul] using gram_mix_gap (X*(1-SbtCosmo.Adequacy.Support.projector L))
    (Y*(1-SbtCosmo.Adequacy.Support.projector L)) hab

/-- Loewner convexity of the actual matrix residual, without a supplied convexity field. -/
theorem residual_loewner_convex (L : Matrix n e ℝ) (X Y : Matrix m e ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    positive (a • residual L X+b • residual L Y-residual L (a • X+b • Y)) := by
  change (a • (residual L X : Matrix m m ℝ)+b • (residual L Y : Matrix m m ℝ)-
    (residual L (a • X+b • Y) : Matrix m m ℝ)).PosSemidef
  rw [residual_mix_gap L X Y hab]
  exact (SbtCosmo.Adequacy.Support.residual_psd L (X-Y)).smul (mul_nonneg ha hb)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem affine_residual_loewner_convex (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    (x y : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    positive (a • residual L (D x)+b • residual L (D y)-residual L (D (a • x+b • y))) := by
  rw [Convex.combo_affine_apply (f := D) hab]
  exact residual_loewner_convex L (D x) (D y) ha hb hab

variable [DecidableEq m]

/-- Actual symmetric budgets and their local finite value are explicit. This is the
differentiable-value matrix theorem; general nonsmooth Slater duality is separate. -/
theorem matrix_price (L : Matrix n e ℝ) (D : E →ᵃ[ℝ] Matrix m e ℝ)
    {A : Set E} {J : E → ℝ} {B : Symmetric m} {star : E} {d : Symmetric m →L[ℝ] ℝ}
    (hJ : ConvexOn ℝ A J)
    (hstar : ConeClosurePrice.PrimalOptimum A J (fun x => residual L (D x)) positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B,
      (ConeClosurePrice.feasibleCosts A J (fun x => residual L (D x)) positive T).Nonempty ∧
      BddBelow (ConeClosurePrice.feasibleCosts A J (fun x => residual L (D x)) positive T))
    (hd : HasFDerivAt (ConeClosurePrice.value A J (fun x => residual L (D x)) positive) d B)
    (hs : ∃ H : Symmetric m, positive H ∧ d H < 0) :
    ∃ P : Matrix m m ℝ, P.PosSemidef ∧ P ≠ 0 ∧
      (∀ H : Symmetric m, trace (P*(H : Matrix m m ℝ)) = -d H) ∧
      trace (P*((residual L (D star) : Matrix m m ℝ)-(B : Matrix m m ℝ)))=0 ∧
      (∀ x ∈ A, J star ≤ J x+trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) ∧
      sInf ((fun x => J x+trace (P*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) '' A) =
        ConeClosurePrice.value A J (fun x => residual L (D x)) positive B := by
  have hc := ConeClosurePrice.price_certificate cone_laws hJ
    (fun x _ y _ a b ha hb hab => affine_residual_loewner_convex L D x y ha hb hab) hstar hfinite hd
  let p : Symmetric m →ₗ[ℝ] ℝ := (-d).toLinearMap
  have hrepr (H : Symmetric m) : trace (priceMatrix p*(H : Matrix m m ℝ)) = -d H :=
    trace_representation p H
  have hgap (x : E) : trace (priceMatrix p*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ))) =
      -d (residual L (D x)-B) := hrepr (residual L (D x)-B)
  refine ⟨priceMatrix p, price_matrix_positive p hc.nonnegative, ?_, hrepr, ?_, ?_, ?_⟩
  · obtain ⟨H,_,hH⟩ := hs
    exact price_matrix_nonzero p (by simpa [p] using neg_pos.mpr hH)
  · exact (hrepr (residual L (D star)-B)).trans hc.complementarity
  · intro x hx
    rw [hgap x]
    exact hc.global_minimum x hx
  · have hfun : (fun x => J x+trace (priceMatrix p*((residual L (D x) : Matrix m m ℝ)-(B : Matrix m m ℝ)))) =
        ConeClosurePrice.lagrangian J (fun x => residual L (D x)) B (-d) := by
      funext x
      rw [hgap x]
      rfl
    rw [hfun]
    exact ConeClosurePrice.certificate_strong_duality hc

end
end SbtCosmo.Derivation.MatrixClosurePrice
