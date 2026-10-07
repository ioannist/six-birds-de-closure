import SbtCosmo.Derivation.ExtendedClosurePrice
import SbtCosmo.Derivation.SchurClosurePrice

/-! The extended-real price returned to the actual singular-support Schur program. -/
namespace SbtCosmo.Derivation.ExtendedSchurClosurePrice
noncomputable section
open Set ExtendedClosurePrice

variable {n m e : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq e]
  {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Energy convexity is earned from fixed native probes, PSD W and affine D.
There is no supplied scalar dual, activity or assumed objective-domain reduction. -/
theorem positive_schur_price {W : Matrix m m ℝ} (hW : W.PosSemidef) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) {A : Set E} {J : E → EReal} {B d lo hi : ℝ} {star : E}
    (hA : Convex ℝ A) (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hstar : PrimalOptimum A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) B star)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi,
      value A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) T ≠ ⊤ ∧
      value A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) T).toReal) d B)
    (hs : d < 0) :
    ∃ price : ℝ, price = -d ∧ 0 < price ∧ SchurClosurePrice.schurEnergy W L (D star) = B ∧
      DualCertificate A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) B price star ∧
      dualValue A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) B price =
        value A J (fun x => SchurClosurePrice.schurEnergy W L (D x)) B :=
  positive_price_certificate hbottom hJ (SchurClosurePrice.affine_schur_energy_convex hW L D hA)
    hstar hB hfinite hd hs

end
end SbtCosmo.Derivation.ExtendedSchurClosurePrice
