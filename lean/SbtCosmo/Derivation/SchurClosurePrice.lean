import SbtCosmo.Derivation.ConvexClosurePrice
import SbtCosmo.Adequacy.Support

/-! The scalar convex price construction instantiated on the actual singular-support Schur energy.
For fixed native probes and PSD audit weight, affine dissolving probes earn energy convexity. -/
namespace SbtCosmo.Derivation.SchurClosurePrice
noncomputable section
open Matrix Set ConvexClosurePrice
open scoped Matrix

variable {n m e : Type*} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq e]

def gramEnergy (W : Matrix m m ℝ) (R : Matrix m e ℝ) : ℝ := trace (W*(R*Rᴴ))

omit [Fintype n] [DecidableEq n] [DecidableEq e] in
theorem gram_energy_nonnegative {W : Matrix m m ℝ} (hW : W.PosSemidef) (R : Matrix m e ℝ) :
    0 ≤ gramEnergy W R := by
  unfold gramEnergy
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simpa only [Matrix.mul_assoc] using (hW.conjTranspose_mul_mul_same R).trace_nonneg

omit [Fintype n] [DecidableEq n] [DecidableEq e] in
theorem gram_energy_mix (W : Matrix m m ℝ) (X Y : Matrix m e ℝ) {a b : ℝ} (hab : a+b=1) :
    gramEnergy W (a • X+b • Y) =
      a*gramEnergy W X+b*gramEnergy W Y-a*b*gramEnergy W (X-Y) := by
  simp only [gramEnergy, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  linear_combination (a*trace (W*(X*Xᴴ))+b*trace (W*(Y*Yᴴ)))*hab

omit [Fintype n] [DecidableEq n] [DecidableEq e] in
theorem gram_energy_convex {W : Matrix m m ℝ} (hW : W.PosSemidef) :
    ConvexOn ℝ univ (gramEnergy (e := e) W) := by
  refine ⟨convex_univ, ?_⟩
  intro X _ Y _ a b ha hb hab
  rw [gram_energy_mix W X Y hab]
  simp only [smul_eq_mul]
  have h := mul_nonneg (mul_nonneg ha hb) (gram_energy_nonnegative hW (X-Y))
  linarith

def schurEnergy (W : Matrix m m ℝ) (L : Matrix n e ℝ) (D : Matrix m e ℝ) : ℝ :=
  trace (W*SbtCosmo.Adequacy.Support.residual L D)

theorem schur_energy_gram (W : Matrix m m ℝ) (L : Matrix n e ℝ) (D : Matrix m e ℝ) :
    schurEnergy W L D = gramEnergy W (D*(1-SbtCosmo.Adequacy.Support.projector L)) := by
  rw [schurEnergy, SbtCosmo.Adequacy.Support.residual_gram]
  rfl

def blindLinear (L : Matrix n e ℝ) : Matrix m e ℝ →ₗ[ℝ] Matrix m e ℝ where
  toFun D := D*(1-SbtCosmo.Adequacy.Support.projector L)
  map_add' X Y := Matrix.add_mul X Y _
  map_smul' a X := Matrix.smul_mul a X _

theorem schur_energy_convex {W : Matrix m m ℝ} (hW : W.PosSemidef) (L : Matrix n e ℝ) :
    ConvexOn ℝ univ (schurEnergy W L) := by
  have h := (gram_energy_convex (e := e) hW).comp_linearMap (blindLinear L)
  simpa only [Set.preimage_univ, Function.comp_def, LinearMap.coe_mk, AddHom.coe_mk,
    blindLinear, ← schur_energy_gram] using h

omit [DecidableEq e] in
/-- Exact return to the original positive-definite Schur-energy convention. -/
theorem positiveDefinite_return [DecidableEq m] (W : Matrix m m ℝ) (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (hK : (L*Lᴴ).PosDef) :
    schurEnergy W L D = ClosurePrice.schurEnergy W (L*Lᴴ) (L*Dᴴ) (D*Dᴴ) := by
  unfold schurEnergy ClosurePrice.schurEnergy
  rw [SbtCosmo.Adequacy.Support.residual_eq_positiveDefinite L D hK]

omit [DecidableEq e] in
/-- The constructed scalar price pairs with exactly the earlier Lagrangian. -/
theorem original_lagrangian_return [DecidableEq m] (W : Matrix m m ℝ) (L : Matrix n e ℝ) (D : Matrix m e ℝ)
    (hK : (L*Lᴴ).PosDef) (J price B : ℝ) :
    J+price*(schurEnergy W L D-B) = ClosurePrice.closureLagrangian J price B W (L*Lᴴ) (L*Dᴴ) (D*Dᴴ) := by
  rw [positiveDefinite_return W L D hK]
  rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem affine_schur_energy_convex {W : Matrix m m ℝ} (hW : W.PosSemidef) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) {A : Set E} (hA : Convex ℝ A) :
    ConvexOn ℝ A (fun x => schurEnergy W L (D x)) := by
  have h := (schur_energy_convex hW L).comp_affineMap D
  rw [Set.preimage_univ] at h
  exact h.subset (subset_univ A) hA

/-- The original support residual, including singular native Gram blocks, earns convexity. -/
theorem positive_schur_price {W : Matrix m m ℝ} (hW : W.PosSemidef) (L : Matrix n e ℝ)
    (D : E →ᵃ[ℝ] Matrix m e ℝ) {A : Set E} {J : E → ℝ} {B d lo hi : ℝ} {star : E}
    (hJ : ConvexOn ℝ A J)
    (hstar : PrimalOptimum A J (fun x => schurEnergy W L (D x)) B star)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi,
      (feasibleCosts A J (fun x => schurEnergy W L (D x)) T).Nonempty ∧
      BddBelow (feasibleCosts A J (fun x => schurEnergy W L (D x)) T))
    (hd : HasDerivAt (budgetValue A J (fun x => schurEnergy W L (D x))) d B) (hs : d < 0) :
    ∃ price : ℝ, price = -d ∧ 0 < price ∧
      DualCertificate A J (fun x => schurEnergy W L (D x)) B price star :=
  positive_price_certificate hJ (affine_schur_energy_convex hW L D hJ.1)
    hstar hB hfinite hd hs

end
end SbtCosmo.Derivation.SchurClosurePrice
