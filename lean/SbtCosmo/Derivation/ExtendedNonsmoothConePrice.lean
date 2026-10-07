import SbtCosmo.Derivation.NonsmoothConePrice
import SbtCosmo.Derivation.ExtendedConeClosurePrice

/-! Derivative-free dual construction returned to the original extended objective and domain. -/
namespace SbtCosmo.Derivation.ExtendedNonsmoothConePrice
noncomputable section
open Set Filter ExtendedClosurePrice ExtendedConeClosurePrice
open scoped Topology
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Actual extended-value finiteness earns the real-cost guards before separation. -/
theorem price_certificate {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {star : E} (hc : ConeClosurePrice.ConeLaws positive)
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B, value A J energy positive T ≠ ⊤ ∧ value A J energy positive T ≠ ⊥) :
    ∃ price : F →L[ℝ] ℝ, DualCertificate A J energy positive B price star := by
  obtain ⟨price,hprice⟩ := NonsmoothConePrice.price_certificate hc
    (epigraph_objective_convex hbottom hJ)
    (fun x hx y hy a b ha hb hab => he x hx.1 y hy.1 a b ha hb hab)
    (primal_domain_return hbottom hstar) (hfinite.mono fun _ hT => finite_cost_guards hT)
  exact ⟨price, certificate_domain_return hbottom hprice⟩

/-- A finite Slater point supplies every local finite-cost guard. Objective infinity
outside the effective domain is retained in the returned original certificate. -/
theorem slater_price_certificate {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {star x₀ : E} (hc : ConeClosurePrice.ConeLaws positive)
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star) (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : B-energy x₀ ∈ interior {H : F | positive H}) :
    ∃ price : F →L[ℝ] ℝ, DualCertificate A J energy positive B price star := by
  obtain ⟨price,hprice⟩ := NonsmoothConePrice.slater_price_certificate hc
    (epigraph_objective_convex hbottom hJ)
    (fun x hx y hy a b ha hb hab => he x hx.1 y hy.1 a b ha hb hab)
    (primal_domain_return hbottom hstar) ⟨hx₀,hfinite₀⟩ hslater
  exact ⟨price, certificate_domain_return hbottom hprice⟩

omit [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ F] in
/-- Complete-lattice infima make strict actual value decrease sufficient for nonzero
price, even if the competing value is minus infinity. -/
theorem certificate_nonzero {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B T : F} {star : E} {price : F →L[ℝ] ℝ}
    (h : DualCertificate A J energy positive B price star)
    (hdecrease : value A J energy positive T < value A J energy positive B) : price ≠ 0 := by
  intro hz
  rw [optimum_value (certificate_primal_optimum h)] at hdecrease
  obtain ⟨_,⟨x,hx,_,rfl⟩,hxc⟩ := sInf_lt_iff.mp hdecrease
  have hh := h.global_minimum x hx
  rw [hz,ContinuousLinearMap.zero_apply] at hh
  simp only [EReal.coe_zero,add_zero] at hh
  exact hxc.not_ge hh

/-- The actual extended primal/dual equality and finite dual are consequences of Slater
and ordinary primal attainment; they are not optimization premises. -/
theorem slater_strong_duality {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {star x₀ : E} (hc : ConeClosurePrice.ConeLaws positive)
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star) (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : B-energy x₀ ∈ interior {H : F | positive H}) :
    ∃ price : F →L[ℝ] ℝ, DualCertificate A J energy positive B price star ∧
      dualValue A J energy B price=value A J energy positive B ∧
      dualValue A J energy B price ≠ ⊤ ∧ dualValue A J energy B price ≠ ⊥ := by
  obtain ⟨price,hprice⟩ := slater_price_certificate hc hbottom hJ he hstar hx₀ hfinite₀ hslater
  exact ⟨price,hprice,certificate_strong_duality hprice,certificate_dual_finite hbottom hprice⟩

end
end SbtCosmo.Derivation.ExtendedNonsmoothConePrice
