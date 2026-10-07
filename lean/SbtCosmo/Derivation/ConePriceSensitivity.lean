import SbtCosmo.Derivation.ExtendedNonsmoothConePrice
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Every earned conic certificate is identified by the actual budget value
derivative. Original extended values and all finite-domain conversions are kept. -/
namespace SbtCosmo.Derivation.ConePriceSensitivity
noncomputable section
open Set Filter ExtendedClosurePrice
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- No convexity or finite-dimensionality is needed once the certificate and
actual value derivative exist. The support bound earns a local minimum. -/
theorem real_price_identification {A : Set E} {J : E → ℝ} {energy : E → F}
    {positive : F → Prop} {B : F} {star : E} {price d : F →L[ℝ] ℝ}
    (hc : ConeClosurePrice.DualCertificate A J energy positive B price star)
    (hne : ∀ᶠ T in 𝓝 B, (ConeClosurePrice.feasibleCosts A J energy positive T).Nonempty)
    (hd : HasFDerivAt (ConeClosurePrice.value A J energy positive) d B) : price = -d := by
  have hm : IsLocalMin (fun T => ConeClosurePrice.value A J energy positive T+price T) B := by
    filter_upwards [hne] with T hT
    have hh := NonsmoothConePrice.certificate_value_support hc hT
    rw [map_sub] at hh
    linarith
  have hz : d+price=0 := hm.hasFDerivAt_eq_zero (hd.add price.hasFDerivAt)
  calc
    price=(d+price)-d := by abel
    _ = -d := by rw [hz,zero_sub]

/-- Reverse certificate return, with every original objective conversion guarded. -/
theorem certificate_real_domain_return {A : Set E} {J : E → EReal} {energy : E → F}
    {positive : F → Prop} {B : F} {star : E} {price : F →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : ExtendedConeClosurePrice.DualCertificate A J energy positive B price star) :
    ConeClosurePrice.DualCertificate (finiteDomain A J) (realObjective J) energy positive B price star := by
  refine ⟨hc.nonnegative,⟨hc.member,hc.finite⟩,hc.feasible,hc.complementarity,?_⟩
  intro x hx
  have hh := hc.global_minimum x hx.1
  rw [← EReal.coe_toReal hc.finite (hbottom star hc.member),
    ← EReal.coe_toReal hx.2 (hbottom x hx.1),← EReal.coe_add] at hh
  exact EReal.coe_le_coe_iff.mp hh

/-- The derivative is of the actual locally finite EReal infimum, not of an
unrestricted toReal objective or a fallback infinite value. -/
theorem price_identification {A : Set E} {J : E → EReal} {energy : E → F}
    {positive : F → Prop} {B : F} {star : E} {price d : F →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : ExtendedConeClosurePrice.DualCertificate A J energy positive B price star)
    (hfinite : ∀ᶠ T in 𝓝 B, ExtendedConeClosurePrice.value A J energy positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J energy positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J energy positive T).toReal) d B) :
    price = -d := by
  have heq : (fun T => (ExtendedConeClosurePrice.value A J energy positive T).toReal) =ᶠ[𝓝 B]
      ConeClosurePrice.value (finiteDomain A J) (realObjective J) energy positive := by
    filter_upwards [hfinite] with T hT
    exact ExtendedConeClosurePrice.finite_value_domain_return hbottom hT
  exact real_price_identification (certificate_real_domain_return hbottom hc)
    (hfinite.mono fun _ hT => (ExtendedConeClosurePrice.finite_cost_guards hT).1)
    (hd.congr_of_eventuallyEq heq.symm)

/-- Uniqueness of the whole budget functional across certificates at possibly
different optimizers; no optimizer or stationarity-support uniqueness follows. -/
theorem price_unique {A : Set E} {J : E → EReal} {energy : E → F}
    {positive : F → Prop} {B : F} {star other : E} {price otherPrice d : F →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hc : ExtendedConeClosurePrice.DualCertificate A J energy positive B price star)
    (ho : ExtendedConeClosurePrice.DualCertificate A J energy positive B otherPrice other)
    (hfinite : ∀ᶠ T in 𝓝 B, ExtendedConeClosurePrice.value A J energy positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J energy positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J energy positive T).toReal) d B) :
    price=otherPrice := by
  rw [price_identification hbottom hc hfinite hd,price_identification hbottom ho hfinite hd]

variable [AddCommGroup E] [Module ℝ E]

/-- Slater earns actual original extended-value finiteness before toReal
sensitivity is used; the real-cost guards return through exact infima. -/
theorem slater_local_finiteness {A : Set E} {J : E → EReal} {energy : E → F}
    {positive : F → Prop} {B : F} {star x₀ : E}
    (hc : ConeClosurePrice.ConeLaws positive)
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : ExtendedConeClosurePrice.PrimalOptimum A J energy positive B star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : B-energy x₀ ∈ interior {H : F | positive H}) :
    ∀ᶠ T in 𝓝 B, ExtendedConeClosurePrice.value A J energy positive T ≠ ⊤ ∧
      ExtendedConeClosurePrice.value A J energy positive T ≠ ⊥ := by
  have hguards := NonsmoothConePrice.slater_local_finiteness hc
    (epigraph_objective_convex hbottom hJ)
    (fun x hx y hy a b ha hb hab => he x hx.1 y hy.1 a b ha hb hab)
    (ExtendedConeClosurePrice.primal_domain_return hbottom hstar) ⟨hx₀,hfinite₀⟩ hslater
  filter_upwards [hguards] with T hT
  rw [ExtendedConeClosurePrice.value_domain_return hbottom hT.1 hT.2]
  exact ⟨EReal.coe_ne_top _,EReal.coe_ne_bot _⟩

/-- Identifies an already earned price using local finiteness constructed from
Slater, rather than assuming guards independently. -/
theorem slater_price_identification {A : Set E} {J : E → EReal} {energy : E → F}
    {positive : F → Prop} {B : F} {star x₀ : E} {price d : F →L[ℝ] ℝ}
    (hc : ConeClosurePrice.ConeLaws positive)
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hprice : ExtendedConeClosurePrice.DualCertificate A J energy positive B price star)
    (hx₀ : x₀ ∈ A) (hfinite₀ : J x₀ ≠ ⊤)
    (hslater : B-energy x₀ ∈ interior {H : F | positive H})
    (hd : HasFDerivAt (fun T => (ExtendedConeClosurePrice.value A J energy positive T).toReal) d B) :
    price = -d :=
  price_identification hbottom hprice
    (slater_local_finiteness hc hbottom hJ he (ExtendedConeClosurePrice.certificate_primal_optimum hprice)
      hx₀ hfinite₀ hslater) hd

end
end SbtCosmo.Derivation.ConePriceSensitivity
