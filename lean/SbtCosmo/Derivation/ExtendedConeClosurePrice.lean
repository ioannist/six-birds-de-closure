import SbtCosmo.Derivation.ConeClosurePrice
import SbtCosmo.Derivation.ExtendedClosurePrice

/-! Exact extended-objective reduction for conic budgets, with complete-lattice dual infima. -/
namespace SbtCosmo.Derivation.ExtendedConeClosurePrice
noncomputable section
open Set Filter
open ExtendedClosurePrice (finiteDomain realObjective epigraph)
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def costs (A : Set E) (J : E → EReal) (energy : E → F) (positive : F → Prop) (B : F) : Set EReal :=
  {r | ∃ x ∈ A, positive (B-energy x) ∧ J x=r}
def value (A : Set E) (J : E → EReal) (energy : E → F) (positive : F → Prop) (B : F) : EReal :=
  sInf (costs A J energy positive B)

structure PrimalOptimum (A : Set E) (J : E → EReal) (energy : E → F)
    (positive : F → Prop) (B : F) (star : E) : Prop where
  member : star ∈ A
  finite : J star ≠ ⊤
  feasible : positive (B-energy star)
  optimal : ∀ x ∈ A, positive (B-energy x) → J star ≤ J x

structure DualCertificate (A : Set E) (J : E → EReal) (energy : E → F)
    (positive : F → Prop) (B : F) (price : F →L[ℝ] ℝ) (star : E) : Prop where
  nonnegative : ∀ H, positive H → 0 ≤ price H
  member : star ∈ A
  finite : J star ≠ ⊤
  feasible : positive (B-energy star)
  complementarity : price (energy star-B)=0
  global_minimum : ∀ x ∈ A, J star ≤ J x+(price (energy x-B) : ℝ)

def lagrangian (J : E → EReal) (energy : E → F) (B : F) (price : F →L[ℝ] ℝ) (x : E) : EReal :=
  J x+(price (energy x-B) : ℝ)
def dualValue (A : Set E) (J : E → EReal) (energy : E → F) (B : F) (price : F →L[ℝ] ℝ) : EReal :=
  sInf ((lagrangian J energy B price) '' A)

omit [NormedSpace ℝ F] in
theorem finite_cost_guards {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop} {B : F}
    (hfinite : value A J energy positive B ≠ ⊤ ∧ value A J energy positive B ≠ ⊥) :
    (ConeClosurePrice.feasibleCosts (finiteDomain A J) (realObjective J) energy positive B).Nonempty ∧
    BddBelow (ConeClosurePrice.feasibleCosts (finiteDomain A J) (realObjective J) energy positive B) := by
  constructor
  · by_contra hn
    apply hfinite.1
    apply sInf_eq_top.mpr
    rintro r ⟨x, hx, he, rfl⟩
    by_contra ht
    exact hn ⟨realObjective J x, x, ⟨hx, ht⟩, he, rfl⟩
  · refine ⟨(value A J energy positive B).toReal, ?_⟩
    rintro r ⟨x, hx, he, rfl⟩
    exact EReal.toReal_le_toReal (sInf_le ⟨x, hx.1, he, rfl⟩) hfinite.2 hx.2

omit [NormedSpace ℝ F] in
theorem value_domain_return {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop} {B : F}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hne : (ConeClosurePrice.feasibleCosts (finiteDomain A J) (realObjective J) energy positive B).Nonempty)
    (hbb : BddBelow (ConeClosurePrice.feasibleCosts (finiteDomain A J) (realObjective J) energy positive B)) :
    value A J energy positive B = (ConeClosurePrice.value (finiteDomain A J) (realObjective J) energy positive B : EReal) := by
  apply le_antisymm
  · obtain ⟨r, x, hx, he, hr⟩ := hne
    have hv : value A J energy positive B ≤ J x := sInf_le ⟨x, hx.1, he, rfl⟩
    have htop : value A J energy positive B ≠ ⊤ := ne_top_of_le_ne_top hx.2 hv
    by_cases hbot : value A J energy positive B = ⊥
    · simp [hbot]
    · rw [← EReal.coe_toReal htop hbot]
      apply EReal.coe_le_coe_iff.mpr
      apply le_csInf (show (ConeClosurePrice.feasibleCosts (finiteDomain A J) (realObjective J) energy positive B).Nonempty
        from ⟨realObjective J x, x, hx, he, rfl⟩)
      rintro s ⟨y, hy, hey, rfl⟩
      exact EReal.toReal_le_toReal (sInf_le ⟨y, hy.1, hey, rfl⟩) hbot hy.2
  · apply le_sInf
    rintro r ⟨x, hx, he, rfl⟩
    by_cases ht : J x = ⊤
    · simp [ht]
    · rw [← EReal.coe_toReal ht (hbottom x hx)]
      exact EReal.coe_le_coe_iff.mpr (ConeClosurePrice.value_le_candidate hbb ⟨hx, ht⟩ he)

omit [NormedSpace ℝ F] in
theorem finite_value_domain_return {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop} {B : F}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hfinite : value A J energy positive B ≠ ⊤ ∧ value A J energy positive B ≠ ⊥) :
    (value A J energy positive B).toReal = ConeClosurePrice.value (finiteDomain A J) (realObjective J) energy positive B := by
  rw [value_domain_return hbottom (finite_cost_guards hfinite).1
    (finite_cost_guards hfinite).2]
  simp

omit [NormedSpace ℝ F] in
theorem primal_domain_return {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop} {B : F} {star : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (h : PrimalOptimum A J energy positive B star) :
    ConeClosurePrice.PrimalOptimum (finiteDomain A J) (realObjective J) energy positive B star := by
  refine ⟨⟨h.member, h.finite⟩, h.feasible, ?_⟩
  intro x hx he
  exact EReal.toReal_le_toReal (h.optimal x hx.1 he) (hbottom star h.member) hx.2

omit [NormedSpace ℝ F] in
theorem optimum_value {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop} {B : F} {star : E}
    (h : PrimalOptimum A J energy positive B star) : value A J energy positive B = J star := by
  apply le_antisymm (sInf_le (show J star ∈ costs A J energy positive B from ⟨star, h.member, h.feasible, rfl⟩))
  apply le_sInf
  rintro r ⟨x, hx, he, rfl⟩
  exact h.optimal x hx he

theorem certificate_domain_return {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {p : F →L[ℝ] ℝ} {star : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (h : ConeClosurePrice.DualCertificate (finiteDomain A J) (realObjective J) energy positive B p star) :
    DualCertificate A J energy positive B p star := by
  refine ⟨h.nonnegative, h.member.1, h.member.2, h.feasible, h.complementarity, ?_⟩
  intro x hx
  by_cases ht : J x = ⊤
  · rw [ht, EReal.top_add_coe]
    exact le_top
  · rw [← EReal.coe_toReal h.member.2 (hbottom star h.member.1),
      ← EReal.coe_toReal ht (hbottom x hx), ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (h.global_minimum x ⟨hx, ht⟩)

theorem certificate_primal_optimum {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {p : F →L[ℝ] ℝ} {star : E} (h : DualCertificate A J energy positive B p star) :
    PrimalOptimum A J energy positive B star := by
  refine ⟨h.member, h.finite, h.feasible, ?_⟩
  intro x hx he
  have hp : (p (energy x-B) : EReal) ≤ 0 := by
    have hh := h.nonnegative (B-energy x) he
    have hn : p (B-energy x) = -p (energy x-B) := by rw [← neg_sub, map_neg]
    rw [hn] at hh
    exact_mod_cast (by linarith : p (energy x-B) ≤ 0)
  exact (h.global_minimum x hx).trans (by simpa only [add_zero] using add_le_add_right hp (J x))

theorem certificate_strong_duality {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {p : F →L[ℝ] ℝ} {star : E} (h : DualCertificate A J energy positive B p star) :
    dualValue A J energy B p = value A J energy positive B := by
  rw [optimum_value (certificate_primal_optimum h)]
  apply le_antisymm
  · apply (sInf_le (show lagrangian J energy B p star ∈ (lagrangian J energy B p) '' A
      from ⟨star, h.member, rfl⟩)).trans
    simp [lagrangian, h.complementarity]
  · apply le_sInf
    rintro r ⟨x, hx, rfl⟩
    exact h.global_minimum x hx

/-- Complete-lattice dual infima allow a competing value of minus infinity safely. -/
theorem weak_duality {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {q : F →L[ℝ] ℝ} {star : E} (h : PrimalOptimum A J energy positive B star) (hq : ∀ H, positive H → 0 ≤ q H) :
    dualValue A J energy B q ≤ value A J energy positive B := by
  rw [optimum_value h]
  have hp : (q (energy star-B) : EReal) ≤ 0 := by
    have hh := hq (B-energy star) h.feasible
    have hn : q (B-energy star) = -q (energy star-B) := by rw [← neg_sub, map_neg]
    rw [hn] at hh
    exact_mod_cast (by linarith : q (energy star-B) ≤ 0)
  apply (sInf_le (show lagrangian J energy B q star ∈ (lagrangian J energy B q) '' A
    from ⟨star, h.member, rfl⟩)).trans
  simpa only [lagrangian, add_zero] using add_le_add_right hp (J star)

theorem certificate_dual_finite {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {p : F →L[ℝ] ℝ} {star : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (h : DualCertificate A J energy positive B p star) :
    dualValue A J energy B p ≠ ⊤ ∧ dualValue A J energy B p ≠ ⊥ := by
  rw [certificate_strong_duality h, optimum_value (certificate_primal_optimum h)]
  exact ⟨h.finite, hbottom star h.member⟩

section Convex
variable [AddCommGroup E] [Module ℝ E]

/-- All finite-domain and derivative bridges are earned from the actual finite conic value. -/
theorem price_certificate {A : Set E} {J : E → EReal} {energy : E → F} {positive : F → Prop}
    {B : F} {star : E} {d : F →L[ℝ] ℝ} (hc : ConeClosurePrice.ConeLaws positive)
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ∀ x ∈ A, ∀ y ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
      positive (a • energy x+b • energy y-energy (a • x+b • y)))
    (hstar : PrimalOptimum A J energy positive B star)
    (hfinite : ∀ᶠ T in 𝓝 B, value A J energy positive T ≠ ⊤ ∧ value A J energy positive T ≠ ⊥)
    (hd : HasFDerivAt (fun T => (value A J energy positive T).toReal) d B) :
    DualCertificate A J energy positive B (-d) star := by
  have hnear : (fun T => (value A J energy positive T).toReal) =ᶠ[𝓝 B]
      ConeClosurePrice.value (finiteDomain A J) (realObjective J) energy positive := by
    filter_upwards [hfinite] with T hT
    exact finite_value_domain_return hbottom hT
  have hdr := hd.congr_of_eventuallyEq hnear.symm
  have hreal := primal_domain_return hbottom hstar
  have hdual := ConeClosurePrice.price_certificate hc
    (ExtendedClosurePrice.epigraph_objective_convex hbottom hJ)
    (fun x hx y hy a b ha hb hab => he x hx.1 y hy.1 a b ha hb hab)
    hreal (hfinite.mono fun _ hT => finite_cost_guards hT) hdr
  exact certificate_domain_return hbottom hdual

end Convex
end
end SbtCosmo.Derivation.ExtendedConeClosurePrice
