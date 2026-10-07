import SbtCosmo.Derivation.ConvexClosurePrice
import Mathlib.Data.EReal.Operations

/-! Exact objective-domain reduction for extended-real scalar closure prices.
Convexity is expressed by the ordinary real epigraph. No conversion of infinity
to a finite objective is permitted outside the proved finite domain. -/
namespace SbtCosmo.Derivation.ExtendedClosurePrice
noncomputable section
open Set Filter ConvexClosurePrice
open scoped Topology

variable {E : Type*}

def finiteDomain (A : Set E) (J : E → EReal) : Set E := {x | x ∈ A ∧ J x ≠ ⊤}
def realObjective (J : E → EReal) (x : E) : ℝ := (J x).toReal
def epigraph (A : Set E) (J : E → EReal) : Set (E × ℝ) :=
  {p | p.1 ∈ A ∧ J p.1 ≤ (p.2 : EReal)}
def costs (A : Set E) (J : E → EReal) (energy : E → ℝ) (B : ℝ) : Set EReal :=
  {r | ∃ x ∈ A, energy x ≤ B ∧ J x = r}
def value (A : Set E) (J : E → EReal) (energy : E → ℝ) (B : ℝ) : EReal :=
  sInf (costs A J energy B)

structure PrimalOptimum (A : Set E) (J : E → EReal) (energy : E → ℝ) (B : ℝ) (star : E) : Prop where
  member : star ∈ A
  finite : J star ≠ ⊤
  feasible : energy star ≤ B
  optimal : ∀ x ∈ A, energy x ≤ B → J star ≤ J x

structure DualCertificate (A : Set E) (J : E → EReal) (energy : E → ℝ)
    (B price : ℝ) (star : E) : Prop where
  nonnegative : 0 ≤ price
  member : star ∈ A
  finite : J star ≠ ⊤
  feasible : energy star ≤ B
  complementarity : price*(energy star-B) = 0
  global_minimum : ∀ x ∈ A, J star ≤ J x + (price*(energy x-B) : ℝ)

def lagrangian (J : E → EReal) (energy : E → ℝ) (B price : ℝ) (x : E) : EReal :=
  J x + (price*(energy x-B) : ℝ)
def dualValue (A : Set E) (J : E → EReal) (energy : E → ℝ) (B price : ℝ) : EReal :=
  sInf ((lagrangian J energy B price) '' A)

theorem finite_cost_guards {A : Set E} {J : E → EReal} {energy : E → ℝ} {B : ℝ}
    (hfinite : value A J energy B ≠ ⊤ ∧ value A J energy B ≠ ⊥) :
    (feasibleCosts (finiteDomain A J) (realObjective J) energy B).Nonempty ∧
    BddBelow (feasibleCosts (finiteDomain A J) (realObjective J) energy B) := by
  constructor
  · by_contra hn
    apply hfinite.1
    apply sInf_eq_top.mpr
    rintro r ⟨x, hx, he, rfl⟩
    by_contra ht
    exact hn ⟨realObjective J x, x, ⟨hx, ht⟩, he, rfl⟩
  · refine ⟨(value A J energy B).toReal, ?_⟩
    rintro r ⟨x, hx, he, rfl⟩
    exact EReal.toReal_le_toReal (sInf_le ⟨x, hx.1, he, rfl⟩) hfinite.2 hx.2

theorem value_domain_return {A : Set E} {J : E → EReal} {energy : E → ℝ} {B : ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (hne : (feasibleCosts (finiteDomain A J) (realObjective J) energy B).Nonempty)
    (hbb : BddBelow (feasibleCosts (finiteDomain A J) (realObjective J) energy B)) :
    value A J energy B = (budgetValue (finiteDomain A J) (realObjective J) energy B : EReal) := by
  apply le_antisymm
  · obtain ⟨r, x, hx, he, hr⟩ := hne
    have hv : value A J energy B ≤ J x := sInf_le ⟨x, hx.1, he, rfl⟩
    have htop : value A J energy B ≠ ⊤ := ne_top_of_le_ne_top hx.2 hv
    by_cases hbot : value A J energy B = ⊥
    · simp [hbot]
    · rw [← EReal.coe_toReal htop hbot]
      apply EReal.coe_le_coe_iff.mpr
      apply le_csInf (show (feasibleCosts (finiteDomain A J) (realObjective J) energy B).Nonempty
        from ⟨realObjective J x, x, hx, he, rfl⟩)
      rintro s ⟨y, hy, hey, rfl⟩
      exact EReal.toReal_le_toReal (sInf_le ⟨y, hy.1, hey, rfl⟩) hbot hy.2
  · apply le_sInf
    rintro r ⟨x, hx, he, rfl⟩
    by_cases ht : J x = ⊤
    · simp [ht]
    · rw [← EReal.coe_toReal ht (hbottom x hx)]
      exact EReal.coe_le_coe_iff.mpr (value_le_candidate hbb ⟨hx, ht⟩ he)

theorem finite_value_domain_return {A : Set E} {J : E → EReal} {energy : E → ℝ} {B : ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hfinite : value A J energy B ≠ ⊤ ∧ value A J energy B ≠ ⊥) :
    (value A J energy B).toReal = budgetValue (finiteDomain A J) (realObjective J) energy B := by
  rw [value_domain_return hbottom (finite_cost_guards hfinite).1
    (finite_cost_guards hfinite).2]
  simp

theorem primal_domain_return {A : Set E} {J : E → EReal} {energy : E → ℝ} {B : ℝ} {star : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (h : PrimalOptimum A J energy B star) :
    ConvexClosurePrice.PrimalOptimum (finiteDomain A J) (realObjective J) energy B star := by
  refine ⟨⟨h.member, h.finite⟩, h.feasible, ?_⟩
  intro x hx he
  exact EReal.toReal_le_toReal (h.optimal x hx.1 he) (hbottom star h.member) hx.2

theorem optimum_value {A : Set E} {J : E → EReal} {energy : E → ℝ} {B : ℝ} {star : E}
    (h : PrimalOptimum A J energy B star) : value A J energy B = J star := by
  apply le_antisymm (sInf_le (show J star ∈ costs A J energy B from ⟨star, h.member, h.feasible, rfl⟩))
  apply le_sInf
  rintro r ⟨x, hx, he, rfl⟩
  exact h.optimal x hx he

theorem certificate_domain_return {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p : ℝ} {star : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (h : ConvexClosurePrice.DualCertificate (finiteDomain A J) (realObjective J) energy B p star) :
    DualCertificate A J energy B p star := by
  refine ⟨h.nonnegative, h.member.1, h.member.2, h.feasible, h.complementarity, ?_⟩
  intro x hx
  by_cases ht : J x = ⊤
  · rw [ht, EReal.top_add_coe]
    exact le_top
  · rw [← EReal.coe_toReal h.member.2 (hbottom star h.member.1),
      ← EReal.coe_toReal ht (hbottom x hx), ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (h.global_minimum x ⟨hx, ht⟩)

theorem certificate_primal_optimum {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p : ℝ} {star : E} (h : DualCertificate A J energy B p star) :
    PrimalOptimum A J energy B star := by
  refine ⟨h.member, h.finite, h.feasible, ?_⟩
  intro x hx he
  have hp : (p*(energy x-B) : EReal) ≤ 0 := by
    exact_mod_cast mul_nonpos_of_nonneg_of_nonpos h.nonnegative (sub_nonpos.mpr he)
  exact (h.global_minimum x hx).trans (by simpa only [add_zero] using add_le_add_right hp (J x))

theorem certificate_strong_duality {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p : ℝ} {star : E} (h : DualCertificate A J energy B p star) :
    dualValue A J energy B p = value A J energy B := by
  rw [optimum_value (certificate_primal_optimum h)]
  apply le_antisymm
  · apply (sInf_le (show lagrangian J energy B p star ∈ (lagrangian J energy B p) '' A
      from ⟨star, h.member, rfl⟩)).trans
    simp [lagrangian, h.complementarity]
  · apply le_sInf
    rintro r ⟨x, hx, rfl⟩
    exact h.global_minimum x hx

/-- Complete-lattice dual infima allow a competing value of minus infinity safely. -/
theorem weak_duality {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B q : ℝ} {star : E} (h : PrimalOptimum A J energy B star) (hq : 0 ≤ q) :
    dualValue A J energy B q ≤ value A J energy B := by
  rw [optimum_value h]
  have hp : (q*(energy star-B) : EReal) ≤ 0 := by
    exact_mod_cast mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr h.feasible)
  apply (sInf_le (show lagrangian J energy B q star ∈ (lagrangian J energy B q) '' A
    from ⟨star, h.member, rfl⟩)).trans
  simpa only [lagrangian, add_zero] using add_le_add_right hp (J star)

theorem certificate_dual_finite {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B p : ℝ} {star : E} (hbottom : ∀ x ∈ A, J x ≠ ⊥)
    (h : DualCertificate A J energy B p star) :
    dualValue A J energy B p ≠ ⊤ ∧ dualValue A J energy B p ≠ ⊥ := by
  rw [certificate_strong_duality h, optimum_value (certificate_primal_optimum h)]
  exact ⟨h.finite, hbottom star h.member⟩

section Convex
variable [AddCommGroup E] [Module ℝ E]

theorem epigraph_domain_convex {A : Set E} {J : E → EReal}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (h : Convex ℝ (epigraph A J)) :
    Convex ℝ (finiteDomain A J) := by
  intro x hx y hy a b ha hb hab
  have hxy := h (show (x, realObjective J x) ∈ epigraph A J from
    ⟨hx.1, by rw [realObjective, EReal.coe_toReal hx.2 (hbottom x hx.1)]⟩)
    (show (y, realObjective J y) ∈ epigraph A J from
    ⟨hy.1, by rw [realObjective, EReal.coe_toReal hy.2 (hbottom y hy.1)]⟩) ha hb hab
  exact ⟨hxy.1, ne_top_of_le_ne_top (EReal.coe_ne_top _) hxy.2⟩

theorem epigraph_objective_convex {A : Set E} {J : E → EReal}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (h : Convex ℝ (epigraph A J)) :
    ConvexOn ℝ (finiteDomain A J) (realObjective J) := by
  refine ⟨epigraph_domain_convex hbottom h, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := h (show (x, realObjective J x) ∈ epigraph A J from
    ⟨hx.1, by rw [realObjective, EReal.coe_toReal hx.2 (hbottom x hx.1)]⟩)
    (show (y, realObjective J y) ∈ epigraph A J from
    ⟨hy.1, by rw [realObjective, EReal.coe_toReal hy.2 (hbottom y hy.1)]⟩) ha hb hab
  exact EReal.toReal_le_toReal hxy.2 (hbottom _ hxy.1) (EReal.coe_ne_top _)

/-- The derivative premise is of the actual complete-lattice infimum, locally finite.
The finite-domain restriction, its convexity and real-infimum guards are earned. -/
theorem positive_price_certificate {A : Set E} {J : E → EReal} {energy : E → ℝ}
    {B d lo hi : ℝ} {star : E}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (he : ConvexOn ℝ A energy) (hstar : PrimalOptimum A J energy B star)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, value A J energy T ≠ ⊤ ∧ value A J energy T ≠ ⊥)
    (hd : HasDerivAt (fun T => (value A J energy T).toReal) d B) (hs : d < 0) :
    ∃ price : ℝ, price = -d ∧ 0 < price ∧ energy star = B ∧
      DualCertificate A J energy B price star ∧ dualValue A J energy B price = value A J energy B := by
  have hnear : (fun T => (value A J energy T).toReal) =ᶠ[𝓝 B]
      budgetValue (finiteDomain A J) (realObjective J) energy := by
    filter_upwards [isOpen_Ioo.mem_nhds hB] with T hT
    exact finite_value_domain_return hbottom (hfinite T hT)
  have hdr := hd.congr_of_eventuallyEq hnear.symm
  have hdom := epigraph_domain_convex hbottom hJ
  have hreal := primal_domain_return hbottom hstar
  have henergy := he.subset (fun _ hx => hx.1) hdom
  obtain ⟨p, hp, hpos, hc⟩ := ConvexClosurePrice.positive_price_certificate
    (epigraph_objective_convex hbottom hJ) henergy hreal hB
    (fun T hT => finite_cost_guards (hfinite T hT)) hdr hs
  have hact : energy star = B := by
    have hh := hc.complementarity
    rcases mul_eq_zero.mp hh with hz | hz
    · exact False.elim (ne_of_gt hpos hz)
    · exact sub_eq_zero.mp hz
  have hout := certificate_domain_return hbottom hc
  exact ⟨p, hp, hpos, hact, hout, certificate_strong_duality hout⟩

end Convex
end
end SbtCosmo.Derivation.ExtendedClosurePrice
