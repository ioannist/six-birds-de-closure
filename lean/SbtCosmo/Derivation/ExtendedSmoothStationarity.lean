import SbtCosmo.Derivation.RelativeSumSplit

/-! Remove an actual smooth finite Lagrangian summand from an original extended
objective, then earn the qualified ambient objective/normal split. Convexity of
the smooth summand away from the optimizer is unnecessary. -/
namespace SbtCosmo.Derivation.ExtendedSmoothStationarity
noncomputable section
open Set ExtendedClosurePrice ConvexSubgradient
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only the original extended objective is convex. The actual smooth summand
need not have a convex ambient extension. -/
theorem restricted_stationarity {A : Set E} {J : E → EReal} {g : E → ℝ}
    {star : E} {k : E →L[ℝ] ℝ}
    (hbottom : ∀ x ∈ A, J x ≠ ⊥) (hJ : Convex ℝ (epigraph A J))
    (hs : star ∈ A) (hfinite : J star ≠ ⊤)
    (hmin : ∀ x ∈ A, J star+(g star : ℝ) ≤ J x+(g x : ℝ))
    (hk : HasFDerivAt g k star) : SubgradientOn A J star (-k) := by
  have hreal : ∀ x ∈ finiteDomain A J, realObjective J star+g star ≤ realObjective J x+g x := by
    intro x hx
    have hh := hmin x hx.1
    rw [← EReal.coe_toReal hfinite (hbottom star hs),
      ← EReal.coe_toReal hx.2 (hbottom x hx.1),← EReal.coe_add,← EReal.coe_add] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hsupport := ConvexSubgradient.remove_smooth_summand
    (epigraph_objective_convex hbottom hJ) ⟨hs,hfinite⟩
    (p := 0) (fun x hx => by simpa only [ContinuousLinearMap.zero_apply,add_zero] using hreal x hx) hk
  refine ⟨hs,hfinite,hbottom star hs,?_⟩
  intro x hx
  by_cases ht : J x=⊤
  · rw [ht]; exact le_top
  · rw [← EReal.coe_toReal hfinite (hbottom star hs),
      ← EReal.coe_toReal ht (hbottom x hx),← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [zero_sub] using hsupport x ⟨hx,ht⟩

/-- Actual smoothness at the optimizer and the common RI point suffice for the
ambient objective/normal split; no smooth-summand convexity is supplied. -/
theorem qualified_stationarity [FiniteDimensional ℝ E]
    {A : Set E} {J : E → EReal} {g : E → ℝ} {star xr : E} {k : E →L[ℝ] ℝ}
    (hbottom : ∀ x, J x ≠ ⊥) (hJ : Convex ℝ (epigraph univ J)) (hA : Convex ℝ A)
    (hC : xr ∈ intrinsicInterior ℝ (finiteDomain univ J)) (hAr : xr ∈ intrinsicInterior ℝ A)
    (hs : star ∈ A) (hfinite : J star ≠ ⊤)
    (hmin : ∀ x ∈ A, J star+(g star : ℝ) ≤ J x+(g x : ℝ))
    (hk : HasFDerivAt g k star) :
    ∃ q η : E →L[ℝ] ℝ, Subgradient J star q ∧ NormalCone A star η ∧ q+k+η=0 := by
  have hrestricted : Convex ℝ (epigraph A J) := by
    intro x hx y hy a b ha hb hab
    exact ⟨hA hx.1 hy.1 ha hb hab,(hJ ⟨mem_univ _,hx.2⟩ ⟨mem_univ _,hy.2⟩ ha hb hab).2⟩
  have hp := restricted_stationarity (fun x _ => hbottom x) hrestricted hs hfinite hmin hk
  obtain ⟨q,η,hq,hη,heq⟩ := RelativeSumSplit.split_subgradient hbottom hJ hA hC hAr hp
  refine ⟨q,η,hq,hη,?_⟩
  calc
    q+k+η=(q+η)+k := by abel
    _ = 0 := by rw [heq,neg_add_cancel]

end
end SbtCosmo.Derivation.ExtendedSmoothStationarity
