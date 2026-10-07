import SbtCosmo.Derivation.GrowthInfinite
/-! Quantitative tails from the actual finite-start IVP, with an explicit native return. -/
namespace SbtCosmo.Derivation.GrowthInfiniteTail
noncomputable section
open Set Filter GrowthInfinite GrowthComparison GrowthExistence GrowthLimit
open GrowthScaleReturn
open scoped Topology

theorem velocity_upper {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    velocity c x ≤ prefactor c * Real.exp (-2*x) / c := by
  have hl := live_nonnegative (a0 := (1 : ℝ)) (L := x) (by norm_num) hc.le
  have hp := (growth_positive hx hl (constructed_growthSolution hx hl) x ⟨hx, le_rfl⟩).1
  simp only [one_pow, mul_one] at hp
  have hr : 0 < rootSquared c x := add_pos (Real.exp_pos _) hc
  have hs := root_sq hr
  have hb : c ≤ rootSquared c x := by unfold rootSquared; linarith [Real.exp_pos (-3*x)]
  have ha : 0 ≤ prefactor c * Real.exp (-2*x) := by
    apply mul_nonneg
    · unfold prefactor; linarith
    · exact (Real.exp_pos _).le
  have hdiv := div_le_div_of_nonneg_left ha hc hb
  have hrate : 0 ≤ rate c x := by
    unfold rate
    positivity
  unfold velocity
  rw [hs]
  nlinarith

theorem growth_tail_bound {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    infiniteGrowth c - growth c x ≤ prefactor c * Real.exp (-2*x) / (2*c) := by
  let q := prefactor c / (2*c)
  let F := fun t => growth c t + q * Real.exp (-2*t)
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (velocity c t - 2*q*Real.exp (-2*t)) t := by
    intro t ht
    convert (growth_derivative (rootLive_positive hc t) ⟨ht, le_rfl⟩).add
      ((((hasDerivAt_id t).const_mul (-2)).exp).const_mul q) using 1
    simp only [id_eq]
    ring
  have hm : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      have hv := velocity_upper hc (interior_subset ht)
      have he : 2*q*Real.exp (-2*t) = prefactor c * Real.exp (-2*t) / c := by
        dsimp [q]
        field_simp
      rw [he]
      linarith
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have ht : Tendsto F atTop (𝓝 (infiniteGrowth c)) := by
    simpa [F] using (growth_tendsto hc).add (he.const_mul q)
  have hb : infiniteGrowth c ≤ F x := by
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm hx (hx.trans hy) hy
  dsimp [F, q] at hb
  have he' : prefactor c / (2*c) * Real.exp (-2*x) = prefactor c * Real.exp (-2*x)/(2*c) := by ring
  rw [he'] at hb
  linarith

theorem native_tail_bound {a0 lam A : ℝ} (ha0 : 0 < a0) (hlam : 0 < lam) (hA : a0 ≤ A) :
    nativeInfinite a0 lam - nativeGrowth a0 lam A ≤
      (lam*a0^2 + 5/(2*a0)) / (2*lam*A^2) := by
  have hAp : 0 < A := ha0.trans_le hA
  have hr : 0 < A/a0 := div_pos hAp ha0
  have he : Real.exp (-2*Real.log (A/a0)) = (a0/A)^2 := by
    rw [show -2*Real.log (A/a0) = -(Real.log (A/a0)+Real.log (A/a0)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log hr]
    field_simp
  have h := growth_tail_bound (mul_pos hlam (pow_pos ha0 3)) (horizon_log_nonneg ha0 hA)
  change nativeInfinite a0 lam - nativeGrowth a0 lam A ≤
    prefactor (lam*a0^3) * Real.exp (-2*Real.log (A/a0)) / (2*(lam*a0^3)) at h
  rw [he] at h
  convert h using 1
  unfold prefactor
  field_simp


end
end SbtCosmo.Derivation.GrowthInfiniteTail
