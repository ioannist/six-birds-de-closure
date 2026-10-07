import SbtCosmo.Derivation.GrowthScaleReturn

/-! A quantitative ODE bound proves the actual growth family's infinity limit. -/
namespace SbtCosmo.Derivation.GrowthLimit
noncomputable section
open Set Filter GrowthComparison GrowthExistence
open scoped Topology

def freeVelocity (x : ℝ) : ℝ := Real.exp (-2 * x)
def freeGrowth (x : ℝ) : ℝ := 3 / 2 - Real.exp (-2 * x) / 2

theorem freeVelocity_derivative (x : ℝ) :
    HasDerivAt freeVelocity (-2 * freeVelocity x) x := by
  change HasDerivAt (fun t => Real.exp (-2 * t)) (-2 * Real.exp (-2 * x)) x
  simpa only [id_eq, mul_one, one_mul, mul_comm] using ((hasDerivAt_id x).const_mul (-2)).exp

theorem freeGrowth_derivative (x : ℝ) : HasDerivAt freeGrowth (freeVelocity x) x := by
  convert (hasDerivAt_const x (3 / 2 : ℝ)).sub ((freeVelocity_derivative x).div_const 2) using 1
  ring

theorem free_initial : freeGrowth 0 = 1 ∧ freeVelocity 0 = 1 := by
  norm_num [freeGrowth, freeVelocity]

/-- Scalar integrating-factor fences control a forced free system with zero initial data. -/
theorem forced_free_bound {D v q : ℝ → ℝ} {L ε : ℝ} (hε : 0 ≤ ε)
    (hDc : ContinuousOn D (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (hD : ∀ x ∈ Icc 0 L, HasDerivAt D (v x) x)
    (hv : ∀ x ∈ Icc 0 L, HasDerivAt v (-2 * v x + q x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ ε) (hD0 : D 0 = 0) (hv0 : v 0 = 0) :
    ∀ x ∈ Icc 0 L, 0 ≤ D x ∧ D x ≤ ε / 2 * x := by
  have hn := cooperative_nonnegative (f := fun _ => 0) (q := q) (K := 0)
    hDc hvc hD (fun x hx => by simpa using hv x hx)
    (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun x hx => (hq x hx).1)
    (by simp [hD0]) (by simp [hv0])
  let W : ℝ → ℝ := fun x => Real.exp (2 * x) * v x
  let B : ℝ → ℝ := fun x => ε / 2 * (Real.exp (2 * x) - 1)
  have hWc : ContinuousOn W (Icc 0 L) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (2 * x))).continuousOn.mul hvc
  have hWd : ∀ x ∈ Icc 0 L, HasDerivAt W (Real.exp (2 * x) * q x) x := by
    intro x hx
    simpa using weighted_velocity_derivative (D := D) (f := fun _ => 0) (q := q)
      (by simpa using hv x hx)
  have hBd : ∀ x : ℝ, HasDerivAt B (ε * Real.exp (2 * x)) x := by
    intro x
    convert ((((hasDerivAt_id x).const_mul 2).exp.sub_const 1).const_mul (ε / 2)) using 1
    simp only [id_eq]
    ring
  have hWbound := image_le_of_deriv_right_le_deriv_boundary hWc
    (fun x hx => (hWd x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (B := B) (by simp [W, B, hv0]) (by unfold B; fun_prop)
    (fun x _ => (hBd x).hasDerivWithinAt)
    (fun x hx => by
      have h := mul_le_mul_of_nonneg_left (hq x (Ico_subset_Icc_self hx)).2
        (Real.exp_pos (2 * x)).le
      simpa [mul_comm] using h)
  have hvbound : ∀ x ∈ Icc 0 L, v x ≤ ε / 2 := by
    intro x hx
    have hw := hWbound hx
    change Real.exp (2 * x) * v x ≤ ε / 2 * (Real.exp (2 * x) - 1) at hw
    have he := Real.exp_pos (2 * x)
    nlinarith
  have hDbound := image_le_of_deriv_right_le_deriv_boundary hDc
    (fun x hx => (hD x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (B := fun x => ε / 2 * x) (by simp [hD0]) (by fun_prop)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul (ε / 2)).hasDerivWithinAt)
    (fun x hx => hvbound x (Ico_subset_Icc_self hx))
  exact fun x hx => ⟨(hn x hx).1, hDbound hx⟩

theorem live_nonnegative {a0 lam L : ℝ} (ha : 0 ≤ a0) (hlam : 0 ≤ lam) : Live a0 lam L := by
  intro x _
  have hp : 0 ≤ (scale a0 x)^3 := pow_nonneg (mul_nonneg ha (Real.exp_pos _).le) 3
  nlinarith [mul_nonneg hlam hp]

theorem coefficient_nonnegative_bound {a0 lam x : ℝ} (ha : 0 < a0)
    (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    coefficient a0 lam x ≤ 3 / (2 * (1 + lam * a0^3)) := by
  have he : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hs : a0 ≤ scale a0 x := by
    simpa [scale] using mul_le_mul_of_nonneg_left he ha.le
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hs 3) hlam
  have hd : 0 < 2 * (1 + lam * a0^3) := by positivity
  unfold coefficient
  exact div_le_div_of_nonneg_left (by norm_num) hd (by linarith)

/-- Comparison is with the finite-start matter IVP, not a growing-mode asymptotic surrogate. -/
theorem growth_matter_bound {a0 lam L : ℝ} (ha : 0 < a0) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam) : ∀ x ∈ Icc 0 L,
    growth (lam * a0^3) x ≤ Real.exp L ∧ velocity (lam * a0^3) x ≤ Real.exp L := by
  have hl := live_nonnegative (L := L) ha.le hlam
  have hs := constructed_growthSolution hL hl
  have hz : Live a0 0 L := by intro x _; simp
  intro x hx
  have he : Real.exp x ≤ Real.exp L := Real.exp_le_exp.mpr hx.2
  by_cases hx0 : x = 0
  · subst x
    rw [hs.growth_initial, hs.velocity_initial]
    exact ⟨by simpa using he, by simpa using he⟩
  by_cases hl0 : lam = 0
  · subst lam
    have hu := growth_unique hz (constructed_growthSolution hL hz) (matter_solution a0 L) x hx
    exact ⟨hu.1.le.trans he, hu.2.le.trans he⟩
  · have hm := growth_strict_parameter ha hL hz hl (lt_of_le_of_ne hlam (Ne.symm hl0))
      (matter_solution a0 L) hs x hx (lt_of_le_of_ne hx.1 (Ne.symm hx0))
    exact ⟨hm.1.le.trans he, hm.2.le.trans he⟩

/-- Quantitative error bound for the actual explicitly constructed IVP family. -/
theorem growth_free_bound {a0 lam L : ℝ} (ha : 0 < a0) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam) : ∀ x ∈ Icc 0 L,
    0 ≤ growth (lam * a0^3) x - freeGrowth x ∧
      growth (lam * a0^3) x - freeGrowth x ≤
        (3 * Real.exp L / (1 + lam * a0^3)) / 2 * x := by
  have hl := live_nonnegative (L := L) ha.le hlam
  have hs := constructed_growthSolution hL hl
  have hp := growth_positive hL hl hs
  have hm := growth_matter_bound ha hL hlam
  let q : ℝ → ℝ := fun x => coefficient a0 lam x *
    (growth (lam * a0^3) x + velocity (lam * a0^3) x)
  have hd : 0 < 1 + lam * a0^3 := by positivity
  have hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ 3 * Real.exp L / (1 + lam * a0^3) := by
    intro x hx
    refine ⟨mul_nonneg (coefficient_positive hl hx).le (add_pos (hp x hx).1 (hp x hx).2).le, ?_⟩
    have hprod := mul_le_mul (coefficient_nonnegative_bound ha hlam hx.1)
      (show growth (lam * a0^3) x + velocity (lam * a0^3) x ≤ 2 * Real.exp L by
        linarith [(hm x hx).1, (hm x hx).2])
      (add_pos (hp x hx).1 (hp x hx).2).le
      (show 0 ≤ 3 / (2 * (1 + lam * a0^3)) by positivity)
    have heq : 3 / (2 * (1 + lam * a0^3)) * (2 * Real.exp L) =
        3 * Real.exp L / (1 + lam * a0^3) := by field_simp
    exact hprod.trans_eq heq
  apply forced_free_bound (q := q) (by positivity)
    (hs.growth_continuous.sub (by unfold freeGrowth; fun_prop))
    (hs.velocity_continuous.sub (by unfold freeVelocity; fun_prop))
    (fun x hx => (hs.growth_derivative x hx).sub (freeGrowth_derivative x))
  · intro x hx
    convert (hs.velocity_derivative x hx).sub (freeVelocity_derivative x) using 1
    dsimp [q]
    ring
  · exact hq
  · simp [hs.growth_initial, free_initial.1]
  · simp [hs.velocity_initial, free_initial.2]

theorem finalGrowth_free_bound {a0 lam L : ℝ} (ha : 0 < a0) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam) :
    0 ≤ finalGrowth a0 L lam - freeGrowth L ∧
      finalGrowth a0 L lam - freeGrowth L ≤
        (3 / 2 * Real.exp L * L) / (1 + lam * a0^3) := by
  have h := growth_free_bound ha hL hlam L ⟨hL, le_rfl⟩
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

/-- No assumed limiting-growth premise: the quantitative ODE error is squeezed to zero. -/
theorem finalGrowth_tendsto_atTop {a0 L : ℝ} (ha : 0 < a0) (hL : 0 ≤ L) :
    Tendsto (finalGrowth a0 L) atTop (𝓝 (freeGrowth L)) := by
  have hden : Tendsto (fun lam : ℝ => 1 + lam * a0^3) atTop atTop := by
    simpa [add_comm] using Tendsto.atTop_add
      (tendsto_id.atTop_mul_const (pow_pos ha 3)) (tendsto_const_nhds (x := (1 : ℝ)))
  have hb := hden.const_div_atTop (3 / 2 * Real.exp L * L)
  have he := squeeze_zero'
    ((eventually_ge_atTop (0 : ℝ)).mono (fun _ hlam => (finalGrowth_free_bound ha hL hlam).1))
    ((eventually_ge_atTop (0 : ℝ)).mono (fun _ hlam => (finalGrowth_free_bound ha hL hlam).2)) hb
  simpa using he.add (tendsto_const_nhds (x := freeGrowth L))


end
end SbtCosmo.Derivation.GrowthLimit
