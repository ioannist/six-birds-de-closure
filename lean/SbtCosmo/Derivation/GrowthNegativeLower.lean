import SbtCosmo.Derivation.GrowthNegativeBounds

/-! A derived subsolution of the actual finite-start expanding growth IVP. -/
namespace SbtCosmo.Derivation.GrowthNegativeLower
noncomputable section
open Set GrowthComparison GrowthExistence GrowthScaleReturn

def lowerGrowth (s x : ℝ) : ℝ :=
  Real.exp x + (s / 6) * (Real.exp (4 * x) - Real.exp x * (1 + 3 * x))
def lowerVelocity (s x : ℝ) : ℝ :=
  Real.exp x + (s / 6) * (4 * Real.exp (4 * x) - Real.exp x * (4 + 3 * x))
def lowerAcceleration (s x : ℝ) : ℝ :=
  Real.exp x + (s / 6) * (16 * Real.exp (4 * x) - Real.exp x * (7 + 3 * x))

theorem lowerGrowth_derivative (s x : ℝ) :
    HasDerivAt (lowerGrowth s) (lowerVelocity s x) x := by
  have h4 := ((hasDerivAt_id x).const_mul 4).exp
  have h3 := ((hasDerivAt_id x).const_mul 3).const_add 1
  convert (Real.hasDerivAt_exp x).add
    ((h4.sub ((Real.hasDerivAt_exp x).mul h3)).const_mul (s / 6)) using 1
  unfold lowerVelocity
  dsimp only [id]
  ring

theorem lowerVelocity_derivative (s x : ℝ) :
    HasDerivAt (lowerVelocity s) (lowerAcceleration s x) x := by
  have h4 := (((hasDerivAt_id x).const_mul 4).exp).const_mul 4
  have h3 := ((hasDerivAt_id x).const_mul 3).const_add 4
  convert (Real.hasDerivAt_exp x).add
    ((h4.sub ((Real.hasDerivAt_exp x).mul h3)).const_mul (s / 6)) using 1
  unfold lowerAcceleration
  dsimp only [id]
  ring

theorem lower_initial (s : ℝ) : lowerGrowth s 0 = 1 ∧ lowerVelocity s 0 = 1 := by
  norm_num [lowerGrowth, lowerVelocity]

theorem lower_matter_bounds {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    Real.exp x ≤ lowerGrowth s x ∧ Real.exp x ≤ lowerVelocity s x := by
  have he : Real.exp (4 * x) = Real.exp x * Real.exp (3 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (3 * x)) (Real.exp_pos x).le
  rw [← he] at ht
  constructor
  · unfold lowerGrowth
    have hb : 0 ≤ Real.exp (4 * x) - Real.exp x * (1 + 3 * x) := by nlinarith
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hs (by norm_num)) hb)
  · unfold lowerVelocity
    have hb : 0 ≤ 4 * Real.exp (4 * x) - Real.exp x * (4 + 3 * x) := by
      nlinarith [mul_nonneg (Real.exp_pos x).le hx]
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hs (by norm_num)) hb)

theorem coefficient_negative_lower {a0 lam L x : ℝ} (hl : Live a0 lam L)
    (hs : 0 ≤ -lam * a0^3) (hx : x ∈ Icc 0 L) :
    (3 / 2) * (-lam * a0^3) * Real.exp (3 * x) ≤ coefficient a0 lam x - 3 / 2 := by
  have he : (Real.exp x)^3 = Real.exp (3 * x) := by
    simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul x 3).symm
  have hd : 0 < 1 - (-lam * a0^3) * Real.exp (3 * x) := by
    have h := hl x hx
    unfold scale at h
    rw [mul_pow, he] at h
    nlinarith
  have hz := mul_nonneg hs (Real.exp_pos (3 * x)).le
  have hf : coefficient a0 lam x = 3 / (2 * (1 - (-lam * a0^3) * Real.exp (3 * x))) := by
    unfold coefficient scale
    rw [mul_pow, he]
    congr 2
    ring
  rw [hf]
  rw [le_sub_iff_add_le]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hd)).mpr
  nlinarith [sq_nonneg ((-lam * a0^3) * Real.exp (3 * x))]

def forcing (a0 lam x : ℝ) : ℝ :=
  coefficient a0 lam x * lowerGrowth (-lam * a0^3) x +
    (coefficient a0 lam x - 2) * lowerVelocity (-lam * a0^3) x -
      lowerAcceleration (-lam * a0^3) x

theorem forcing_nonnegative {a0 lam L x : ℝ} (hl : Live a0 lam L)
    (hs : 0 ≤ -lam * a0^3) (hx : x ∈ Icc 0 L) : 0 ≤ forcing a0 lam x := by
  let s := -lam * a0^3
  have hb := lower_matter_bounds hs hx.1
  have hc := coefficient_negative_lower hl hs hx
  have hd : 0 ≤ coefficient a0 lam x - 3 / 2 :=
    (mul_nonneg (mul_nonneg (by norm_num) hs) (Real.exp_pos _).le).trans hc
  have hm := mul_le_mul hc (show 2 * Real.exp x ≤ lowerGrowth s x + lowerVelocity s x by
    dsimp [s]; linarith) (by positivity) hd
  have he : Real.exp (3 * x) * Real.exp x = Real.exp (4 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hr : lowerAcceleration s x - (3 / 2) * lowerGrowth s x + (1 / 2) * lowerVelocity s x =
      (s / 4) * (11 * Real.exp (4 * x) - 5 * Real.exp x) := by
    unfold lowerAcceleration lowerGrowth lowerVelocity
    ring
  have hq : forcing a0 lam x =
      (coefficient a0 lam x - 3 / 2) * (lowerGrowth s x + lowerVelocity s x) -
        (s / 4) * (11 * Real.exp (4 * x) - 5 * Real.exp x) := by
    rw [← hr]
    dsimp [forcing, s]
    ring
  have hm' : 3 * s * Real.exp (4 * x) ≤
      (coefficient a0 lam x - 3 / 2) * (lowerGrowth s x + lowerVelocity s x) := by
    convert hm using 1
    dsimp [s]
    calc
      3 * (-lam * a0^3) * Real.exp (4 * x) =
          3 * (-lam * a0^3) * (Real.exp (3 * x) * Real.exp x) := by rw [he]
      _ = _ := by ring
  rw [hq]
  have h4 := mul_nonneg hs (Real.exp_pos (4 * x)).le
  have h1 := mul_nonneg hs (Real.exp_pos x).le
  dsimp [s] at hm' ⊢
  nlinarith

theorem growth_lower {a0 lam L : ℝ} (hL : 0 ≤ L) (hl : Live a0 lam L)
    (hs : 0 ≤ -lam * a0^3) :
    ∀ x ∈ Icc 0 L, lowerGrowth (-lam * a0^3) x ≤ growth (lam * a0^3) x := by
  have sol := constructed_growthSolution hL hl
  obtain ⟨K, hK⟩ := coefficient_bounded hl
  have hv : ∀ x ∈ Icc 0 L,
      HasDerivAt (fun t => velocity (lam * a0^3) t - lowerVelocity (-lam * a0^3) t)
        (coefficient a0 lam x * (growth (lam * a0^3) x - lowerGrowth (-lam * a0^3) x) +
          (coefficient a0 lam x - 2) * (velocity (lam * a0^3) x - lowerVelocity (-lam * a0^3) x) +
            forcing a0 lam x) x := by
    intro x hx
    convert (sol.velocity_derivative x hx).sub (lowerVelocity_derivative (-lam * a0^3) x) using 1
    unfold forcing
    ring
  have h := cooperative_nonnegative
    (sol.growth_continuous.sub (fun x _ => (lowerGrowth_derivative (-lam * a0^3) x).continuousAt.continuousWithinAt))
    (sol.velocity_continuous.sub (fun x _ => (lowerVelocity_derivative (-lam * a0^3) x).continuousAt.continuousWithinAt))
    (fun x hx => (sol.growth_derivative x hx).sub (lowerGrowth_derivative (-lam * a0^3) x))
    hv hK (fun x hx => forcing_nonnegative hl hs hx)
    (by rw [sol.growth_initial, (lower_initial (-lam * a0^3)).1]; norm_num)
    (by rw [sol.velocity_initial, (lower_initial (-lam * a0^3)).2]; norm_num)
  intro x hx
  exact sub_nonneg.mp (h x hx).1

theorem native_lower {a0 a lam : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a)
    (hlam : -(1 / a^3) < lam) (hnonpos : lam ≤ 0) :
    lowerGrowth (-lam * a0^3) (logScale a0 a) ≤ nativeGrowth a0 lam a := by
  have hL := horizon_log_nonneg ha0 ha
  have hl := live_of_horizon ha0 (scale_log_horizon ha0 (ha0.trans_le ha)) hlam
  exact growth_lower hL hl (mul_nonneg (neg_nonneg.mpr hnonpos) (pow_pos ha0 3).le) _ ⟨hL, le_rfl⟩

end
end SbtCosmo.Derivation.GrowthNegativeLower
