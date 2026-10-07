import SbtCosmo.Derivation.WindowRecords
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Positivity and strict parameter comparison for the original growth ODE.
Solutions satisfy the actual differential equations; monotonicity is derived.
Global solution existence is constructed downstream in GrowthExistence, with
the original scale-factor return in GrowthScaleReturn.
-/
namespace SbtCosmo.Derivation.GrowthComparison
noncomputable section
open Set Filter
open scoped Topology

def negativeSquare (x : ℝ) : ℝ := (min x 0)^2

theorem negativeSquare_nonneg (x : ℝ) : 0 ≤ negativeSquare x := sq_nonneg _

theorem negativeSquare_eq_zero_iff (x : ℝ) : negativeSquare x = 0 ↔ 0 ≤ x := by
  simp [negativeSquare]

theorem continuous_negativeSquare : Continuous negativeSquare := by
  unfold negativeSquare
  fun_prop

theorem hasDerivAt_negativeSquare (x : ℝ) :
    HasDerivAt negativeSquare (2 * min x 0) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hd := (hasDerivAt_id x).pow 2
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hd
    rw [min_eq_left hx.le]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [negativeSquare, min_eq_left (show y < 0 from hy).le]
  · subst x
    have hl : HasDerivWithinAt negativeSquare 0 (Iic 0) 0 := by
      have hd := ((hasDerivAt_id (0 : ℝ)).pow 2).hasDerivWithinAt (s := Iic 0)
      norm_num at hd
      apply hd.congr
      · intro y hy
        simp [negativeSquare, min_eq_left (show y ≤ 0 from hy)]
      · simp [negativeSquare]
    have hr : HasDerivWithinAt negativeSquare 0 (Ici 0) 0 := by
      apply (hasDerivWithinAt_const (0 : ℝ) (Ici 0) (0 : ℝ)).congr
      · intro y hy
        simp [negativeSquare, min_eq_right (show 0 ≤ y from hy)]
      · simp [negativeSquare]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, min_self, mul_zero] using hl.union hr
  · rw [min_eq_right hx.le, mul_zero]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [negativeSquare, min_eq_right (show 0 < y from hy).le]

/-- Algebraic cone estimate: no positivity premise on the evolving coordinates. -/
theorem negative_energy_derivative_bound {D v f q K : ℝ}
    (hf : 0 ≤ f) (hK : f ≤ K) (hq : 0 ≤ q) :
    2 * min D 0 * v + 2 * min v 0 * (f * D + (f - 2) * v + q) ≤
      (4 * (K + 1)) * (negativeSquare D + negativeSquare v) := by
  have hK0 : 0 ≤ K := hf.trans hK
  rcases le_total D 0 with hD | hD <;> rcases le_total v 0 with hv | hv
  · simp only [min_eq_left hD, min_eq_left hv, negativeSquare]
    have hqv : v * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv hq
    have hy := mul_nonneg (by linarith : 0 ≤ f + 1) (sq_nonneg (D - v))
    have hkD := mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg D)
    have hkv := mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg v)
    nlinarith [sq_nonneg D, sq_nonneg v]
  · simp only [min_eq_left hD, min_eq_right hv, negativeSquare]
    have hDv := mul_nonpos_of_nonpos_of_nonneg hD hv
    have hr := mul_nonneg (by linarith : 0 ≤ 4 * (K + 1)) (sq_nonneg D)
    nlinarith
  · simp only [min_eq_right hD, min_eq_left hv, negativeSquare]
    have hfDv := mul_nonpos_of_nonpos_of_nonneg hv (mul_nonneg hf hD)
    have hqv := mul_nonpos_of_nonpos_of_nonneg hv hq
    have hkv := mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg v)
    nlinarith [sq_nonneg v]
  · simp [negativeSquare, min_eq_right hD, min_eq_right hv]

/-- Any solution of the forced cooperative system preserves the nonnegative cone.
Only differential equations, a coefficient bound and initial signs are supplied. -/
theorem cooperative_nonnegative {D v f q : ℝ → ℝ} {L K : ℝ}
    (hDc : ContinuousOn D (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (hD : ∀ x ∈ Icc 0 L, HasDerivAt D (v x) x)
    (hv : ∀ x ∈ Icc 0 L,
      HasDerivAt v (f x * D x + (f x - 2) * v x + q x) x)
    (hf : ∀ x ∈ Icc 0 L, 0 ≤ f x ∧ f x ≤ K)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x) (hD0 : 0 ≤ D 0) (hv0 : 0 ≤ v 0) :
    ∀ x ∈ Icc 0 L, 0 ≤ D x ∧ 0 ≤ v x := by
  let E : ℝ → ℝ := fun x => negativeSquare (D x) + negativeSquare (v x)
  let dE : ℝ → ℝ := fun x => 2 * min (D x) 0 * v x +
    2 * min (v x) 0 * (f x * D x + (f x - 2) * v x + q x)
  have hEc : ContinuousOn E (Icc 0 L) :=
    (continuous_negativeSquare.comp_continuousOn hDc).add
      (continuous_negativeSquare.comp_continuousOn hvc)
  have hEd : ∀ x ∈ Icc 0 L, HasDerivAt E (dE x) x := by
    intro x hx
    exact ((hasDerivAt_negativeSquare (D x)).comp x (hD x hx)).add
      ((hasDerivAt_negativeSquare (v x)).comp x (hv x hx))
  have hE0 : E 0 ≤ 0 := by simp [E, negativeSquare, min_eq_right hD0, min_eq_right hv0]
  have hbound := le_gronwallBound_of_liminf_deriv_right_le (f' := dE)
    (K := 4 * (K + 1)) (ε := 0) hEc
    (fun x hx r hr => ((hEd x (Ico_subset_Icc_self hx)).hasDerivWithinAt).liminf_right_slope_le hr)
    hE0 (fun x hx => by
      simpa [E, dE] using negative_energy_derivative_bound
        (hf x (Ico_subset_Icc_self hx)).1 (hf x (Ico_subset_Icc_self hx)).2
        (hq x (Ico_subset_Icc_self hx)))
  intro x hx
  have he : E x ≤ 0 := by simpa [gronwallBound_ε0_δ0] using hbound x hx
  have hd0 := negativeSquare_nonneg (D x)
  have hv0' := negativeSquare_nonneg (v x)
  have hd : negativeSquare (D x) = 0 := by dsimp [E] at he; linarith
  have hv' : negativeSquare (v x) = 0 := by dsimp [E] at he; linarith
  exact ⟨(negativeSquare_eq_zero_iff _).mp hd, (negativeSquare_eq_zero_iff _).mp hv'⟩

/-- The integrating factor exposes a nonnegative derivative without assuming v's sign. -/
theorem weighted_velocity_derivative {D v f q : ℝ → ℝ} {x : ℝ}
    (hv : HasDerivAt v (f x * D x + (f x - 2) * v x + q x) x) :
    HasDerivAt (fun t => Real.exp (2 * t) * v t)
      (Real.exp (2 * x) * (f x * (D x + v x) + q x)) x := by
  convert (((hasDerivAt_id x).const_mul 2).exp.mul hv) using 1
  simp only [id_eq]
  ring

/-- Strict positivity follows from positive initial conditions and cooperative sourcing. -/
theorem cooperative_positive {D v f q : ℝ → ℝ} {L K : ℝ}
    (hL : 0 ≤ L)
    (hDc : ContinuousOn D (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (hD : ∀ x ∈ Icc 0 L, HasDerivAt D (v x) x)
    (hv : ∀ x ∈ Icc 0 L,
      HasDerivAt v (f x * D x + (f x - 2) * v x + q x) x)
    (hf : ∀ x ∈ Icc 0 L, 0 ≤ f x ∧ f x ≤ K)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x) (hD0 : 0 < D 0) (hv0 : 0 < v 0) :
    ∀ x ∈ Icc 0 L, 0 < D x ∧ 0 < v x := by
  have hn := cooperative_nonnegative hDc hvc hD hv hf hq hD0.le hv0.le
  have hDm : MonotoneOn D (Icc 0 L) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 L) hDc
    · intro x hx
      exact (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hD x (interior_subset hx)).deriv]
      exact (hn x (interior_subset hx)).2
  have hWc : ContinuousOn (fun x => Real.exp (2 * x) * v x) (Icc 0 L) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (2 * x))).continuousOn.mul hvc
  have hWm : MonotoneOn (fun x => Real.exp (2 * x) * v x) (Icc 0 L) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 L) hWc
    · intro x hx
      exact (weighted_velocity_derivative (hv x (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(weighted_velocity_derivative (hv x (interior_subset hx))).deriv]
      have hn' := hn x (interior_subset hx)
      exact mul_nonneg (Real.exp_pos _).le
        (add_nonneg (mul_nonneg (hf x (interior_subset hx)).1 (add_nonneg hn'.1 hn'.2))
          (hq x (interior_subset hx)))
  intro x hx
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  refine ⟨hD0.trans_le (hDm h0 hx hx.1), ?_⟩
  have hw : 0 < Real.exp (2 * x) * v x := by
    have hw' := hWm h0 hx hx.1
    simp only [mul_zero, Real.exp_zero, one_mul] at hw'
    exact hv0.trans_le hw'
  exact (mul_pos_iff.mp hw).resolve_right (by intro h; exact (Real.exp_pos _).not_ge h.1.le)
    |>.2

/-- Strictly positive forcing, from equal initial data, strictly separates both coordinates. -/
theorem cooperative_strict_forcing {D v f q : ℝ → ℝ} {L K : ℝ}
    (hL : 0 ≤ L)
    (hDc : ContinuousOn D (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (hD : ∀ x ∈ Icc 0 L, HasDerivAt D (v x) x)
    (hv : ∀ x ∈ Icc 0 L,
      HasDerivAt v (f x * D x + (f x - 2) * v x + q x) x)
    (hf : ∀ x ∈ Icc 0 L, 0 ≤ f x ∧ f x ≤ K)
    (hq : ∀ x ∈ Icc 0 L, 0 < q x) (hD0 : D 0 = 0) (hv0 : v 0 = 0) :
    ∀ x ∈ Icc 0 L, 0 < x → 0 < D x ∧ 0 < v x := by
  have hn := cooperative_nonnegative hDc hvc hD hv hf
    (fun x hx => (hq x hx).le) (by simp [hD0]) (by simp [hv0])
  have hWc : ContinuousOn (fun x => Real.exp (2 * x) * v x) (Icc 0 L) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (2 * x))).continuousOn.mul hvc
  have hWm : StrictMonoOn (fun x => Real.exp (2 * x) * v x) (Icc 0 L) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 L) hWc
    intro x hx
    rw [(weighted_velocity_derivative (hv x (interior_subset hx))).deriv]
    have hn' := hn x (interior_subset hx)
    exact mul_pos (Real.exp_pos _) (add_pos_of_nonneg_of_pos
      (mul_nonneg (hf x (interior_subset hx)).1 (add_nonneg hn'.1 hn'.2))
      (hq x (interior_subset hx)))
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hvpos : ∀ x ∈ Icc 0 L, 0 < x → 0 < v x := by
    intro x hx hxp
    have hw : 0 < Real.exp (2 * x) * v x := by
      simpa [hv0] using hWm h0 hx hxp
    exact (mul_pos_iff.mp hw).resolve_right (by intro h; exact (Real.exp_pos _).not_ge h.1.le)
      |>.2
  have hDm : StrictMonoOn D (Icc 0 L) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 L) hDc
    intro x hx
    rw [(hD x (interior_subset hx)).deriv]
    rw [interior_Icc] at hx
    exact hvpos x ⟨hx.1.le, hx.2.le⟩ hx.1
  intro x hx hxp
  exact ⟨by simpa [hD0] using hDm h0 hx hxp, hvpos x hx hxp⟩

def scale (a0 x : ℝ) : ℝ := a0 * Real.exp x
def coefficient (a0 lam x : ℝ) : ℝ := 3 / (2 * (1 + lam * (scale a0 x)^3))
def Live (a0 lam L : ℝ) : Prop := ∀ x ∈ Icc 0 L, 0 < 1 + lam * (scale a0 x)^3

theorem coefficient_positive {a0 lam L x : ℝ} (hl : Live a0 lam L)
    (hx : x ∈ Icc 0 L) : 0 < coefficient a0 lam x := by
  exact div_pos (by norm_num) (mul_pos (by norm_num) (hl x hx))

theorem coefficient_continuous {a0 lam L : ℝ} (hl : Live a0 lam L) :
    ContinuousOn (coefficient a0 lam) (Icc 0 L) := by
  apply continuousOn_const.div
    (by unfold scale; fun_prop : ContinuousOn (fun x => 2 * (1 + lam * (scale a0 x)^3)) (Icc 0 L))
  intro x hx
  exact (mul_pos (by norm_num) (hl x hx)).ne'

/-- The bounded coefficient needed by the cone estimate is constructed on the live compact interval. -/
theorem coefficient_bounded {a0 lam L : ℝ} (hl : Live a0 lam L) :
    ∃ K : ℝ, ∀ x ∈ Icc 0 L, 0 ≤ coefficient a0 lam x ∧ coefficient a0 lam x ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image (coefficient_continuous hl)
  exact ⟨K, fun x hx => ⟨(coefficient_positive hl hx).le, hK (mem_image_of_mem _ hx)⟩⟩

theorem coefficient_strict_parameter {a0 lam1 lam2 L x : ℝ}
    (ha : 0 < a0) (h1 : Live a0 lam1 L)
    (hlam : lam1 < lam2) (hx : x ∈ Icc 0 L) :
    coefficient a0 lam2 x < coefficient a0 lam1 x := by
  have hs : 0 < (scale a0 x)^3 := pow_pos (mul_pos ha (Real.exp_pos _)) 3
  unfold coefficient
  apply div_lt_div_of_pos_left (by norm_num) (mul_pos (by norm_num) (h1 x hx))
  nlinarith [mul_lt_mul_of_pos_right hlam hs]

/-- The exact original log-scale growth IVP. Signs and comparison are not fields of this record. -/
structure GrowthSolution (a0 lam L : ℝ) (D v : ℝ → ℝ) : Prop where
  growth_continuous : ContinuousOn D (Icc 0 L)
  velocity_continuous : ContinuousOn v (Icc 0 L)
  growth_derivative : ∀ x ∈ Icc 0 L, HasDerivAt D (v x) x
  velocity_derivative : ∀ x ∈ Icc 0 L,
    HasDerivAt v (coefficient a0 lam x * D x + (coefficient a0 lam x - 2) * v x) x
  growth_initial : D 0 = 1
  velocity_initial : v 0 = 1

theorem growth_positive {a0 lam L : ℝ} {D v : ℝ → ℝ} (hL : 0 ≤ L)
    (hl : Live a0 lam L) (hs : GrowthSolution a0 lam L D v) :
    ∀ x ∈ Icc 0 L, 0 < D x ∧ 0 < v x := by
  obtain ⟨K, hK⟩ := coefficient_bounded hl
  apply cooperative_positive (f := coefficient a0 lam) (q := fun _ => 0) (K := K)
    hL hs.growth_continuous hs.velocity_continuous hs.growth_derivative
  · intro x hx
    simpa using hs.velocity_derivative x hx
  · exact hK
  · intro _ _; exact le_rfl
  · simp [hs.growth_initial]
  · simp [hs.velocity_initial]

theorem growth_strict_in_time {a0 lam L : ℝ} {D v : ℝ → ℝ} (hL : 0 ≤ L)
    (hl : Live a0 lam L) (hs : GrowthSolution a0 lam L D v) : StrictMonoOn D (Icc 0 L) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 L) hs.growth_continuous
  intro x hx
  rw [(hs.growth_derivative x (interior_subset hx)).deriv]
  exact (growth_positive hL hl hs x (interior_subset hx)).2

/-- Strict parameter ordering is derived for any actual IVP solutions, with no ordered-growth premise. -/
theorem growth_strict_parameter {a0 lam1 lam2 L : ℝ} {D1 v1 D2 v2 : ℝ → ℝ}
    (ha : 0 < a0) (hL : 0 ≤ L) (h1 : Live a0 lam1 L) (h2 : Live a0 lam2 L)
    (hlam : lam1 < lam2) (hs1 : GrowthSolution a0 lam1 L D1 v1)
    (hs2 : GrowthSolution a0 lam2 L D2 v2) :
    ∀ x ∈ Icc 0 L, 0 < x → D2 x < D1 x ∧ v2 x < v1 x := by
  obtain ⟨K, hK⟩ := coefficient_bounded h1
  let q := fun x => (coefficient a0 lam1 x - coefficient a0 lam2 x) * (D2 x + v2 x)
  have hpos := growth_positive hL h2 hs2
  have hq : ∀ x ∈ Icc 0 L, 0 < q x := by
    intro x hx
    exact mul_pos (sub_pos.mpr (coefficient_strict_parameter ha h1 hlam hx))
      (add_pos (hpos x hx).1 (hpos x hx).2)
  have hv : ∀ x ∈ Icc 0 L, HasDerivAt (fun t => v1 t - v2 t)
      (coefficient a0 lam1 x * (D1 x - D2 x) +
        (coefficient a0 lam1 x - 2) * (v1 x - v2 x) + q x) x := by
    intro x hx
    convert (hs1.velocity_derivative x hx).sub (hs2.velocity_derivative x hx) using 1
    dsimp [q]
    ring
  have h0D : D1 0 - D2 0 = 0 := by rw [hs1.growth_initial, hs2.growth_initial]; ring
  have h0v : v1 0 - v2 0 = 0 := by rw [hs1.velocity_initial, hs2.velocity_initial]; ring
  have h := cooperative_strict_forcing hL
    (hs1.growth_continuous.sub hs2.growth_continuous)
    (hs1.velocity_continuous.sub hs2.velocity_continuous)
    (fun x hx => (hs1.growth_derivative x hx).sub (hs2.growth_derivative x hx))
    hv hK hq h0D h0v
  intro x hx hxp
  exact ⟨sub_pos.mp (h x hx hxp).1, sub_pos.mp (h x hx hxp).2⟩

theorem horizon_denominator_positive {a A lam : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hlam : -(1 / A^3) < lam) : 0 < 1 + lam * a^3 := by
  have hA : 0 < A := ha.trans_le haA
  have hAp : 0 < A^3 := pow_pos hA 3
  have hdenA : 0 < 1 + lam * A^3 := by
    have h := mul_lt_mul_of_pos_right hlam hAp
    have hi : -(1 / A^3) * A^3 = -1 := by field_simp
    rw [hi] at h
    linarith
  by_cases hl : 0 ≤ lam
  · positivity
  · have hp := pow_le_pow_left₀ ha.le haA 3
    have hm := mul_le_mul_of_nonpos_left hp (le_of_not_ge hl)
    linarith

/-- The original live horizon supplies positivity on the entire log-scale interval. -/
theorem live_of_horizon {a0 A lam L : ℝ} (ha : 0 < a0)
    (hA : scale a0 L = A) (hlam : -(1 / A^3) < lam) : Live a0 lam L := by
  intro x hx
  apply horizon_denominator_positive (mul_pos ha (Real.exp_pos _)) _ hlam
  rw [← hA]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.2) ha.le

theorem scale_log_horizon {a0 A : ℝ} (ha : 0 < a0) (hA : 0 < A) :
    scale a0 (Real.log (A / a0)) = A := by
  rw [scale, Real.exp_log (div_pos hA ha)]
  exact mul_div_cancel₀ A ha.ne'

/-- Exact algebraic bridge from the implemented scale-factor acceleration to log time. -/
def scaleAcceleration (a lam D p : ℝ) : ℝ :=
  (3 / (2 * a^5 * WindowRecords.hubbleSquared a lam)) * D -
    (3 / a - 3 / (2 * a^4 * WindowRecords.hubbleSquared a lam)) * p

theorem scale_acceleration_bridge {a lam D p : ℝ} (ha : a ≠ 0)
    (hh : WindowRecords.hubbleSquared a lam ≠ 0) :
    a * p + a^2 * scaleAcceleration a lam D p =
      (3 / (2 * (1 + lam * a^3))) * D +
        (3 / (2 * (1 + lam * a^3)) - 2) * (a * p) := by
  have hd : 1 + lam * a^3 ≠ 0 := by
    have hmul : 1 + lam * a^3 = a^3 * WindowRecords.hubbleSquared a lam := by
      unfold WindowRecords.hubbleSquared
      field_simp
    rw [hmul]
    exact mul_ne_zero (pow_ne_zero _ ha) hh
  unfold scaleAcceleration WindowRecords.hubbleSquared
  field_simp
  ring

theorem hasDerivAt_scale (a0 x : ℝ) : HasDerivAt (scale a0) (scale a0 x) x := by
  simpa [scale] using (Real.hasDerivAt_exp x).const_mul a0

theorem log_growth_derivative {a0 x : ℝ} {D p : ℝ → ℝ}
    (hD : HasDerivAt D (p (scale a0 x)) (scale a0 x)) :
    HasDerivAt (fun t => D (scale a0 t)) (scale a0 x * p (scale a0 x)) x := by
  simpa [mul_comm] using hD.comp x (hasDerivAt_scale a0 x)

theorem log_velocity_derivative {a0 lam x : ℝ} {D p : ℝ → ℝ}
    (ha : scale a0 x ≠ 0) (hh : WindowRecords.hubbleSquared (scale a0 x) lam ≠ 0)
    (hp : HasDerivAt p (scaleAcceleration (scale a0 x) lam (D (scale a0 x))
      (p (scale a0 x))) (scale a0 x)) :
    HasDerivAt (fun t => scale a0 t * p (scale a0 t))
      (coefficient a0 lam x * D (scale a0 x) +
        (coefficient a0 lam x - 2) * (scale a0 x * p (scale a0 x))) x := by
  convert (hasDerivAt_scale a0 x).mul (hp.comp x (hasDerivAt_scale a0 x)) using 1
  unfold coefficient
  rw [← scale_acceleration_bridge ha hh]
  simp only [Function.comp_apply]
  ring

/-- Uniqueness follows from the same cone estimate applied to both signed differences. -/
theorem growth_unique {a0 lam L : ℝ} {D1 v1 D2 v2 : ℝ → ℝ}
    (hl : Live a0 lam L) (hs1 : GrowthSolution a0 lam L D1 v1)
    (hs2 : GrowthSolution a0 lam L D2 v2) :
    ∀ x ∈ Icc 0 L, D1 x = D2 x ∧ v1 x = v2 x := by
  obtain ⟨K, hK⟩ := coefficient_bounded hl
  have hordered : ∀ D v D' v' : ℝ → ℝ,
      GrowthSolution a0 lam L D v → GrowthSolution a0 lam L D' v' →
      ∀ x ∈ Icc 0 L, D' x ≤ D x ∧ v' x ≤ v x := by
    intro D v D' v' hs hs'
    have hv : ∀ x ∈ Icc 0 L, HasDerivAt (fun t => v t - v' t)
        (coefficient a0 lam x * (D x - D' x) +
          (coefficient a0 lam x - 2) * (v x - v' x) + 0) x := by
      intro x hx
      convert (hs.velocity_derivative x hx).sub (hs'.velocity_derivative x hx) using 1
      ring
    have h := cooperative_nonnegative (f := coefficient a0 lam) (q := fun _ => 0)
      (hs.growth_continuous.sub hs'.growth_continuous)
      (hs.velocity_continuous.sub hs'.velocity_continuous)
      (fun x hx => (hs.growth_derivative x hx).sub (hs'.growth_derivative x hx))
      hv hK (fun _ _ => le_rfl) (by simp [hs.growth_initial, hs'.growth_initial])
      (by simp [hs.velocity_initial, hs'.velocity_initial])
    intro x hx
    exact ⟨sub_nonneg.mp (h x hx).1, sub_nonneg.mp (h x hx).2⟩
  intro x hx
  have h12 := hordered D1 v1 D2 v2 hs1 hs2 x hx
  have h21 := hordered D2 v2 D1 v1 hs2 hs1 x hx
  exact ⟨le_antisymm h21.1 h12.1, le_antisymm h21.2 h12.2⟩

/-- The matter-only control is an actual solution, not a stipulated growth value. -/
theorem matter_solution (a0 L : ℝ) :
    GrowthSolution a0 0 L Real.exp Real.exp := by
  refine ⟨Real.continuous_exp.continuousOn, Real.continuous_exp.continuousOn,
    fun x _ => Real.hasDerivAt_exp x, ?_, Real.exp_zero, Real.exp_zero⟩
  intro x _
  convert Real.hasDerivAt_exp x using 1
  simp [coefficient]
  ring

/-- Collapse anywhere on the expanding interval is equivalent to collapse by its horizon. -/
theorem ever_collapse_iff_final {a0 lam L amplitude threshold : ℝ} {D v : ℝ → ℝ}
    (hL : 0 ≤ L) (hl : Live a0 lam L) (hs : GrowthSolution a0 lam L D v)
    (ha : 0 ≤ amplitude) :
    (∃ x ∈ Icc 0 L, threshold ≤ amplitude * D x) ↔ threshold ≤ amplitude * D L := by
  have hmon := (growth_strict_in_time hL hl hs).monotoneOn
  have hend : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  constructor
  · rintro ⟨x, hx, hc⟩
    exact hc.trans (mul_le_mul_of_nonneg_left (hmon hx hend hx.2) ha)
  · intro hc
    exact ⟨L, hend, hc⟩

/-- Returns derived ODE monotonicity to the original two-tag record history. -/
theorem record_history_iff_threshold {ι : Type*} {amplitude : ι → ℝ} {tag : ι → Bool}
    {a0 lam L m0 m1 threshold : ℝ} {D v : ℝ → ℝ}
    (hL : 0 ≤ L) (hl : Live a0 lam L) (hs : GrowthSolution a0 lam L D v)
    (ha : ∀ i, 0 ≤ amplitude i)
    (h0 : WindowRecords.TagMaximum amplitude tag false m0)
    (h1 : WindowRecords.TagMaximum amplitude tag true m1) (hm0 : 0 < m0) (hm1 : 0 < m1) :
    WindowRecords.RecordBearing
      (fun i => ∃ x ∈ Icc 0 L, threshold ≤ amplitude i * D x) tag ↔
      max (threshold / m0) (threshold / m1) ≤ D L := by
  have heq : (fun i => ∃ x ∈ Icc 0 L, threshold ≤ amplitude i * D x) =
      (fun i => threshold ≤ amplitude i * D L) := by
    funext i
    exact propext (ever_collapse_iff_final hL hl hs (ha i))
  rw [heq]
  exact WindowRecords.record_iff_threshold h0 h1 hm0 hm1
    (growth_positive hL hl hs L ⟨hL, le_rfl⟩).1.le

/-- On the live branch, the actual fixed-tag record gate is downward closed in lambda. -/
theorem record_gate_parameter_downward {ι : Type*} {amplitude : ι → ℝ} {tag : ι → Bool}
    {a0 lam1 lam2 L threshold : ℝ} {D1 v1 D2 v2 : ℝ → ℝ}
    (ha0 : 0 < a0) (hL : 0 < L) (h1 : Live a0 lam1 L) (h2 : Live a0 lam2 L)
    (hlam : lam1 < lam2) (hs1 : GrowthSolution a0 lam1 L D1 v1)
    (hs2 : GrowthSolution a0 lam2 L D2 v2) (ha : ∀ i, 0 ≤ amplitude i)
    (hc : WindowRecords.RecordBearing (fun i => threshold ≤ amplitude i * D2 L) tag) :
    WindowRecords.RecordBearing (fun i => threshold ≤ amplitude i * D1 L) tag := by
  have hg := (growth_strict_parameter ha0 hL.le h1 h2 hlam hs1 hs2 L ⟨hL.le, le_rfl⟩ hL).1
  exact WindowRecords.collapse_monotone
    (fun i hi => hi.trans (mul_le_mul_of_nonneg_left hg.le (ha i))) hc

end
end SbtCosmo.Derivation.GrowthComparison
