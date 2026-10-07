import SbtCosmo.Derivation.GrowthComparison
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Explicit quadrature constructs the original growth IVP at every live lambda. -/
namespace SbtCosmo.Derivation.GrowthExistence
noncomputable section
open Set MeasureTheory
open scoped Topology
open GrowthComparison

def rootSquared (c x : ℝ) : ℝ := Real.exp (-3 * x) + c
def root (c x : ℝ) : ℝ := Real.sqrt (rootSquared c x)
def rate (c x : ℝ) : ℝ := 3 * Real.exp (-3 * x) / (2 * rootSquared c x)
def RootLive (c L : ℝ) : Prop := ∀ x ∈ Icc 0 L, 0 < rootSquared c x

theorem continuous_root (c : ℝ) : Continuous (root c) := by
  unfold root rootSquared
  fun_prop

theorem root_positive {c x : ℝ} (hx : 0 < rootSquared c x) : 0 < root c x :=
  Real.sqrt_pos.mpr hx

theorem root_sq {c x : ℝ} (hx : 0 < rootSquared c x) : (root c x)^2 = rootSquared c x :=
  Real.sq_sqrt hx.le

theorem hasDerivAt_rate {c x : ℝ} (hx : 0 < rootSquared c x) :
    HasDerivAt (rate c) (2 * (rate c x)^2 - 3 * rate c x) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-3 * t)) (-3 * Real.exp (-3 * x)) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-3)).exp
  convert (he.const_mul 3).div ((he.add_const c).const_mul 2)
    (mul_ne_zero (by norm_num) hx.ne') using 1
  unfold rate rootSquared
  field_simp
  ring

theorem hasDerivAt_root {c x : ℝ} (hx : 0 < rootSquared c x) :
    HasDerivAt (root c) (-rate c x * root c x) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-3 * t)) (-3 * Real.exp (-3 * x)) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-3)).exp
  have hr : root c x ≠ 0 := (root_positive hx).ne'
  have hs := root_sq hx
  convert (he.add_const c).sqrt hx.ne' using 1
  change -rate c x * root c x = (-3 * Real.exp (-3 * x)) / (2 * root c x)
  unfold rate
  field_simp
  nlinarith [hs]

def integrand (c x : ℝ) : ℝ := Real.exp (-2 * x) / (root c x)^3
def primitive (c x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, integrand c s
def prefactor (c : ℝ) : ℝ := c + 5 / 2
def growth (c x : ℝ) : ℝ := root c x * ((root c 0)⁻¹ + prefactor c * primitive c x)
def velocity (c x : ℝ) : ℝ :=
  -rate c x * growth c x + prefactor c * Real.exp (-2 * x) / (root c x)^2

theorem integrand_continuousAt {c x : ℝ} (hx : 0 < rootSquared c x) :
    ContinuousAt (integrand c) x := by
  apply ContinuousAt.div (by fun_prop) ((continuous_root c).continuousAt.pow 3)
  exact pow_ne_zero _ (root_positive hx).ne'

theorem integrand_measurable (c : ℝ) : Measurable (integrand c) := by
  exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (-2 * x))).div
    ((continuous_root c).measurable.pow_const 3)

theorem primitive_derivative {c L x : ℝ} (hl : RootLive c L) (hx : x ∈ Icc 0 L) :
    HasDerivAt (primitive c) (integrand c x) x := by
  have hcont : ContinuousOn (integrand c) (Icc 0 x) := by
    intro t ht
    exact (integrand_continuousAt (hl t ⟨ht.1, ht.2.trans hx.2⟩)).continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable_of_Icc hx.1)
    (integrand_measurable c).stronglyMeasurable.stronglyMeasurableAtFilter
    (integrand_continuousAt (hl x hx))

theorem growth_derivative {c L x : ℝ} (hl : RootLive c L) (hx : x ∈ Icc 0 L) :
    HasDerivAt (growth c) (velocity c x) x := by
  have hr := (root_positive (hl x hx)).ne'
  convert (hasDerivAt_root (hl x hx)).mul
    (((primitive_derivative hl hx).const_mul (prefactor c)).const_add ((root c 0)⁻¹)) using 1
  unfold velocity growth integrand
  field_simp

theorem velocity_derivative {c L x : ℝ} (hl : RootLive c L) (hx : x ∈ Icc 0 L) :
    HasDerivAt (velocity c) (rate c x * growth c x + (rate c x - 2) * velocity c x) x := by
  have hr := (root_positive (hl x hx)).ne'
  have he : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (-2 * Real.exp (-2 * x)) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-2)).exp
  convert ((hasDerivAt_rate (hl x hx)).neg.mul (growth_derivative hl hx)).add
    ((he.const_mul (prefactor c)).div ((hasDerivAt_root (hl x hx)).pow 2) (pow_ne_zero _ hr)) using 1
  unfold velocity
  simp only [Pi.pow_apply, Pi.neg_apply]
  field_simp
  ring

theorem growth_initial {c : ℝ} (hc : 0 < rootSquared c 0) : growth c 0 = 1 := by
  simp [growth, primitive, (root_positive hc).ne']

theorem velocity_initial {c : ℝ} (hc : 0 < rootSquared c 0) : velocity c 0 = 1 := by
  have hr := (root_positive hc).ne'
  have hs := root_sq hc
  unfold velocity
  rw [growth_initial hc]
  simp only [mul_zero, Real.exp_zero, mul_one]
  unfold rate prefactor rootSquared at *
  norm_num at *
  field_simp
  nlinarith [hs]

/-- The exponential rescaling preserves the exact native coefficient. -/
theorem rootSquared_bridge (a0 lam x : ℝ) :
    rootSquared (lam * a0^3) x = Real.exp (-3 * x) * (1 + lam * (scale a0 x)^3) := by
  have he : Real.exp (-3 * x) * (Real.exp x)^3 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  unfold rootSquared scale
  calc
    Real.exp (-3 * x) + lam * a0^3 =
        Real.exp (-3 * x) + lam * a0^3 * (Real.exp (-3 * x) * (Real.exp x)^3) := by rw [he]; ring
    _ = Real.exp (-3 * x) * (1 + lam * (a0 * Real.exp x)^3) := by ring

theorem rootLive_of_live {a0 lam L : ℝ} (hl : Live a0 lam L) :
    RootLive (lam * a0^3) L := by
  intro x hx
  rw [rootSquared_bridge]
  exact mul_pos (Real.exp_pos _) (hl x hx)

theorem rate_eq_coefficient {a0 lam x : ℝ} (hd : 1 + lam * (scale a0 x)^3 ≠ 0) :
    rate (lam * a0^3) x = coefficient a0 lam x := by
  have he := (Real.exp_pos (-3 * x)).ne'
  unfold rate coefficient
  rw [rootSquared_bridge]
  field_simp

/-- An explicit IVP solution is constructed on the entire original live interval. -/
theorem constructed_growthSolution {a0 lam L : ℝ} (hL : 0 ≤ L) (hl : Live a0 lam L) :
    GrowthSolution a0 lam L (growth (lam * a0^3)) (velocity (lam * a0^3)) := by
  have hr := rootLive_of_live hl
  have h0 := hr 0 ⟨le_rfl, hL⟩
  refine ⟨?_, ?_, fun x hx => growth_derivative hr hx, ?_, growth_initial h0, velocity_initial h0⟩
  · intro x hx
    exact (growth_derivative hr hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (velocity_derivative hr hx).continuousAt.continuousWithinAt
  · intro x hx
    simpa [rate_eq_coefficient (hl x hx).ne'] using velocity_derivative hr hx

theorem exists_growthSolution {a0 lam L : ℝ} (hL : 0 ≤ L) (hl : Live a0 lam L) :
    ∃ D v : ℝ → ℝ, GrowthSolution a0 lam L D v :=
  ⟨growth (lam * a0^3), velocity (lam * a0^3), constructed_growthSolution hL hl⟩

/-- Returns all-lambda construction to the original horizon rather than a supplied live predicate. -/
theorem exists_growthSolution_of_horizon {a0 A lam L : ℝ}
    (ha : 0 < a0) (hL : 0 ≤ L) (hA : scale a0 L = A) (hlam : -(1 / A^3) < lam) :
    ∃ D v : ℝ → ℝ, GrowthSolution a0 lam L D v :=
  exists_growthSolution hL (live_of_horizon ha hA hlam)

def safeIntegrand (ε c x : ℝ) : ℝ :=
  Real.exp (-2 * x) / (Real.sqrt (max (rootSquared c x) ε))^3

theorem continuous_safeIntegrand {ε : ℝ} (hε : 0 < ε) :
    Continuous (Function.uncurry (safeIntegrand ε)) := by
  apply Continuous.div (by fun_prop)
    (by unfold rootSquared; fun_prop : Continuous (fun p : ℝ × ℝ =>
      (Real.sqrt (max (rootSquared p.1 p.2) ε))^3))
  intro p
  exact pow_ne_zero _ (Real.sqrt_pos.mpr (hε.trans_le (le_max_right _ _))).ne'

/-- A continuous globally regularized integral agrees locally with the original quadrature.
The regularization is only a continuity proof device; the constructed solution is unchanged. -/
theorem primitive_continuous_parameter {c L : ℝ} (hL : 0 ≤ L)
    (hp : 0 < rootSquared c L) : ContinuousAt (fun d => primitive d L) c := by
  let ε := rootSquared c L / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hc : c - ε < c := by linarith
  have hsafe : Continuous (fun d => ∫ x in (0 : ℝ)..L, safeIntegrand ε d x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_safeIntegrand hε) 0 L
  apply hsafe.continuousAt.congr
  filter_upwards [Ioi_mem_nhds hc] with d hd
  change c - ε < d at hd
  unfold primitive
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hL] at hx
  have he : Real.exp (-3 * L) ≤ Real.exp (-3 * x) :=
    Real.exp_le_exp.mpr (by nlinarith [hx.2])
  have hb : ε ≤ rootSquared d x := by dsimp [ε, rootSquared] at *; linarith
  simp [safeIntegrand, integrand, root, max_eq_left hb]

theorem root_continuous_parameter (x : ℝ) : Continuous (fun c => root c x) := by
  unfold root rootSquared
  fun_prop

theorem rate_continuous_parameter {c x : ℝ} (hp : 0 < rootSquared c x) :
    ContinuousAt (fun d => rate d x) c := by
  apply ContinuousAt.div continuousAt_const (by unfold rootSquared; fun_prop)
  exact (mul_pos (by norm_num) hp).ne'

theorem growth_continuous_parameter {c L : ℝ} (hL : 0 ≤ L)
    (hp : 0 < rootSquared c L) : ContinuousAt (fun d => growth d L) c := by
  have h0 : 0 < rootSquared c 0 := by
    have he : Real.exp (-3 * L) ≤ Real.exp (-3 * 0) :=
      Real.exp_le_exp.mpr (by nlinarith)
    dsimp [rootSquared] at *
    linarith
  exact (root_continuous_parameter L).continuousAt.mul
    (((root_continuous_parameter 0).continuousAt.inv₀ (root_positive h0).ne').add
      ((by unfold prefactor; fun_prop : ContinuousAt prefactor c).mul
        (primitive_continuous_parameter hL hp)))

theorem velocity_continuous_parameter {c L : ℝ} (hL : 0 ≤ L)
    (hp : 0 < rootSquared c L) : ContinuousAt (fun d => velocity d L) c := by
  exact ((rate_continuous_parameter hp).neg.mul (growth_continuous_parameter hL hp)).add
    (((by unfold prefactor; fun_prop : ContinuousAt prefactor c).mul continuousAt_const).div
      ((root_continuous_parameter L).continuousAt.pow 2) (pow_ne_zero _ (root_positive hp).ne'))

def finalGrowth (a0 L lam : ℝ) : ℝ := growth (lam * a0^3) L

theorem finalGrowth_continuousAt {a0 lam L : ℝ} (hL : 0 ≤ L) (hl : Live a0 lam L) :
    ContinuousAt (finalGrowth a0 L) lam := by
  exact ContinuousAt.comp (f := fun d : ℝ => d * a0^3) (x := lam)
    (growth_continuous_parameter hL (rootLive_of_live hl L ⟨hL, le_rfl⟩)) (by fun_prop)

theorem finalGrowth_strictAntiOn {a0 L : ℝ} (ha : 0 < a0) (hL : 0 < L) :
    StrictAntiOn (finalGrowth a0 L) {lam | Live a0 lam L} := by
  intro lam1 hl1 lam2 hl2 hlam
  exact (growth_strict_parameter ha hL.le hl1 hl2 hlam
    (constructed_growthSolution hL.le hl1) (constructed_growthSolution hL.le hl2)
    L ⟨hL.le, le_rfl⟩ hL).1

theorem finalGrowth_at_zero (a0 : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    finalGrowth a0 L 0 = Real.exp L := by
  have hl : Live a0 0 L := by intro x _; simp
  exact (growth_unique hl (constructed_growthSolution hL hl) (matter_solution a0 L)
    L ⟨hL, le_rfl⟩).1

end
end SbtCosmo.Derivation.GrowthExistence
