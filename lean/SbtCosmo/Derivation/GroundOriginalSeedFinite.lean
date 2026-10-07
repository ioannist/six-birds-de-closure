import SbtCosmo.Derivation.GroundNativeZeroFinite
import SbtCosmo.Derivation.GroundOriginalSeed

/-! A kernel-earned first-step entry and finite squared Euclidean distance bound
for the unchanged native original seed at zero coupling. Exact arithmetic only. -/
namespace SbtCosmo.Derivation.GroundOriginalSeedFinite
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration
open GroundNativeZeroGeometry GroundNativeZeroOrbit GroundNativeZeroFinite GroundOriginalSeed
open GroundRationalInterval GroundKernelTube GroundOriginalFirstTube GroundOriginalSamples GroundResidualEnclosure
open scoped BigOperators

def imagExpr : Expression := Expr.sum (fun i : Fin 8 => .mul (.const (I i)) (uExpr i))
def radiusExpr : Expression := .add (.mul dotExpr dotExpr) (.mul imagExpr imagExpr)
def radiusBox : Interval := radiusExpr.enclose (box originalBackground GroundSamples.Point000.a
  GroundSamples.Point000.c GroundSamples.Point000.z GroundSamples.Point000.r)
def g : Field := positiveGround (background originalBackground)
def reflected : State := unpack (-initial)

theorem finite_seed_arithmetic : (99/100 : ℚ)^2 < rawNorm ∧ radiusBox.hi < (207/1000 : ℚ)^2 := by
  constructor <;> decide +kernel

theorem imag_expression_return (x : GroundBorder.Point) :
    imagExpr.eval (valuation (background originalBackground) 0 x) = dot x.1 rawState.2 := by
  simp [imagExpr, Expr.eval_sum, Expr.eval, uExpr, valuation, GroundPointCoordinates.coord,
    Fin.lastCases_castSucc, rawState, dot, mul_comm]

theorem raw_radius_budget : (radius g rawState)^2 < (207/1000 : ℝ)^2 ∧
    (99/100 : ℝ)^2 < stateNormSq rawState := by
  have hx := branch_in_sample_ball 0
  have hk : (couplings 0 : ℝ) = 0 := by norm_num [couplings]
  rw [hk] at hx
  change GroundOriginalContinuation.branch 0 ∈
    Metric.closedBall (center GroundSamples.Point000.z) (GroundSamples.Point000.r : ℝ) at hx
  have hbox := box_sound originalBackground GroundSamples.Point000.a GroundSamples.Point000.c
    GroundSamples.Point000.z GroundSamples.Point000.r (κ := 0)
    (by norm_num [GroundSamples.Point000.a, GroundSamples.Point000.c]) hx
  have hd := Expr.enclose_sound radiusExpr hbox
  have he : radiusExpr.eval (valuation (background originalBackground) 0 (GroundOriginalContinuation.branch 0)) =
      (radius g rawState)^2 := by
    change dotExpr.eval _ * dotExpr.eval _ + imagExpr.eval _ * imagExpr.eval _ = _
    rw [dot_expression_return, imag_expression_return, radius_sq]
    simp only [g, ground_identity, GroundNativeZeroGeometry.realPart, GroundNativeZeroGeometry.imagPart, pow_two]
  rw [he] at hd
  constructor
  · have h : (radiusBox.hi : ℝ) < ((((207/1000 : ℚ)^2) : ℚ) : ℝ) := by
      exact_mod_cast finite_seed_arithmetic.2
    have hh : (radiusBox.hi : ℝ) < (207/1000 : ℝ)^2 := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h
    exact hd.2.trans_lt hh
  · rw [raw_norm_return]
    have h : ((((99/100 : ℚ)^2) : ℚ) : ℝ) < (rawNorm : ℝ) := by
      exact_mod_cast finite_seed_arithmetic.1
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h

theorem initial_radius_bound : radius g (unpack initial) < 21/100 := by
  have he : unpack initial = normalizeState rawState := by
    rw [double_normalization]; exact packCLE.symm_apply_apply _
  rw [he]
  have hb := raw_radius_budget
  have hn := radius_normalize_sq g raw_norm_pos
  have hr0 : 0 ≤ radius g (normalizeState rawState) := Real.sqrt_nonneg _
  by_contra h
  have hr : (21/100 : ℝ)^2 ≤ (radius g (normalizeState rawState))^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hr raw_norm_pos.le
  nlinarith

theorem reflected_conditions : stateNormSq reflected = 1 ∧ 1/5 < realPart g reflected ∧
    radius g reflected < 21/100 := by
  have he : pack reflected = -initial := packCLE.apply_symm_apply _
  have hu : stateNormSq reflected = 1 := by
    rw [← norm_pack, he, GroundNativeReflection.complexNormSq_neg, initial_unit]
  have hr : realPart g reflected = -realPart g (unpack initial) := by
    simp [reflected, GroundNativeZeroGeometry.realPart, dot, unpack, Finset.sum_neg_distrib]
  have hi : imagPart g reflected = -imagPart g (unpack initial) := by
    simp [reflected, GroundNativeZeroGeometry.imagPart, dot, unpack, Finset.sum_neg_distrib]
  refine ⟨hu, ?_, ?_⟩
  · rw [hr]; have h := initial_overlap_negative; change realPart g (unpack initial) < -1/5 at h; linarith
  · have he : radius g reflected = radius g (unpack initial) := by
      simp only [radius, hr, hi, neg_sq]
    rw [he]; exact initial_radius_bound


theorem initial_half_region_rejected : ¬ (1/2 ≤ realPart g reflected) := by
  have hg : normSq g = 1 := (positiveGround_spec (background originalBackground)).2.1
  have h := reflected_conditions
  have hr := radius_bounds hg h.1 (by linarith [h.2.1])
  linarith [hr.2.1, h.2.2]

theorem first_reflected_overlap : stateNormSq (step g reflected) = 1 ∧
    1/2 < realPart g (step g reflected) := by
  have hg := (positiveGround_spec (background originalBackground)).2.1
  change normSq g = 1 at hg
  have h := reflected_conditions
  exact ⟨(step_estimate hg h.1 (by linarith [h.2.1])).1,
    first_overlap_half hg h.1 h.2.1 h.2.2⟩

theorem actual_seed_distance_sq (n : ℕ) :
    complexNormSq ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground)
      0 (1/2))^[n+1] initial - realEmbed (-(GroundOriginalContinuation.branch 0).1)) ≤
      2*(1/2 : ℝ)^n := by
  let f := nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 0 (1/2)
  have ht : GroundNativeControls.originalTolerance < realPart g reflected := by
    have hh : GroundNativeControls.originalTolerance < 1/5 := by norm_num [GroundNativeControls.originalTolerance]
    exact hh.trans reflected_conditions.2.1
  have hp : pack ((step g)^[n+1] reflected) = -(f^[n+1] initial) := by
    have he := orbit_native_return (background originalBackground) reflected_conditions.1
      GroundNativeControls.originalTolerance_guard.1 ht (n+1)
    have hg := actual_seed_zero_convergence.2
    have hr := GroundNativeReflection.native_iterate_neg (background originalBackground) 0 (1/2) initial
      GroundNativeControls.originalTolerance_guard.1 (n+1) (fun j _ => (hg j).1)
    have hi : pack reflected = -initial := packCLE.apply_symm_apply _
    change pack ((step g)^[n+1] reflected) = (f^[n+1] (pack reflected)) at he
    rw [hi] at he
    exact he.trans hr
  have hd : f^[n+1] initial-realEmbed (-g) = -pack ((step g)^[n+1] reflected-(g,0)) := by
    have hs : pack ((step g)^[n+1] reflected-(g,0)) =
        pack ((step g)^[n+1] reflected)-realEmbed g := packCLE.map_sub _ _
    rw [hs, hp, GroundNativeReflection.realEmbed_neg]; abel
  change complexNormSq (f^[n+1] initial-realEmbed (-(GroundOriginalContinuation.branch 0).1)) ≤ _
  rw [← ground_identity]
  change complexNormSq (f^[n+1] initial-realEmbed (-g)) ≤ _
  rw [hd, GroundNativeReflection.complexNormSq_neg, norm_pack, Function.iterate_succ_apply]
  exact orbit_half_distance_sq (positiveGround_spec (background originalBackground)).2.1
    first_reflected_overlap.1 first_reflected_overlap.2.le n

theorem actual_seed_sixty_distance_sq :
    complexNormSq ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground)
      0 (1/2))^[60] initial - realEmbed (-(GroundOriginalContinuation.branch 0).1)) <
      (1/500000000 : ℝ)^2 := by
  have h := actual_seed_distance_sq 59
  have he : (2 : ℝ)*(1/2 : ℝ)^59 < (1/500000000 : ℝ)^2 := by norm_num
  exact h.trans_lt he

theorem actual_seed_fifty_nine_distance_sq :
    complexNormSq ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground)
      0 (1/2))^[59] initial - realEmbed (-(GroundOriginalContinuation.branch 0).1)) <
      (3/1000000000 : ℝ)^2 := by
  have h := actual_seed_distance_sq 58
  have he : (2 : ℝ)*(1/2 : ℝ)^58 < (3/1000000000 : ℝ)^2 := by norm_num
  exact h.trans_lt he

end
end SbtCosmo.Derivation.GroundOriginalSeedFinite
