import SbtCosmo.Derivation.GroundNativeZeroOrbit
import SbtCosmo.Derivation.GroundOriginalSamples

/-! The original raw seed coefficients, two exact initialization normalizations,
and a kernel-earned signed overlap return at original coupling zero. -/
namespace SbtCosmo.Derivation.GroundOriginalSeed
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration
open GroundNativeZeroGeometry GroundNativeZeroOrbit GroundRationalInterval
open GroundKernelTube GroundOriginalFirstTube GroundOriginalSamples GroundResidualEnclosure
open Filter
open scoped BigOperators Topology

def R : Fin 8 → ℚ := ![(6006223287328529/36028797018963968), (4551147308228299/36028797018963968), (-4163904640858891/288230376151711744), (-5270902660261269/18014398509481984), (-8367469616521093/36028797018963968), (-818924992691439/2251799813685248), (3943085655770265/36028797018963968), (5116725450809315/18014398509481984)]
def I : Fin 8 → ℚ := ![(390720993588021/9007199254740992), (5914864750726069/18014398509481984), (5741860574972641/18014398509481984), (4117252468161551/72057594037927936), (7488982978537591/36028797018963968), (-4963060414965437/18014398509481984), (-6393121202882627/18014398509481984), (-818050745092773/2251799813685248)]

def rawNorm : ℚ := (∑ i, (R i)^2) + (∑ i, (I i)^2)
def rawState : State := (fun i => (R i : ℝ), fun i => (I i : ℝ))
def initial : ComplexField := pack (normalizeState (normalizeState rawState))
def dotExpr : Expression := Expr.sum (fun i : Fin 8 => .mul (.const (R i)) (uExpr i))
def dotBox : Interval := dotExpr.enclose (box originalBackground GroundSamples.Point000.a
  GroundSamples.Point000.c GroundSamples.Point000.z GroundSamples.Point000.r)

theorem seed_arithmetic : 1/2 < rawNorm ∧ rawNorm ≤ (101/100 : ℚ)^2 ∧ dotBox.hi < -101/500 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · decide +kernel

theorem initial_native_normalization :
    initial = complexNormalize (complexNormalize (pack rawState)) := by
  unfold initial
  rw [pack_normalizeState, pack_normalizeState]

theorem raw_norm_return : stateNormSq rawState = (rawNorm : ℝ) := by
  dsimp only [stateNormSq, normSq, rawState, rawNorm]
  push_cast
  rfl

theorem raw_norm_pos : 0 < stateNormSq rawState := by
  rw [raw_norm_return]
  exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1/2) seed_arithmetic.1)

theorem first_normalized_unit : stateNormSq (normalizeState rawState) = 1 :=
  GroundNativeEscape.normalizeState_unit raw_norm_pos

theorem initialization_guards :
    GroundNativeControls.originalTolerance < Real.sqrt (complexNormSq (pack rawState)) ∧
    GroundNativeControls.originalTolerance < Real.sqrt (complexNormSq (complexNormalize (pack rawState))) := by
  have hq : (1/2 : ℝ) < stateNormSq rawState := by
    rw [raw_norm_return]
    have h : (((1/2 : ℚ) : ℝ)) < (rawNorm : ℝ) := by exact_mod_cast seed_arithmetic.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hs : (1/2 : ℝ) < Real.sqrt (stateNormSq rawState) := by
    nlinarith [Real.sq_sqrt raw_norm_pos.le, Real.sqrt_nonneg (stateNormSq rawState)]
  have ht : GroundNativeControls.originalTolerance < 1/2 := by norm_num [GroundNativeControls.originalTolerance]
  constructor
  · rw [norm_pack]
    exact ht.trans hs
  · rw [← pack_normalizeState, norm_pack, first_normalized_unit, Real.sqrt_one]
    exact GroundNativeControls.originalTolerance_guard.2

theorem double_normalization : initial = pack (normalizeState rawState) := by
  unfold initial
  congr 1
  rw [normalizeState, first_normalized_unit, Real.sqrt_one, inv_one, one_smul]

theorem initial_unit : complexNormSq initial = 1 := by
  rw [double_normalization, norm_pack]
  exact first_normalized_unit

theorem ground_identity : positiveGround (background originalBackground) =
    (GroundOriginalContinuation.branch 0).1 := by
  have hf := (sample_ground_return 0).2.2.2.2
  have hk : (couplings 0 : ℝ) = 0 := by norm_num [couplings]
  rw [hk, GroundNormalizedJacobian.zero_coupling_groundMap] at hf
  exact hf

theorem dot_expression_return (x : GroundBorder.Point) :
    dotExpr.eval (valuation (background originalBackground) 0 x) = dot x.1 rawState.1 := by
  simp [dotExpr, Expr.eval_sum, Expr.eval, uExpr, valuation, GroundPointCoordinates.coord,
    Fin.lastCases_castSucc, rawState, dot, mul_comm]

theorem initial_overlap_negative :
    realPart (positiveGround (background originalBackground)) (unpack initial) < -1/5 := by
  have hx := branch_in_sample_ball 0
  have hk : (couplings 0 : ℝ) = 0 := by norm_num [couplings]
  rw [hk] at hx
  change GroundOriginalContinuation.branch 0 ∈
    Metric.closedBall (center GroundSamples.Point000.z) (GroundSamples.Point000.r : ℝ) at hx
  have hbox := box_sound originalBackground GroundSamples.Point000.a GroundSamples.Point000.c
    GroundSamples.Point000.z GroundSamples.Point000.r (κ := 0) (by norm_num [GroundSamples.Point000.a, GroundSamples.Point000.c]) hx
  have hd := Expr.enclose_sound dotExpr hbox
  rw [dot_expression_return] at hd
  have hhi : (dotBox.hi : ℝ) < -101/500 := by exact_mod_cast seed_arithmetic.2.2
  have hdot : dot (positiveGround (background originalBackground)) rawState.1 < -101/500 := by
    rw [ground_identity]
    exact hd.2.trans_lt hhi
  have hupper : stateNormSq rawState ≤ (101/100 : ℝ)^2 := by
    rw [raw_norm_return]
    have h : (rawNorm : ℝ) ≤ (((101/100 : ℚ)^2 : ℚ) : ℝ) := by exact_mod_cast seed_arithmetic.2.1
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h
  have hs : Real.sqrt (stateNormSq rawState) ≤ 101/100 := by
    nlinarith [Real.sq_sqrt raw_norm_pos.le, Real.sqrt_nonneg (stateNormSq rawState)]
  have hsp : 0 < Real.sqrt (stateNormSq rawState) := Real.sqrt_pos.mpr raw_norm_pos
  rw [double_normalization]
  change dot (positiveGround (background originalBackground))
    ((Real.sqrt (stateNormSq rawState))⁻¹ • rawState.1) < -1/5
  rw [show (Real.sqrt (stateNormSq rawState))⁻¹ • rawState.1 =
    (fun i => (Real.sqrt (stateNormSq rawState))⁻¹ * rawState.1 i) from rfl, dot_smul_right]
  rw [mul_comm, ← div_eq_mul_inv]
  apply (div_lt_iff₀ hsp).mpr
  nlinarith

theorem positive_overlap_rejected :
    ¬ (0 < realPart (positiveGround (background originalBackground)) (unpack initial)) := by
  linarith [initial_overlap_negative]

/-- Exact mathematical reification of the original seed converges to the
negative actual ground at zero coupling. This does not emulate IEEE rounding. -/
theorem actual_seed_zero_convergence :
    Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
      (background originalBackground) 0 (1/2))^[n] initial) atTop
      (nhds (realEmbed (-(GroundOriginalContinuation.branch 0).1))) ∧
      ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) 0
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 0 (1/2))^[n] initial) ∧
        NativeLegal GroundNativeControls.originalTolerance (background originalBackground) 0 (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 0 (1/2))^[n] initial) := by
  have ha : GroundNativeControls.originalTolerance <
      -realPart (positiveGround (background originalBackground)) (unpack initial) := by
    have ht : GroundNativeControls.originalTolerance < 1/5 := by norm_num [GroundNativeControls.originalTolerance]
    linarith [initial_overlap_negative]
  simpa only [ground_identity] using actual_negative_zero_convergence (background originalBackground)
    initial_unit GroundNativeControls.originalTolerance_guard.1 ha

end
end SbtCosmo.Derivation.GroundOriginalSeed
