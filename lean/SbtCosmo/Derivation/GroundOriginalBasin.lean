import SbtCosmo.Derivation.GroundBasin.Point002Bridge
import SbtCosmo.Derivation.GroundBasin.Point002Arithmetic

/-! Original-seed entry, infinite native convergence and all guards at original
coupling .3, returned from populated whole-ball kernel certificates. -/
namespace SbtCosmo.Derivation.GroundOriginalBasin
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open Filter Metric NNReal GroundState GroundBorder GroundSourceJacobian GroundNativePhase
open GroundNativeIteration GroundNativeDerivative GroundNativeBox GroundNativeDerivativeBox GroundRationalInterval
open GroundBasin.Point002Data GroundOriginalFirstTube
open GroundNativePrefixInitial (κ τ coupling_return tolerance_return)
open scoped BigOperators Topology

def contraction : ℝ≥0 := ⟨(rate : ℝ), by norm_num [rate]⟩

theorem whole_ball_guards : ∀ x ∈ closedBall (T.symm (u, 0)) (ρ : ℝ),
    GroundNativeControls.originalTolerance < overlapNorm b (κ : ℝ) (T x) ∧
    GroundNativeControls.originalTolerance < Real.sqrt (stateNormSq (mixed b (κ : ℝ) (1/2) (T x))) := by
  intro x hx
  exact core_guards GroundBasin.Point002Arithmetic.native_arithmetic (input_box_on_ball hx)

theorem whole_ball_derivative : ∀ x ∈ closedBall (T.symm (u, 0)) (ρ : ℝ),
    ‖GroundNativeQuantitativeBall.derivative T b (κ : ℝ) (1/2) x‖ ≤ (rate : ℝ) := by
  intro x hx
  exact core_derivative_norm GroundBasin.Point002Arithmetic.native_arithmetic
    GroundBasin.Point002Arithmetic.real_response GroundBasin.Point002Arithmetic.imag_response
    GroundBasin.Point002Arithmetic.real_response_cache GroundBasin.Point002Arithmetic.imag_response_cache
    GroundBasin.Point002Arithmetic.real_jet_cache GroundBasin.Point002Arithmetic.imag_jet_cache
    GroundBasin.Point002Arithmetic.real_rows GroundBasin.Point002Arithmetic.imag_rows (input_box_on_ball hx)

theorem original_endpoint_entry :
    T.symm (unpack (-GroundOriginalNativePrefix.orbit 16)) ∈ closedBall (T.symm (u, 0)) (ρ : ℝ) := by
  rw [mem_closedBall]
  exact (core_endpoint_entry GroundBasin.Point002Arithmetic.endpoint_rows).trans (by norm_num [ρ])

theorem positive_future :
    Tendsto (fun n : ℕ => (GroundOriginalNativePrefix.f)^[n] (-GroundOriginalNativePrefix.orbit 16))
      atTop (nhds (realEmbed u)) ∧
    ∀ n : ℕ,
      ActivePhase GroundNativeControls.originalTolerance b (κ : ℝ)
        ((GroundOriginalNativePrefix.f)^[n] (-GroundOriginalNativePrefix.orbit 16)) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ : ℝ) (1/2)
        ((GroundOriginalNativePrefix.f)^[n] (-GroundOriginalNativePrefix.orbit 16)) ∧
      dist (T.symm (unpack ((GroundOriginalNativePrefix.f)^[n] (-GroundOriginalNativePrefix.orbit 16))))
        (T.symm (u, 0)) ≤ (rate : ℝ)^n *
        dist (T.symm (unpack (-GroundOriginalNativePrefix.orbit 16))) (T.symm (u, 0)) := by
  exact GroundNativeQuantitativeBall.explicit_native_ball_convergence T contraction
    ground_data.1 ground_data.2 GroundNativeControls.originalTolerance_guard.1
    GroundNativeControls.originalTolerance_guard.2 (by norm_num [ρ])
    (by change (rate : ℝ) < 1; norm_num [rate]) whole_ball_guards whole_ball_derivative
    _ original_endpoint_entry

theorem reflected_tail (n : ℕ) :
    GroundOriginalNativePrefix.orbit (n+16) =
      -((GroundOriginalNativePrefix.f)^[n] (-GroundOriginalNativePrefix.orbit 16)) := by
  have hn := GroundNativeReflection.native_iterate_neg b (κ : ℝ) (1/2)
    (-GroundOriginalNativePrefix.orbit 16) GroundNativeControls.originalTolerance_guard.1 n
    (fun j _ => (positive_future.2 j).1)
  simpa only [neg_neg, GroundOriginalNativePrefix.orbit, GroundOriginalNativePrefix.f,
    Function.iterate_add_apply] using hn

theorem original_seed_converges_negative_ground :
    Tendsto GroundOriginalNativePrefix.orbit atTop (nhds (realEmbed (-u))) := by
  apply (tendsto_add_atTop_iff_nat 16).mp
  simpa only [← reflected_tail, ← GroundNativeReflection.realEmbed_neg] using positive_future.1.neg

theorem original_seed_all_guards (n : ℕ) :
    ActivePhase GroundNativeControls.originalTolerance b (κ : ℝ) (GroundOriginalNativePrefix.orbit n) ∧
    NativeLegal GroundNativeControls.originalTolerance b (κ : ℝ) (1/2) (GroundOriginalNativePrefix.orbit n) := by
  by_cases hn : n < 16
  · exact GroundOriginalNativePrefix.native_prefix_guards ⟨n, hn⟩
  · have he : n = (n-16)+16 := (Nat.sub_add_cancel (Nat.le_of_not_gt hn)).symm
    rw [he, reflected_tail]
    have hg := positive_future.2 (n-16)
    exact ⟨(GroundNativeReflection.activePhase_neg_iff _ _ _ _).mpr hg.1,
      (GroundNativeReflection.nativeLegal_neg_iff _ _ _ _ GroundNativeControls.originalTolerance_guard.1 hg.1).mpr hg.2.1⟩

theorem original_seed_all_unit (n : ℕ) : complexNormSq (GroundOriginalNativePrefix.orbit n) = 1 := by
  cases n with
  | zero => exact GroundOriginalSeed.initial_unit
  | succ n =>
    rw [GroundOriginalNativePrefix.orbit, Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 (original_seed_all_guards n).2

theorem reflected_tail_rate (n : ℕ) :
    dist (T.symm (unpack (-GroundOriginalNativePrefix.orbit (n+16)))) (T.symm (u, 0)) ≤
      (3/5 : ℝ)^n * (1/48000 : ℝ) := by
  rw [reflected_tail, neg_neg]
  have he := mul_le_mul_of_nonneg_left
    (core_endpoint_entry GroundBasin.Point002Arithmetic.endpoint_rows)
    (pow_nonneg (by norm_num [rate] : (0 : ℝ) ≤ (rate : ℝ)) n)
  simpa only [rate, Rat.cast_div, Rat.cast_ofNat] using (positive_future.2 n).2.2.trans he


end
end SbtCosmo.Derivation.GroundOriginalBasin
