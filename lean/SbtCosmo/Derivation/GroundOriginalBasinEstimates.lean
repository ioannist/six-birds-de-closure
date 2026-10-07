import SbtCosmo.Derivation.GroundOriginalBasin
import SbtCosmo.Derivation.GroundComplexNormBridge

/-! Whole-basin selector and Euclidean estimates, returned to the actual
original orbit and actual sourced selector. Coordinate and l2 norms differ. -/
namespace SbtCosmo.Derivation.GroundOriginalBasinEstimates
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open Filter Metric NNReal GroundState GroundBorder GroundSourceJacobian GroundNativePhase
open GroundNativeIteration GroundNativeDerivative GroundNativeBox GroundNativeDerivativeBox GroundRationalInterval
open GroundBasin.Point002Data GroundOriginalFirstTube GroundOriginalBasin GroundComplexEuclidean
open GroundComplexNormBridge
open GroundNativePrefixInitial (κ τ coupling_return tolerance_return)
open scoped BigOperators Topology

theorem real_response_enclosed {x : State} (hx : x ∈ closedBall (T.symm (u, 0)) (ρ : ℝ)) (j i : Fin 8) :
    (DR j i).Contains (selectedDerivative b (κ : ℝ) (T x) (T (GroundLocalDynamics.column j, 0)) i) := by
  have hd := selectedDerivative_enclosed GroundBasin.Point002Arithmetic.ground_arithmetic
    (GroundBasin.Point002Arithmetic.real_response j) (input_box_on_ball hx) (real_direction_sound j) i
  exact GroundNativeBox.included_sound (GroundBasin.Point002Arithmetic.real_response_cache j i) hd

theorem imag_response_enclosed {x : State} (hx : x ∈ closedBall (T.symm (u, 0)) (ρ : ℝ)) (j i : Fin 8) :
    (DI j i).Contains (selectedDerivative b (κ : ℝ) (T x) (T (0, GroundLocalDynamics.column j)) i) := by
  have hd := selectedDerivative_enclosed GroundBasin.Point002Arithmetic.ground_arithmetic
    (GroundBasin.Point002Arithmetic.imag_response j) (input_box_on_ball hx) (imag_direction_sound j) i
  exact GroundNativeBox.included_sound (GroundBasin.Point002Arithmetic.imag_response_cache j i) hd

theorem selector_derivative_bound {x : State} (hx : x ∈ closedBall (T.symm (u, 0)) (ρ : ℝ)) :
    ‖(selectedDerivative b (κ : ℝ) (T x)).comp T.toContinuousLinearMap‖ ≤ (1 : ℝ) := by
  apply GroundStateRows.field_operator_norm_le_rows _ (by norm_num)
  intro i
  calc
    (∑ j, (|((selectedDerivative b (κ : ℝ) (T x)).comp T.toContinuousLinearMap) (GroundLocalDynamics.column j, 0) i|+
      |((selectedDerivative b (κ : ℝ) (T x)).comp T.toContinuousLinearMap) (0, GroundLocalDynamics.column j) i|)) ≤
        ∑ j, (((DR j i).bound : ℝ)+((DI j i).bound : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact add_le_add (Interval.abs_le_bound (real_response_enclosed hx j i))
        (Interval.abs_le_bound (imag_response_enclosed hx j i))
    _ ≤ 1 := by
      have hc : ((∑ j : Fin 8, ((DR j i).bound + (DI j i).bound) : ℚ) : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast GroundBasin.Point002Arithmetic.selector_rows i
      simpa only [Rat.cast_sum, Rat.cast_add] using hc

theorem selector_lipschitz : LipschitzOnWith 1 (fun x : State => selected b (κ : ℝ) (T x))
    (closedBall (T.symm (u, 0)) (ρ : ℝ)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x _ => ((selected_hasFDerivAt b (κ : ℝ) (T x)).comp x T.toContinuousLinearMap.hasFDerivAt).hasFDerivWithinAt)
    (fun x hx => by exact_mod_cast selector_derivative_bound hx) (convex_closedBall _ _)

theorem tail_in_ball (n : ℕ) :
    T.symm (unpack (-GroundOriginalNativePrefix.orbit (n+16))) ∈ closedBall (T.symm (u, 0)) (ρ : ℝ) := by
  rw [mem_closedBall]
  have hp : (3/5 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact (reflected_tail_rate n).trans
    ((mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 1/48000)).trans (by norm_num [ρ]))

theorem physical_tail_bound (n : ℕ) :
    ‖unpack (-GroundOriginalNativePrefix.orbit (n+16))-(u, 0)‖ ≤
      (basisBudget : ℝ)*((3/5 : ℝ)^n*(1/48000 : ℝ)) := by
  have h := T.toContinuousLinearMap.le_opNorm
    (T.symm (unpack (-GroundOriginalNativePrefix.orbit (n+16)))-T.symm (u, 0))
  change ‖T (T.symm (unpack (-GroundOriginalNativePrefix.orbit (n+16)))-T.symm (u, 0))‖ ≤ _ at h
  rw [map_sub, T.apply_symm_apply, T.apply_symm_apply] at h
  exact h.trans (mul_le_mul basis_norm (by simpa only [dist_eq_norm] using reflected_tail_rate n)
    (norm_nonneg _) (by norm_num [basisBudget]))

theorem euclidean_tail_bound (n : ℕ) :
    l2 (GroundOriginalNativePrefix.orbit (n+16)-realEmbed (-u)) ≤
      4*(basisBudget : ℝ)*((3/5 : ℝ)^n*(1/48000 : ℝ)) := by
  have he : GroundOriginalNativePrefix.orbit (n+16)-realEmbed (-u) =
      -(pack (unpack (-GroundOriginalNativePrefix.orbit (n+16))-(u, 0))) := by
    rw [← packCLE_apply, map_sub, packCLE_apply, packCLE_apply]
    have hp : pack (unpack (-GroundOriginalNativePrefix.orbit (n+16))) = -GroundOriginalNativePrefix.orbit (n+16) := packCLE.apply_symm_apply _
    rw [hp]
    have hu : pack (u, 0) = realEmbed u := rfl
    rw [hu, GroundNativeReflection.realEmbed_neg]
    abel
  rw [he, l2_neg]
  exact (l2_pack_le _).trans (by nlinarith [physical_tail_bound n])

theorem selector_tail_bound (n : ℕ) :
    ‖selected b (κ : ℝ) (unpack (-GroundOriginalNativePrefix.orbit (n+16)))-u‖ ≤
      (3/5 : ℝ)^n*(1/48000 : ℝ) := by
  have h := selector_lipschitz.dist_le_mul _ (tail_in_ball n) _
    (mem_closedBall_self (by norm_num [ρ] : (0 : ℝ) ≤ (ρ : ℝ)))
  simp only [T.apply_symm_apply, selected_real, ground_data.2, NNReal.coe_one, one_mul, dist_eq_norm] at h
  exact h.trans (by simpa only [dist_eq_norm] using reflected_tail_rate n)

theorem native_candidate_return (n : ℕ) : nativeCandidate b (κ : ℝ) (GroundOriginalNativePrefix.orbit (n+16)) =
    realEmbed (selected b (κ : ℝ) (unpack (-GroundOriginalNativePrefix.orbit (n+16)))) := by
  have h := nativeCandidate_pack b (κ : ℝ) (unpack (-GroundOriginalNativePrefix.orbit (n+16)))
  have hp : pack (unpack (-GroundOriginalNativePrefix.orbit (n+16))) = -GroundOriginalNativePrefix.orbit (n+16) := packCLE.apply_symm_apply _
  rw [hp, GroundNativeReflection.nativeCandidate_neg] at h
  exact h

theorem actual_candidate_distance (n : ℕ) :
    l2 (GroundOriginalNativePrefix.orbit (n+16)-(-nativeCandidate b (κ : ℝ) (GroundOriginalNativePrefix.orbit (n+16)))) ≤
      (4*(basisBudget : ℝ)+4)*((3/5 : ℝ)^n*(1/48000 : ℝ)) := by
  have h := l2_sub_triangle (GroundOriginalNativePrefix.orbit (n+16)) (realEmbed (-u))
    (-nativeCandidate b (κ : ℝ) (GroundOriginalNativePrefix.orbit (n+16)))
  have he : realEmbed (-u)-(-nativeCandidate b (κ : ℝ) (GroundOriginalNativePrefix.orbit (n+16))) =
      realEmbed (selected b (κ : ℝ) (unpack (-GroundOriginalNativePrefix.orbit (n+16)))-u) := by
    rw [native_candidate_return, GroundNativeReflection.realEmbed_neg]
    funext i
    simp [realEmbed]
    ring
  rw [he] at h
  have hc := (l2_realEmbed_le _).trans (mul_le_mul_of_nonneg_left (selector_tail_bound n) (by norm_num : (0 : ℝ) ≤ 4))
  nlinarith [euclidean_tail_bound n]

theorem sourced_potential_budget (n : ℕ) : ∀ i : Fin 8,
    0 ≤ complexSourcePotential b (κ : ℝ) (GroundOriginalNativePrefix.orbit (n+16)) i ∧
    complexSourcePotential b (κ : ℝ) (GroundOriginalNativePrefix.orbit (n+16)) i ≤ 1/2 := by
  have hx : input.Contains (unpack (-GroundOriginalNativePrefix.orbit (n+16))) := by
    simpa only [T.apply_symm_apply] using input_box_on_ball (tail_in_ball n)
  have hp := source_pack b (κ : ℝ) (unpack (-GroundOriginalNativePrefix.orbit (n+16)))
  have hr : pack (unpack (-GroundOriginalNativePrefix.orbit (n+16))) = -GroundOriginalNativePrefix.orbit (n+16) := packCLE.apply_symm_apply _
  rw [hr, GroundNativeReflection.complexSourcePotential_neg] at hp
  intro i
  have hs := sourceBox_sound originalBackground κ hx i
  change (sourceBox originalBackground κ input i).Contains
    (pairSource b (κ : ℝ) (unpack (-GroundOriginalNativePrefix.orbit (n+16))) i) at hs
  rw [← hp] at hs
  have hnum := GroundBasin.Point002Arithmetic.source_bounds i
  have hlo : (0 : ℝ) ≤ (sourceBox originalBackground κ input i).lo := by exact_mod_cast hnum.1
  have hhi : ((sourceBox originalBackground κ input i).hi : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hnum.2
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hhi
  exact ⟨hlo.trans hs.1, hs.2.trans hhi⟩


end
end SbtCosmo.Derivation.GroundOriginalBasinEstimates
