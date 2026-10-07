import SbtCosmo.Derivation.GroundComplexResidual

namespace SbtCosmo.Derivation.GroundComplexResidualBudget
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
open GroundState GroundNativePhase GroundComplexEuclidean GroundComplexResidual
open scoped BigOperators

theorem shifted_l2_bound {b : Field} {e B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ B) (he : 0 ≤ e ∧ e ≤ B) (z : ComplexField) :
    l2 (shifted b e z) ≤ (2+B)*l2 z := by
  have hd : l2 (fun i => ((1+b i-e : ℝ) : ℂ)*z i) ≤ (1+B)*l2 z :=
    l2_diagonal (by linarith) (fun i => abs_le.mpr ⟨by linarith [(hb i).1], by linarith [(hb i).2]⟩) z
  have hx : shifted b e z = (fun i => ((1+b i-e : ℝ) : ℂ)*z i)-
      (1/2 : ℂ) • (fun i => z (prev i))-(1/2 : ℂ) • (fun i => z (next i)) := by
    funext i; simp [shifted, complexHamiltonian]; ring
  rw [hx]
  have h1 := l2_sub (fun i => ((1+b i-e : ℝ) : ℂ)*z i) ((1/2 : ℂ) • (fun i => z (prev i)))
  have h2 := l2_sub ((fun i => ((1+b i-e : ℝ) : ℂ)*z i)-
      (1/2 : ℂ) • (fun i => z (prev i))) ((1/2 : ℂ) • (fun i => z (next i)))
  rw [l2_smul, l2_shift_prev] at h1
  rw [l2_smul, l2_shift_next] at h2
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc] at h1 h2
  linarith

theorem ground_energy_budget {b g : Field} {e B : ℝ} (hg : IsGround b g e)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ B) : 0 ≤ e ∧ e ≤ B := by
  have hpos : 0 ≤ energy b g := by
    rw [energy_identity]
    exact add_nonneg (kineticEnergy_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (hb i).1 (sq_nonneg _))
  rw [ground_energy hg] at hpos
  have hu : energy b uniform ≤ B := by
    rw [energy_identity]
    have hk : kineticEnergy uniform = 0 := by simp [kineticEnergy, uniform]
    rw [hk, zero_add]
    have hs := Finset.sum_le_sum (fun (i : Fin 8) (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (hb i).2 (sq_nonneg (uniform i)))
    rw [← Finset.mul_sum] at hs
    change (∑ i, b i*(uniform i)^2) ≤ B*normSq uniform at hs
    simpa only [uniform_normalized, mul_one] using hs
  have hmin := hg.2.2 uniform
  rw [uniform_normalized, mul_one] at hmin
  exact ⟨hpos, hmin.trans hu⟩

end
end SbtCosmo.Derivation.GroundComplexResidualBudget
