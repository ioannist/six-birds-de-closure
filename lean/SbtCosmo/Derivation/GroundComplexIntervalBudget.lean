import SbtCosmo.Derivation.GroundComplexResidualBudget
/-! Euclidean shifted-Hamiltonian bounds for arbitrary signed potential intervals. -/
namespace SbtCosmo.Derivation.GroundComplexIntervalBudget
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
open GroundState GroundNativePhase GroundComplexEuclidean GroundComplexResidual
open scoped BigOperators

theorem shifted_l2_bound {b : Field} {e A B : ℝ}
    (hb : ∀ i, A ≤ b i ∧ b i ≤ B) (he : A ≤ e ∧ e ≤ B) (z : ComplexField) :
    l2 (shifted b e z) ≤ (2+(B-A))*l2 z := by
  have hAB : A ≤ B := (hb 0).1.trans (hb 0).2
  have h := GroundComplexResidualBudget.shifted_l2_bound
    (b := fun i => b i-A) (e := e-A) (B := B-A) (by linarith)
    (fun i => ⟨by linarith [(hb i).1],by linarith [(hb i).2]⟩)
    ⟨by linarith,by linarith⟩ z
  have hid : shifted (fun i => b i-A) (e-A) z = shifted b e z := by
    funext i
    simp [shifted,complexHamiltonian]
    ring
  rw [hid] at h
  exact h

theorem ground_energy_budget {b g : Field} {e A B : ℝ} (hg : IsGround b g e)
    (hb : ∀ i, A ≤ b i ∧ b i ≤ B) : A ≤ e ∧ e ≤ B := by
  have hl : A ≤ energy b g := by
    rw [energy_identity]
    have hs := Finset.sum_le_sum (fun (i : Fin 8) (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (hb i).1 (sq_nonneg (g i)))
    rw [← Finset.mul_sum] at hs
    change A*normSq g ≤ ∑ i, b i*(g i)^2 at hs
    rw [hg.1,mul_one] at hs
    linarith [kineticEnergy_nonneg g]
  rw [ground_energy hg] at hl
  have hu : energy b uniform ≤ B := by
    rw [energy_identity]
    have hk : kineticEnergy uniform = 0 := by simp [kineticEnergy,uniform]
    rw [hk,zero_add]
    have hs := Finset.sum_le_sum (fun (i : Fin 8) (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (hb i).2 (sq_nonneg (uniform i)))
    rw [← Finset.mul_sum] at hs
    change (∑ i, b i*(uniform i)^2) ≤ B*normSq uniform at hs
    simpa only [uniform_normalized,mul_one] using hs
  have hm := hg.2.2 uniform
  rw [uniform_normalized,mul_one] at hm
  exact ⟨hl,hm.trans hu⟩
end
end SbtCosmo.Derivation.GroundComplexIntervalBudget
