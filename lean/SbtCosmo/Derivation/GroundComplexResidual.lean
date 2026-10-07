import SbtCosmo.Derivation.GroundComplexEuclidean

/-! Exact Euclidean bounds for the original cycle Hamiltonian and its Rayleigh
residual. All operator budgets are derived from the actual potential entries. -/
namespace SbtCosmo.Derivation.GroundComplexResidual
noncomputable section
set_option maxHeartbeats 8000000
open GroundState GroundNativePhase GroundComplexEuclidean
open scoped BigOperators

def shifted (b : Field) (e : ℝ) (z : ComplexField) : ComplexField :=
  complexHamiltonian b z-(e : ℂ) • z

theorem overlap_add_left (z w q : ComplexField) : overlap (z+w) q = overlap z q+overlap w q := by
  simp [overlap, add_mul, Finset.sum_add_distrib]

theorem overlap_sub_right (z w q : ComplexField) : overlap z (w-q) = overlap z w-overlap z q := by
  simp [overlap, mul_sub, Finset.sum_sub_distrib]

theorem overlap_smul_right (z w : ComplexField) (c : ℂ) : overlap z (c • w) = c*overlap z w := by
  simp only [overlap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem overlap_smul_left (z w : ComplexField) (c : ℂ) : overlap (c • z) w = star c*overlap z w := by
  simp only [overlap, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem overlap_self (z : ComplexField) : overlap z z = (complexNormSq z : ℂ) := by
  simp only [overlap, complexNormSq, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rfl

theorem hamiltonian_symmetric (b : Field) (z w : ComplexField) :
    overlap z (complexHamiltonian b w) = overlap (complexHamiltonian b z) w := by
  apply Complex.ext <;>
    simp [overlap, complexHamiltonian, next, prev, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem shifted_symmetric (b : Field) (e : ℝ) (z w : ComplexField) :
    overlap z (shifted b e w) = overlap (shifted b e z) w := by
  rw [shifted, overlap_sub_right, overlap_smul_right, hamiltonian_symmetric]
  have hs : overlap (shifted b e z) w = overlap (complexHamiltonian b z) w-
      (e : ℂ)*overlap z w := by
    simp [shifted, overlap, star_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  exact hs.symm

theorem shifted_sub (b : Field) (e : ℝ) (z w : ComplexField) :
    shifted b e (z-w) = shifted b e z-shifted b e w := by
  funext i; simp [shifted, complexHamiltonian]; ring

theorem l2_shift_next (z : ComplexField) : l2 (fun i => z (next i)) = l2 z := by
  have he : complexNormSq (fun i => z (next i)) = complexNormSq z := by
    simp [complexNormSq, next, Fin.sum_univ_succ]; ring
  nlinarith [l2_sq (fun i => z (next i)), l2_sq z, l2_nonneg (fun i => z (next i)), l2_nonneg z]

theorem l2_shift_prev (z : ComplexField) : l2 (fun i => z (prev i)) = l2 z := by
  have he : complexNormSq (fun i => z (prev i)) = complexNormSq z := by
    simp [complexNormSq, prev, Fin.sum_univ_succ]; ring
  nlinarith [l2_sq (fun i => z (prev i)), l2_sq z, l2_nonneg (fun i => z (prev i)), l2_nonneg z]

theorem l2_diagonal {c : Field} {B : ℝ} (hB : 0 ≤ B) (hc : ∀ i, |c i| ≤ B) (z : ComplexField) :
    l2 (fun i => (c i : ℂ)*z i) ≤ B*l2 z := by
  have he : complexNormSq (fun i => (c i : ℂ)*z i) ≤ B^2*complexNormSq z := by
    rw [complexNormSq, complexNormSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb : (c i)^2 ≤ B^2 := by nlinarith [hc i, sq_abs (c i), abs_nonneg (c i)]
    simpa only [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] using
      mul_le_mul_of_nonneg_right hb (Complex.normSq_nonneg (z i))
  rw [← l2_sq, ← l2_sq] at he
  exact (sq_le_sq₀ (l2_nonneg _) (mul_nonneg hB (l2_nonneg z))).mp
    (by simpa only [mul_pow] using he)

theorem shifted_l2_bound {b : Field} {e : ℝ} (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 2/5)
    (he : 0 ≤ e ∧ e ≤ 2/5) (z : ComplexField) : l2 (shifted b e z) ≤ (12/5)*l2 z := by
  have hd : l2 (fun i => ((1+b i-e : ℝ) : ℂ)*z i) ≤ (7/5)*l2 z :=
    l2_diagonal (by norm_num) (fun i => abs_le.mpr ⟨by linarith [(hb i).1], by linarith [(hb i).2]⟩) z
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

theorem ground_energy_budget {b g : Field} {e : ℝ} (hg : IsGround b g e)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 2/5) : 0 ≤ e ∧ e ≤ 2/5 := by
  have hpos : 0 ≤ energy b g := by
    rw [energy_identity]
    exact add_nonneg (kineticEnergy_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (hb i).1 (sq_nonneg _))
  rw [ground_energy hg] at hpos
  have hu : energy b uniform ≤ 2/5 := by
    rw [energy_identity]
    have hk : kineticEnergy uniform = 0 := by simp [kineticEnergy, uniform]
    rw [hk, zero_add]
    have hs := Finset.sum_le_sum (fun (i : Fin 8) (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (hb i).2 (sq_nonneg (uniform i)))
    rw [← Finset.mul_sum] at hs
    change (∑ i, b i*(uniform i)^2) ≤ (2/5)*normSq uniform at hs
    simpa only [uniform_normalized, mul_one] using hs
  have hmin := hg.2.2 uniform
  rw [uniform_normalized, mul_one] at hmin
  exact ⟨hpos, hmin.trans hu⟩

theorem rayleigh_error {b : Field} {e M : ℝ} {g z : ComplexField}
    (hg : ∀ i, complexHamiltonian b g i = (e : ℂ)*g i)
    (hz : complexNormSq z = 1) (hM : ∀ w, l2 (shifted b e w) ≤ M*l2 w) :
    |complexEnergy b z-e| ≤ M*(l2 (z-g))^2 := by
  let d := z-g
  have hzero : shifted b e g = 0 := by funext i; simp [shifted, hg]
  have he : shifted b e z = shifted b e d := by dsimp only [d]; rw [shifted_sub, hzero, sub_zero]
  have hc : overlap g (shifted b e d) = 0 := by
    rw [shifted_symmetric, hzero]; simp [overlap]
  have hid : overlap z (shifted b e z) = overlap d (shifted b e d) := by
    rw [he]
    have hd : z = d+g := by dsimp only [d]; abel
    rw [hd, overlap_add_left, hc, add_zero]
  have henergy : complexEnergy b z-e = (overlap d (shifted b e d)).re := by
    rw [← hid, shifted, overlap_sub_right, overlap_smul_right, overlap_self, hz]
    simp [complexEnergy, overlap]
  rw [henergy]
  calc
    _ ≤ ‖overlap d (shifted b e d)‖ := Complex.abs_re_le_norm _
    _ ≤ l2 d*l2 (shifted b e d) := overlap_bound _ _
    _ ≤ l2 d*(M*l2 d) := mul_le_mul_of_nonneg_left (hM d) (l2_nonneg d)
    _ = _ := by ring

theorem eigen_residual_bound {b : Field} {e M : ℝ} {g z : ComplexField}
    (hg : ∀ i, complexHamiltonian b g i = (e : ℂ)*g i)
    (hz : complexNormSq z = 1) (hM : ∀ w, l2 (shifted b e w) ≤ M*l2 w) :
    l2 (shifted b (complexEnergy b z) z) ≤ M*l2 (z-g)+M*(l2 (z-g))^2 := by
  have hzero : shifted b e g = 0 := by funext i; simp [shifted, hg]
  have he : shifted b e z = shifted b e (z-g) := by rw [shifted_sub, hzero, sub_zero]
  have hx : shifted b (complexEnergy b z) z = shifted b e z-((complexEnergy b z-e : ℝ) : ℂ) • z := by
    funext i; simp [shifted]; ring
  rw [hx, he]
  have hh := l2_sub (shifted b e z) (((complexEnergy b z-e : ℝ) : ℂ) • z)
  rw [l2_smul, l2_unit hz, mul_one, Complex.norm_real, Real.norm_eq_abs, he] at hh
  have hr := rayleigh_error hg hz hM
  linarith [hM (z-g)]

end
end SbtCosmo.Derivation.GroundComplexResidual
