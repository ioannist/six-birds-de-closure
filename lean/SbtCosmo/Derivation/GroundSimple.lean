import SbtCosmo.Derivation.GroundSelector

/-! Simplicity of the actual lowest eigenspace, including signed eigenvectors. -/
namespace SbtCosmo.Derivation.GroundState
noncomputable section
open scoped BigOperators

theorem ground_abs {v u : Field} {e : ℝ} (hg : IsGround v u e) :
    IsGround v (fun i => |u i|) e := by
  have hn : normSq (fun i => |u i|) = 1 := (normSq_abs u).trans hg.1
  have he : energy v (fun i => |u i|) = e := by
    have hl := hg.2.2 (fun i => |u i|)
    rw [hn, mul_one] at hl
    exact le_antisymm ((energy_abs_le v u).trans_eq (ground_energy hg)) hl
  have hm : IsMinOn (energy v) unitFields (fun i => |u i|) := by
    intro w hw
    have hl := hg.2.2 w
    change normSq w = 1 at hw
    simpa [he, hw] using hl
  refine ⟨hn, ?_, hg.2.2⟩
  simpa [he] using minimizer_eigen hn hm

theorem ground_coordinate_ne_zero {v u : Field} {e : ℝ}
    (hg : IsGround v u e) (i : Fin 8) : u i ≠ 0 := by
  have ha := ground_abs hg
  have hp := normalized_nonnegative_eigen_positive (fun j => abs_nonneg (u j)) ha.2.1 ha.1 i
  exact abs_pos.mp hp

/-- A lowest eigenvector with a zero coordinate must vanish, even without a sign premise. -/
theorem lowest_eigen_zero_forces_zero {v u w : Field} {e : ℝ}
    (hg : IsGround v u e) (hw : ∀ j, hamiltonian v w j = e * w j)
    {i : Fin 8} (hi : w i = 0) : w = 0 := by
  by_contra hne
  have hpos : 0 < normSq w :=
    lt_of_le_of_ne (normSq_nonneg w) (fun h => hne ((normSq_zero_iff w).mp h.symm))
  let c : ℝ := (Real.sqrt (normSq w))⁻¹
  let z : Field := fun j => c * w j
  have hz : IsGround v z e := by
    refine ⟨?_, ?_, hg.2.2⟩
    · change normSq (fun j => c * w j) = 1
      rw [normSq_homogeneous]
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt hpos.le]
      exact inv_mul_cancel₀ hpos.ne'
    · intro j
      have hj := hw j
      dsimp [z, hamiltonian] at *
      linear_combination c * hj
  exact ground_coordinate_ne_zero hz i (by simp [z, hi])

/-- Every real lowest eigenvector is a scalar multiple of any unit ground vector. -/
theorem real_lowest_eigen_span {v u w : Field} {e : ℝ}
    (hg : IsGround v u e) (hw : ∀ j, hamiltonian v w j = e * w j) :
    ∃ c : ℝ, w = fun j => c * u j := by
  let c : ℝ := w 0 / u 0
  let z : Field := fun j => w j - c * u j
  have hez : ∀ j, hamiltonian v z j = e * z j := by
    intro j
    have h1 := hw j
    have h2 := hg.2.1 j
    dsimp [z, hamiltonian] at *
    linear_combination h1 - c * h2
  have hz0 : z 0 = 0 := by
    dsimp [z, c]
    rw [div_mul_cancel₀ _ (ground_coordinate_ne_zero hg 0), sub_self]
  have hz := lowest_eigen_zero_forces_zero hg hez hz0
  refine ⟨c, ?_⟩
  funext j
  have hj := congrFun hz j
  exact sub_eq_zero.mp hj

end
end SbtCosmo.Derivation.GroundState
