import SbtCosmo.Derivation.GroundSimple
import SbtCosmo.Derivation.GroundAlternating
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Earned invertibility of the actual normalized ground eigen equation.
No spectral gap, inverse or selector derivative is supplied as an input. -/
namespace SbtCosmo.Derivation.GroundBorder
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
open GroundState

abbrev Point := Field × ℝ
def dot (u w : Field) : ℝ := ∑ i, u i * w i
def shifted (v : Field) (e : ℝ) (w : Field) : Field := fun i => hamiltonian v w i - e * w i

theorem dot_self (u : Field) : dot u u = normSq u := by
  simp [dot, normSq, pow_two]

theorem dot_smul_right (u w : Field) (c : ℝ) : dot u (fun i => c * w i) = c * dot u w := by
  simp [dot, Finset.mul_sum, mul_left_comm]

theorem dot_zero_right (u : Field) : dot u 0 = 0 := by simp [dot]
theorem dot_zero_left (u : Field) : dot 0 u = 0 := by simp [dot]

theorem shifted_symmetric (v u w : Field) (e : ℝ) :
    dot u (shifted v e w) = dot (shifted v e u) w := by
  simp only [dot, shifted, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [GroundAlternating.pairing_symmetric]
  congr 1 <;> apply Finset.sum_congr rfl
  all_goals intro i _; ring

def borderLM (v u : Field) (e : ℝ) : Point →ₗ[ℝ] Point where
  toFun y := (fun i => shifted v e y.1 i - y.2 * u i, dot u y.1)
  map_add' a b := by
    apply Prod.ext
    · funext i
      dsimp [shifted, hamiltonian]
      ring
    · simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    apply Prod.ext
    · funext i
      simp [shifted, hamiltonian, smul_eq_mul]
      ring
    · simp [dot, Finset.mul_sum, smul_eq_mul, mul_left_comm]

def border (v u : Field) (e : ℝ) : Point →L[ℝ] Point := (borderLM v u e).toContinuousLinearMap

theorem border_apply (v u : Field) (e : ℝ) (y : Point) :
    border v u e y = (fun i => shifted v e y.1 i - y.2 * u i, dot u y.1) := rfl

theorem border_kernel_trivial {v u : Field} {e : ℝ} (hg : IsGround v u e)
    {y : Point} (hy : border v u e y = 0) : y = 0 := by
  have he : shifted v e u = 0 := by
    funext i
    simp [shifted, hg.2.1 i]
  have hw : shifted v e y.1 = fun i => y.2 * u i := by
    funext i
    have h := congrArg (fun z : Point => z.1 i) hy
    exact sub_eq_zero.mp h
  have hd : dot u y.1 = 0 := congrArg Prod.snd hy
  have hs := shifted_symmetric v u y.1 e
  rw [he, hw, dot_zero_left, dot_smul_right, dot_self, hg.1, mul_one] at hs
  have heigen : ∀ i, hamiltonian v y.1 i = e * y.1 i := by
    intro i
    have h := congrFun hw i
    rw [hs, zero_mul] at h
    exact sub_eq_zero.mp h
  obtain ⟨c, hc⟩ := real_lowest_eigen_span hg heigen
  rw [hc, dot_smul_right, dot_self, hg.1, mul_one] at hd
  apply Prod.ext
  · funext i
    simp [hc, hd]
  · exact hs

theorem border_injective {v u : Field} {e : ℝ} (hg : IsGround v u e) :
    Function.Injective (border v u e) := by
  intro a b hab
  have hz : border v u e (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (border_kernel_trivial hg hz)

theorem border_bijective {v u : Field} {e : ℝ} (hg : IsGround v u e) :
    Function.Bijective (border v u e) := by
  have hi := border_injective hg
  exact ⟨hi, LinearMap.surjective_of_injective (f := (border v u e).toLinearMap) hi⟩

def groundPair (v : Field) : Point := (positiveGround v, energy v (positiveGround v))
def groundBorder (v : Field) : Point ≃L[ℝ] Point :=
  ContinuousLinearEquiv.ofBijective (border v (groundPair v).1 (groundPair v).2)
    (LinearMap.ker_eq_bot.mpr (border_bijective (positiveGround_spec v).2).1)
    (LinearMap.range_eq_top.mpr (border_bijective (positiveGround_spec v).2).2)

theorem groundBorder_apply (v : Field) (y : Point) :
    groundBorder v y = border v (groundPair v).1 (groundPair v).2 y := rfl

theorem continuous_groundPair : Continuous groundPair :=
  continuous_positiveGround.prodMk
    (continuous_joint_energy.comp (continuous_id.prodMk continuous_positiveGround))

end
end SbtCosmo.Derivation.GroundBorder
