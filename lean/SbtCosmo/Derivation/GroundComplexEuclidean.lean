import SbtCosmo.Derivation.GroundOriginalSeedFinite
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The source's full Euclidean complex norm and overlap, without changing the
coordinate sup norm on ComplexField used by earlier calculus. -/
namespace SbtCosmo.Derivation.GroundComplexEuclidean
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundNativeIteration
open scoped BigOperators ComplexOrder

def l2 (z : ComplexField) : ℝ := ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 8))‖

theorem l2_nonneg (z : ComplexField) : 0 ≤ l2 z := norm_nonneg _

theorem l2_sq (z : ComplexField) : (l2 z)^2 = complexNormSq z := by
  simp only [l2, EuclideanSpace.norm_sq_eq, complexNormSq, ← Complex.normSq_eq_norm_sq]

theorem l2_unit {z : ComplexField} (hz : complexNormSq z = 1) : l2 z = 1 := by
  nlinarith [l2_sq z, l2_nonneg z]

theorem l2_neg (z : ComplexField) : l2 (-z) = l2 z := norm_neg _

theorem l2_smul (c : ℂ) (z : ComplexField) : l2 (c • z) = ‖c‖*l2 z := by
  simpa only [l2, WithLp.toLp_smul] using norm_smul c (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 8))

theorem l2_add (z w : ComplexField) : l2 (z+w) ≤ l2 z+l2 w := norm_add_le _ _

theorem l2_sub_triangle (z w q : ComplexField) : l2 (z-q) ≤ l2 (z-w)+l2 (w-q) := by
  have h : z-q = (z-w)+(w-q) := by abel
  rw [h]; exact l2_add _ _

theorem overlap_inner (z w : ComplexField) : overlap z w =
    inner ℂ (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 8)) (WithLp.toLp 2 w) := by
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, overlap]
  apply Finset.sum_congr rfl
  intro i _; exact mul_comm _ _

theorem overlap_bound (z w : ComplexField) : ‖overlap z w‖ ≤ l2 z*l2 w := by
  rw [overlap_inner]; exact norm_inner_le_norm _ _

theorem distance_unit_identity {z w : ComplexField} (hz : complexNormSq z = 1)
    (hw : complexNormSq w = 1) : (l2 (z-w))^2 = 2-2*(overlap w z).re := by
  have h := norm_sub_sq (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 8)) (WithLp.toLp 2 z)
  rw [← overlap_inner] at h
  change (l2 (w-z))^2 = (l2 w)^2-2*(overlap w z).re+(l2 z)^2 at h
  have he : w-z = -(z-w) := by abel
  rw [he, l2_neg, l2_sq w, l2_sq z, hw, hz] at h
  linarith

theorem phase_unit {τ : ℝ} {g z : ComplexField} (hg : complexNormSq g = 1)
    (hτ : 0 ≤ τ) (ho : τ < ‖overlap g z‖) :
    complexNormSq (nativePhase τ g z) = 1 := by
  rw [nativePhase_ratio hτ ho]
  have hr : 0 < ‖overlap g z‖ := hτ.trans_lt ho
  have hc : ‖star (overlap g z)/(‖overlap g z‖ : ℂ)‖ = 1 := by
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have he : (fun i => (star (overlap g z)/(‖overlap g z‖ : ℂ))*g i) =
      (star (overlap g z)/(‖overlap g z‖ : ℂ)) • g := rfl
  rw [he, ← l2_sq, l2_smul, hc, l2_unit hg]; norm_num

theorem phase_distance {τ : ℝ} {g z : ComplexField} (hg : complexNormSq g = 1)
    (hz : complexNormSq z = 1) (hτ : 0 ≤ τ) (ho : τ < ‖overlap g z‖)
    (ha : 0 ≤ (overlap g z).re) :
    l2 (nativePhase τ g z-g) ≤ l2 (z-g) := by
  let c := overlap g z
  let r := ‖c‖
  let t : ℂ := star c/(r : ℂ)
  have hr : 0 < r := hτ.trans_lt ho
  have hru : r ≤ 1 := by simpa only [l2_unit hg, l2_unit hz, mul_one] using overlap_bound g z
  have ht : ‖t‖ = 1 := by
    dsimp only [t, r]
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hre : t.re = c.re/r := by simp [t, Complex.div_ofReal_re]
  have he : nativePhase τ g z-g = (t-1) • g := by
    rw [nativePhase_ratio hτ ho]
    funext i; change t*g i-g i = (t-1)*g i; ring
  have hs : (l2 (nativePhase τ g z-g))^2 = 2-2*c.re/r := by
    rw [he, l2_smul, l2_unit hg, mul_one, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub, Complex.normSq_eq_norm_sq, ht]
    simp only [one_pow, map_one, mul_one]
    rw [hre]; ring
  have hc : c.re ≤ c.re/r := by
    apply (le_div_iff₀ hr).mpr
    exact mul_le_of_le_one_right ha hru
  have hd := distance_unit_identity hz hg
  change (l2 (z-g))^2 = 2-2*c.re at hd
  simp only [div_eq_mul_inv] at hs hc
  nlinarith [l2_nonneg (nativePhase τ g z-g), l2_nonneg (z-g)]

theorem l2_sub (z w : ComplexField) : l2 (z-w) ≤ l2 z+l2 w := by
  simpa only [sub_eq_add_neg, l2_neg] using l2_add z (-w)

theorem phase_guard_of_distance {τ d : ℝ} {g z : ComplexField}
    (hg : complexNormSq g = 1) (hz : complexNormSq z = 1) (hd : l2 (z-g) ≤ d)
    (hd0 : 0 ≤ d) (hτ : τ < 1-d^2/2) : τ < ‖overlap g z‖ := by
  have he := distance_unit_identity hz hg
  have ha : 1-d^2/2 ≤ (overlap g z).re := by nlinarith [l2_nonneg (z-g)]
  exact hτ.trans_le (ha.trans (Complex.re_le_norm _))

theorem double_phase_gap {τ d : ℝ} {g z : ComplexField}
    (hg : complexNormSq g = 1) (hz : complexNormSq z = 1) (hd : l2 (z-g) ≤ d)
    (hd0 : 0 ≤ d) (hd1 : 2*d^2 ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1-2*d^2) :
    τ < ‖overlap g z‖ ∧ τ < ‖overlap (nativePhase τ g z) z‖ ∧
      l2 (nativePhase τ (nativePhase τ g z) z-z) ≤ 4*d := by
  have ho : τ < ‖overlap g z‖ := phase_guard_of_distance hg hz hd hd0 (by nlinarith)
  have hre : 0 ≤ (overlap g z).re := by
    have he := distance_unit_identity hz hg
    nlinarith [l2_nonneg (z-g)]
  have hw := phase_unit hg hτ0 ho
  have hdist := (phase_distance hg hz hτ0 ho hre).trans hd
  have hr : l2 (z-nativePhase τ g z) ≤ 2*d := by
    have h := l2_sub_triangle z g (nativePhase τ g z)
    have he : g-nativePhase τ g z = -(nativePhase τ g z-g) := by abel
    rw [he, l2_neg] at h
    linarith
  have ho2 : τ < ‖overlap (nativePhase τ g z) z‖ :=
    phase_guard_of_distance hw hz hr (by linarith) (by nlinarith)
  have hre2 : 0 ≤ (overlap (nativePhase τ g z) z).re := by
    have he := distance_unit_identity hz hw
    nlinarith [l2_nonneg (z-nativePhase τ g z)]
  have hdist2 := phase_distance hw hz hτ0 ho2 hre2
  refine ⟨ho, ho2, ?_⟩
  have h := l2_sub_triangle (nativePhase τ (nativePhase τ g z) z) (nativePhase τ g z) z
  have he : nativePhase τ g z-z = -(z-nativePhase τ g z) := by abel
  rw [he, l2_neg] at h
  linarith

end
end SbtCosmo.Derivation.GroundComplexEuclidean
