import SbtCosmo.Derivation.GrowthQuadratureSharp
import SbtCosmo.Derivation.RobustEdgeLowerData
import SbtCosmo.Derivation.RobustEdgePrefixData
import SbtCosmo.Derivation.RobustEdgeUpperData

/-! Kernel-certified fixed quadratures used after exact scale covariance. -/
namespace SbtCosmo.Derivation.RobustEdgeQuadrature
noncomputable section
open Set GrowthQuadrature

theorem lower_grid {lam cap : ℚ} {n : ℕ} {a lo : ℕ → ℚ}
    (hlam : 1 ≤ lam)
    (hcell : ∀ i : Fin n, 0 < a i ∧ a i ≤ a (i+1) ∧ 0 ≤ lo i ∧
      (lo i)^2*(1+lam*(a i)^3)^3 ≤ (a i)^3 ∧
      (lo i)^2*(1+lam*(a (i+1))^3)^3 ≤ (a (i+1))^3)
    (hsum : cap ≤ ∑ i ∈ Finset.range n,(a (i+1)-a i)*lo i) :
    (cap : ℝ) ≤ integral lam (a 0) (a n) := by
  have hlarge : (1:ℝ) ≤ lam := by exact_mod_cast hlam
  have hl : (0:ℝ) < lam := by linarith
  have hb := GrowthQuadratureSharp.integral_grid_bounds (n := n)
    (a := fun i => (a i : ℝ)) (lo := fun i => (lo i : ℝ)) (hi := fun _ => 1)
    hl.le (by
      intro i hi
      have hc : (0:ℝ) < a i ∧ (a i : ℝ) ≤ a (i+1) ∧ (0:ℝ) ≤ lo i ∧
          (lo i : ℝ)^2*(1+(lam:ℝ)*(a i : ℝ)^3)^3 ≤ (a i : ℝ)^3 ∧
          (lo i : ℝ)^2*(1+(lam:ℝ)*(a (i+1) : ℝ)^3)^3 ≤ (a (i+1) : ℝ)^3 := by
        exact_mod_cast hcell ⟨i,hi⟩
      refine ⟨hc.1,hc.2.1,?_⟩
      intro x hx
      have hx0 : 0 ≤ x := hc.1.le.trans hx.1
      refine ⟨GrowthQuadratureSharp.density_cell_lower hl.le hc.1.le hx hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2,?_⟩
      exact GrowthQuadratureSharp.density_global_upper hl hx0 (by norm_num)
        (by nlinarith : (4:ℝ) ≤ 27*(lam:ℝ)*1^2))
  have hs : (cap : ℝ) ≤ ∑ i ∈ Finset.range n,((a (i+1) : ℝ)-a i)*(lo i : ℝ) := by
    exact_mod_cast hsum
  exact hs.trans hb.1

theorem upper_grid {lam cap : ℚ} {n : ℕ} {a hi : ℕ → ℚ}
    (hlam : 0 < lam)
    (hcell : ∀ i : Fin n, 0 < a i ∧ a i ≤ a (i+1) ∧ 0 ≤ hi i ∧
      ((2*lam*(a (i+1))^3 ≤ 1 ∧ (a (i+1))^3 ≤ (hi i)^2*(1+lam*(a (i+1))^3)^3) ∨
       (1 ≤ 2*lam*(a i)^3 ∧ (a i)^3 ≤ (hi i)^2*(1+lam*(a i)^3)^3) ∨
       4 ≤ 27*lam*(hi i)^2))
    (hsum : (∑ i ∈ Finset.range n,(a (i+1)-a i)*hi i) ≤ cap) :
    integral lam (a 0) (a n) ≤ (cap : ℝ) := by
  have hl : (0:ℝ) < lam := by exact_mod_cast hlam
  have hb := GrowthQuadratureSharp.integral_grid_bounds (n := n)
    (a := fun i => (a i : ℝ)) (lo := fun _ => 0) (hi := fun i => (hi i : ℝ)) hl.le (by
      intro i hn
      have hc : (0:ℝ) < a i ∧ (a i : ℝ) ≤ a (i+1) ∧ (0:ℝ) ≤ hi i ∧
          ((2*(lam:ℝ)*(a (i+1) : ℝ)^3 ≤ 1 ∧ (a (i+1) : ℝ)^3 ≤ (hi i : ℝ)^2*(1+(lam:ℝ)*(a (i+1) : ℝ)^3)^3) ∨
           (1 ≤ 2*(lam:ℝ)*(a i : ℝ)^3 ∧ (a i : ℝ)^3 ≤ (hi i : ℝ)^2*(1+(lam:ℝ)*(a i : ℝ)^3)^3) ∨
           4 ≤ 27*(lam:ℝ)*(hi i : ℝ)^2) := by exact_mod_cast hcell ⟨i,hn⟩
      refine ⟨hc.1,hc.2.1,?_⟩
      intro x hx
      exact ⟨density_nonnegative,
        GrowthQuadratureSharp.density_cell_upper hl hc.1.le hx hc.2.2.1 hc.2.2.2⟩)
  have hs : (∑ i ∈ Finset.range n,((a (i+1) : ℝ)-a i)*(hi i : ℝ)) ≤ (cap : ℝ) := by
    exact_mod_cast hsum
  exact hb.2.trans hs

theorem lower_integral : (224:ℝ)/1000 ≤ integral 3 (1/200) 5 := by
  have h := lower_grid (by norm_num : (1:ℚ) ≤ 3/1) RobustEdgeLowerData.cells RobustEdgeLowerData.integral_sum
  rw [RobustEdgeLowerData.grid_endpoints.1,RobustEdgeLowerData.grid_endpoints.2] at h
  norm_num at h ⊢
  exact h

theorem prefix_integral : (1909:ℝ)/10000 ≤ integral (7/2) (1/200) (8/3) := by
  have h := lower_grid (by norm_num : (1:ℚ) ≤ 7/2) RobustEdgePrefixData.cells RobustEdgePrefixData.integral_sum
  rw [RobustEdgePrefixData.grid_endpoints.1,RobustEdgePrefixData.grid_endpoints.2] at h
  norm_num at h ⊢
  exact h

theorem upper_integral : integral (7/2) (1/4000) 100 ≤ (2035:ℝ)/10000 := by
  have h := upper_grid (by norm_num : (0:ℚ) < 7/2) RobustEdgeUpperData.cells RobustEdgeUpperData.integral_sum
  rw [RobustEdgeUpperData.grid_endpoints.1,RobustEdgeUpperData.grid_endpoints.2] at h
  norm_num at h ⊢
  exact h

end
end SbtCosmo.Derivation.RobustEdgeQuadrature
