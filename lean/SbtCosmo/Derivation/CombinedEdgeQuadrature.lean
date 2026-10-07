import SbtCosmo.Derivation.RobustEdgeQuadrature
import SbtCosmo.Derivation.CombinedEdgeLowerData
import SbtCosmo.Derivation.CombinedEdgePrefixData
import SbtCosmo.Derivation.CombinedEdgeUpperData

/-! Exact whole-cell quadratures for the full combined rescaling range. -/
namespace SbtCosmo.Derivation.CombinedEdgeQuadrature
noncomputable section
open GrowthQuadrature RobustEdgeQuadrature

theorem lower_integral : (245:ℝ)/1000 ≤ integral (5/2) (3/500) 4 := by
  have h := lower_grid (by norm_num : (1:ℚ) ≤ 5/2) CombinedEdgeLowerData.cells CombinedEdgeLowerData.integral_sum
  rw [CombinedEdgeLowerData.grid_endpoints.1,CombinedEdgeLowerData.grid_endpoints.2] at h
  norm_num at h ⊢
  exact h

theorem prefix_integral : (1908:ℝ)/10000 ≤ integral (7/2) (3/500) (8/3) := by
  have h := lower_grid (by norm_num : (1:ℚ) ≤ 7/2) CombinedEdgePrefixData.cells CombinedEdgePrefixData.integral_sum
  rw [CombinedEdgePrefixData.grid_endpoints.1,CombinedEdgePrefixData.grid_endpoints.2] at h
  norm_num at h ⊢
  exact h

theorem upper_integral : integral (7/2) (1/5000) 120 ≤ (2036:ℝ)/10000 := by
  have h := upper_grid (by norm_num : (0:ℚ) < 7/2) CombinedEdgeUpperData.cells CombinedEdgeUpperData.integral_sum
  rw [CombinedEdgeUpperData.grid_endpoints.1,CombinedEdgeUpperData.grid_endpoints.2] at h
  norm_num at h ⊢
  exact h

end
end SbtCosmo.Derivation.CombinedEdgeQuadrature
