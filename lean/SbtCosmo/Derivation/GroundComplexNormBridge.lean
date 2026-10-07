import SbtCosmo.Derivation.GroundComplexEuclidean

namespace SbtCosmo.Derivation.GroundComplexNormBridge
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open GroundState GroundNativePhase GroundComplexEuclidean
open scoped BigOperators

theorem stateNormSq_le (x : State) : stateNormSq x ≤ 16*‖x‖^2 := by
  have hR (i : Fin 8) : |x.1 i| ≤ ‖x‖ := by
    have hp : |x.1 i| ≤ ‖x.1‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.1 i
    exact hp.trans (by rw [Prod.norm_def]; exact le_max_left _ _)
  have hI (i : Fin 8) : |x.2 i| ≤ ‖x‖ := by
    have hp : |x.2 i| ≤ ‖x.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.2 i
    exact hp.trans (by rw [Prod.norm_def]; exact le_max_right _ _)
  have hr := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 8) _ =>
    (sq_le_sq₀ (abs_nonneg (x.1 i)) (norm_nonneg x)).mpr (hR i))
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin 8) _ =>
    (sq_le_sq₀ (abs_nonneg (x.2 i)) (norm_nonneg x)).mpr (hI i))
  simp only [sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr hi
  norm_num only [Nat.cast_ofNat] at hr hi
  dsimp only [stateNormSq, normSq]
  linarith

theorem l2_pack_le (x : State) : l2 (pack x) ≤ 4*‖x‖ := by
  have he := l2_sq (pack x)
  rw [norm_pack] at he
  nlinarith [stateNormSq_le x, l2_nonneg (pack x), norm_nonneg x]

theorem l2_realEmbed_le (u : Field) : l2 (realEmbed u) ≤ 4*‖u‖ := by
  have h := l2_pack_le (u, 0)
  have he : pack (u, 0) = realEmbed u := by rfl
  rw [he, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg u)] at h
  exact h

end
end SbtCosmo.Derivation.GroundComplexNormBridge
