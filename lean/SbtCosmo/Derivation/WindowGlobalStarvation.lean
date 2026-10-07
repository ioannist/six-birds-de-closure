import SbtCosmo.Derivation.GrowthStarvationCertified
import SbtCosmo.Derivation.WindowEternalPatchCounts

/-! All-time starvation of every actual original patch, at a modest sufficient cutoff.
The N=32 and N=128 populations are separately realized; no tag or amplitude coupling is used. -/
namespace SbtCosmo.Derivation.WindowGlobalStarvation
noncomputable section
open GrowthScaleReturn GrowthPopulation GrowthStarvationCertified
attribute [local instance] Classical.propDecidable

theorem rational_margin_original (j : Fin 12) :
    485 * max (WindowSampleData.maximumFalseRat j) (WindowSampleData.maximumTrueRat j) <
      WindowSampleData.deltaRat := by
  revert j
  decide +kernel

theorem amplitude_margin_original (j : Fin 12) (i : Fin 64) : 485 * WindowSample.amplitude j i < WindowSample.delta := by
  have hb : WindowSample.amplitude j i ≤ max (WindowSample.maximumFalse j) (WindowSample.maximumTrue j) := by
    cases ht : WindowSampleData.tag j i
    · exact ((WindowSample.sampled_maxima j).2.2.2.1.2 i ht).trans (le_max_left _ _)
    · exact ((WindowSample.sampled_maxima j).2.2.2.2.2 i ht).trans (le_max_right _ _)
  have hm : 485 * max (WindowSample.maximumFalse j) (WindowSample.maximumTrue j) < WindowSample.delta := by
    dsimp only [WindowSample.maximumFalse, WindowSample.maximumTrue, WindowSample.delta]
    exact_mod_cast rational_margin_original j
  exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_lt hm


theorem rational_margin_robustness (v : Bool) (j : Fin 12) :
    485 * max (WindowPatchCountData.maximumFalseRat v j) (WindowPatchCountData.maximumTrueRat v j) <
      WindowSampleData.deltaRat := by
  revert v j
  decide +kernel

theorem amplitude_margin_robustness (v : Bool) (j : Fin 12) (i : Fin (WindowPatchCountData.patchCount v)) :
    485 * WindowPatchCounts.amplitude v j i < WindowPatchCounts.delta := by
  have hb : WindowPatchCounts.amplitude v j i ≤ max (WindowPatchCounts.maximumFalse v j) (WindowPatchCounts.maximumTrue v j) := by
    cases ht : WindowPatchCountData.tag v j i
    · exact ((WindowPatchCounts.sampled_maxima v j).2.2.2.1.2 i ht).trans (le_max_left _ _)
    · exact ((WindowPatchCounts.sampled_maxima v j).2.2.2.2.2 i ht).trans (le_max_right _ _)
  have hm : 485 * max (WindowPatchCounts.maximumFalse v j) (WindowPatchCounts.maximumTrue v j) < WindowPatchCounts.delta := by
    dsimp only [WindowPatchCounts.maximumFalse, WindowPatchCounts.maximumTrue, WindowPatchCounts.delta]
    exact_mod_cast rational_margin_robustness v j
  exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_lt hm


theorem no_original_patch_ever {lam : ℝ} (hlam : (32 : ℝ) ≤ lam)
    (j : Fin 12) (i : Fin 64) :
    ¬ ∃ a : ℝ, (1 / 1000 : ℝ) ≤ a ∧ WindowSample.delta ≤
      WindowSample.amplitude j i * nativeGrowth (1 / 1000) lam a :=
  patch_never_collapses hlam ((WindowSample.sampled_maxima j).1 i) (amplitude_margin_original j i)

theorem no_robustness_patch_ever (v : Bool) {lam : ℝ} (hlam : (32 : ℝ) ≤ lam)
    (j : Fin 12) (i : Fin (WindowPatchCountData.patchCount v)) :
    ¬ ∃ a : ℝ, (1 / 1000 : ℝ) ≤ a ∧ WindowPatchCounts.delta ≤
      WindowPatchCounts.amplitude v j i * nativeGrowth (1 / 1000) lam a :=
  patch_never_collapses hlam ((WindowPatchCounts.sampled_maxima v j).1 i) (amplitude_margin_robustness v j i)

theorem no_original_record {lam A : ℝ} (hlam : (32 : ℝ) ≤ lam) (j : Fin 12) :
    ¬ nativeRecord (WindowSample.amplitude j) (WindowSampleData.tag j)
      (1 / 1000) A WindowSample.delta lam :=
  no_native_record hlam (WindowSample.sampled_maxima j).1 (amplitude_margin_original j)

theorem no_robustness_record (v : Bool) {lam A : ℝ} (hlam : (32 : ℝ) ≤ lam) (j : Fin 12) :
    ¬ nativeRecord (WindowPatchCounts.amplitude v j) (WindowPatchCountData.tag v j)
      (1 / 1000) A WindowPatchCounts.delta lam :=
  no_native_record hlam (WindowPatchCounts.sampled_maxima v j).1 (amplitude_margin_robustness v j)

theorem original_record_count_zero {lam A : ℝ} (hlam : (32 : ℝ) ≤ lam) :
    (Finset.univ.filter (fun j => nativeRecord (WindowSample.amplitude j)
      (WindowSampleData.tag j) (1 / 1000) A WindowSample.delta lam)).card = 0 := by
  simp only [no_original_record hlam, Finset.filter_false, Finset.card_empty]

theorem robustness_record_count_zero (v : Bool) {lam A : ℝ} (hlam : (32 : ℝ) ≤ lam) :
    (Finset.univ.filter (fun j => nativeRecord (WindowPatchCounts.amplitude v j)
      (WindowPatchCountData.tag v j) (1 / 1000) A WindowPatchCounts.delta lam)).card = 0 := by
  simp only [no_robustness_record v hlam, Finset.filter_false, Finset.card_empty]

end
end SbtCosmo.Derivation.WindowGlobalStarvation
