import SbtCosmo.Derivation.WindowPatchCountData

/-! Exact first-ANY-patch thresholds of the separately realized N32/N128 inputs.
No data are resampled, rescaled, or identified with the original N64 inputs. -/
namespace SbtCosmo.Derivation.WindowPatchCountFirstData
open WindowPatchCountData
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def firstThresholdRat (v : Bool) (j : Fin 12) : ℚ :=
  WindowSampleData.deltaRat / max (maximumFalseRat v j) (maximumTrueRat v j)
def scaleRat (v : Bool) : ℚ := aggregateRat v / 965

theorem rational_scale_bounds : ∀ v : Bool, (1 : ℚ)/5 < scaleRat v ∧ scaleRat v < 4 := by
  decide +kernel

theorem rational_scale_tight : (129 : ℚ)/100 < scaleRat false ∧ scaleRat false < 131/100 ∧
    83/100 < scaleRat true ∧ scaleRat true < 84/100 := by
  decide +kernel

theorem rational_first_bounds : ∀ (v : Bool) (j : Fin 12),
    1 < firstThresholdRat v j ∧ firstThresholdRat v j < 2000 ∧
      450*scaleRat v < firstThresholdRat v j ∧ firstThresholdRat v j < 897*scaleRat v := by
  decide +kernel

/-- The original N64 lower bound cannot be transferred to every N32 seed. -/
theorem rational_original_lower_fails : ∃ j : Fin 12,
    firstThresholdRat false j ≤ 500*scaleRat false := by
  decide +kernel

end SbtCosmo.Derivation.WindowPatchCountFirstData
