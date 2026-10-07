import SbtCosmo.Derivation.WindowSampleData

/-! Exact count and tag certificates for the unchanged original seed 1100 population. -/
namespace SbtCosmo.Derivation.WindowErasureData
open WindowSampleData
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def collapsedRat (D : ℚ) (i : Fin 64) : Prop := deltaRat ≤ amplitudeRat 0 i * D
instance (D : ℚ) (i : Fin 64) : Decidable (collapsedRat D i) :=
  inferInstanceAs (Decidable (deltaRat ≤ amplitudeRat 0 i * D))

theorem count_at_lower : (Finset.univ.filter (collapsedRat 17000)).card = 58 := by
  decide +kernel

theorem gap_certificate : ∀ i : Fin 64, collapsedRat 17000 i ↔ collapsedRat 26000 i := by
  decide +kernel

theorem tags_at_lower : tag 0 54 = false ∧ collapsedRat 17000 54 ∧
    tag 0 58 = true ∧ collapsedRat 17000 58 := by
  decide +kernel

end SbtCosmo.Derivation.WindowErasureData
