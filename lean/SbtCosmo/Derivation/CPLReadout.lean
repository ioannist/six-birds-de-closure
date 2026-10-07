import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
The actual CPL chart used by `de_audit_run.b1b_chart`, on z > -1.
The positive additive density and the fluid log-derivative chart encode the
same declared expansion history. This establishes representation regularity,
not ghost absence, dynamical stability, or a physical closure interpretation.
-/
namespace SbtCosmo.Derivation.CPLReadout

noncomputable section

def exponent (w0 wa z : ℝ) : ℝ :=
  3 * (1 + w0 + wa) * Real.log (1 + z) - 3 * wa * z / (1 + z)

def density (amplitude w0 wa z : ℝ) : ℝ :=
  amplitude * Real.exp (exponent w0 wa z)

def fluidW (w0 wa z : ℝ) : ℝ := w0 + wa * z / (1 + z)

def expansionSquared (matter radiation amplitude w0 wa z : ℝ) : ℝ :=
  matter * (1 + z)^3 + radiation * (1 + z)^4 + density amplitude w0 wa z

theorem density_positive {amplitude : ℝ} (ha : 0 < amplitude) (w0 wa z : ℝ) :
    0 < density amplitude w0 wa z := by
  exact mul_pos ha (Real.exp_pos _)

/-- Bridge to the product/power formula implemented by `_e_z`. -/
theorem density_eq_cpl_product (amplitude w0 wa : ℝ) {z : ℝ} (hz : -1 < z) :
    density amplitude w0 wa z =
      amplitude * (1 + z) ^ (3 * (1 + w0 + wa)) *
        Real.exp (-3 * wa * z / (1 + z)) := by
  rw [Real.rpow_def_of_pos (show 0 < 1 + z by linarith)]
  unfold density
  rw [show exponent w0 wa z = Real.log (1 + z) * (3 * (1 + w0 + wa)) +
    (-3 * wa * z / (1 + z)) by unfold exponent; ring]
  rw [Real.exp_add]
  ring

theorem exponent_hasDerivAt (w0 wa : ℝ) {z : ℝ} (hz : -1 < z) :
    HasDerivAt (exponent w0 wa)
      (3 * (1 + fluidW w0 wa z) / (1 + z)) z := by
  have hn : 1 + z ≠ 0 := ne_of_gt (by linarith)
  have hi : HasDerivAt (fun t : ℝ => 1 + t) 1 z :=
    (hasDerivAt_id z).const_add 1
  have h := ((hi.log hn).const_mul (3 * (1 + w0 + wa))).sub
    (((hasDerivAt_id z).const_mul (3 * wa)).div hi hn)
  convert h using 1
  simp only [fluidW, id_eq]
  field_simp [hn]
  ring

theorem density_hasDerivAt (amplitude w0 wa : ℝ) {z : ℝ} (hz : -1 < z) :
    HasDerivAt (density amplitude w0 wa)
      (density amplitude w0 wa z * (3 * (1 + fluidW w0 wa z) / (1 + z))) z := by
  convert ((exponent_hasDerivAt w0 wa hz).exp).const_mul amplitude using 1
  unfold density
  ring

theorem fluid_is_log_derivative {amplitude w0 wa z : ℝ}
    (ha : 0 < amplitude) (hz : -1 < z) :
    -1 + (1 + z) * deriv (density amplitude w0 wa) z /
      (3 * density amplitude w0 wa z) = fluidW w0 wa z := by
  rw [(density_hasDerivAt amplitude w0 wa hz).deriv]
  have hd := ne_of_gt (density_positive ha w0 wa z)
  have hn : 1 + z ≠ 0 := ne_of_gt (by linarith)
  field_simp [hd, hn]
  ring

theorem density_continuousAt (amplitude w0 wa : ℝ) {z : ℝ} (hz : -1 < z) :
    ContinuousAt (density amplitude w0 wa) z :=
  (density_hasDerivAt amplitude w0 wa hz).continuousAt

/-- The additive chart is exactly the same expansion history minus its
declared matter and radiation terms, including at the phantom crossing. -/
theorem same_history_additive (matter radiation amplitude w0 wa z : ℝ) :
    expansionSquared matter radiation amplitude w0 wa z -
      matter * (1 + z)^3 - radiation * (1 + z)^4 = density amplitude w0 wa z := by
  unfold expansionSquared
  ring

theorem expansion_positive {matter radiation amplitude z : ℝ}
    (hm : 0 ≤ matter) (hr : 0 ≤ radiation) (ha : 0 < amplitude)
    (hz : -1 < z) (w0 wa : ℝ) :
    0 < expansionSquared matter radiation amplitude w0 wa z := by
  have hp := density_positive ha w0 wa z
  unfold expansionSquared
  have hn : 0 < 1 + z := by linarith
  positivity

/-- The exact crossing equation needs no interpolation of a redshift grid. -/
theorem crossing_iff {w0 wa z : ℝ} (hz : -1 < z) :
    fluidW w0 wa z = -1 ↔ (1 + w0) + (1 + w0 + wa) * z = 0 := by
  have hn : 1 + z ≠ 0 := ne_of_gt (by linarith)
  unfold fluidW
  constructor
  · intro h
    have hmul := congrArg (fun t : ℝ => t * (1 + z)) h
    field_simp at hmul
    nlinarith [hmul]
  · intro h
    field_simp [hn]
    nlinarith

theorem exact_crossing {w0 wa z : ℝ} (hz : -1 < z)
    (hc : 1 + w0 + wa ≠ 0) :
    fluidW w0 wa z = -1 ↔ z = -(1 + w0) / (1 + w0 + wa) := by
  rw [crossing_iff hz, eq_div_iff hc]
  constructor <;> intro h <;> nlinarith

/-- Phantom is a sign of the regular density derivative; there is no
singularity at a zero of this affine numerator. -/
theorem phantom_iff {w0 wa z : ℝ} (hz : -1 < z) :
    fluidW w0 wa z < -1 ↔ (1 + w0) + (1 + w0 + wa) * z < 0 := by
  have hn : 0 < 1 + z := by linarith
  have he : fluidW w0 wa z + 1 =
      ((1 + w0) + (1 + w0 + wa) * z) / (1 + z) := by
    unfold fluidW
    field_simp [ne_of_gt hn]
    ring
  have hs : ((1 + w0) + (1 + w0 + wa) * z) / (1 + z) < 0 ↔
      (1 + w0) + (1 + w0 + wa) * z < 0 := by
    rw [div_lt_iff₀ hn]
    simp
  constructor
  · intro h
    apply hs.mp
    rw [← he]
    linarith
  · intro h
    have hh := hs.mpr h
    rw [← he] at hh
    linarith

end

end SbtCosmo.Derivation.CPLReadout
