import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
import SbtCosmo.PhantomStableReadout

/-!
A single analytic density determines the effective equation-of-state readout.
This strengthens the uncoupled finite T5 samples. The independent diagonal
decay certificate remains a toy stability condition, with no physical bridge.
-/
namespace SbtCosmo.Derivation.AnalyticReadout

noncomputable section

def rho (rhoMin curvature crossing z : ℝ) : ℝ :=
  rhoMin + curvature * (z - crossing)^2

def wEff (rhoMin curvature crossing z : ℝ) : ℝ :=
  -1 + (1 + z) * (2 * curvature * (z - crossing)) / (3 * rho rhoMin curvature crossing z)

theorem rho_positive {rhoMin curvature crossing z : ℝ}
    (hm : 0 < rhoMin) (hc : 0 ≤ curvature) : 0 < rho rhoMin curvature crossing z := by
  unfold rho
  positivity

theorem rho_hasDerivAt (rhoMin curvature crossing z : ℝ) :
    HasDerivAt (rho rhoMin curvature crossing) (2 * curvature * (z - crossing)) z := by
  convert (hasDerivAt_const z rhoMin).add
    ((((hasDerivAt_id z).sub_const crossing).pow 2).const_mul curvature) using 1
  simp
  ring

theorem wEff_crossing {rhoMin curvature crossing : ℝ} (_hm : 0 < rhoMin) :
    wEff rhoMin curvature crossing crossing = -1 := by simp [wEff]

theorem wEff_phantom_iff {rhoMin curvature crossing z : ℝ}
    (hm : 0 < rhoMin) (hc : 0 < curvature) (hz : -1 < z) :
    wEff rhoMin curvature crossing z < -1 ↔ z < crossing := by
  have hden : 0 < 3 * rho rhoMin curvature crossing z :=
    mul_pos (by norm_num) (rho_positive hm hc.le)
  have hfactor : 0 < (1 + z) * (2 * curvature) :=
    mul_pos (by linarith) (mul_pos (by norm_num) hc)
  rw [wEff]
  have hsign : (1 + z) * (2 * curvature * (z - crossing)) /
      (3 * rho rhoMin curvature crossing z) < 0 ↔ z - crossing < 0 := by
    rw [div_neg_iff, ← mul_assoc]
    constructor
    · intro h
      rcases h with ⟨_, hneg⟩ | ⟨hnum, _⟩
      · linarith
      · rcases mul_neg_iff.mp hnum with ⟨_, hneg⟩ | ⟨hneg, _⟩
        · exact hneg
        · linarith
    · intro h
      exact Or.inr ⟨mul_neg_of_pos_of_neg hfactor h, hden⟩
  constructor
  · intro h
    have : z - crossing < 0 := hsign.mp (by linarith)
    linarith
  · intro h
    have : (1 + z) * (2 * curvature * (z - crossing)) /
        (3 * rho rhoMin curvature crossing z) < 0 := hsign.mpr (by linarith)
    linarith

/-- The original T5 density samples now belong to this one analytic density. -/
theorem toy3_density_samples_consistent (i : SbtCosmo.PhantomStableReadout.Grid3) :
    rho (287 / 4) 16 (7 / 8)
        (SbtCosmo.PhantomStableReadout.toy3Witness.z i : ℝ) =
      (SbtCosmo.PhantomStableReadout.toy3Witness.rhoEff i : ℝ) := by
  cases i <;> norm_num [rho, SbtCosmo.PhantomStableReadout.toy3Witness]

/-- The T5 `w` samples are the log-derivative readout of the same density. -/
theorem toy3_w_samples_consistent (i : SbtCosmo.PhantomStableReadout.Grid3) :
    wEff (287 / 4) 16 (7 / 8)
        (SbtCosmo.PhantomStableReadout.toy3Witness.z i : ℝ) =
      (SbtCosmo.PhantomStableReadout.wEff SbtCosmo.PhantomStableReadout.toy3Witness i : ℝ) := by
  cases i <;>
    simp only [SbtCosmo.PhantomStableReadout.wEff,
      SbtCosmo.PhantomStableReadout.toy3Witness, Rat.cast_add, Rat.cast_neg, Rat.cast_one] <;>
    norm_num [wEff, rho, Rat.cast_def]

end

end SbtCosmo.Derivation.AnalyticReadout
