import SbtCosmo.Derivation.GroundUncertainNativeBasin
/-! Actual coordinate distances from outward state/root enclosures.
The returned distance is to the actual field, not a proposal center. -/
namespace SbtCosmo.Derivation.GroundCertifiedNativeEntry
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval
open GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open Filter
open scoped BigOperators Topology

def differenceBox (B A : StateBox) : StateBox where
  R i := (B.R i).add (A.R i).neg
  I i := (B.I i).add (A.I i).neg

theorem differenceBox_sound {B A : StateBox} {x u : State}
    (hx : B.Contains x) (hu : A.Contains u) : (differenceBox B A).Contains (x-u) := by
  intro i
  exact ⟨Interval.add_sound (hx i).1 (Interval.neg_sound (hu i).1),
    Interval.add_sound (hx i).2 (Interval.neg_sound (hu i).2)⟩

theorem coordinate_distance (c : Certificate) {B A : StateBox} {x u : State} {δ : ℚ}
    (hδ : 0 ≤ δ) (hx : B.Contains x) (hu : A.Contains u)
    (hrows : ∀ i, ((c.coordinateBox (differenceBox B A)).R i).bound ≤ δ ∧
      ((c.coordinateBox (differenceBox B A)).I i).bound ≤ δ) :
    dist (c.T.symm x) (c.T.symm u) ≤ (δ : ℝ) := by
  have hc := c.coordinateBox_sound (differenceBox_sound hx hu)
  rw [dist_eq_norm,← map_sub,Prod.norm_def]
  apply max_le
  all_goals apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast hδ : (0 : ℝ) ≤ (δ : ℝ))).mpr
  all_goals intro i
  · have h : (((c.coordinateBox (differenceBox B A)).R i).bound : ℝ) ≤ (δ : ℝ) :=
      Rat.cast_le.mpr (hrows i).1
    simpa only [Real.norm_eq_abs] using (Interval.abs_le_bound (hc i).1).trans h
  · have h : (((c.coordinateBox (differenceBox B A)).I i).bound : ℝ) ≤ (δ : ℝ) :=
      Rat.cast_le.mpr (hrows i).2
    simpa only [Real.norm_eq_abs] using (Interval.abs_le_bound (hc i).2).trans h

def negativeTargetBox (z : Fin 9 → ℚ) (r : ℚ) : StateBox where
  R i := (GroundBackgroundKernel.fieldBox z r i).neg
  I _ := Interval.point 0

theorem negativeTargetBox_sound {z : Fin 9 → ℚ} {r : ℚ} {u : Field}
    (hu : ∀ i, (GroundBackgroundKernel.fieldBox z r i).Contains (u i)) :
    (negativeTargetBox z r).Contains (-u,0) := by
  intro i
  exact ⟨Interval.neg_sound (hu i),by simpa only [Rat.cast_zero] using Interval.point_sound 0⟩

theorem iterate_tendsto_of_tail (f : ComplexField → ComplexField) (z y : ComplexField)
    (N : ℕ) (h : Tendsto (fun n : ℕ => f^[n] (f^[N] z)) atTop (nhds y)) :
    Tendsto (fun n : ℕ => f^[n] z) atTop (nhds y) := by
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [Function.iterate_add_apply] using h

theorem iterate_property_of_tail (f : ComplexField → ComplexField) (z : ComplexField)
    (P : ComplexField → Prop) (N : ℕ)
    (hp : ∀ i : Fin N, P (f^[i.val] z))
    (ht : ∀ n : ℕ, P (f^[n] (f^[N] z))) : ∀ n : ℕ, P (f^[n] z) := by
  intro n
  by_cases h : n < N
  · exact hp ⟨n,h⟩
  · have he : n = (n-N)+N := by omega
    rw [he,Function.iterate_add_apply]
    exact ht (n-N)
end
end SbtCosmo.Derivation.GroundCertifiedNativeEntry
