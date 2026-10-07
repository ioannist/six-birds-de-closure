import SbtCosmo.Derivation.GroundUncertainNativeBox
import SbtCosmo.Derivation.GroundNativeQuantitativeBall
import SbtCosmo.Derivation.GroundStateRows
import SbtCosmo.Derivation.GroundMatrixCoordinates
import SbtCosmo.Derivation.GroundNativeReflection

/-! Conditional whole-background-box bridges for quantitative native basins.
Every response, entry-cache and derivative-row budget remains visible. -/
namespace SbtCosmo.Derivation.GroundUncertainNativeBasin
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundNativeDerivative
open GroundRationalInterval GroundNativeBox GroundNativeDerivativeBox GroundMatrixCoordinates
open Metric Filter NNReal
open scoped BigOperators Topology

structure Certificate where
  β : Fin 8 → Interval
  κ : ℚ
  τ : ℚ
  input : StateBox
  z : Fin 9 → ℚ
  r : ℚ
  q : ℚ
  a : ℚ
  C : Matrix (Fin 9) (Fin 9) ℚ
  K : Interval
  L : Interval
  S : QMatrix
  P : QMatrix
  R : QMatrix
  Q : QMatrix
  real_inverse : InverseArithmetic S P
  imag_inverse : InverseArithmetic R Q
  DG : Fin 16 → Fin 8 → Interval
  DF : Fin 16 → StateBox
  y : Fin 16 → ℚ
  e : Fin 16 → ℚ
  rate : ℚ
  ground : GroundBackgroundKernel.Arithmetic (GroundUncertainNativeBox.sourceBox β κ input) z r q a C
  phase_inverse : GroundIntervalReciprocal.Arithmetic (overlapBox input (GroundBackgroundKernel.fieldBox z r)) K
  mixed_inverse : GroundIntervalReciprocal.Arithmetic
    (normBox (mixedBox input (GroundBackgroundKernel.fieldBox z r) K)) L
  threshold_nonneg : 0 ≤ τ
  phase_margin : τ^2 < (overlapBox input (GroundBackgroundKernel.fieldBox z r)).lo
  normalization_margin : τ^2 < (normBox (mixedBox input (GroundBackgroundKernel.fieldBox z r) K)).lo

namespace Certificate

def T (c : Certificate) : State ≃L[ℝ] State := (basis c.real_inverse).prodCongr (basis c.imag_inverse)
def G (c : Certificate) : Fin 8 → Interval := GroundBackgroundKernel.fieldBox c.z c.r
def direction (c : Certificate) (j : Fin 16) : StateBox where
  R i := Interval.point (if h : j.val < 8 then c.S i ⟨j.val,h⟩ else 0)
  I i := Interval.point (if h : j.val < 8 then 0 else c.R i ⟨j.val-8,by omega⟩)
def column (j : Fin 16) : State := if h : j.val < 8 then (GroundLocalDynamics.column ⟨j.val,h⟩,0)
    else (0,GroundLocalDynamics.column ⟨j.val-8,by omega⟩)
def coordinateBox (c : Certificate) (B : StateBox) : StateBox where
  R i := sumBox (fun j => (Interval.point (c.P i j)).mul (B.R j))
  I i := sumBox (fun j => (Interval.point (c.Q i j)).mul (B.I j))
def derivativeBox (c : Certificate) (j : Fin 16) : StateBox := c.coordinateBox (c.DF j)
def responseBox (c : Certificate) (j : Fin 16) (i : Fin 8) : Interval :=
  GroundBackgroundResponse.responseInterval c.C c.G
    (GroundUncertainNativeBox.sourceDerivativeBox c.β c.κ c.input (c.direction j)) (c.e j) i

def ResponseArithmetic (c : Certificate) : Prop := ∀ j,
  GroundBackgroundResponse.ResponseArithmetic c.C c.G
    (GroundUncertainNativeBox.sourceDerivativeBox c.β c.κ c.input (c.direction j)) c.q (c.y j) (c.e j)
def ResponseIncluded (c : Certificate) : Prop := ∀ j i, included (c.responseBox j i) (c.DG j i)
def DerivativeIncluded (c : Certificate) : Prop := ∀ j,
  (fullDerivativeBox c.input (c.direction j) c.G (c.DG j) c.K c.L).Included (c.DF j)

theorem coordinateBox_sound (c : Certificate) {B : StateBox} {x : State} (hx : B.Contains x) :
    (c.coordinateBox B).Contains (c.T.symm x) := by
  intro i
  constructor
  · change (sumBox (fun j => (Interval.point (c.P i j)).mul (B.R j))).Contains ((basis c.real_inverse).symm x.1 i)
    rw [basis_symm_apply]
    exact sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound _) (hx j).1)
  · change (sumBox (fun j => (Interval.point (c.Q i j)).mul (B.I j))).Contains ((basis c.imag_inverse).symm x.2 i)
    rw [basis_symm_apply]
    exact sumBox_sound (fun j => Interval.mul_sound (Interval.point_sound _) (hx j).2)

theorem direction_sound (c : Certificate) (j : Fin 16) :
    (c.direction j).Contains (c.T (column j)) := by
  intro i
  by_cases h : j.val < 8
  · constructor
    · change (Interval.point (if hj : j.val < 8 then c.S i ⟨j.val,hj⟩ else 0)).Contains
        ((basis c.real_inverse) (column j).1 i)
      simp only [h, dite_true, column]
      rw [basis_apply]
      simpa [GroundLocalDynamics.column, Pi.single_apply] using Interval.point_sound (c.S i ⟨j.val,h⟩)
    · change (Interval.point (if hj : j.val < 8 then 0 else c.R i ⟨j.val-8,by omega⟩)).Contains
        ((basis c.imag_inverse) (column j).2 i)
      simp only [h, dite_true, column, map_zero, Pi.zero_apply]
      simpa only [Rat.cast_zero] using Interval.point_sound 0
  · constructor
    · change (Interval.point (if hj : j.val < 8 then c.S i ⟨j.val,hj⟩ else 0)).Contains
        ((basis c.real_inverse) (column j).1 i)
      simp only [h, dite_false, column, map_zero, Pi.zero_apply]
      simpa only [Rat.cast_zero] using Interval.point_sound 0
    · change (Interval.point (if hj : j.val < 8 then 0 else c.R i ⟨j.val-8,by omega⟩)).Contains
        ((basis c.imag_inverse) (column j).2 i)
      simp only [h, dite_false, column]
      rw [basis_apply]
      simpa [GroundLocalDynamics.column, Pi.single_apply] using Interval.point_sound (c.R i ⟨j.val-8,by omega⟩)

theorem actual_jet_enclosed (c : Certificate) (hR : c.ResponseArithmetic)
    (hD : c.ResponseIncluded) (hJ : c.DerivativeIncluded) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {x : State} (hx : c.input.Contains x) (j : Fin 16) :
    (c.derivativeBox j).Contains (c.T.symm (GroundNativeGeneralDerivative.fullDerivative b (c.κ : ℝ) (1/2) x
      (c.T (column j)))) := by
  have hg := GroundBackgroundKernel.actual_selected_enclosed c.ground (GroundUncertainNativeBox.sourceBox_sound c.β c.κ hb hx)
  have hd := GroundUncertainNativeBox.selectedDerivative_enclosed c.ground (hR j) hb hx (c.direction_sound j)
  have hdCached := fun i => GroundNativeBox.included_sound (hD j i) (hd i)
  have hk := (GroundIntervalReciprocal.inverse_sqrt_sound c.phase_inverse (overlapBox_sound hx hg)).2
  have hm := mixedBox_sound hx hg hk
  have hl := (GroundIntervalReciprocal.inverse_sqrt_sound c.mixed_inverse (normBox_sound hm)).2
  exact c.coordinateBox_sound (StateBox.included_sound (hJ j)
    (fullDerivativeBox_sound hx (c.direction_sound j) hg hdCached hk hl))

theorem column_real (j : Fin 8) : column (j.castAdd 8) = (GroundLocalDynamics.column j,0) := by
  simp [column, Fin.castAdd, j.isLt]

theorem column_imag (j : Fin 8) : column (Fin.natAdd 8 j) = (0,GroundLocalDynamics.column j) := by
  simp [column, Fin.natAdd]

structure RowArithmetic (c : Certificate) : Prop where
  rate_nonneg : 0 ≤ c.rate
  rate_lt : c.rate < 1
  real_rows : ∀ i : Fin 8,
    (∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).R i).bound+
      ((c.derivativeBox (Fin.natAdd 8 j)).R i).bound)) ≤ c.rate
  imag_rows : ∀ i : Fin 8,
    (∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).I i).bound+
      ((c.derivativeBox (Fin.natAdd 8 j)).I i).bound)) ≤ c.rate

theorem actual_derivative_norm (c : Certificate) (hR : c.ResponseArithmetic)
    (hD : c.ResponseIncluded) (hJ : c.DerivativeIncluded) (hrows : c.RowArithmetic) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {x : State} (hx : c.input.Contains (c.T x)) :
    ‖GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x‖ ≤ (c.rate : ℝ) := by
  have hreal (j : Fin 8) := c.actual_jet_enclosed hR hD hJ hb hx (j.castAdd 8)
  have himag (j : Fin 8) := c.actual_jet_enclosed hR hD hJ hb hx (Fin.natAdd 8 j)
  simp only [column_real] at hreal
  simp only [column_imag] at himag
  apply GroundStateRows.operator_norm_le_rows _ (by exact_mod_cast hrows.rate_nonneg)
  · intro i
    calc
      (∑ j, (|(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (GroundLocalDynamics.column j,0)).1 i|+
        |(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (0,GroundLocalDynamics.column j)).1 i|)) ≤
        ∑ j, ((((c.derivativeBox (j.castAdd 8)).R i).bound : ℝ)+(((c.derivativeBox (Fin.natAdd 8 j)).R i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((hreal j) i).1) (Interval.abs_le_bound ((himag j) i).1)
      _ ≤ (c.rate : ℝ) := by
        have h : ((∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).R i).bound+((c.derivativeBox (Fin.natAdd 8 j)).R i).bound) : ℚ) : ℝ) ≤ (c.rate : ℝ) := Rat.cast_le.mpr (hrows.real_rows i)
        simpa only [Rat.cast_sum, Rat.cast_add] using h
  · intro i
    calc
      (∑ j, (|(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (GroundLocalDynamics.column j,0)).2 i|+
        |(GroundNativeQuantitativeBall.derivative c.T b (c.κ : ℝ) (1/2) x (0,GroundLocalDynamics.column j)).2 i|)) ≤
        ∑ j, ((((c.derivativeBox (j.castAdd 8)).I i).bound : ℝ)+(((c.derivativeBox (Fin.natAdd 8 j)).I i).bound : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (Interval.abs_le_bound ((hreal j) i).2) (Interval.abs_le_bound ((himag j) i).2)
      _ ≤ (c.rate : ℝ) := by
        have h : ((∑ j : Fin 8, (((c.derivativeBox (j.castAdd 8)).I i).bound+((c.derivativeBox (Fin.natAdd 8 j)).I i).bound) : ℚ) : ℝ) ≤ (c.rate : ℝ) := Rat.cast_le.mpr (hrows.imag_rows i)
        simpa only [Rat.cast_sum, Rat.cast_add] using h

theorem actual_guards (c : Certificate) {b : Field}
    (hb : ∀ i, (c.β i).Contains (b i)) {x : State} (hx : c.input.Contains x) :
    (c.τ : ℝ) < overlapNorm b (c.κ : ℝ) x ∧
    (c.τ : ℝ) < Real.sqrt (stateNormSq (mixed b (c.κ : ℝ) (1/2) x)) := by
  have hg := GroundBackgroundKernel.actual_selected_enclosed c.ground (GroundUncertainNativeBox.sourceBox_sound c.β c.κ hb hx)
  have hr := overlapBox_sound hx hg
  have hk := (GroundIntervalReciprocal.inverse_sqrt_sound c.phase_inverse hr).2
  have hn := normBox_sound (mixedBox_sound hx hg hk)
  have ht : (0 : ℝ) ≤ (c.τ : ℝ) := by exact_mod_cast c.threshold_nonneg
  have hp : (c.τ : ℝ)^2 < ((overlapBox c.input c.G).lo : ℝ) := by exact_mod_cast c.phase_margin
  have hm : (c.τ : ℝ)^2 < ((normBox (mixedBox c.input c.G c.K)).lo : ℝ) := by exact_mod_cast c.normalization_margin
  exact ⟨GroundIntervalReciprocal.threshold_guard hr ht hp,GroundIntervalReciprocal.threshold_guard hn ht hm⟩

def aroundBox (z₀ : Fin 9 → ℚ) (r₀ ρ s : ℚ) : StateBox where
  R i := ⟨z₀ i.castSucc-r₀-ρ*s,z₀ i.castSucc+r₀+ρ*s⟩
  I _ := ⟨-(ρ*s),ρ*s⟩

theorem basis_norm (c : Certificate) {s : ℚ} (hs : 0 ≤ s)
    (hrows : ∀ i : Fin 8, (∑ j, |c.S i j|) ≤ s ∧ (∑ j, |c.R i j|) ≤ s) :
    ‖c.T.toContinuousLinearMap‖ ≤ (s : ℝ) := by
  have hS : ‖(basis c.real_inverse).toContinuousLinearMap‖ ≤ (s : ℝ) := by
    apply GroundLocalDynamics.operator_norm_le_rows _ (by exact_mod_cast hs)
    intro i
    have hcol (j : Fin 8) : basis c.real_inverse (GroundLocalDynamics.column j) i = (c.S i j : ℝ) := by
      rw [basis_apply]
      simp [GroundLocalDynamics.column,Pi.single_apply]
    simp only [ContinuousLinearEquiv.coe_coe,hcol]
    exact_mod_cast (hrows i).1
  have hR : ‖(basis c.imag_inverse).toContinuousLinearMap‖ ≤ (s : ℝ) := by
    apply GroundLocalDynamics.operator_norm_le_rows _ (by exact_mod_cast hs)
    intro i
    have hcol (j : Fin 8) : basis c.imag_inverse (GroundLocalDynamics.column j) i = (c.R i j : ℝ) := by
      rw [basis_apply]
      simp [GroundLocalDynamics.column,Pi.single_apply]
    simp only [ContinuousLinearEquiv.coe_coe,hcol]
    exact_mod_cast (hrows i).2
  change ‖(basis c.real_inverse).toContinuousLinearMap.prodMap
    (basis c.imag_inverse).toContinuousLinearMap‖ ≤ (s : ℝ)
  exact (GroundNativeLocal.product_operator_norm_bound _ _).trans (max_le hS hR)

theorem input_box_on_ball (c : Certificate) {z₀ : Fin 9 → ℚ} {r₀ ρ s : ℚ} {u : Field}
    (hs : 0 ≤ s) (hT : ‖c.T.toContinuousLinearMap‖ ≤ (s : ℝ))
    (hu : ∀ i, (GroundBackgroundKernel.fieldBox z₀ r₀ i).Contains (u i))
    (hbox : (aroundBox z₀ r₀ ρ s).Included c.input) {x : State}
    (hx : x ∈ closedBall (c.T.symm (u,0)) (ρ : ℝ)) : c.input.Contains (c.T x) := by
  have hd : ‖x-c.T.symm (u,0)‖ ≤ (ρ : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hx
  have hp : ‖c.T x-(u,0)‖ ≤ (s : ℝ)*(ρ : ℝ) := by
    rw [← c.T.apply_symm_apply (u,(0 : Field)),← map_sub]
    exact (c.T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hT hd (norm_nonneg _) (by exact_mod_cast hs))
  have hR (i : Fin 8) : |(c.T x).1 i-u i| ≤ (s : ℝ)*(ρ : ℝ) := by
    have hcoord : |(c.T x).1 i-u i| ≤ ‖(c.T x-(u,0)).1‖ := by
      simpa only [Real.norm_eq_abs,Prod.fst_sub,Pi.sub_apply] using norm_le_pi_norm (c.T x-(u,0)).1 i
    exact hcoord.trans ((by rw [Prod.norm_def]; exact le_max_left _ _ :
      ‖(c.T x-(u,0)).1‖ ≤ ‖c.T x-(u,0)‖).trans hp)
  have hI (i : Fin 8) : |(c.T x).2 i| ≤ (s : ℝ)*(ρ : ℝ) := by
    have hcoord : |(c.T x).2 i| ≤ ‖(c.T x-(u,0)).2‖ := by
      have he : (c.T x-(u,0)).2 = (c.T x).2 := by change (c.T x).2-0 = (c.T x).2; exact sub_zero _
      rw [he]
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (c.T x).2 i
    exact hcoord.trans ((by rw [Prod.norm_def]; exact le_max_right _ _ :
      ‖(c.T x-(u,0)).2‖ ≤ ‖c.T x-(u,0)‖).trans hp)
  apply StateBox.included_sound hbox
  intro i
  have hz := hu i
  have hr := abs_le.mp (hR i)
  have hi := abs_le.mp (hI i)
  simp only [GroundBackgroundKernel.fieldBox,Interval.Contains,Rat.cast_sub,Rat.cast_add] at hz
  simp only [aroundBox,Interval.Contains,Rat.cast_sub,Rat.cast_add,Rat.cast_neg,Rat.cast_mul]
  constructor <;> constructor <;> nlinarith

def contractionRate (c : Certificate) (h : c.RowArithmetic) : ℝ≥0 :=
  ⟨(c.rate : ℝ),by exact_mod_cast h.rate_nonneg⟩

theorem actual_ball_convergence (c : Certificate) (hR : c.ResponseArithmetic)
    (hD : c.ResponseIncluded) (hJ : c.DerivativeIncluded) (hrows : c.RowArithmetic)
    {b u : Field} (hb : ∀ i, (c.β i).Contains (b i))
    (hu : normSq u = 1) (hf : GroundSourceJacobian.groundMap b (c.κ : ℝ) u = u)
    (hτ1 : (c.τ : ℝ) < 1) {z₀ : Fin 9 → ℚ} {r₀ ρ s : ℚ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hT : ‖c.T.toContinuousLinearMap‖ ≤ (s : ℝ))
    (hroot : ∀ i, (GroundBackgroundKernel.fieldBox z₀ r₀ i).Contains (u i))
    (hbox : (aroundBox z₀ r₀ ρ s).Included c.input) {z : ComplexField}
    (hz : c.T.symm (unpack z) ∈ closedBall (c.T.symm (u,0)) (ρ : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z)
      atTop (nhds (realEmbed u)) ∧
    ∀ n : ℕ, ActivePhase (c.τ : ℝ) b (c.κ : ℝ) ((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z) ∧
      NativeLegal (c.τ : ℝ) b (c.κ : ℝ) (1/2) ((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z) ∧
      dist (c.T.symm (unpack ((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z))) (c.T.symm (u,0)) ≤
        ((c.contractionRate hrows : ℝ)^n)*dist (c.T.symm (unpack z)) (c.T.symm (u,0)) := by
  exact GroundNativeQuantitativeBall.explicit_native_ball_convergence c.T (c.contractionRate hrows) hu hf
    (by exact_mod_cast c.threshold_nonneg) hτ1 (by exact_mod_cast hρ)
    (show c.contractionRate hrows < 1 by change (c.rate : ℝ) < 1; exact_mod_cast hrows.rate_lt)
    (fun x hx => c.actual_guards hb (c.input_box_on_ball hs hT hroot hbox hx))
    (fun x hx => c.actual_derivative_norm hR hD hJ hrows hb (c.input_box_on_ball hs hT hroot hbox hx)) z hz

theorem actual_negative_ball_convergence (c : Certificate) (hR : c.ResponseArithmetic)
    (hD : c.ResponseIncluded) (hJ : c.DerivativeIncluded) (hrows : c.RowArithmetic)
    {b u : Field} (hb : ∀ i, (c.β i).Contains (b i))
    (hu : normSq u = 1) (hf : GroundSourceJacobian.groundMap b (c.κ : ℝ) u = u)
    (hτ1 : (c.τ : ℝ) < 1) {z₀ : Fin 9 → ℚ} {r₀ ρ s : ℚ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hT : ‖c.T.toContinuousLinearMap‖ ≤ (s : ℝ))
    (hroot : ∀ i, (GroundBackgroundKernel.fieldBox z₀ r₀ i).Contains (u i))
    (hbox : (aroundBox z₀ r₀ ρ s).Included c.input) {z : ComplexField}
    (hz : c.T.symm (unpack z) ∈ closedBall (c.T.symm (-u,0)) (ρ : ℝ)) :
    Tendsto (fun n : ℕ => (nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z)
      atTop (nhds (realEmbed (-u))) ∧
    ∀ n : ℕ, ActivePhase (c.τ : ℝ) b (c.κ : ℝ) ((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z) ∧
      NativeLegal (c.τ : ℝ) b (c.κ : ℝ) (1/2) ((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z) ∧
      dist (c.T.symm (unpack ((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z))) (c.T.symm (-u,0)) ≤
        ((c.contractionRate hrows : ℝ)^n)*dist (c.T.symm (unpack z)) (c.T.symm (-u,0)) := by
  have hcenter : c.T.symm (-u,0) = -c.T.symm (u,0) := by
    rw [← map_neg]
    simp only [Prod.neg_mk,neg_zero]
  have hstart : dist (c.T.symm (unpack (-z))) (c.T.symm (u,0)) =
      dist (c.T.symm (unpack z)) (c.T.symm (-u,0)) := by
    rw [GroundNativeReflection.unpack_neg,map_neg,hcenter]
    simpa only [neg_neg] using dist_neg_neg (c.T.symm (unpack z)) (-c.T.symm (u,0))
  have hz' : c.T.symm (unpack (-z)) ∈ closedBall (c.T.symm (u,0)) (ρ : ℝ) := by
    rw [mem_closedBall,hstart]
    exact hz
  obtain ⟨ht,hg⟩ := c.actual_ball_convergence hR hD hJ hrows hb hu hf hτ1 hρ hs hT hroot hbox hz'
  have hτ : (0 : ℝ) ≤ (c.τ : ℝ) := by exact_mod_cast c.threshold_nonneg
  have he (n : ℕ) : (nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] z =
      -((nativeUpdate (c.τ : ℝ) b (c.κ : ℝ) (1/2))^[n] (-z)) := by
    simpa only [neg_neg] using GroundNativeReflection.native_iterate_neg b (c.κ : ℝ) (1/2) (-z)
      hτ n (fun j _ => (hg j).1)
  refine ⟨?_,fun n => ?_⟩
  · simpa only [← he,← GroundNativeReflection.realEmbed_neg] using ht.neg
  · rw [he n]
    refine ⟨(GroundNativeReflection.activePhase_neg_iff _ _ _ _).mpr (hg n).1,
      (GroundNativeReflection.nativeLegal_neg_iff _ _ _ _ hτ (hg n).1).mpr (hg n).2.1,?_⟩
    have hbound := (hg n).2.2
    rw [hstart] at hbound
    simpa only [GroundNativeReflection.unpack_neg,map_neg,hcenter,dist_neg_neg] using hbound

end Certificate
end
end SbtCosmo.Derivation.GroundUncertainNativeBasin
