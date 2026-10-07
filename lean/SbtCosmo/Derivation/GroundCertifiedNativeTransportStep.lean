import SbtCosmo.Derivation.GroundFiniteNativeTransport
import SbtCosmo.Derivation.GroundNativeTransportGeometry
import SbtCosmo.Derivation.GroundNativeTransportJets
import SbtCosmo.Derivation.GroundCertifiedNativePrefix
import SbtCosmo.Derivation.GroundCertifiedNativeEntry

/-! Uniform finite native transport. Point defects and whole-neighborhood
responses are earned separately. A finite derivative bound may exceed one. -/
namespace SbtCosmo.Derivation.GroundCertifiedNativeTransportStep
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundUncertainNativeBasin GroundUncertainNativeBasin.Certificate
open GroundNativeTransportGeometry GroundCertifiedNativeEntry Metric
open scoped BigOperators

structure Data (β : Fin 8 → Interval) (κ τ : ℚ) (T : State ≃L[ℝ] State) where
  u : Fin 8 → ℚ
  v : Fin 8 → ℚ
  next_u : Fin 8 → ℚ
  next_v : Fin 8 → ℚ
  radius : ℚ
  next_radius : ℚ
  defect : ℚ
  s : ℚ
  jet : Certificate
  inputs : jet.β = β
  coupling : jet.κ = κ
  threshold : jet.τ = τ
  frame : jet.T = T
  input : jet.input = around u v radius s
  pointStep : GroundCertifiedNativePrefix.Step β κ τ
  point_input : pointStep.input = around u v 0 s
  responses : jet.ResponseArithmetic
  response_included : jet.ResponseIncluded
  derivative_included : jet.DerivativeIncluded
  rows : GroundNativeTransportJets.RowBounds jet
  basis_nonneg : 0 ≤ s
  basis_rows : ∀ i : Fin 8, (∑ j, |jet.S i j|) ≤ s ∧ (∑ j, |jet.R i j|) ≤ s
  radius_nonneg : 0 ≤ radius
  next_radius_nonneg : 0 ≤ next_radius
  defect_nonneg : 0 ≤ defect
  defect_rows : ∀ i : Fin 8,
    ((jet.coordinateBox (differenceBox pointStep.output (around next_u next_v 0 s))).R i).bound ≤ defect ∧
    ((jet.coordinateBox (differenceBox pointStep.output (around next_u next_v 0 s))).I i).bound ≤ defect
  budget : jet.rate*radius+defect ≤ next_radius

namespace Data
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State}
def center (d : Data β κ τ T) : State := T.symm (point d.u d.v)
def nextCenter (d : Data β κ τ T) : State := T.symm (point d.next_u d.next_v)
def rate (d : Data β κ τ T) : NNReal := ⟨(d.jet.rate : ℝ),by exact_mod_cast d.rows.rate_nonneg⟩
def f (b : Field) : State → State := GroundNativeLocal.coordinateMap T (τ : ℝ) b (κ : ℝ) (1/2)

theorem input_on_ball (d : Data β κ τ T) {x : State}
    (hx : x ∈ closedBall d.center (d.radius : ℝ)) : d.jet.input.Contains (T x) := by
  have hT := d.jet.basis_norm d.basis_nonneg d.basis_rows
  rw [d.frame] at hT
  rw [d.input]
  exact GroundNativeTransportGeometry.input_on_ball T d.u d.v d.basis_nonneg hT hx

theorem pair_guards (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall d.center (d.radius : ℝ)) :
    (τ : ℝ) < overlapNorm b (κ : ℝ) (T x) ∧
    (τ : ℝ) < Real.sqrt (stateNormSq (mixed b (κ : ℝ) (1/2) (T x))) := by
  have hg := d.jet.actual_guards (by simpa only [d.inputs] using hb) (d.input_on_ball hx)
  simpa only [d.coupling,d.threshold] using hg

theorem native_guards (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall d.center (d.radius : ℝ)) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (pack (T x)) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack (T x)) := by
  have hg := d.pair_guards hb hx
  exact GroundNativeQuantitativeBall.native_guards b (κ : ℝ) (1/2) (τ : ℝ) (T x)
    (by exact_mod_cast d.pointStep.proof.threshold_nonneg) hg.1 hg.2

theorem lipschitz (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) :
    LipschitzOnWith d.rate (f (T := T) (κ := κ) (τ := τ) b) (closedBall d.center (d.radius : ℝ)) := by
  apply GroundNativeQuantitativeBall.coordinate_lipschitz T b (κ : ℝ) (1/2) (τ : ℝ)
    (d.radius : ℝ) d.center d.rate (by exact_mod_cast d.pointStep.proof.threshold_nonneg)
    (fun x hx => d.pair_guards hb hx)
  intro x hx
  have hi : d.jet.input.Contains (d.jet.T x) := by rw [d.frame];exact d.input_on_ball hx
  have h := GroundNativeTransportJets.actual_derivative_norm d.jet d.responses d.response_included
    d.derivative_included d.rows (by simpa only [d.inputs] using hb) hi
  simpa only [d.frame,d.coupling,rate,NNReal.coe_mk] using h

theorem center_defect (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) :
    dist (f (T := T) (κ := κ) (τ := τ) b d.center) d.nextCenter ≤ (d.defect : ℝ) := by
  have hx : d.pointStep.input.Contains (point d.u d.v) := by
    rw [d.point_input]
    exact point_enclosed d.u d.v (by norm_num) d.basis_nonneg
  have hy := (GroundUncertainNativeBox.arithmetic_native_step d.pointStep.proof hb hx).2.2
  have ht := point_enclosed d.next_u d.next_v (by norm_num : (0 : ℚ) ≤ 0) d.basis_nonneg
  have h := coordinate_distance d.jet d.defect_nonneg hy ht d.defect_rows
  rw [d.frame] at h
  simpa only [f,center,nextCenter,GroundNativeLocal.coordinateMap,T.apply_symm_apply,
    GroundNativeJacobian.nativePairMap] using h

theorem advance (d : Data β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall d.center (d.radius : ℝ)) :
    f (T := T) (κ := κ) (τ := τ) b x ∈ closedBall d.nextCenter (d.next_radius : ℝ) := by
  apply GroundFiniteNativeTransport.step _ (by exact_mod_cast d.radius_nonneg)
    (d.lipschitz hb) (d.center_defect hb) ?_ hx
  change (d.jet.rate : ℝ)*(d.radius : ℝ)+(d.defect : ℝ) ≤ (d.next_radius : ℝ)
  exact_mod_cast d.budget
end Data
end
end SbtCosmo.Derivation.GroundCertifiedNativeTransportStep
