import SbtCosmo.Derivation.GroundCertifiedNativeTransportStep
import SbtCosmo.Derivation.GroundOffsetPrefixInitial

/-! Original-seed finite transport, uniform over a fixed background in its hull.
Each centre/radius seam and each populated step is an explicit obligation. -/
namespace SbtCosmo.Derivation.GroundCertifiedNativeTransport
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundNativeTransportGeometry GroundCertifiedNativeTransportStep Metric

structure Certificate (β : Fin 8 → Interval) (κ τ : ℚ) (T : State ≃L[ℝ] State) (N : ℕ) where
  u : Fin (N+1) → Fin 8 → ℚ
  v : Fin (N+1) → Fin 8 → ℚ
  radius : Fin (N+1) → ℚ
  steps : Fin N → GroundCertifiedNativeTransportStep.Data β κ τ T
  source_seams : ∀ j : Fin N,
    (steps j).u = u j.castSucc ∧ (steps j).v = v j.castSucc ∧ (steps j).radius = radius j.castSucc
  target_seams : ∀ j : Fin N,
    (steps j).next_u = u j.succ ∧ (steps j).next_v = v j.succ ∧ (steps j).next_radius = radius j.succ
  threshold_nonneg : 0 ≤ τ
  initial : T.symm (unpack GroundOriginalSeed.initial) ∈ closedBall
    (T.symm (point (u 0) (v 0))) (radius 0 : ℝ)

namespace Certificate
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State} {N : ℕ}
def center (c : Certificate β κ τ T N) (j : Fin (N+1)) : State := T.symm (point (c.u j) (c.v j))
def f (b : Field) : ComplexField → ComplexField := nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2)
def orbit (b : Field) (n : ℕ) : ComplexField := (f (κ := κ) (τ := τ) b)^[n] GroundOriginalSeed.initial

theorem enclosed (c : Certificate β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (j : Fin (N+1)) :
    T.symm (unpack (orbit (κ := κ) (τ := τ) b j.val)) ∈ closedBall (c.center j) (c.radius j : ℝ) := by
  refine Fin.induction ?_ (fun i ih => ?_) j
  · exact c.initial
  · have hx : T.symm (unpack (orbit (κ := κ) (τ := τ) b i.val)) ∈
        closedBall (c.steps i).center ((c.steps i).radius : ℝ) := by
      simpa only [GroundCertifiedNativeTransportStep.Data.center,(c.source_seams i).1,
        (c.source_seams i).2.1,(c.source_seams i).2.2,center] using ih
    have h := (c.steps i).advance hb hx
    have he : pack (unpack (orbit (κ := κ) (τ := τ) b i.val)) = orbit (κ := κ) (τ := τ) b i.val :=
      packCLE.apply_symm_apply _
    simp only [GroundCertifiedNativeTransportStep.Data.f,GroundNativeLocal.coordinateMap,
      T.apply_symm_apply,GroundNativeJacobian.nativePairMap] at h
    rw [he] at h
    simp only [GroundCertifiedNativeTransportStep.Data.nextCenter,(c.target_seams i).1,
      (c.target_seams i).2.1,(c.target_seams i).2.2] at h
    change T.symm (unpack (orbit (κ := κ) (τ := τ) b (i.val+1))) ∈
      closedBall (c.center i.succ) (c.radius i.succ : ℝ)
    rw [orbit,Function.iterate_succ_apply']
    exact h

theorem guards (c : Certificate β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (j : Fin N) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (orbit (κ := κ) (τ := τ) b j.val) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (orbit (κ := κ) (τ := τ) b j.val) := by
  have hx : T.symm (unpack (orbit (κ := κ) (τ := τ) b j.val)) ∈
      closedBall (c.steps j).center ((c.steps j).radius : ℝ) := by
    simpa only [GroundCertifiedNativeTransportStep.Data.center,(c.source_seams j).1,
      (c.source_seams j).2.1,(c.source_seams j).2.2,center] using c.enclosed hb j.castSucc
  have h := (c.steps j).native_guards hb hx
  simpa only [T.apply_symm_apply,packCLE_apply,packCLE_symm_apply,packCLE.apply_symm_apply] using h

theorem unit (c : Certificate β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (j : Fin (N+1)) :
    complexNormSq (orbit (κ := κ) (τ := τ) b j.val) = 1 := by
  refine Fin.induction ?_ (fun i _ => ?_) j
  · exact GroundOriginalSeed.initial_unit
  · change complexNormSq (orbit (κ := κ) (τ := τ) b (i.val+1)) = 1
    rw [orbit,Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit (by exact_mod_cast c.threshold_nonneg) (c.guards hb i).2
end Certificate
end
end SbtCosmo.Derivation.GroundCertifiedNativeTransport
