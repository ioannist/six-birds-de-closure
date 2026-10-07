import SbtCosmo.Derivation.GroundNativeDerivativeBox

/-! Interval propagation and native derivatives for a whole background box.
All arithmetic obligations are explicit; callers must populate them. -/
namespace SbtCosmo.Derivation.GroundUncertainNativeBox
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundKernelTube
open GroundNativeDerivative GroundSourceJacobian
open GroundRationalInterval GroundIntervalReciprocal GroundNativeBox
open scoped BigOperators

def sourceBox (β : Fin 8 → Interval) (κ : ℚ) (B : StateBox) (i : Fin 8) : Interval :=
  (β i).add ((Interval.point κ).mul
    ((((gradientBox B.R i).mul (gradientBox B.R i)).add ((gradientBox B.I i).mul (gradientBox B.I i))).add
      ((β i).mul (((B.R i).mul (B.R i)).add ((B.I i).mul (B.I i))))))

theorem sourceBox_sound (β : Fin 8 → Interval) (κ : ℚ) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {B : StateBox} {x : State} (hx : B.Contains x) (i : Fin 8) :
    (sourceBox β κ B i).Contains (pairSource b (κ : ℝ) x i) := by
  have hr := gradientBox_sound (fun j => (hx j).1) i
  have hi := gradientBox_sound (fun j => (hx j).2) i
  have h := Interval.add_sound (hb i)
    (Interval.mul_sound (Interval.point_sound κ)
      (Interval.add_sound (Interval.add_sound (Interval.mul_sound hr hr) (Interval.mul_sound hi hi))
        (Interval.mul_sound (hb i)
          (Interval.add_sound (Interval.mul_sound (hx i).1 (hx i).1) (Interval.mul_sound (hx i).2 (hx i).2)))))
  simpa only [sourceBox, pairSource, pow_two] using h

structure Arithmetic (β : Fin 8 → Interval) (κ τ : ℚ) (B D : StateBox) (z : Fin 9 → ℚ)
    (r q y : ℚ) (C : Matrix (Fin 9) (Fin 9) ℚ) (K L : Interval) : Prop where
  ground : GroundBackgroundKernel.Arithmetic (sourceBox β κ B) z r q y C
  overlap_inverse : GroundIntervalReciprocal.Arithmetic (overlapBox B (GroundBackgroundKernel.fieldBox z r)) K
  mixed_inverse : GroundIntervalReciprocal.Arithmetic
    (normBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K)) L
  threshold_nonneg : 0 ≤ τ
  phase_margin : τ^2 < (overlapBox B (GroundBackgroundKernel.fieldBox z r)).lo
  normalization_margin : τ^2 < (normBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K)).lo
  output : (normalizedBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K) L).Included D

theorem arithmetic_native_step {β : Fin 8 → Interval} {κ τ : ℚ} {B D : StateBox} {z : Fin 9 → ℚ}
    {r q y : ℚ} {C : Matrix (Fin 9) (Fin 9) ℚ} {K L : Interval}
    (h : Arithmetic β κ τ B D z r q y C K L) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State} (hx : B.Contains x) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (pack x) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack x) ∧
    D.Contains (unpack (nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2) (pack x))) := by
  have hs := sourceBox_sound β κ hb hx
  have hg := GroundBackgroundKernel.actual_selected_enclosed h.ground hs
  have hr := overlapBox_sound hx hg
  have hk := (inverse_sqrt_sound h.overlap_inverse hr).2
  have hτ : (0 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast h.threshold_nonneg
  have hb : (τ : ℝ)^2 < ((overlapBox B (GroundBackgroundKernel.fieldBox z r)).lo : ℝ) := by
    exact_mod_cast h.phase_margin
  have ho : (τ : ℝ) < overlapNorm b (κ : ℝ) x := threshold_guard hr hτ hb
  have hm := mixedBox_sound hx hg hk
  have hn := normBox_sound hm
  have hl := (inverse_sqrt_sound h.mixed_inverse hn).2
  have hnb : (τ : ℝ)^2 < ((normBox (mixedBox B (GroundBackgroundKernel.fieldBox z r) K)).lo : ℝ) := by
    exact_mod_cast h.normalization_margin
  have hnorm := threshold_guard hn hτ hnb
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using ho
  · rw [NativeLegal, ← pack_mixed_native hτ b (κ : ℝ) (1/2) x ho, norm_pack]
    exact hnorm
  · rw [← fullMap_native_return hτ b (κ : ℝ) (1/2) x ho]
    exact StateBox.included_sound h.output (normalizedBox_sound hm hl)


def sourceDerivativeBox (β : Fin 8 → Interval) (κ : ℚ) (B H : StateBox) (i : Fin 8) : Interval :=
  (Interval.point (2*κ)).mul
    ((((gradientBox B.R i).mul (gradientBox H.R i)).add
      (((β i).mul (B.R i)).mul (H.R i))).add
     (((gradientBox B.I i).mul (gradientBox H.I i)).add
      (((β i).mul (B.I i)).mul (H.I i))))

theorem sourceDerivativeBox_sound (β : Fin 8 → Interval) (κ : ℚ) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {B H : StateBox} {x h : State}
    (hx : B.Contains x) (hh : H.Contains h) (i : Fin 8) :
    (sourceDerivativeBox β κ B H i).Contains (pairSourceDerivative b (κ : ℝ) x h i) := by
  have hdR := Interval.add_sound
    (Interval.mul_sound (gradientBox_sound (fun j => (hx j).1) i) (gradientBox_sound (fun j => (hh j).1) i))
    (Interval.mul_sound (Interval.mul_sound (hb i) (hx i).1) (hh i).1)
  have hdI := Interval.add_sound
    (Interval.mul_sound (gradientBox_sound (fun j => (hx j).2) i) (gradientBox_sound (fun j => (hh j).2) i))
    (Interval.mul_sound (Interval.mul_sound (hb i) (hx i).2) (hh i).2)
  have hv := Interval.mul_sound (Interval.point_sound (2*κ)) (Interval.add_sound hdR hdI)
  have he : pairSourceDerivative b (κ : ℝ) x h i =
      ((2*κ : ℚ) : ℝ) *
        (GroundState.gradient x.1 i*GroundState.gradient h.1 i+b i*x.1 i*h.1 i+
         (GroundState.gradient x.2 i*GroundState.gradient h.2 i+b i*x.2 i*h.2 i)) := by
    simp [pairSourceDerivative, sourceDerivative_apply]
    ring
  rw [he]
  exact hv

theorem selectedDerivative_enclosed {β : Fin 8 → Interval} {κ : ℚ} {B H : StateBox} {z : Fin 9 → ℚ}
    {r q a y e : ℚ} {C : Matrix (Fin 9) (Fin 9) ℚ}
    (hg : GroundBackgroundKernel.Arithmetic (sourceBox β κ B) z r q a C)
    (hr : GroundBackgroundResponse.ResponseArithmetic C (GroundBackgroundKernel.fieldBox z r)
      (sourceDerivativeBox β κ B H) q y e) {b : Field} (hb : ∀ i, (β i).Contains (b i)) {x h : State} (hx : B.Contains x) (hh : H.Contains h) (i : Fin 8) :
    (GroundBackgroundResponse.responseInterval C (GroundBackgroundKernel.fieldBox z r)
      (sourceDerivativeBox β κ B H) e i).Contains (selectedDerivative b (κ : ℝ) x h i) :=
  GroundBackgroundResponse.actual_selector_response_enclosed hg hr (sourceBox_sound β κ hb hx)
    (sourceDerivativeBox_sound β κ hb hx hh) i

end
end SbtCosmo.Derivation.GroundUncertainNativeBox
