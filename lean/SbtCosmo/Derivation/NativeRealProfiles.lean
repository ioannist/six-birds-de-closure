import SbtCosmo.Derivation.GroundNativeIteration
namespace SbtCosmo.Derivation.NativeRealProfiles
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration Filter
open scoped Topology BigOperators

def IsReal (z : ComplexField) : Prop := ∀ i, (z i).im = 0

theorem candidate_real (b : Field) (κ : ℝ) (z : ComplexField) :
    IsReal (nativeCandidate b κ z) := by
  intro i
  simp [nativeCandidate,realEmbed]

theorem phase_real {τ : ℝ} {candidate reference : ComplexField}
    (hτ : 0 ≤ τ) (hc : IsReal candidate) (hr : IsReal reference) :
    IsReal (nativePhase τ candidate reference) := by
  have ho : (overlap candidate reference).im = 0 := by
    have hc' : ∀ i, (candidate i).im = 0 := hc
    have hr' : ∀ i, (reference i).im = 0 := hr
    simp [overlap,Complex.mul_im,hc',hr']
  by_cases h : ‖overlap candidate reference‖ ≤ τ
  · simpa only [nativePhase,h,if_pos] using hc
  · rw [nativePhase_ratio hτ (not_le.mp h)]
    intro i
    simp [Complex.mul_im,Complex.div_ofReal_im,hc i,ho]

theorem update_real {τ : ℝ} (b : Field) (κ m : ℝ) {z : ComplexField}
    (hτ : 0 ≤ τ) (hz : IsReal z) : IsReal (nativeUpdate τ b κ m z) := by
  have hp := phase_real hτ (candidate_real b κ z) hz
  intro i
  simp [nativeUpdate,complexNormalize,nativeMixed,Complex.div_ofReal_im,
    Complex.mul_im,hz i,hp i]

theorem iterate_real {τ : ℝ} (b : Field) (κ m : ℝ) {z : ComplexField}
    (hτ : 0 ≤ τ) (hz : IsReal z) (n : ℕ) :
    IsReal ((nativeUpdate τ b κ m)^[n] z) := by
  induction n with
  | zero => exact hz
  | succ n ih => rw [Function.iterate_succ_apply'];exact update_real b κ m hτ ih

theorem limit_real {z : ℕ → ComplexField} {a : ComplexField}
    (hz : ∀ n, IsReal (z n)) (ht : Tendsto z atTop (nhds a)) : IsReal a := by
  intro i
  have hc : Continuous (fun z : ComplexField => (z i).im) := by fun_prop
  have hl := (hc.tendsto a).comp ht
  have hzero : Tendsto (fun n => (z n i).im) atTop (nhds (0 : ℝ)) := by
    have he : (fun n => (z n i).im) = (fun _ : ℕ => (0 : ℝ)) :=
      funext (fun n => hz n i)
    rw [he]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hl hzero

theorem real_embed_return {z : ComplexField} (hz : IsReal z) :
    realEmbed (fun i => (z i).re) = z := by
  funext i
  apply Complex.ext
  · rfl
  · simpa using (hz i).symm
end
end SbtCosmo.Derivation.NativeRealProfiles
