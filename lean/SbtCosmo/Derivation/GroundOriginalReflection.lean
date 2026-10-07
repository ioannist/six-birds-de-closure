import SbtCosmo.Derivation.GroundNativeReflection
import SbtCosmo.Derivation.GroundOriginalSpectrum

/-! Actual negative representatives of the original constructed branch,
with local native attraction and finite guarded escape returns. -/
namespace SbtCosmo.Derivation.GroundOriginalReflection
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundKernelTube GroundOriginalFirstTube GroundOriginalSamples
open GroundNativePhase GroundNativeIteration GroundNativeLocal GroundOriginalCoordinates
open Filter Metric
open scoped Topology

theorem actual_negative_native_fixed (κ m : ℝ) (hk : κ ∈ Set.Icc (0 : ℝ) 30) :
    nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) κ m
      (realEmbed (-(GroundOriginalContinuation.branch κ).1)) =
      realEmbed (-(GroundOriginalContinuation.branch κ).1) ∧
    ActivePhase GroundNativeControls.originalTolerance (background originalBackground) κ
      (realEmbed (-(GroundOriginalContinuation.branch κ).1)) ∧
    NativeLegal GroundNativeControls.originalTolerance (background originalBackground) κ m
      (realEmbed (-(GroundOriginalContinuation.branch κ).1)) := by
  obtain ⟨hf, ha, hl⟩ := GroundOriginalContinuation.whole_native_fixed κ m hk
  rw [GroundNativeReflection.realEmbed_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [GroundNativeReflection.nativeUpdate_neg _ _ _ _ GroundNativeControls.originalTolerance_guard.1 ha, hf]
  · exact (GroundNativeReflection.activePhase_neg_iff _ _ _ _).mpr ha
  · exact (GroundNativeReflection.nativeLegal_neg_iff _ _ _ _ GroundNativeControls.originalTolerance_guard.1 ha).mpr hl

theorem actual_negative_native_attraction (i : Fin 10) :
    ∃ r > 0, ∀ z : ComplexField,
      (fullBasis (i.castLE (by decide))).symm (unpack z) ∈
        closedBall ((fullBasis (i.castLE (by decide))).symm (-root (i.castLE (by decide)), 0)) r →
      Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
        (background originalBackground) (couplings (sampleIndex (i.castLE (by decide)))) (1/2))^[n] z)
        atTop (nhds (realEmbed (-root (i.castLE (by decide))))) ∧
      ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance
        (background originalBackground) (couplings (sampleIndex (i.castLE (by decide))))
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground)
          (couplings (sampleIndex (i.castLE (by decide)))) (1/2))^[n] z) ∧
      NativeLegal GroundNativeControls.originalTolerance (background originalBackground)
        (couplings (sampleIndex (i.castLE (by decide)))) (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground)
          (couplings (sampleIndex (i.castLE (by decide)))) (1/2))^[n] z) :=
  GroundNativeReflection.native_negative_local_attraction (fullBasis (i.castLE (by decide)))
    (sample_ground_return (sampleIndex (i.castLE (by decide)))).2.2.1
    (sample_ground_return (sampleIndex (i.castLE (by decide)))).2.2.2.2
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2
    (actual_stable_full_norm i)

theorem actual_negative_twenty_native_escape :
    ∃ s > 0, ∀ ε > 0, ∃ z : ComplexField, ∃ N : ℕ,
      complexNormSq z = 1 ∧ ‖(fullBasis 10).symm (GroundNativePhase.unpack z) - (fullBasis 10).symm (-root 10, 0)‖ < ε ∧
      s/2 ≤ ‖(fullBasis 10).symm (GroundNativePhase.unpack
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2))^[N] z)) -
        (fullBasis 10).symm (-root 10, 0)‖ ∧
      ∀ j ≤ N, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) 20
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2))^[j] z) ∧
        NativeLegal GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 20 (1/2))^[j] z) := by
  obtain ⟨ell, hell, v, hv, he⟩ := GroundOriginalSpectrum.actual_twenty_mode
  have hk : couplings 10 = 20 := by decide +kernel
  have hu := (sample_ground_return 10).2.2.1
  have hf := (sample_ground_return 10).2.2.2.2
  rw [hk] at hu hf
  have hn : ell < 0 := by linarith [hell.2]
  have heabs : |ell| = -ell := abs_of_neg hn
  have habs : 1 < |ell| := by rw [heabs]; linarith [hell.2]
  have hgap : ‖coordinateDerivative (fullBasis 10) (background originalBackground) 20 (1/2) (root 10)‖ < |ell|^2 := by
    rw [heabs]
    nlinarith [GroundOriginalCoordinates.actual_twenty_norm, hell.2]
  exact GroundNativeReflection.native_negative_local_escape (fullBasis 10) hu hf
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2 hv he habs hgap

theorem actual_negative_thirty_native_escape :
    ∃ s > 0, ∀ ε > 0, ∃ z : ComplexField, ∃ N : ℕ,
      complexNormSq z = 1 ∧ ‖(fullBasis 11).symm (GroundNativePhase.unpack z) - (fullBasis 11).symm (-root 11, 0)‖ < ε ∧
      s/2 ≤ ‖(fullBasis 11).symm (GroundNativePhase.unpack
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2))^[N] z)) -
        (fullBasis 11).symm (-root 11, 0)‖ ∧
      ∀ j ≤ N, ActivePhase GroundNativeControls.originalTolerance (background originalBackground) 30
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2))^[j] z) ∧
        NativeLegal GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2)
        ((nativeUpdate GroundNativeControls.originalTolerance (background originalBackground) 30 (1/2))^[j] z) := by
  obtain ⟨ell, hell, v, hv, he⟩ := GroundOriginalSpectrum.actual_thirty_mode
  have hk : couplings 11 = 30 := by decide +kernel
  have hu := (sample_ground_return 11).2.2.1
  have hf := (sample_ground_return 11).2.2.2.2
  rw [hk] at hu hf
  have hn : ell < 0 := by linarith [hell.2]
  have heabs : |ell| = -ell := abs_of_neg hn
  have habs : 1 < |ell| := by rw [heabs]; linarith [hell.2]
  have hgap : ‖coordinateDerivative (fullBasis 11) (background originalBackground) 30 (1/2) (root 11)‖ < |ell|^2 := by
    rw [heabs]
    nlinarith [GroundOriginalCoordinates.actual_thirty_norm, hell.2]
  exact GroundNativeReflection.native_negative_local_escape (fullBasis 11) hu hf
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2 hv he habs hgap


end
end SbtCosmo.Derivation.GroundOriginalReflection
