import SbtCosmo.Derivation.NativeCycle30.Pair
import SbtCosmo.Derivation.NativePairOrbit
import SbtCosmo.Derivation.NativePairDensity
namespace SbtCosmo.Derivation.NativeCycle30
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open GroundState GroundNativePhase GroundNativeIteration GroundCertifiedNativeTransportStep
open GroundCertifiedNativeTransportStep.Data GroundNativeLocal GroundNativeJacobian
open GroundRationalInterval GroundNativeBox Metric Filter
open scoped Topology

def source (x : State) : ComplexField := pack (NativeCycleFrame30.T x)
def g : ComplexField → ComplexField := nativeUpdate (GroundNativePrefixInitial.τ : ℝ)
  (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2)

theorem source_injective : Function.Injective source :=
  packCLE.injective.comp NativeCycleFrame30.T.injective

theorem source_step (x : State) : source (f x) = g (source x) := by
  change pack (NativeCycleFrame30.T (NativeCycleFrame30.T.symm
    (unpack (g (pack (NativeCycleFrame30.T x)))))) = _
  rw [NativeCycleFrame30.T.apply_symm_apply]
  exact packCLE.apply_symm_apply _

theorem source_iterate (x : State) (n : ℕ) : source ((f^[n]) x) = (g^[n]) (source x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',source_step,ih]

theorem source_continuous : Continuous source := packCLE.continuous.comp NativeCycleFrame30.T.continuous

theorem invariant : Set.MapsTo (f^[2]) (closedBall pair.first.center (Step000.ρ : ℝ))
    (closedBall pair.first.center (Step000.ρ : ℝ)) :=
  NativePairOrbit.invariant pair NativeCycleFrame30.background_sound self_defect
    (by change (pairRate : ℝ)*(Step000.ρ : ℝ)+(selfDefect : ℝ) ≤ (Step000.ρ : ℝ); exact_mod_cast cycle_budgets.2.1)

theorem density_gap_arithmetic : (9/20 : ℚ) <
    (NativePairDensity.densityBox Step001.input 4).lo-(NativePairDensity.densityBox Step000.input 4).hi := by decide +kernel

theorem actual_source_cycle : ∃ z₀ z₁ : ComplexField,
    g z₀ = z₁ ∧ g z₁ = z₀ ∧ z₁ ≠ z₀ ∧
    complexNormSq z₀ = 1 ∧ complexNormSq z₁ = 1 ∧
    (9/20 : ℝ) < Complex.normSq (z₁ 4)-Complex.normSq (z₀ 4) ∧
    ∀ z : ComplexField, NativeCycleFrame30.T.symm (unpack z) ∈
        closedBall pair.first.center (Step000.ρ : ℝ) →
      Tendsto (fun n : ℕ => (g^[2*n]) z) atTop (nhds z₀) ∧
      Tendsto (fun n : ℕ => (g^[2*n+1]) z) atTop (nhds z₁) ∧
      (∀ n : ℕ, ActivePhase (GroundNativePrefixInitial.τ : ℝ)
        (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) ((g^[n]) z) ∧
        NativeLegal (GroundNativePrefixInitial.τ : ℝ)
          (GroundKernelTube.background GroundOriginalFirstTube.originalBackground) (NativeCycleFrame30.κ : ℝ) (1/2) ((g^[n]) z)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => (g^[n]) z) atTop (nhds l) := by
  obtain ⟨a,ha,h2,hne,_,hreturn⟩ := actual_cycle
  have h2' : f (f a) = a := by simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply] using h2
  have hne' : source (f a) ≠ source a := fun h => hne (source_injective h)
  have hguards := NativePairOrbit.guards pair NativeCycleFrame30.background_sound invariant ha
  have hunit₁ : complexNormSq (source (f a)) = 1 := by
    rw [source_step]
    exact GroundNativeEscape.nativeUpdate_unit
      (by exact_mod_cast Step000.threshold_nonneg) (hguards 0).2
  have hunit₀ : complexNormSq (source a) = 1 := by
    rw [← h2',source_step]
    exact GroundNativeEscape.nativeUpdate_unit
      (by exact_mod_cast Step000.threshold_nonneg) (hguards 1).2
  have hdensity := NativePairDensity.pair_gap pair NativeCycleFrame30.background_sound ha density_gap_arithmetic
  rw [← NativePairDensity.complex_density,← NativePairDensity.complex_density] at hdensity
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hdensity
  refine ⟨source a,source (f a),(source_step a).symm,?_,hne',hunit₀,hunit₁,hdensity,?_⟩
  · rw [← source_step,h2']
  · intro z hz
    let y := NativeCycleFrame30.T.symm (unpack z)
    have hsrc : source y = z := by
      dsimp [source,y]
      rw [NativeCycleFrame30.T.apply_symm_apply]
      exact packCLE.apply_symm_apply _
    have hr := hreturn y hz
    have he := source_continuous.continuousAt.tendsto.comp hr.1
    have ho := source_continuous.continuousAt.tendsto.comp hr.2.1
    simp only [Function.comp_def,source_iterate,hsrc] at he ho
    refine ⟨he,ho,?_,?_⟩
    · intro n
      simpa only [g] using NativePairOrbit.source_guards pair NativeCycleFrame30.background_sound invariant hz n
    · rintro ⟨l,hl⟩
      have hinv : Continuous (fun z : ComplexField => NativeCycleFrame30.T.symm (unpack z)) :=
        NativeCycleFrame30.T.symm.continuous.comp packCLE.symm.continuous
      have ht := hinv.continuousAt.tendsto.comp hl
      simp only [Function.comp_def,g,NativePairOrbit.coordinate_from_source] at ht
      exact hr.2.2.2 ⟨_,ht⟩
end
end SbtCosmo.Derivation.NativeCycle30
