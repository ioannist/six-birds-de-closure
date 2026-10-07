import SbtCosmo.Derivation.NativeOriginalSampleInterface
import SbtCosmo.Derivation.NativeOriginalEventualSourceSuccess
import SbtCosmo.Derivation.NativeStableSeed001.Transport
import SbtCosmo.Derivation.NativeStableSeed001.Sixty
import SbtCosmo.Derivation.NativeStableSeed003.Transport
import SbtCosmo.Derivation.NativeStableSeed003.Sixty
import SbtCosmo.Derivation.NativeStableSeed004.Transport
import SbtCosmo.Derivation.NativeStableSeed004.Sixty
import SbtCosmo.Derivation.NativeStableSeed005.Transport
import SbtCosmo.Derivation.NativeStableSeed005.Sixty
import SbtCosmo.Derivation.NativeStableSeed006.Transport
import SbtCosmo.Derivation.NativeStableSeed006.Sixty
import SbtCosmo.Derivation.NativeStableSeed007.Transport
import SbtCosmo.Derivation.NativeStableSeed007.Sixty
import SbtCosmo.Derivation.NativeStableSeed008.Transport
import SbtCosmo.Derivation.NativeStableSeed008.Sixty
import SbtCosmo.Derivation.NativeStableSeed009.Transport
import SbtCosmo.Derivation.NativeStableSeed009.Sixty
import SbtCosmo.Derivation.NativeCycleSeed20.Return
import SbtCosmo.Derivation.NativeCycleSeed20.Sixty
import SbtCosmo.Derivation.NativeCycleSeed30.Return
import SbtCosmo.Derivation.NativeCycleSeed30.Sixty
import SbtCosmo.Derivation.NativeStableSeed009.PrefixFailures
import SbtCosmo.Derivation.NativeCycleSeed20.PrefixFailures
import SbtCosmo.Derivation.NativeCycleSeed30.PrefixFailures

/-! Original twelve sampled source orbits: guarded unit execution, stable limits,
period-two returns,and exact sixty-update source verdicts. Generated candidate:
no claim is proved until all finite imports and this module pass fresh checking. -/
namespace SbtCosmo.Derivation.NativeOriginalSampleResults
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
-- The generated frame bindings use uniform simplification lists.
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundSourceDiagnostics Metric Filter
open NativeOriginalSampleInterface
open scoped Topology

def densityGap (i : Fin 12) : ℝ := if i.val=10 then 1/4 else 9/20

/-- Every actual sample orbit is active,legally normalized,and unit at every update. -/
theorem original_sample_guards_unit (i : Fin 12) (n : ℕ) :
    ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) (orbit i n) ∧
    NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) (orbit i n) ∧
    complexNormSq (orbit i n) = 1 := by
  fin_cases i
  all_goals dsimp only at *
  · exact zero_seed_return.2 n
  · simpa [orbit,g,b,κ,target,NativeStableSeed001.g,NativeStableFrame001.u,NativeStableFrame001.κ,GroundSamples.Point001.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed001.original_seed_return.2 n)
  · exact positive_seed_return.2 n
  · simpa [orbit,g,b,κ,target,NativeStableSeed003.g,NativeStableFrame003.u,NativeStableFrame003.κ,GroundSamples.Point003.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed003.original_seed_return.2 n)
  · simpa [orbit,g,b,κ,target,NativeStableSeed004.g,NativeStableFrame004.u,NativeStableFrame004.κ,GroundSamples.Point004.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed004.original_seed_return.2 n)
  · simpa [orbit,g,b,κ,target,NativeStableSeed005.g,NativeStableFrame005.u,NativeStableFrame005.κ,GroundSamples.Point005.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed005.original_seed_return.2 n)
  · simpa [orbit,g,b,κ,target,NativeStableSeed006.g,NativeStableFrame006.u,NativeStableFrame006.κ,GroundSamples.Point006.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed006.original_seed_return.2 n)
  · simpa [orbit,g,b,κ,target,NativeStableSeed007.g,NativeStableFrame007.u,NativeStableFrame007.κ,GroundSamples.Point007.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed007.original_seed_return.2 n)
  · simpa [orbit,g,b,κ,target,NativeStableSeed008.g,NativeStableFrame008.u,NativeStableFrame008.κ,GroundSamples.Point008.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed008.original_seed_return.2 n)
  · simpa [orbit,g,b,κ,target,NativeStableSeed009.g,NativeStableFrame009.u,NativeStableFrame009.κ,GroundSamples.Point009.a,GroundNativePrefixInitial.tolerance_return] using (NativeStableSeed009.original_seed_return.2 n)
  · obtain ⟨a,b',_,_,_,_,_,_,_,hg,_⟩ := NativeCycleSeed20.original_seed_cycle
    simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return] using hg n
  · obtain ⟨a,b',_,_,_,_,_,_,_,hg,_⟩ := NativeCycleSeed30.original_seed_cycle
    simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return] using hg n

/-- All ten original samples through15 converge to the actual negative coupled root. -/
theorem original_sample_stable_return (i : Fin 12) (hi : i.val < 10) :
    Tendsto (orbit i) atTop (nhds (target i)) := by
  fin_cases i
  all_goals dsimp only at *
  · exact zero_seed_return.1
  · have hf : orbit 1 = (fun n : ℕ => (NativeStableSeed001.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed001.g,NativeStableFrame001.u,NativeStableFrame001.κ,GroundSamples.Point001.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 1 = realEmbed (-NativeStableFrame001.u) := by simp [orbit,g,b,κ,target,NativeStableSeed001.g,NativeStableFrame001.u,NativeStableFrame001.κ,GroundSamples.Point001.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed001.original_seed_return.1
  · exact positive_seed_return.1
  · have hf : orbit 3 = (fun n : ℕ => (NativeStableSeed003.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed003.g,NativeStableFrame003.u,NativeStableFrame003.κ,GroundSamples.Point003.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 3 = realEmbed (-NativeStableFrame003.u) := by simp [orbit,g,b,κ,target,NativeStableSeed003.g,NativeStableFrame003.u,NativeStableFrame003.κ,GroundSamples.Point003.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed003.original_seed_return.1
  · have hf : orbit 4 = (fun n : ℕ => (NativeStableSeed004.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed004.g,NativeStableFrame004.u,NativeStableFrame004.κ,GroundSamples.Point004.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 4 = realEmbed (-NativeStableFrame004.u) := by simp [orbit,g,b,κ,target,NativeStableSeed004.g,NativeStableFrame004.u,NativeStableFrame004.κ,GroundSamples.Point004.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed004.original_seed_return.1
  · have hf : orbit 5 = (fun n : ℕ => (NativeStableSeed005.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed005.g,NativeStableFrame005.u,NativeStableFrame005.κ,GroundSamples.Point005.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 5 = realEmbed (-NativeStableFrame005.u) := by simp [orbit,g,b,κ,target,NativeStableSeed005.g,NativeStableFrame005.u,NativeStableFrame005.κ,GroundSamples.Point005.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed005.original_seed_return.1
  · have hf : orbit 6 = (fun n : ℕ => (NativeStableSeed006.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed006.g,NativeStableFrame006.u,NativeStableFrame006.κ,GroundSamples.Point006.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 6 = realEmbed (-NativeStableFrame006.u) := by simp [orbit,g,b,κ,target,NativeStableSeed006.g,NativeStableFrame006.u,NativeStableFrame006.κ,GroundSamples.Point006.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed006.original_seed_return.1
  · have hf : orbit 7 = (fun n : ℕ => (NativeStableSeed007.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed007.g,NativeStableFrame007.u,NativeStableFrame007.κ,GroundSamples.Point007.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 7 = realEmbed (-NativeStableFrame007.u) := by simp [orbit,g,b,κ,target,NativeStableSeed007.g,NativeStableFrame007.u,NativeStableFrame007.κ,GroundSamples.Point007.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed007.original_seed_return.1
  · have hf : orbit 8 = (fun n : ℕ => (NativeStableSeed008.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed008.g,NativeStableFrame008.u,NativeStableFrame008.κ,GroundSamples.Point008.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 8 = realEmbed (-NativeStableFrame008.u) := by simp [orbit,g,b,κ,target,NativeStableSeed008.g,NativeStableFrame008.u,NativeStableFrame008.κ,GroundSamples.Point008.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed008.original_seed_return.1
  · have hf : orbit 9 = (fun n : ℕ => (NativeStableSeed009.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,target,NativeStableSeed009.g,NativeStableFrame009.u,NativeStableFrame009.κ,GroundSamples.Point009.a,GroundNativePrefixInitial.tolerance_return]
    have ht : target 9 = realEmbed (-NativeStableFrame009.u) := by simp [orbit,g,b,κ,target,NativeStableSeed009.g,NativeStableFrame009.u,NativeStableFrame009.κ,GroundSamples.Point009.a,GroundNativePrefixInitial.tolerance_return]
    simpa only [←hf,←ht] using NativeStableSeed009.original_seed_return.1
  · omega
  · omega

/-- The actual seed at20/30 approaches distinct unit period-two states,with the
sample's full earned site-density gap and no whole-state or site-density limit. -/
theorem original_sample_cyclic_return (i : Fin 12) (hi : 10 ≤ i.val) :
    ∃ a c : ComplexField,
      g i a = c ∧ g i c = a ∧ c ≠ a ∧ complexNormSq a = 1 ∧ complexNormSq c = 1 ∧
      densityGap i < Complex.normSq (c 4)-Complex.normSq (a 4) ∧
      Tendsto (fun n : ℕ => orbit i (2*n)) atTop (nhds a) ∧
      Tendsto (fun n : ℕ => orbit i (2*n+1)) atTop (nhds c) ∧
      (¬ ∃ l, Tendsto (orbit i) atTop (nhds l)) ∧
      ¬ ∃ l, Tendsto (fun n : ℕ => Complex.normSq (orbit i n 4)) atTop (nhds l) := by
  fin_cases i
  all_goals dsimp only at *
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have hf : orbit 10 = (fun n : ℕ => (NativeCycleSeed20.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return]
    have hg : g 10 = NativeCycleSeed20.g := by
      funext z
      simp [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return]
    obtain ⟨a,c,h01,h10,hu0,hu1,hgap,he,ho,_,hn,_,_,_,hdn⟩ := NativeCycleSeed20.original_seed_cycle
    have hne : c ≠ a := by
      intro h
      rw [h] at hgap
      norm_num at hgap
    refine ⟨a,c,?_,?_,hne,hu0,hu1,?_,?_,?_,?_,?_⟩
    · simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return] using h01
    · simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return] using h10
    · simpa [densityGap] using hgap
    · simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return] using he
    · simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return] using ho
    · simpa only [←hf] using hn
    · simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,GroundNativePrefixInitial.tolerance_return] using hdn
  · have hf : orbit 11 = (fun n : ℕ => (NativeCycleSeed30.g^[n]) GroundOriginalSeed.initial) := by
      funext n
      simp [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return]
    have hg : g 11 = NativeCycleSeed30.g := by
      funext z
      simp [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return]
    obtain ⟨a,c,h01,h10,hu0,hu1,hgap,he,ho,_,hn,_,_,_,hdn⟩ := NativeCycleSeed30.original_seed_cycle
    have hne : c ≠ a := by
      intro h
      rw [h] at hgap
      norm_num at hgap
    refine ⟨a,c,?_,?_,hne,hu0,hu1,?_,?_,?_,?_,?_⟩
    · simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return] using h01
    · simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return] using h10
    · simpa [densityGap] using hgap
    · simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return] using he
    · simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return] using ho
    · simpa only [←hf] using hn
    · simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,GroundNativePrefixInitial.tolerance_return] using hdn

/-- Infinite-limit classification of the finite original twelve-sample family. -/
theorem original_sample_has_limit_iff (i : Fin 12) :
    (∃ l : ComplexField, Tendsto (orbit i) atTop (nhds l)) ↔ i.val < 10 := by
  constructor
  · intro hl
    by_contra hi
    have hge : 10 ≤ i.val := by omega
    obtain ⟨a,c,_,_,_,_,_,_,_,_,hn,_⟩ := original_sample_cyclic_return i hge
    exact hn hl
  · intro hi
    exact ⟨target i,original_sample_stable_return i hi⟩

/-- Each site's source density has the actual coupled-root limit at stable samples. -/
theorem original_sample_stable_density_limit (i : Fin 12) (hi : i.val < 10) (j : Fin 8) :
    Tendsto (fun n : ℕ => Complex.normSq (orbit i n j)) atTop
      (nhds (Complex.normSq (target i j))) := by
  have hc : Continuous (fun z : ComplexField => Complex.normSq (z j)) := by fun_prop
  exact (hc.tendsto (target i)).comp (original_sample_stable_return i hi)

/-- Exact native-source verdict after sixty updates; not an earliest-stop theorem. -/
theorem original_sample_sixty_tests_iff (i : Fin 12) :
    MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      b (κ i : ℝ) (1/2) (orbit i 59) (orbit i 60) ↔ i.val < 9 := by
  fin_cases i
  all_goals dsimp only at *
  · exact ⟨fun _ => by decide,fun _ => zero_sixty_tests⟩
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed001.SixtyGeometry.orbit,NativeStableSeed001.SixtyGeometry.g,NativeStableSeed001.SixtyGeometry.b,NativeStableFrame001.κ,GroundSamples.Point001.a] using NativeStableSeed001.Sixty.actual_four_source_tests
  · exact ⟨fun _ => by decide,fun _ => positive_sixty_tests⟩
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed003.SixtyGeometry.orbit,NativeStableSeed003.SixtyGeometry.g,NativeStableSeed003.SixtyGeometry.b,NativeStableFrame003.κ,GroundSamples.Point003.a] using NativeStableSeed003.Sixty.actual_four_source_tests
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed004.SixtyGeometry.orbit,NativeStableSeed004.SixtyGeometry.g,NativeStableSeed004.SixtyGeometry.b,NativeStableFrame004.κ,GroundSamples.Point004.a] using NativeStableSeed004.Sixty.actual_four_source_tests
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed005.SixtyGeometry.orbit,NativeStableSeed005.SixtyGeometry.g,NativeStableSeed005.SixtyGeometry.b,NativeStableFrame005.κ,GroundSamples.Point005.a] using NativeStableSeed005.Sixty.actual_four_source_tests
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed006.SixtyGeometry.orbit,NativeStableSeed006.SixtyGeometry.g,NativeStableSeed006.SixtyGeometry.b,NativeStableFrame006.κ,GroundSamples.Point006.a] using NativeStableSeed006.Sixty.actual_four_source_tests
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed007.SixtyGeometry.orbit,NativeStableSeed007.SixtyGeometry.g,NativeStableSeed007.SixtyGeometry.b,NativeStableFrame007.κ,GroundSamples.Point007.a] using NativeStableSeed007.Sixty.actual_four_source_tests
  · constructor
    · intro _;decide
    · intro _
      simpa [orbit,g,b,κ,NativeStableSeed008.SixtyGeometry.orbit,NativeStableSeed008.SixtyGeometry.g,NativeStableSeed008.SixtyGeometry.b,NativeStableFrame008.κ,GroundSamples.Point008.a] using NativeStableSeed008.Sixty.actual_four_source_tests
  · have hf : ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
        b (κ 9 : ℝ) (1/2) (orbit 9 59) (orbit 9 60) := by
      simpa [orbit,g,b,κ,NativeStableSeed009.SixtyGeometry.orbit,NativeStableSeed009.SixtyGeometry.g,NativeStableSeed009.SixtyGeometry.b,NativeStableFrame009.κ,GroundSamples.Point009.a] using NativeStableSeed009.Sixty.actual_four_source_tests_fail
    exact ⟨fun h => (hf h).elim,fun h => by norm_num at h⟩
  · have hf : ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
        b (κ 10 : ℝ) (1/2) (orbit 10 59) (orbit 10 60) := by
      simpa [orbit,g,b,κ,NativeCycleSeed20.Sixty.orbit,NativeCycleSeed20.Sixty.g,NativeCycleSeed20.SixtyGeometry.g,NativeCycleFrame20.κ] using NativeCycleSeed20.Sixty.actual_four_source_tests_fail
    exact ⟨fun h => (hf h).elim,fun h => by norm_num at h⟩
  · have hf : ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
        b (κ 11 : ℝ) (1/2) (orbit 11 59) (orbit 11 60) := by
      simpa [orbit,g,b,κ,NativeCycleSeed30.Sixty.orbit,NativeCycleSeed30.Sixty.g,NativeCycleSeed30.SixtyGeometry.g,NativeCycleFrame30.κ] using NativeCycleSeed30.Sixty.actual_four_source_tests_fail
    exact ⟨fun h => (hf h).elim,fun h => by norm_num at h⟩

/-- At15 the actual orbit has an infinite limit although its sixty-update test fails. -/
theorem coupling_fifteen_finite_failure_with_limit :
    (∃ l : ComplexField, Tendsto (orbit 9) atTop (nhds l)) ∧
    ¬ MeetsConvergence GroundNativeControls.originalTolerance GroundOriginalResiduals.ε
      b (κ 9 : ℝ) (1/2) (orbit 9 59) (orbit 9 60) := by
  refine ⟨(original_sample_has_limit_iff 9).mpr (by decide),?_⟩
  intro h
  have hf := (original_sample_sixty_tests_iff 9).mp h
  norm_num at hf

/-- Literal unit normalization rules out norm blow-up along all twelve actual sample orbits. -/
theorem original_sample_euclidean_norm (i : Fin 12) (n : ℕ) :
    GroundComplexEuclidean.l2 (orbit i n) = 1 := by
  have hu := (original_sample_guards_unit i n).2.2
  have hs := GroundComplexEuclidean.l2_sq (orbit i n)
  nlinarith [GroundComplexEuclidean.l2_nonneg (orbit i n)]

/-- Eventual source-test success has a different sample boundary from the
sixty-update verdict: the coupling15 sample eventually passes. -/
theorem original_sample_eventual_tests_iff (i : Fin 12) :
    (∀ᶠ n in atTop, MeetsConvergence GroundNativeControls.originalTolerance
      GroundOriginalResiduals.ε b (κ i : ℝ) (1/2) (orbit i n) (orbit i (n+1))) ↔
      i.val < 10 := by
  constructor
  · intro hp
    by_contra hi
    have hge : 10 ≤ i.val := by omega
    fin_cases i
    all_goals dsimp only at *
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · have hn : ∀ᶠ n in atTop, ¬ MeetsConvergence GroundNativeControls.originalTolerance
          GroundOriginalResiduals.ε b (κ 10 : ℝ) (1/2) (orbit 10 n) (orbit 10 (n+1)) := by
        simpa [orbit,g,b,κ,NativeCycleSeed20.g,NativeCycleFrame20.κ,
          GroundNativePrefixInitial.tolerance_return] using
            NativeCycleSeed20.original_seed_eventual_source_failure.2
      obtain ⟨n, hpn, hnn⟩ := (hp.and hn).exists
      exact hnn hpn
    · have hn : ∀ᶠ n in atTop, ¬ MeetsConvergence GroundNativeControls.originalTolerance
          GroundOriginalResiduals.ε b (κ 11 : ℝ) (1/2) (orbit 11 n) (orbit 11 (n+1)) := by
        simpa [orbit,g,b,κ,NativeCycleSeed30.g,NativeCycleFrame30.κ,
          GroundNativePrefixInitial.tolerance_return] using
            NativeCycleSeed30.original_seed_eventual_source_failure.2
      obtain ⟨n, hpn, hnn⟩ := (hp.and hn).exists
      exact hnn hpn
  · intro hi
    exact NativeOriginalEventualSourceSuccess.original_sample_eventual_tests_of_limit i
      (fun n => (original_sample_guards_unit i n).2.2)
      (original_sample_stable_return i hi)

/-- Coupling15 eventually passes every literal source diagnostic, despite its
verified failure at update60. No earliest successful update is asserted. -/
theorem coupling_fifteen_eventual_success :
    ∀ᶠ n in atTop, MeetsConvergence GroundNativeControls.originalTolerance
      GroundOriginalResiduals.ε b (κ 9 : ℝ) (1/2) (orbit 9 n) (orbit 9 (n+1)) :=
  (original_sample_eventual_tests_iff 9).mpr (by decide)


/-- A successful diagnostic prefix among updates1..60 exists exactly for the
nine original samples below15. The source itself always runs its fixed budget. -/
theorem original_sample_successful_prefix_iff (i : Fin 12) :
    (∃ n : ℕ, n < 60 ∧ MeetsConvergence GroundNativeControls.originalTolerance
      GroundOriginalResiduals.ε b (κ i : ℝ) (1/2) (orbit i n) (orbit i (n+1))) ↔
      i.val < 9 := by
  constructor
  · rintro ⟨n,hn,hp⟩
    by_contra hi
    have hge : 9 ≤ i.val := by omega
    fin_cases i
    all_goals dsimp only at *
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · have hf : ¬ MeetsConvergence GroundNativeControls.originalTolerance
          GroundOriginalResiduals.ε b (κ 9 : ℝ) (1/2) (orbit 9 n) (orbit 9 (n+1)) := by
        simpa [orbit,g,b,κ,NativeStableSeed009.SixtyGeometry.orbit,
          NativeStableSeed009.SixtyGeometry.g,NativeStableSeed009.SixtyGeometry.b,
          NativeStableFrame009.κ,GroundSamples.Point009.a] using
            NativeStableSeed009.PrefixFailures.all_first_sixty_fail n hn
      exact hf hp
    · have hf : ¬ MeetsConvergence GroundNativeControls.originalTolerance
          GroundOriginalResiduals.ε b (κ 10 : ℝ) (1/2) (orbit 10 n) (orbit 10 (n+1)) := by
        simpa [orbit,g,b,κ,NativeCycleSeed20.Sixty.orbit,NativeCycleSeed20.Sixty.g,
          NativeCycleSeed20.SixtyGeometry.g,NativeCycleFrame20.κ] using
            NativeCycleSeed20.PrefixFailures.all_first_sixty_fail n hn
      exact hf hp
    · have hf : ¬ MeetsConvergence GroundNativeControls.originalTolerance
          GroundOriginalResiduals.ε b (κ 11 : ℝ) (1/2) (orbit 11 n) (orbit 11 (n+1)) := by
        simpa [orbit,g,b,κ,NativeCycleSeed30.Sixty.orbit,NativeCycleSeed30.Sixty.g,
          NativeCycleSeed30.SixtyGeometry.g,NativeCycleFrame30.κ] using
            NativeCycleSeed30.PrefixFailures.all_first_sixty_fail n hn
      exact hf hp
  · intro hi
    exact ⟨59,by decide,(original_sample_sixty_tests_iff i).mpr hi⟩

end
end SbtCosmo.Derivation.NativeOriginalSampleResults
