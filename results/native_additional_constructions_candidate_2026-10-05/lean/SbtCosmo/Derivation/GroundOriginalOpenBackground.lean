import SbtCosmo.Derivation.GroundOriginalOffsetSeed
import SbtCosmo.Derivation.GroundNativeBackgroundSeedReturn

/-! Positive open background neighborhoods for the actual original complex
seed at all eighteen stored rounded offset backgrounds. The nearby ground
branches are earned by the existing implicit-function theorem and certified
Newton defects. No continuous whole-window classification is asserted. -/
namespace SbtCosmo.Derivation.GroundOriginalOpenBackground
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open GroundState GroundBorder GroundSourceJacobian GroundRootCertificate GroundPointCoordinates GroundResidualEnclosure
open GroundOriginalOffsets GroundParameterEquations GroundParameterBranch
open GroundNativePhase GroundNativeIteration GroundNativeLocal Filter Metric
open scoped Topology ContDiff

theorem rounded_newton_defect (i : Fin 18) :
    ‖correctionDerivative (rounded_b i) ((certificates i).κ : ℝ)
      (preconditioner (certificates i).C) (roundedRoot i)‖ < 1 := by
  exact ((roundedTube i).defect _ (rounded_interval i) _ (rounded_root_spec i).1).trans_lt
    (roundedTube i).rate_lt

def localPoint (i : Fin 18) (b : Field) : Point :=
  branch (rounded_b i,((certificates i).κ : ℝ)) (roundedRoot i)
    (preconditioner (certificates i).C) (rounded_newton_defect i) (b,((certificates i).κ : ℝ))

theorem localPoint_center (i : Fin 18) : localPoint i (rounded_b i) = roundedRoot i :=
  branch_center (rounded_b i,((certificates i).κ : ℝ)) (roundedRoot i)
    (preconditioner (certificates i).C) (rounded_newton_defect i)

theorem localPoint_smooth_at (i : Fin 18) : ContDiffAt ℝ ∞ (localPoint i) (rounded_b i) := by
  have hp : ContDiffAt ℝ ∞ (fun b : Field => (b,((certificates i).κ : ℝ))) (rounded_b i) := by fun_prop
  exact ContDiffAt.comp
    (g := branch (rounded_b i,((certificates i).κ : ℝ)) (roundedRoot i)
      (preconditioner (certificates i).C) (rounded_newton_defect i))
    (f := fun b : Field => (b,((certificates i).κ : ℝ))) (rounded_b i)
    (branch_smooth_at (rounded_b i,((certificates i).κ : ℝ)) (roundedRoot i)
      (preconditioner (certificates i).C) (rounded_newton_defect i)) hp

theorem localPoint_ground_eventually (i : Fin 18) :
    ∀ᶠ b in nhds (rounded_b i),
      residual b ((certificates i).κ : ℝ) (localPoint i b) = 0 ∧
      (∀ j, 0 < (localPoint i b).1 j) ∧
      normSq (localPoint i b).1 = 1 ∧
      groundPair (sourcePotential b ((certificates i).κ : ℝ) (localPoint i b).1) = localPoint i b ∧
      groundMap b ((certificates i).κ : ℝ) (localPoint i b).1 = (localPoint i b).1 := by
  have hp : Tendsto (fun b : Field => (b,((certificates i).κ : ℝ)))
      (nhds (rounded_b i)) (nhds (rounded_b i,((certificates i).κ : ℝ))) :=
    continuousAt_id.prodMk continuousAt_const
  have hroot := branch_root_eventually (p := (rounded_b i,((certificates i).κ : ℝ)))
    (x := roundedRoot i) (preconditioner (certificates i).C)
    (rounded_newton_defect i) (rounded_root_spec i).2.1
  have hpos := branch_positive_eventually (p := (rounded_b i,((certificates i).κ : ℝ)))
    (x := roundedRoot i) (preconditioner (certificates i).C)
    (rounded_newton_defect i) (rounded_root_positive i)
  have hground := branch_ground_eventually (p := (rounded_b i,((certificates i).κ : ℝ)))
    (x := roundedRoot i) (preconditioner (certificates i).C)
    (rounded_newton_defect i) (rounded_root_spec i).2.1 (rounded_root_positive i)
  filter_upwards [hp.eventually hroot,hp.eventually hpos,hp.eventually hground] with b hz hp hg
  exact ⟨hz,hp,hg⟩

theorem rounded_coordinate_contraction (i : Fin 18) :
    ‖coordinateDerivative (GroundOriginalOffsetStability.fullBasis i) (rounded_b i)
      ((certificates i).κ : ℝ) (1/2) (roundedRoot i).1‖ < 1 :=
  GroundOriginalOffsetStability.actual_stable_full_norm i (rounded_inputs_sound i)
    (rounded_root_spec i).1 (rounded_ground_return i).2 (rounded_root_spec i).2.2.2.1

theorem open_background_original_seed_return (i : Fin 18) :
    ∃ δ > 0, ∀ b ∈ closedBall (rounded_b i) δ,
      residual b ((certificates i).κ : ℝ) (localPoint i b) = 0 ∧
      (∀ j, 0 < (localPoint i b).1 j) ∧
      normSq (localPoint i b).1 = 1 ∧
      groundPair (sourcePotential b ((certificates i).κ : ℝ) (localPoint i b).1) = localPoint i b ∧
      groundMap b ((certificates i).κ : ℝ) (localPoint i b).1 = (localPoint i b).1 ∧
      Tendsto (fun n : ℕ => (nativeUpdate GroundNativeControls.originalTolerance
        b ((certificates i).κ : ℝ) (1/2))^[n] GroundOriginalSeed.initial)
        atTop (nhds (realEmbed (-(localPoint i b).1))) ∧
      ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b ((certificates i).κ : ℝ)
          ((nativeUpdate GroundNativeControls.originalTolerance b ((certificates i).κ : ℝ) (1/2))^[n]
            GroundOriginalSeed.initial) ∧
        NativeLegal GroundNativeControls.originalTolerance b ((certificates i).κ : ℝ) (1/2)
          ((nativeUpdate GroundNativeControls.originalTolerance b ((certificates i).κ : ℝ) (1/2))^[n]
            GroundOriginalSeed.initial) ∧
        complexNormSq ((nativeUpdate GroundNativeControls.originalTolerance b
          ((certificates i).κ : ℝ) (1/2))^[n] GroundOriginalSeed.initial) = 1 := by
  have hv : ContinuousAt (fun b : Field => (localPoint i b).1) (rounded_b i) :=
    (localPoint_smooth_at i).continuousAt.fst
  have hv0 : (localPoint i (rounded_b i)).1 = (roundedRoot i).1 := by rw [localPoint_center]
  have hvg : ∀ᶠ b in nhds (rounded_b i), normSq (localPoint i b).1 = 1 ∧
      groundMap b ((certificates i).κ : ℝ) (localPoint i b).1 = (localPoint i b).1 := by
    filter_upwards [localPoint_ground_eventually i] with b hb
    exact ⟨hb.2.2.1,hb.2.2.2.2⟩
  have hseed := GroundOriginalOffsetSeed.rounded_original_seed_return i
  obtain ⟨δ0,hδ0,hreturn⟩ := GroundNativeBackgroundSeedReturn.nearby_native_seed_branch_return
    (GroundOriginalOffsetStability.fullBasis i)
    (b₀ := rounded_b i) (u := (roundedRoot i).1)
    (κ := ((certificates i).κ : ℝ)) (m := 1/2) (τ := GroundNativeControls.originalTolerance)
    (z := GroundOriginalSeed.initial) (v := fun b => (localPoint i b).1)
    GroundNativeControls.originalTolerance_guard.1 GroundNativeControls.originalTolerance_guard.2
    (rounded_ground_return i).1 (rounded_root_spec i).2.2.2.1
    (rounded_coordinate_contraction i) hv hv0 hvg hseed.1
    (fun n => ⟨(hseed.2 n).1,(hseed.2 n).2.1⟩) GroundOriginalSeed.initial_unit
  obtain ⟨δ,hδ,hinside⟩ := nhds_basis_closedBall.mem_iff.mp
    ((localPoint_ground_eventually i).and (closedBall_mem_nhds (rounded_b i) hδ0))
  refine ⟨δ,hδ,fun b hb => ?_⟩
  obtain ⟨hground,hb0⟩ := hinside hb
  exact ⟨hground.1,hground.2.1,hground.2.2.1,hground.2.2.2.1,hground.2.2.2.2,
    (hreturn b hb0).1,(hreturn b hb0).2⟩
end
end SbtCosmo.Derivation.GroundOriginalOpenBackground
