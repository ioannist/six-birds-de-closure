import SbtCosmo.Derivation.GroundOriginalContinuation
import SbtCosmo.Derivation.GroundSamples.Point000
import SbtCosmo.Derivation.GroundSamples.Point001
import SbtCosmo.Derivation.GroundSamples.Point002
import SbtCosmo.Derivation.GroundSamples.Point003
import SbtCosmo.Derivation.GroundSamples.Point004
import SbtCosmo.Derivation.GroundSamples.Point005
import SbtCosmo.Derivation.GroundSamples.Point006
import SbtCosmo.Derivation.GroundSamples.Point007
import SbtCosmo.Derivation.GroundSamples.Point008
import SbtCosmo.Derivation.GroundSamples.Point009
import SbtCosmo.Derivation.GroundSamples.Point010
import SbtCosmo.Derivation.GroundSamples.Point011
import SbtCosmo.Derivation.GroundSamples.Point012
import SbtCosmo.Derivation.GroundSamples.Point013

/-! Twelve original coupling sample boxes and two determinant-crossing probe
boxes, fully kernel instantiated and identified with the actual global branch.
This supplies thin-box membership for subsequent actual derivative enclosures. -/
namespace SbtCosmo.Derivation.GroundOriginalSamples
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open Metric GroundState GroundBorder GroundRootCertificate GroundKernelTube GroundKernelChain
open GroundParameterPatch GroundOriginalFirstTube

def points : Fin 14 → Data originalBackground := ![
  GroundSamples.Point000.datum,
  GroundSamples.Point001.datum,
  GroundSamples.Point002.datum,
  GroundSamples.Point003.datum,
  GroundSamples.Point004.datum,
  GroundSamples.Point005.datum,
  GroundSamples.Point006.datum,
  GroundSamples.Point007.datum,
  GroundSamples.Point008.datum,
  GroundSamples.Point009.datum,
  GroundSamples.Point010.datum,
  GroundSamples.Point011.datum,
  GroundSamples.Point012.datum,
  GroundSamples.Point013.datum]

def couplings : Fin 14 → ℚ := ![0, (3602879701896397/36028797018963968), (5404319552844595/18014398509481984), (1/2), 1, 2, 3, 5, 10, 15, 20, 30, (79/5), (159/10)]

def owners : Fin 14 → Fin 286 := ![0, 0, 2, 4, 8, 17, 25, 42, 85, 127, 159, 285, 133, 133]

theorem point_bounds : ∀ i : Fin 14,
    (points i).a = couplings i ∧ (points i).c = couplings i := by
  decide +kernel

theorem owner_bounds : ∀ i : Fin 14,
    (GroundOriginalContinuation.pieces (owners i)).a ≤ couplings i ∧
      couplings i ≤ (GroundOriginalContinuation.pieces (owners i)).c := by
  decide +kernel

theorem containment : ∀ i : Fin 14, ∀ j : Fin 9,
    |(points i).z j - (GroundOriginalContinuation.pieces (owners i)).z j| + (points i).r ≤
      (GroundOriginalContinuation.pieces (owners i)).r := by
  decide +kernel

theorem sample_interval (i : Fin 14) : (couplings i : ℝ) ∈ (points i).toTube.interval := by
  change (couplings i : ℝ) ∈ Set.Icc ((points i).a : ℝ) ((points i).c : ℝ)
  rw [(point_bounds i).1, (point_bounds i).2]
  exact ⟨le_rfl, le_rfl⟩

theorem owner_interval (i : Fin 14) :
    (couplings i : ℝ) ∈ (GroundOriginalContinuation.cover.tube (owners i)).interval := by
  change (couplings i : ℝ) ∈ Set.Icc
    ((GroundOriginalContinuation.pieces (owners i)).a : ℝ)
    ((GroundOriginalContinuation.pieces (owners i)).c : ℝ)
  constructor
  · exact_mod_cast (owner_bounds i).1
  · exact_mod_cast (owner_bounds i).2

theorem coupling_range (i : Fin 14) : (couplings i : ℝ) ∈ Set.Icc (0 : ℝ) 30 := by
  rw [← GroundOriginalContinuation.domain_eq]
  exact GroundOriginalContinuation.cover.mem_domain.mpr ⟨owners i, owner_interval i⟩

theorem root_eq_branch (i : Fin 14) :
    (points i).toTube.root (couplings i) = GroundOriginalContinuation.branch (couplings i) := by
  have hs := (points i).toTube.root_spec (sample_interval i)
  exact GroundOriginalContinuation.cover.sample_root_return (owner_interval i) hs.2.1
    ((points i).ball_subset (GroundOriginalContinuation.pieces (owners i)) (containment i) hs.1)

theorem branch_in_sample_ball (i : Fin 14) :
    GroundOriginalContinuation.branch (couplings i) ∈
      closedBall (center (points i).z) ((points i).r : ℝ) := by
  rw [← root_eq_branch i]
  exact ((points i).toTube.root_spec (sample_interval i)).1

theorem sample_ground_return (i : Fin 14) :
    residual (background originalBackground) (couplings i)
      (GroundOriginalContinuation.branch (couplings i)) = 0 ∧
      (∀ j, 0 < (GroundOriginalContinuation.branch (couplings i)).1 j) ∧
      normSq (GroundOriginalContinuation.branch (couplings i)).1 = 1 ∧
      groundPair (sourcePotential (background originalBackground) (couplings i)
        (GroundOriginalContinuation.branch (couplings i)).1) = GroundOriginalContinuation.branch (couplings i) ∧
      GroundSourceJacobian.groundMap (background originalBackground) (couplings i)
        (GroundOriginalContinuation.branch (couplings i)).1 = (GroundOriginalContinuation.branch (couplings i)).1 :=
  GroundOriginalContinuation.whole_ground (couplings i) (coupling_range i)

end
end SbtCosmo.Derivation.GroundOriginalSamples
