import SbtCosmo.Derivation.GroundCertifiedNativeEntry
import SbtCosmo.Derivation.GroundCertifiedNativePrefix
import SbtCosmo.Derivation.GroundOriginalOffsetBasins
import SbtCosmo.Derivation.GroundOffsetPrefixInitial

/-! Guarded actual rounded-offset seed returns from a populated prefix and
explicit basin entry. The entry and prefix remain visible obligations. -/
namespace SbtCosmo.Derivation.GroundOffsetSeedReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundRationalInterval
open GroundCertifiedNativeEntry Filter Metric
open scoped Topology

def β (i : Fin 18) : Fin 8 → Interval := fun j => Interval.point ((GroundOriginalOffsets.certificates i).roundedBackground j)
def κ (i : Fin 18) : ℚ := (GroundOriginalOffsets.certificates i).κ
def Prefix (i : Fin 18) (N : ℕ) := GroundCertifiedNativePrefix.Certificate (β i) (κ i) GroundNativePrefixInitial.τ N
def f (i : Fin 18) := nativeUpdate GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2)
def orbit (i : Fin 18) (n : ℕ) := (f i)^[n] GroundOriginalSeed.initial

theorem background_sound (i : Fin 18) : ∀ j, (β i j).Contains (GroundOriginalOffsets.rounded_b i j) :=
  fun j => Interval.point_sound ((GroundOriginalOffsets.certificates i).roundedBackground j)

theorem prefix_guards (i : Fin 18) {N : ℕ} (c : Prefix i N) (j : Fin N) :
    ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (orbit i j.val) ∧
    NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2) (orbit i j.val) := by
  simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using c.guards (background_sound i) j

theorem distance_from_boxes (i : Fin 18) {N : ℕ} (c : Prefix i N) {δ : ℚ}
    (hδ : 0 ≤ δ)
    (hrows : ∀ j : Fin 8,
      ((((GroundOriginalOffsetBasins.data i).c).coordinateBox
        (differenceBox (c.boxes (Fin.last N))
          (negativeTargetBox (GroundOriginalOffsets.certificates i).z (GroundOriginalOffsets.certificates i).r))).R j).bound ≤ δ ∧
      ((((GroundOriginalOffsetBasins.data i).c).coordinateBox
        (differenceBox (c.boxes (Fin.last N))
          (negativeTargetBox (GroundOriginalOffsets.certificates i).z (GroundOriginalOffsets.certificates i).r))).I j).bound ≤ δ) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤ (δ : ℝ) := by
  have hx : (c.boxes (Fin.last N)).Contains (unpack (orbit i N)) := by
    simpa only [GroundCertifiedNativePrefix.Certificate.orbit,GroundCertifiedNativePrefix.Certificate.f,
      GroundNativePrefixInitial.tolerance_return,f,orbit] using c.enclosed (background_sound i) (Fin.last N)
  have ht := negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box i
    (GroundOriginalOffsets.rounded_inputs_sound i))
  exact coordinate_distance (GroundOriginalOffsetBasins.data i).c hδ hx ht hrows

theorem rounded_seed_return (i : Fin 18) {N : ℕ} (c : Prefix i N)
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)) :
    Tendsto (orbit i) atTop (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (orbit i n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2) (orbit i n) ∧
      complexNormSq (orbit i n) = 1 := by
  have hs := GroundOriginalOffsetBasins.whole_background_box_explicit_negative_native_basin i
    (GroundOriginalOffsets.rounded_inputs_sound i) hentry
  have ht : Tendsto (fun n : ℕ => (f i)^[n] (orbit i N)) atTop
      (nhds (realEmbed (-(GroundOriginalOffsets.roundedRoot i).1))) := hs.1
  have hg : ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (orbit i n) ∧
      NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2) (orbit i n) :=
    iterate_property_of_tail (f i) GroundOriginalSeed.initial
      (fun z => ActivePhase GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) z ∧
        NativeLegal GroundNativeControls.originalTolerance (GroundOriginalOffsets.rounded_b i) (κ i : ℝ) (1/2) z)
      N (prefix_guards i c) (fun n => ⟨(hs.2 n).1,(hs.2 n).2.1⟩)
  have hu (n : ℕ) : complexNormSq (orbit i n) = 1 := by
    induction n with
    | zero => exact GroundOriginalSeed.initial_unit
    | succ n _ =>
      rw [orbit,Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 (hg n).2
  exact ⟨iterate_tendsto_of_tail (f i) GroundOriginalSeed.initial _ N ht,fun n => ⟨(hg n).1,(hg n).2,hu n⟩⟩

theorem rounded_seed_geometric_tail (i : Fin 18) {N : ℕ}
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)) (n : ℕ) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i (n+N))))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) ≤
      (GroundOriginalOffsetBasins.rate i : ℝ)^n *
        dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i N)))
          ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsets.roundedRoot i).1,0)) := by
  have hs := GroundOriginalOffsetBasins.whole_background_box_explicit_negative_native_basin i
    (GroundOriginalOffsets.rounded_inputs_sound i) hentry
  simpa only [orbit,f,κ,Function.iterate_add_apply] using (hs.2 n).2.2

end
end SbtCosmo.Derivation.GroundOffsetSeedReturn
