import SbtCosmo.Derivation.GroundCertifiedNativeTransport
import SbtCosmo.Derivation.GroundOriginalOffsetBasins

/-! Whole-hull original-seed returns from populated finite transport and earned
entry. Finite certificates and actual root distance remain visible here. -/
namespace SbtCosmo.Derivation.GroundOffsetTransportReturn
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval
open GroundNativeTransportGeometry GroundCertifiedNativeEntry Metric Filter
open scoped Topology

def β (i : Fin 18) : Fin 8 → Interval := (GroundOriginalOffsets.certificates i).B
def κ (i : Fin 18) : ℚ := (GroundOriginalOffsets.certificates i).κ
def Prefix (i : Fin 18) (N : ℕ) := GroundCertifiedNativeTransport.Certificate (β i) (κ i)
  GroundNativePrefixInitial.τ (GroundOriginalOffsetBasins.T i) N
def f (i : Fin 18) (b : Field) := nativeUpdate GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2)
def orbit (i : Fin 18) (b : Field) (n : ℕ) := (f i b)^[n] GroundOriginalSeed.initial

theorem prefix_guards (i : Fin 18) {N : ℕ} (c : Prefix i N) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) (j : Fin N) :
    ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) (orbit i b j.val) ∧
    NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) (orbit i b j.val) := by
  simpa only [GroundCertifiedNativeTransport.Certificate.orbit,GroundCertifiedNativeTransport.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,f,orbit] using c.guards hb j

theorem center_distance (i : Fin 18) {N : ℕ} (c : Prefix i N) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) {γ : ℚ} (hγ : 0 ≤ γ)
    (hrows : ∀ j : Fin 8,
      (((GroundOriginalOffsetBasins.data i).c.coordinateBox (differenceBox
        (around (c.u (Fin.last N)) (c.v (Fin.last N)) 0 0)
        (negativeTargetBox (GroundOriginalOffsets.certificates i).z (GroundOriginalOffsets.certificates i).r))).R j).bound ≤ γ ∧
      (((GroundOriginalOffsetBasins.data i).c.coordinateBox (differenceBox
        (around (c.u (Fin.last N)) (c.v (Fin.last N)) 0 0)
        (negativeTargetBox (GroundOriginalOffsets.certificates i).z (GroundOriginalOffsets.certificates i).r))).I j).bound ≤ γ) :
    dist (c.center (Fin.last N))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤ (γ : ℝ) := by
  have hc := point_enclosed (c.u (Fin.last N)) (c.v (Fin.last N))
    (by norm_num : (0 : ℚ) ≤ 0) (by norm_num : (0 : ℚ) ≤ 0)
  have ht := negativeTargetBox_sound (GroundOriginalOffsetBasins.root_field_box i hb)
  exact coordinate_distance (GroundOriginalOffsetBasins.data i).c hγ hc ht hrows

theorem endpoint_distance (i : Fin 18) {N : ℕ} (c : Prefix i N) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j)) {γ : ℚ}
    (hcenter : dist (c.center (Fin.last N))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤ (γ : ℝ)) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤
      (c.radius (Fin.last N) : ℝ)+(γ : ℝ) := by
  have hx := c.enclosed hb (Fin.last N)
  simp only [GroundCertifiedNativeTransport.Certificate.orbit,GroundCertifiedNativeTransport.Certificate.f,
    GroundNativePrefixInitial.tolerance_return,Fin.val_last] at hx
  exact GroundFiniteNativeTransport.endpoint_distance hx hcenter

theorem whole_seed_return (i : Fin 18) {N : ℕ} (c : Prefix i N) {b : Field}
    (hb : ∀ j, (β i j).Contains (b j))
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)) :
    Tendsto (orbit i b) atTop (nhds (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hb).1))) ∧
    ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) (orbit i b n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) (orbit i b n) ∧
      complexNormSq (orbit i b n) = 1 := by
  have hs := GroundOriginalOffsetBasins.whole_background_box_explicit_negative_native_basin i hb hentry
  have ht : Tendsto (fun n : ℕ => (f i b)^[n] (orbit i b N)) atTop
      (nhds (realEmbed (-(GroundOriginalOffsetStability.wholeRoot i hb).1))) := hs.1
  have hg : ∀ n : ℕ, ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) (orbit i b n) ∧
      NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) (orbit i b n) :=
    iterate_property_of_tail (f i b) GroundOriginalSeed.initial
      (fun z => ActivePhase GroundNativeControls.originalTolerance b (κ i : ℝ) z ∧
        NativeLegal GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2) z)
      N (prefix_guards i c hb) (fun n => ⟨(hs.2 n).1,(hs.2 n).2.1⟩)
  have hu (n : ℕ) : complexNormSq (orbit i b n) = 1 := by
    induction n with
    | zero => exact GroundOriginalSeed.initial_unit
    | succ n _ =>
      rw [orbit,Function.iterate_succ_apply']
      exact GroundNativeEscape.nativeUpdate_unit GroundNativeControls.originalTolerance_guard.1 (hg n).2
  exact ⟨iterate_tendsto_of_tail (f i b) GroundOriginalSeed.initial _ N ht,fun n => ⟨(hg n).1,(hg n).2,hu n⟩⟩

theorem whole_seed_geometric_tail (i : Fin 18) {N : ℕ} {b : Field}
    (hb : ∀ j, (β i j).Contains (b j))
    (hentry : (GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)) ∈ closedBall
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0))
      ((GroundOriginalOffsetBasins.data i).ρ : ℝ)) (n : ℕ) :
    dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b (n+N))))
      ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) ≤
      (GroundOriginalOffsetBasins.rate i : ℝ)^n *
        dist ((GroundOriginalOffsetBasins.T i).symm (unpack (orbit i b N)))
          ((GroundOriginalOffsetBasins.T i).symm (-(GroundOriginalOffsetStability.wholeRoot i hb).1,0)) := by
  have hs := GroundOriginalOffsetBasins.whole_background_box_explicit_negative_native_basin i hb hentry
  simpa only [orbit,f,κ,Function.iterate_add_apply] using (hs.2 n).2.2
end
end SbtCosmo.Derivation.GroundOffsetTransportReturn
