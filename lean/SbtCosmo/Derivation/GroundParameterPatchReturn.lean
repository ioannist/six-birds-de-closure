import SbtCosmo.Derivation.GroundParameterPatch
import SbtCosmo.Derivation.GroundParameterSpectrum

/-! Return the constructed finite branch to the actual ground/energy selector,
certified sample roots, legal native complex fixed points, and distinct mode
contacts. The determinant signs and concrete tube inequalities remain explicit
quantitative obligations, without an assumed continuous fixed-point branch. -/
namespace SbtCosmo.Derivation.GroundParameterPatchReturn
noncomputable section
set_option maxHeartbeats 2000000
open Metric GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian
open GroundNativePhase GroundNativeDerivative GroundNativeIteration GroundNativeJacobian
open GroundParameterPatch GroundParameterSpectrum
open scoped ContDiff Topology

variable {b : Field} {ι : Type*}

theorem closedBall_containment {x y : Point} {r s : ℝ} (h : dist x y + r ≤ s) :
    closedBall x r ⊆ closedBall y s := by
  intro z hz
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle z x y
    _ ≤ r + dist x y := add_le_add (show dist z x ≤ r from hz) le_rfl
    _ ≤ s := by simpa only [add_comm] using h

theorem certified_sample_return (v : TubeCover b ι) (a : GroundParameterTube.TubeCertificate b)
    {i : ι} {k : ℝ} (hi : k ∈ (v.tube i).interval) (ha : k ∈ a.interval)
    (hbox : dist a.center (v.tube i).center + a.radius ≤ (v.tube i).radius) :
    a.root k = v.root k := by
  have hs := a.root_spec ha
  exact v.sample_root_return hi hs.2.1 (closedBall_containment hbox hs.1)

def field (v : TubeCover b ι) (k : ℝ) : Field := (v.root k).1

theorem field_smooth_on [Finite ι] (v : TubeCover b ι) :
    ContDiffOn ℝ ∞ (field v) v.domain := v.root_smooth_on.fst

theorem field_continuous_on [Finite ι] (v : TubeCover b ι) :
    ContinuousOn (field v) v.domain := (field_smooth_on v).continuousOn

theorem field_fixed (v : TubeCover b ι) {k : ℝ} (hk : k ∈ v.domain) :
    normSq ((field v k)) = 1 ∧ groundMap b k ((field v k)) = (field v k) :=
  ⟨(v.groundPair_return hk).1, (v.root_spec hk).2.2.2⟩

theorem native_fixed_legal (v : TubeCover b ι) {k τ m : ℝ}
    (hk : k ∈ v.domain) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    nativeUpdate τ b k m (realEmbed ((field v k))) = realEmbed ((field v k)) ∧
      ActivePhase τ b k (realEmbed ((field v k))) ∧
      NativeLegal τ b k m (realEmbed ((field v k))) := by
  obtain ⟨hu, hf⟩ := field_fixed v hk
  have hn := (nativeUpdate_near_fixed (m := m) hu hf hτ0 hτ1).self_of_nhds
  refine ⟨?_, hn.2⟩
  change nativeUpdate τ b k m (pack ((field v k), 0)) = pack ((field v k), 0)
  rw [← hn.1, fullMap_fixed hu hf]

/-- Actual tangent mode and derivative of the unchanged native update. -/
def ModeContact (b : Field) (u : Field) (τ k : ℝ) : Prop :=
  ∃ h : Field, h ≠ 0 ∧ dot u h = 0 ∧ normalizedJacobian b k (1/2) u h = -h ∧
    fullDerivative b k (1/2) u (h, 0) = -(h, 0) ∧
    HasFDerivAt (nativePairMap τ b k (1/2)) (fullDerivative b k (1/2) u) (u, 0)

theorem minus_one_contact [Finite ι] (v : TubeCover b ι) {a c τ : ℝ}
    (hac : a < c) (hcover : Set.Icc a c ⊆ v.domain) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hsign : crossingDet ((b, a), (field v a)) * crossingDet ((b, c), (field v c)) < 0) :
    ∃ k ∈ Set.Ioo a c, ModeContact b ((field v k)) τ k :=
  actual_minus_one_crossing hac ((field_continuous_on v).mono hcover)
    (fun _ hk => field_fixed v (hcover hk)) hτ0 hτ1 hsign

/-- Two sign reversals on the same constructed branch earn distinct contacts.
No first, unique, simple, or transverse contact assertion is made. -/
theorem two_distinct_contacts [Finite ι] (v : TubeCover b ι) {a d c τ : ℝ}
    (had : a < d) (hdc : d < c) (hcover : Set.Icc a c ⊆ v.domain)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hsign₁ : crossingDet ((b, a), (field v a)) * crossingDet ((b, d), (field v d)) < 0)
    (hsign₂ : crossingDet ((b, d), (field v d)) * crossingDet ((b, c), (field v c)) < 0) :
    ∃ k₁ ∈ Set.Ioo a d, ∃ k₂ ∈ Set.Ioo d c, k₁ < k₂ ∧
      ModeContact b ((field v k₁)) τ k₁ ∧ ModeContact b ((field v k₂)) τ k₂ := by
  have hleft : Set.Icc a d ⊆ v.domain := fun _ hk => hcover ⟨hk.1, hk.2.trans hdc.le⟩
  have hright : Set.Icc d c ⊆ v.domain := fun _ hk => hcover ⟨had.le.trans hk.1, hk.2⟩
  obtain ⟨k₁, hk₁, hm₁⟩ := minus_one_contact v had hleft hτ0 hτ1 hsign₁
  obtain ⟨k₂, hk₂, hm₂⟩ := minus_one_contact v hdc hright hτ0 hτ1 hsign₂
  exact ⟨k₁, hk₁, k₂, hk₂, hk₁.2.trans hk₂.1, hm₁, hm₂⟩

end
end SbtCosmo.Derivation.GroundParameterPatchReturn
