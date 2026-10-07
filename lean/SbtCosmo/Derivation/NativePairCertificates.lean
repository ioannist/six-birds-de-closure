import SbtCosmo.Derivation.NativePairedTransport
namespace NativePairCertificates
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox Metric StateBoxComposition NativeTransportPowers
open scoped BigOperators

structure Pair (β : Fin 8 → Interval) (κ τ : ℚ) (T : State ≃L[ℝ] State) where
  first : Data β κ τ T
  second : Data β κ τ T
  seam : first.nextCenter = second.center
  intermediate_radius : first.next_radius ≤ second.radius
  firstCache : MatrixBox
  secondCache : MatrixBox
  productCache : MatrixBox
  first_included : Included first.jet.derivativeBox firstCache
  second_included : Included second.jet.derivativeBox secondCache
  product_included : Included (compose secondCache firstCache) productCache
  rate : ℚ
  rate_nonneg : 0 ≤ rate
  rowsR : ∀ i : Fin 8, (∑ j : Fin 8, (((productCache (j.castAdd 8)).R i).bound+
    ((productCache (Fin.natAdd 8 j)).R i).bound)) ≤ rate
  rowsI : ∀ i : Fin 8, (∑ j : Fin 8, (((productCache (j.castAdd 8)).I i).bound+
    ((productCache (Fin.natAdd 8 j)).I i).bound)) ≤ rate
  defect : ℚ
  defect_budget : second.jet.rate*first.defect+second.defect ≤ defect
  small_defect : first.defect ≤ second.radius
  next_radius : ℚ
  transport_budget : rate*first.radius+defect ≤ next_radius

namespace Pair
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State}
def nnrate (p : Pair β κ τ T) : NNReal := ⟨(p.rate : ℝ),by exact_mod_cast p.rate_nonneg⟩

theorem lipschitz (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) :
    LipschitzOnWith p.nnrate ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2])
      (closedBall p.first.center (p.first.radius : ℝ)) :=
  pair_lipschitz p.first p.second hb p.seam p.intermediate_radius p.rate_nonneg
    p.first_included p.second_included p.product_included p.rowsR p.rowsI

theorem center_defect (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) :
    dist (((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) p.first.center)
      p.second.nextCenter ≤ (p.defect : ℝ) :=
  pair_center_defect p.first p.second hb p.seam p.small_defect p.defect_budget

theorem advance (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall p.first.center (p.first.radius : ℝ)) :
    ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) x ∈
      closedBall p.second.nextCenter (p.next_radius : ℝ) := by
  apply pair_advance p.first p.second hb p.seam p.small_defect p.defect_budget (p.lipschitz hb) ?_ hx
  change (p.rate : ℝ)*(p.first.radius : ℝ)+(p.defect : ℝ) ≤ (p.next_radius : ℝ)
  exact_mod_cast p.transport_budget

/-- Disjoint actual physical-coordinate boxes exclude a fixed point of the
one-step source update throughout the first ball. -/
theorem separated (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {i : Fin 8}
    (hsep : (p.second.jet.input.R i).hi < (p.first.jet.input.R i).lo)
    {x : State} (hx : x ∈ closedBall p.first.center (p.first.radius : ℝ)) :
    Data.f (T := T) (κ := κ) (τ := τ) b x ≠ x := by
  intro he
  have h₀ := (p.first.input_on_ball hx i).1
  have h₁ := (p.second.input_on_ball (next_on_ball p.first p.second hb p.seam p.intermediate_radius hx) i).1
  rw [he] at h₁
  have hs : ((p.second.jet.input.R i).hi : ℝ) < ((p.first.jet.input.R i).lo : ℝ) := by exact_mod_cast hsep
  linarith [h₀.1,h₁.2]
end Pair

structure Finite (β : Fin 8 → Interval) (κ τ : ℚ) (T : State ≃L[ℝ] State) (N : ℕ) where
  centers : Fin (N+1) → State
  radii : Fin (N+1) → ℚ
  radius_nonneg : ∀ j, 0 ≤ radii j
  pairs : Fin N → Pair β κ τ T
  source_center : ∀ j, (pairs j).first.center = centers j.castSucc
  source_radius : ∀ j, radii j.castSucc ≤ (pairs j).first.radius
  target_center : ∀ j, (pairs j).second.nextCenter = centers j.succ
  transport_budget : ∀ j, (pairs j).rate*radii j.castSucc+(pairs j).defect ≤ radii j.succ

namespace Finite
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State} {N : ℕ}
theorem enclosed (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {initial : State}
    (hi : initial ∈ closedBall (c.centers 0) (c.radii 0 : ℝ)) (j : Fin (N+1)) :
    ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j.val]) initial ∈
      closedBall (c.centers j) (c.radii j : ℝ) := by
  have h := GroundFiniteNativeTransport.enclosed
    ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) c.centers (fun j => (c.radii j : ℝ))
    (fun j => (c.pairs j).nnrate) (fun j => ((c.pairs j).defect : ℝ))
    (fun j => by change (0 : ℝ) ≤ (c.radii j : ℝ); exact_mod_cast c.radius_nonneg j)
    (fun j => by
      rw [← c.source_center j]
      exact ((c.pairs j).lipschitz hb).mono (closedBall_subset_closedBall (Rat.cast_le.mpr (c.source_radius j))))
    (fun j => by simpa only [c.source_center j,c.target_center j] using (c.pairs j).center_defect hb)
    (fun j => ?_) hi j
  · simpa only [← Function.iterate_mul] using h
  · change ((c.pairs j).rate : ℝ)*(c.radii j.castSucc : ℝ)+((c.pairs j).defect : ℝ) ≤ (c.radii j.succ : ℝ)
    exact_mod_cast c.transport_budget j

theorem guards_even_odd (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {initial : State}
    (hi : initial ∈ closedBall (c.centers 0) (c.radii 0 : ℝ)) (j : Fin N) :
    (ActivePhase (τ : ℝ) b (κ : ℝ) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j.val] initial))) ∧
      NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j.val] initial)))) ∧
    (ActivePhase (τ : ℝ) b (κ : ℝ) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j.val+1] initial))) ∧
      NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j.val+1] initial)))) := by
  have hx : (Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j.val] initial ∈
      closedBall (c.pairs j).first.center ((c.pairs j).first.radius : ℝ) := by
    rw [c.source_center j]
    exact closedBall_subset_closedBall (Rat.cast_le.mpr (c.source_radius j)) (c.enclosed hb hi j.castSucc)
  refine ⟨(c.pairs j).first.native_guards hb hx,?_⟩
  rw [Function.iterate_succ_apply']
  exact (c.pairs j).second.native_guards hb
    (next_on_ball (c.pairs j).first (c.pairs j).second hb (c.pairs j).seam (c.pairs j).intermediate_radius hx)
end Finite
end
end NativePairCertificates
