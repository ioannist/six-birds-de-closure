import SbtCosmo.Derivation.NativePairCertificates
namespace NativeFinitePairJets
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox Metric StateBoxComposition NativeTransportPowers NativePairCertificates
open GroundNativeQuantitativeBall
open scoped BigOperators
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State} {N : ℕ}

def steps (c : Finite β κ τ T N) (j : Fin (2*N)) : Data β κ τ T :=
  let k : Fin N := ⟨j.val/2,by omega⟩
  if j.val%2=0 then (c.pairs k).first else (c.pairs k).second

theorem orbit_enclosed (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall (c.centers 0) (c.radii 0 : ℝ)) (j : Fin (2*N)) :
    (Data.f (T := T) (κ := κ) (τ := τ) b)^[j.val] x ∈
      closedBall (steps c j).center ((steps c j).radius : ℝ) := by
  let k : Fin N := ⟨j.val/2,by omega⟩
  have he : (Data.f (T := T) (κ := κ) (τ := τ) b)^[2*k.val] x ∈
      closedBall (c.pairs k).first.center ((c.pairs k).first.radius : ℝ) := by
    rw [c.source_center k]
    exact closedBall_subset_closedBall (Rat.cast_le.mpr (c.source_radius k)) (c.enclosed hb hx k.castSucc)
  by_cases hj : j.val%2=0
  · have hn : j.val = 2*k.val := by dsimp [k];omega
    have hs : steps c j = (c.pairs k).first := by simp only [steps,hj,if_pos]; rfl
    rw [hs,hn]
    exact he
  · have hn : j.val = 2*k.val+1 := by dsimp [k];omega
    have ho := next_on_ball (c.pairs k).first (c.pairs k).second hb
      (c.pairs k).seam (c.pairs k).intermediate_radius he
    have hs : steps c j = (c.pairs k).second := by simp only [steps,hj]; rfl
    rw [hs,hn,Function.iterate_succ_apply']
    exact ho

theorem derivative_power (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {x : State}
    (hx : x ∈ closedBall (c.centers 0) (c.radii 0 : ℝ)) (m : ℕ) (hm : m ≤ 2*N) :
    HasFDerivAt ((Data.f (T := T) (κ := κ) (τ := τ) b)^[m])
      (derivativePower (Data.f (T := T) (κ := κ) (τ := τ) b)
        (derivative T b (κ : ℝ) (1/2)) m x) x := by
  apply derivativePower_return
  intro j
  exact native_derivative (steps c ⟨j.val,by omega⟩) hb
    (orbit_enclosed c hb hx ⟨j.val,by omega⟩)

theorem power_lipschitz (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i))
    (cache : Fin (2*N) → MatrixBox) (products : Fin (2*N+1) → MatrixBox)
    (hcache : ∀ j, Included (steps c j).jet.derivativeBox (cache j))
    (hzero : Included identityBox (products 0))
    (hproducts : ∀ j : Fin (2*N), Included (compose (cache j) (products j.castSucc)) (products j.succ))
    {q : ℚ} (hq : 0 ≤ q)
    (hR : ∀ i : Fin 8, (∑ j : Fin 8, ((((products (Fin.last (2*N))) (j.castAdd 8)).R i).bound+
      (((products (Fin.last (2*N))) (Fin.natAdd 8 j)).R i).bound)) ≤ q)
    (hI : ∀ i : Fin 8, (∑ j : Fin 8, ((((products (Fin.last (2*N))) (j.castAdd 8)).I i).bound+
      (((products (Fin.last (2*N))) (Fin.natAdd 8 j)).I i).bound)) ≤ q) :
    LipschitzOnWith (⟨(q : ℝ),by exact_mod_cast hq⟩ : NNReal)
      ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*N])
      (closedBall (c.centers 0) (c.radii 0 : ℝ)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (derivative_power c hb hx (2*N) le_rfl).hasFDerivWithinAt)
    (fun x hx => ?_) (convex_closedBall (c.centers 0) (c.radii 0 : ℝ))
  have he := derivativePower_enclosed (Data.f (T := T) (κ := κ) (τ := τ) b)
    (derivative T b (κ : ℝ) (1/2)) (2*N) x cache products hzero
    (fun j => included_sound (hcache j) (native_matrix (steps c j) hb (orbit_enclosed c hb hx j))) hproducts
  exact_mod_cast norm_le_rows he hq hR hI
end
end NativeFinitePairJets
