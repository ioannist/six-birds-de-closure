import SbtCosmo.Derivation.NativeFinitePairJets
import SbtCosmo.Derivation.NativePairOrbit
namespace NativeFinitePairOrbit
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox Metric NativeTransportPowers NativePairCertificates NativeFinitePairJets
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State} {N : ℕ}

theorem guards (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (hN : 0 < N)
    (hm : Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*N])
      (closedBall (c.centers 0) (c.radii 0 : ℝ)) (closedBall (c.centers 0) (c.radii 0 : ℝ)))
    {y : State} (hy : y ∈ closedBall (c.centers 0) (c.radii 0 : ℝ)) (n : ℕ) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[n] y))) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[n] y))) := by
  have hp : 0 < 2*N := by omega
  have hblock : (Data.f (T := T) (κ := κ) (τ := τ) b)^[2*N*(n/(2*N))] y ∈
      closedBall (c.centers 0) (c.radii 0 : ℝ) := by
    simpa only [← Function.iterate_mul] using hm.iterate (n/(2*N)) hy
  let j : Fin (2*N) := ⟨n%(2*N),Nat.mod_lt _ hp⟩
  have hg := (steps c j).native_guards hb (orbit_enclosed c hb hblock j)
  have hn : j.val+2*N*(n/(2*N)) = n := by dsimp [j];exact Nat.mod_add_div n (2*N)
  simpa only [← Function.iterate_add_apply,hn] using hg

theorem source_guards (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (hN : 0 < N)
    (hm : Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*N])
      (closedBall (c.centers 0) (c.radii 0 : ℝ)) (closedBall (c.centers 0) (c.radii 0 : ℝ)))
    {z : ComplexField} (hz : T.symm (unpack z) ∈ closedBall (c.centers 0) (c.radii 0 : ℝ)) (n : ℕ) :
    ActivePhase (τ : ℝ) b (κ : ℝ) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) := by
  simpa only [NativePairOrbit.source_iterate] using guards c hb hN hm hz n

theorem source_unit (c : Finite β κ τ T N) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) (hN : 0 < N)
    (hm : Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2*N])
      (closedBall (c.centers 0) (c.radii 0 : ℝ)) (closedBall (c.centers 0) (c.radii 0 : ℝ)))
    {z : ComplexField} (hz : T.symm (unpack z) ∈ closedBall (c.centers 0) (c.radii 0 : ℝ))
    (hu : complexNormSq z = 1) (n : ℕ) :
    complexNormSq ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) = 1 := by
  cases n with
  | zero => exact hu
  | succ n =>
    rw [Function.iterate_succ_apply']
    have ht : 0 ≤ τ := (c.pairs ⟨0,hN⟩).first.pointStep.proof.threshold_nonneg
    exact GroundNativeEscape.nativeUpdate_unit (by exact_mod_cast ht) (source_guards c hb hN hm hz n).2
end
end NativeFinitePairOrbit
