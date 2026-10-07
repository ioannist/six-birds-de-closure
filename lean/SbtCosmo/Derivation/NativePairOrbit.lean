import SbtCosmo.Derivation.NativePairCertificates
namespace NativePairOrbit
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open GroundCertifiedNativeTransportStep GroundCertifiedNativeTransportStep.Data
open GroundRationalInterval GroundNativeBox Metric NativePairCertificates
open GroundNativeLocal GroundNativeJacobian NativeTransportPowers
open scoped Topology
variable {β : Fin 8 → Interval} {κ τ : ℚ} {T : State ≃L[ℝ] State}

theorem invariant (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i)) {d : ℝ}
    (hd : dist (((Data.f (T := T) (κ := κ) (τ := τ) b)^[2]) p.first.center) p.first.center ≤ d)
    (hbudget : (p.rate : ℝ)*(p.first.radius : ℝ)+d ≤ (p.first.radius : ℝ)) :
    Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2])
      (closedBall p.first.center (p.first.radius : ℝ)) (closedBall p.first.center (p.first.radius : ℝ)) := by
  intro x hx
  exact GroundFiniteNativeTransport.step _ (by exact_mod_cast p.first.radius_nonneg) (p.lipschitz hb) hd hbudget hx

theorem guards (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i))
    (hm : Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2])
      (closedBall p.first.center (p.first.radius : ℝ)) (closedBall p.first.center (p.first.radius : ℝ)))
    {y : State} (hy : y ∈ closedBall p.first.center (p.first.radius : ℝ)) (n : ℕ) :
    ActivePhase (τ : ℝ) b (κ : ℝ) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[n] y))) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) (pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[n] y))) := by
  have he (j : ℕ) : (Data.f (T := T) (κ := κ) (τ := τ) b)^[2*j] y ∈
      closedBall p.first.center (p.first.radius : ℝ) := by
    simpa only [← Function.iterate_mul] using hm.iterate j hy
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hi : n = 2*(n/2) := by omega
    rw [hi]
    exact p.first.native_guards hb (he (n/2))
  · have hi : n = 2*(n/2)+1 := by omega
    rw [hi,Function.iterate_succ_apply']
    exact p.second.native_guards hb
      (next_on_ball p.first p.second hb p.seam p.intermediate_radius (he (n/2)))

/-- Exact conjugacy to the unchanged source update, including totalized guard
branches. Legal-region proofs are separately supplied by `guards`. -/
theorem source_iterate (b : Field) (z : ComplexField) (n : ℕ) :
    pack (T ((Data.f (T := T) (κ := κ) (τ := τ) b)^[n] (T.symm (unpack z)))) =
      (nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z := by
  rw [Data.f,coordinate_iterate_return]
  simpa only [T.apply_symm_apply,packCLE_apply,packCLE_symm_apply,packCLE.apply_symm_apply] using
    nativePairMap_iterate_return (τ : ℝ) b (κ : ℝ) (1/2) (unpack z) n

theorem source_guards (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i))
    (hm : Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2])
      (closedBall p.first.center (p.first.radius : ℝ)) (closedBall p.first.center (p.first.radius : ℝ)))
    {z : ComplexField} (hz : T.symm (unpack z) ∈ closedBall p.first.center (p.first.radius : ℝ)) (n : ℕ) :
    ActivePhase (τ : ℝ) b (κ : ℝ) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) ∧
    NativeLegal (τ : ℝ) b (κ : ℝ) (1/2) ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) := by
  simpa only [source_iterate] using guards p hb hm hz n

theorem source_unit (p : Pair β κ τ T) {b : Field}
    (hb : ∀ i, (β i).Contains (b i))
    (hm : Set.MapsTo ((Data.f (T := T) (κ := κ) (τ := τ) b)^[2])
      (closedBall p.first.center (p.first.radius : ℝ)) (closedBall p.first.center (p.first.radius : ℝ)))
    {z : ComplexField} (hz : T.symm (unpack z) ∈ closedBall p.first.center (p.first.radius : ℝ))
    (hu : complexNormSq z = 1) (n : ℕ) :
    complexNormSq ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z) = 1 := by
  cases n with
  | zero => exact hu
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact GroundNativeEscape.nativeUpdate_unit
      (by exact_mod_cast p.first.pointStep.proof.threshold_nonneg) (source_guards p hb hm hz n).2

theorem coordinate_from_source (b : Field) (z : ComplexField) (n : ℕ) :
    T.symm (unpack ((nativeUpdate (τ : ℝ) b (κ : ℝ) (1/2))^[n] z)) =
      (Data.f (T := T) (κ := κ) (τ := τ) b)^[n] (T.symm (unpack z)) := by
  rw [← source_iterate (T := T) b z n]
  change T.symm (packCLE.symm (packCLE (T _))) = _
  rw [packCLE.symm_apply_apply,T.symm_apply_apply]
end
end NativePairOrbit
