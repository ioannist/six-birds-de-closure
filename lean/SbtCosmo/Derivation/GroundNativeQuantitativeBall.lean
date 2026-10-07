import SbtCosmo.Derivation.GroundNativeGeneralDerivative
import SbtCosmo.Derivation.GroundNativeLocal

/-! Explicit-radius native attraction from a uniform whole-ball derivative bound.
All guards and bounds are visible hypotheses here; concrete original instances
must establish them, rather than compare a finite endpoint to an unknown radius. -/
namespace SbtCosmo.Derivation.GroundNativeQuantitativeBall
noncomputable section
set_option maxHeartbeats 3000000
open Filter NNReal Metric GroundState GroundBorder GroundSourceJacobian GroundNativePhase
open GroundNativeIteration GroundNativeLocal
open scoped Topology

def derivative (T : State ≃L[ℝ] State) (b : Field) (κ m : ℝ) (x : State) : State →L[ℝ] State :=
  T.symm.toContinuousLinearMap.comp
    ((GroundNativeGeneralDerivative.fullDerivative b κ m (T x)).comp T.toContinuousLinearMap)

theorem coordinate_hasFDerivAt (T : State ≃L[ℝ] State) (b : Field) (κ m τ : ℝ) (x : State)
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ (T x))
    (hn : τ < Real.sqrt (stateNormSq (mixed b κ m (T x)))) :
    HasFDerivAt (coordinateMap T τ b κ m) (derivative T b κ m x) x := by
  have hpos : 0 < stateNormSq (mixed b κ m (T x)) := Real.sqrt_pos.mp (hτ.trans_lt hn)
  have hd := GroundNativeGeneralDerivative.nativePairMap_hasFDerivAt b κ m τ (T x) hτ ho hpos
  exact T.symm.toContinuousLinearMap.hasFDerivAt.comp x
    (hd.comp x T.toContinuousLinearMap.hasFDerivAt)

theorem native_guards (b : Field) (κ m τ : ℝ) (x : State) (hτ : 0 ≤ τ)
    (ho : τ < overlapNorm b κ x) (hn : τ < Real.sqrt (stateNormSq (mixed b κ m x))) :
    ActivePhase τ b κ (pack x) ∧ NativeLegal τ b κ m (pack x) := by
  constructor
  · simpa only [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using ho
  · rw [NativeLegal, ← pack_mixed_native hτ b κ m x ho, norm_pack]
    exact hn

theorem coordinate_lipschitz (T : State ≃L[ℝ] State) (b : Field) (κ m τ r : ℝ)
    (c : State) (q : ℝ≥0) (hτ : 0 ≤ τ)
    (hguards : ∀ x ∈ closedBall c r, τ < overlapNorm b κ (T x) ∧
      τ < Real.sqrt (stateNormSq (mixed b κ m (T x))))
    (hbound : ∀ x ∈ closedBall c r, ‖derivative T b κ m x‖ ≤ (q : ℝ)) :
    LipschitzOnWith q (coordinateMap T τ b κ m) (closedBall c r) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (coordinate_hasFDerivAt T b κ m τ x hτ (hguards x hx).1 (hguards x hx).2).hasFDerivWithinAt)
    (fun x hx => by exact_mod_cast hbound x hx) (convex_closedBall c r)

theorem explicit_native_ball_convergence (T : State ≃L[ℝ] State) {b u : Field} {κ m τ r : ℝ}
    (q : ℝ≥0) (hu : normSq u = 1) (hf : groundMap b κ u = u)
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) (hr : 0 ≤ r) (hq : q < 1)
    (hguards : ∀ x ∈ closedBall (T.symm (u, 0)) r, τ < overlapNorm b κ (T x) ∧
      τ < Real.sqrt (stateNormSq (mixed b κ m (T x))))
    (hbound : ∀ x ∈ closedBall (T.symm (u, 0)) r, ‖derivative T b κ m x‖ ≤ (q : ℝ)) :
    ∀ z : ComplexField, T.symm (unpack z) ∈ closedBall (T.symm (u, 0)) r →
      Tendsto (fun n : ℕ => (nativeUpdate τ b κ m)^[n] z) atTop (nhds (realEmbed u)) ∧
      ∀ n : ℕ, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[n] z) ∧
        NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) ∧
        dist (T.symm (unpack ((nativeUpdate τ b κ m)^[n] z))) (T.symm (u, 0)) ≤
          (q : ℝ)^n * dist (T.symm (unpack z)) (T.symm (u, 0)) := by
  have hl := coordinate_lipschitz T b κ m τ r (T.symm (u, 0)) q hτ hguards hbound
  have hfix := coordinate_fixed T (m := m) hu hf hτ hτ1
  intro z hz
  have ht := GroundLocalDynamics.lipschitz_fixed_orbit_converges hr hq hfix hl hz
  have hb := GroundLocalDynamics.lipschitz_fixed_orbit_bound hr hq.le hfix hl hz
  have hreturn (n : ℕ) : pack (T ((coordinateMap T τ b κ m)^[n] (T.symm (unpack z)))) =
      (nativeUpdate τ b κ m)^[n] z := by
    rw [coordinate_iterate_return]
    simpa only [T.apply_symm_apply, packCLE_apply, packCLE_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] using
      GroundNativeJacobian.nativePairMap_iterate_return τ b κ m (unpack z) n
  have hcoord (n : ℕ) : T.symm (unpack ((nativeUpdate τ b κ m)^[n] z)) =
      (coordinateMap T τ b κ m)^[n] (T.symm (unpack z)) := by
    rw [← hreturn n]
    change T.symm (packCLE.symm (packCLE (T _))) = _
    simp only [packCLE.symm_apply_apply, T.symm_apply_apply]
  constructor
  · have hh := packCLE.continuous.continuousAt.tendsto.comp (T.continuous.continuousAt.tendsto.comp ht)
    simpa only [Function.comp_def, packCLE_apply, hreturn, T.apply_symm_apply] using hh
  · intro n
    obtain ⟨ho, hn⟩ := hguards _ (hb n).1
    have hg := native_guards b κ m τ _ hτ ho hn
    rw [hreturn n] at hg
    exact ⟨hg.1, hg.2, by rw [hcoord n]; exact (hb n).2⟩

end
end SbtCosmo.Derivation.GroundNativeQuantitativeBall
