import SbtCosmo.Derivation.GroundNativeDerivative

/-! Exact native complex update on its declared phase/normalization guard.
The total formula is used for calculus; source legality is a separate predicate.
No value of this total formula at zero is attributed to source execution. -/
namespace SbtCosmo.Derivation.GroundNativeIteration
noncomputable section
set_option maxHeartbeats 2000000
open Filter GroundState GroundBorder GroundSourceJacobian GroundNativePhase GroundNativeDerivative
open scoped BigOperators ContDiff Topology

def mixed (b : Field) (κ m : ℝ) (x : State) : State := (1-m) • x + m • aligned b κ x
def normalizeState (x : State) : State := (Real.sqrt (stateNormSq x))⁻¹ • x
def fullMap (b : Field) (κ m : ℝ) (x : State) : State := normalizeState (mixed b κ m x)
def complexNormalize (z : ComplexField) : ComplexField := fun i => z i / (Real.sqrt (complexNormSq z) : ℂ)
def nativeCandidate (b : Field) (κ : ℝ) (z : ComplexField) : ComplexField :=
  realEmbed (positiveGround (complexSourcePotential b κ z))
def nativeMixed (τ : ℝ) (b : Field) (κ m : ℝ) (z : ComplexField) : ComplexField :=
  (1-m) • z + m • nativePhase τ (nativeCandidate b κ z) z
def nativeUpdate (τ : ℝ) (b : Field) (κ m : ℝ) (z : ComplexField) : ComplexField :=
  complexNormalize (nativeMixed τ b κ m z)
def NativeLegal (τ : ℝ) (b : Field) (κ m : ℝ) (z : ComplexField) : Prop :=
  τ < Real.sqrt (complexNormSq (nativeMixed τ b κ m z))
def ActivePhase (τ : ℝ) (b : Field) (κ : ℝ) (z : ComplexField) : Prop :=
  τ < ‖overlap (nativeCandidate b κ z) z‖

theorem pack_normalizeState (x : State) : pack (normalizeState x) = complexNormalize (pack x) := by
  rw [normalizeState, ← packCLE_apply, map_smul]
  rw [packCLE_apply]
  funext i
  simp [complexNormalize, norm_pack, div_eq_mul_inv]
  ring

theorem nativeCandidate_pack (b : Field) (κ : ℝ) (x : State) :
    nativeCandidate b κ (pack x) = realEmbed (selected b κ x) := by
  simp [nativeCandidate, source_pack, selected]

theorem pack_mixed_native {τ : ℝ} (hτ : 0 ≤ τ) (b : Field) (κ m : ℝ) (x : State)
    (ho : τ < overlapNorm b κ x) :
    pack (mixed b κ m x) = nativeMixed τ b κ m (pack x) := by
  change packCLE ((1-m) • x + m • aligned b κ x) = _
  simp only [map_add, map_smul, packCLE_apply, nativeMixed, nativeCandidate_pack]
  rw [aligned_native_return b κ x hτ ho]

theorem fullMap_native_return {τ : ℝ} (hτ : 0 ≤ τ) (b : Field) (κ m : ℝ) (x : State)
    (ho : τ < overlapNorm b κ x) :
    pack (fullMap b κ m x) = nativeUpdate τ b κ m (pack x) := by
  unfold fullMap nativeUpdate
  rw [pack_normalizeState, pack_mixed_native hτ b κ m x ho]

theorem realOverlap_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (realOverlap b κ) := by
  have hg := selected_smooth b κ
  unfold realOverlap dot
  fun_prop

theorem imagOverlap_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (imagOverlap b κ) := by
  have hg := selected_smooth b κ
  unfold imagOverlap dot
  fun_prop

theorem overlapSq_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (overlapSq b κ) :=
  ((realOverlap_smooth b κ).pow 2).add ((imagOverlap_smooth b κ).pow 2)

theorem overlapNorm_smooth_at {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    ContDiffAt ℝ ∞ (overlapNorm b κ) (u, 0) := by
  obtain ⟨hr, hi, _⟩ := overlap_at_fixed hu hf
  exact (overlapSq_smooth b κ).contDiffAt.sqrt (by simp [overlapSq, hr, hi])

theorem aligned_smooth_at {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    ContDiffAt ℝ ∞ (aligned b κ) (u, 0) := by
  have hn : overlapNorm b κ (u, 0) ≠ 0 := by rw [(overlap_at_fixed hu hf).2.2]; norm_num
  have hd := overlapNorm_smooth_at hu hf
  have hg := (selected_smooth b κ).contDiffAt (x := (u, 0))
  exact (((realOverlap_smooth b κ).contDiffAt.div hd hn).smul hg).prodMk
    ((((imagOverlap_smooth b κ).neg.contDiffAt.div hd hn)).smul hg)

theorem aligned_fixed {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) : aligned b κ (u, 0) = (u, 0) := by
  obtain ⟨hr, hi, hn⟩ := overlap_at_fixed hu hf
  apply Prod.ext
  · funext i
    simp [aligned, hr, hn, selected_real, hf]
  · funext i
    simp [aligned, hi]

theorem mixed_fixed {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) : mixed b κ m (u, 0) = (u, 0) := by
  rw [mixed, aligned_fixed hu hf, ← add_smul]
  simp

theorem stateNormSq_smooth : ContDiff ℝ ∞ stateNormSq :=
  (GroundLocalDynamics.normSq_smooth.comp contDiff_fst).add
    (GroundLocalDynamics.normSq_smooth.comp contDiff_snd)

theorem normalizeState_smooth_at {x : State} (hx : 0 < stateNormSq x) :
    ContDiffAt ℝ ∞ normalizeState x :=
  ((stateNormSq_smooth.contDiffAt.sqrt hx.ne').inv (Real.sqrt_pos.mpr hx).ne').smul contDiffAt_id

theorem stateNormSq_real {u : Field} (hu : normSq u = 1) : stateNormSq (u, 0) = 1 := by
  change normSq u + normSq 0 = 1
  rw [hu]
  simp [normSq]

theorem normalizeState_real_fixed {u : Field} (hu : normSq u = 1) : normalizeState (u, 0) = (u, 0) := by
  simp [normalizeState, stateNormSq_real hu]

theorem fullMap_fixed {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) : fullMap b κ m (u, 0) = (u, 0) := by
  rw [fullMap, mixed_fixed hu hf, normalizeState_real_fixed hu]

theorem mixed_smooth_at {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    ContDiffAt ℝ ∞ (mixed b κ m) (u, 0) :=
  (contDiffAt_id.const_smul (1-m)).add ((aligned_smooth_at hu hf).const_smul m)

theorem fullMap_smooth_at {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    ContDiffAt ℝ ∞ (fullMap b κ m) (u, 0) := by
  have hn : ContDiffAt ℝ ∞ normalizeState (mixed b κ m (u, 0)) := by
    rw [mixed_fixed hu hf]
    apply normalizeState_smooth_at
    rw [stateNormSq_real hu]
    norm_num
  exact hn.comp (u, 0) (mixed_smooth_at hu hf)

theorem phase_guard_near_fixed {b u : Field} {κ τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ : τ < 1) :
    ∀ᶠ x in nhds (u, (0 : Field)), τ < overlapNorm b κ x := by
  have hc := (overlapNorm_smooth_at hu hf).continuousAt
  have hh : τ < overlapNorm b κ (u, 0) := by rw [(overlap_at_fixed hu hf).2.2]; exact hτ
  exact hc.eventually (lt_mem_nhds hh)

theorem normalization_guard_near_fixed {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ : τ < 1) :
    ∀ᶠ x in nhds (u, (0 : Field)), τ < Real.sqrt (stateNormSq (mixed b κ m x)) := by
  have hc : ContinuousAt (fun x => Real.sqrt (stateNormSq (mixed b κ m x))) (u, 0) :=
    Real.continuous_sqrt.continuousAt.comp
      (stateNormSq_smooth.continuous.continuousAt.comp (mixed_smooth_at hu hf).continuousAt)
  have hh : τ < Real.sqrt (stateNormSq (mixed b κ m (u, 0))) := by
    rw [mixed_fixed hu hf, stateNormSq_real hu]
    simpa using hτ
  exact hc.eventually (lt_mem_nhds hh)

theorem nativeUpdate_near_fixed {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ∀ᶠ x in nhds (u, (0 : Field)),
      pack (fullMap b κ m x) = nativeUpdate τ b κ m (pack x) ∧
      ActivePhase τ b κ (pack x) ∧ NativeLegal τ b κ m (pack x) := by
  filter_upwards [phase_guard_near_fixed hu hf hτ1,
    normalization_guard_near_fixed (m := m) hu hf hτ1] with x hx hn
  refine ⟨fullMap_native_return hτ0 b κ m x hx, ?_, ?_⟩
  · simpa [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using hx
  · simpa only [NativeLegal, ← pack_mixed_native hτ0 b κ m x hx, norm_pack] using hn

end
end SbtCosmo.Derivation.GroundNativeIteration
