import SbtCosmo.Derivation.GroundNativeJacobian

/-! Local convergence of the unchanged native complex update with its actual
phase and normalization guards maintained at every iterate. -/
namespace SbtCosmo.Derivation.GroundNativeLocal
noncomputable section
set_option maxHeartbeats 2000000
open Filter NNReal Metric GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian
open GroundNativePhase GroundNativeDerivative GroundNativeIteration GroundNativeJacobian
open scoped Topology ContDiff BigOperators

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem c1_local_attraction_inside {f : E → E} {u : E} {s : Set E}
    (hc : ContDiffAt ℝ 1 f u) (hf : f u = u) (hd : ‖fderiv ℝ f u‖ < 1) (hs : s ∈ nhds u) :
    ∃ r > 0, ∃ q : ℝ≥0, q < 1 ∧ closedBall u r ⊆ s ∧
      ∀ y ∈ closedBall u r,
        Tendsto (fun n : ℕ => f^[n] y) atTop (nhds u) ∧
        ∀ n : ℕ, f^[n] y ∈ s ∧ dist (f^[n] y) u ≤ (q : ℝ)^n * dist y u := by
  have hd' : ‖fderiv ℝ f u‖₊ < (1 : ℝ≥0) := by exact_mod_cast hd
  obtain ⟨q, hlower, hupper⟩ := exists_between hd'
  obtain ⟨t, ht, hl⟩ := hc.exists_lipschitzOnWith_of_nnnorm_lt q hlower
  obtain ⟨r, hr, hrt⟩ := nhds_basis_closedBall.mem_iff.mp (Filter.inter_mem ht hs)
  have hl' := hl.mono (hrt.trans Set.inter_subset_left)
  have hrs := hrt.trans Set.inter_subset_right
  refine ⟨r, hr, q, hupper, hrs, fun y hy => ?_⟩
  refine ⟨GroundLocalDynamics.lipschitz_fixed_orbit_converges hr.le hupper hf hl' hy, fun n => ?_⟩
  have hb := GroundLocalDynamics.lipschitz_fixed_orbit_bound hr.le hupper.le hf hl' hy n
  exact ⟨hrs hb.1, hb.2⟩

end General

def coordinateMap (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ) (x : State) : State :=
  T.symm (nativePairMap τ b κ m (T x))
def coordinateDerivative (T : State ≃L[ℝ] State) (b : Field) (κ m : ℝ) (u : Field) : State →L[ℝ] State :=
  T.symm.toContinuousLinearMap.comp ((fullDerivative b κ m u).comp T.toContinuousLinearMap)
def NativeRegion (τ : ℝ) (b : Field) (κ m : ℝ) : Set State :=
  {x | ActivePhase τ b κ (pack x) ∧ NativeLegal τ b κ m (pack x)}

theorem native_region_near_fixed {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    NativeRegion τ b κ m ∈ nhds (u, (0 : Field)) := by
  filter_upwards [nativeUpdate_near_fixed (m := m) hu hf hτ0 hτ1] with x hx
  exact hx.2

theorem coordinate_hasFDerivAt (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    HasFDerivAt (coordinateMap T τ b κ m) (coordinateDerivative T b κ m u) (T.symm (u, 0)) := by
  have hd : HasFDerivAt (nativePairMap τ b κ m) (fullDerivative b κ m u) (T (T.symm (u, 0))) := by
    simpa using nativePairMap_hasFDerivAt (m := m) hu hf hτ0 hτ1
  exact T.symm.toContinuousLinearMap.hasFDerivAt.comp _
    (hd.comp _ T.toContinuousLinearMap.hasFDerivAt)

theorem coordinate_smooth_at (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ContDiffAt ℝ ∞ (coordinateMap T τ b κ m) (T.symm (u, 0)) := by
  have hc : ContDiffAt ℝ ∞ (nativePairMap τ b κ m) (T (T.symm (u, 0))) := by
    simpa using nativePairMap_smooth_at (m := m) hu hf hτ0 hτ1
  exact T.symm.contDiff.contDiffAt.comp _ (hc.comp _ T.contDiff.contDiffAt)

theorem coordinate_fixed (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    coordinateMap T τ b κ m (T.symm (u, 0)) = T.symm (u, 0) := by
  simp [coordinateMap, nativePairMap_fixed hu hf hτ0 hτ1]

theorem coordinate_iterate_return (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ)
    (x : State) (n : ℕ) :
    T ((coordinateMap T τ b κ m)^[n] x) = (nativePairMap τ b κ m)^[n] (T x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp [coordinateMap, ih]

/-- Native sixteen-real-coordinate convergence with no illegal iterate hidden
behind a totalized normalization formula. The actual derivative bound is explicit. -/
theorem native_complex_local_attraction (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hd : ‖coordinateDerivative T b κ m u‖ < 1) :
    ∃ r > 0, ∀ z : ComplexField, T.symm (unpack z) ∈ closedBall (T.symm (u, 0)) r →
      Tendsto (fun n : ℕ => (nativeUpdate τ b κ m)^[n] z) atTop (nhds (realEmbed u)) ∧
      ∀ n : ℕ, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[n] z) ∧
        NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) := by
  have hc : ContDiffAt ℝ 1 (coordinateMap T τ b κ m) (T.symm (u, 0)) :=
    (coordinate_smooth_at T hu hf hτ0 hτ1).of_le (by simp)
  have hd' : ‖fderiv ℝ (coordinateMap T τ b κ m) (T.symm (u, 0))‖ < 1 := by
    rw [(coordinate_hasFDerivAt T hu hf hτ0 hτ1).fderiv]
    exact hd
  have hregion : {x | T x ∈ NativeRegion τ b κ m} ∈ nhds (T.symm (u, 0)) := by
    have hh := T.continuous.continuousAt (x := T.symm (u, 0)) |>.tendsto
    have hr := native_region_near_fixed (m := m) hu hf hτ0 hτ1
    rw [T.apply_symm_apply] at hh
    exact hh.eventually hr
  obtain ⟨r, hr, _, _, _, ho⟩ := c1_local_attraction_inside hc
    (coordinate_fixed T hu hf hτ0 hτ1) hd' hregion
  refine ⟨r, hr, fun z hz => ?_⟩
  obtain ⟨ht, hg⟩ := ho (T.symm (unpack z)) hz
  have hreturn (n : ℕ) : pack (T ((coordinateMap T τ b κ m)^[n] (T.symm (unpack z)))) =
      (nativeUpdate τ b κ m)^[n] z := by
    rw [coordinate_iterate_return]
    simpa only [T.apply_symm_apply, packCLE_apply, packCLE_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] using
      nativePairMap_iterate_return τ b κ m (unpack z) n
  refine ⟨?_, fun n => ?_⟩
  · have hh := packCLE.continuous.continuousAt.tendsto.comp (T.continuous.continuousAt.tendsto.comp ht)
    simpa only [Function.comp_def, packCLE_apply, hreturn, T.apply_symm_apply] using hh
  · have hguard := (hg n).1
    change ActivePhase τ b κ (pack (T ((coordinateMap T τ b κ m)^[n] (T.symm (unpack z))))) ∧
      NativeLegal τ b κ m (pack (T ((coordinateMap T τ b κ m)^[n] (T.symm (unpack z))))) at hguard
    simpa only [hreturn] using hguard

def imaginaryCoordinate (S : Field ≃L[ℝ] Field) (m : ℝ) (u : Field) : Field →L[ℝ] Field :=
  S.symm.toContinuousLinearMap.comp ((imaginaryDerivative m u).comp S.toContinuousLinearMap)

theorem coordinateDerivative_blocks (S R : Field ≃L[ℝ] Field) (b : Field) (κ m : ℝ) (u : Field) :
    coordinateDerivative (S.prodCongr R) b κ m u =
      (GroundLocalDynamics.coordinateJacobian S b κ m u).prodMap (imaginaryCoordinate R m u) := by
  apply ContinuousLinearMap.ext
  intro h
  rfl

theorem product_operator_norm_bound (L K : Field →L[ℝ] Field) :
    ‖L.prodMap K‖ ≤ max ‖L‖ ‖K‖ := by
  apply (L.prodMap K).opNorm_le_bound (le_max_of_le_left (norm_nonneg L))
  intro h
  rw [Prod.norm_def]
  apply max_le
  · exact (L.le_opNorm h.1).trans (mul_le_mul (le_max_left _ _) (by rw [Prod.norm_def]; exact le_max_left _ _)
      (norm_nonneg _) (le_max_of_le_left (norm_nonneg L)))
  · exact (K.le_opNorm h.2).trans (mul_le_mul (le_max_right _ _) (by rw [Prod.norm_def]; exact le_max_right _ _)
      (norm_nonneg _) (le_max_of_le_left (norm_nonneg L)))

theorem native_complex_local_attraction_of_rows (S R : Field ≃L[ℝ] Field)
    {b u : Field} {κ m τ a c : ℝ} (hu : normSq u = 1) (hf : groundMap b κ u = u)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 ≤ c) (hc1 : c < 1)
    (hreal : ∀ i, (∑ j, |GroundLocalDynamics.coordinateJacobian S b κ m u (GroundLocalDynamics.column j) i|) ≤ a)
    (himag : ∀ i, (∑ j, |imaginaryCoordinate R m u (GroundLocalDynamics.column j) i|) ≤ c) :
    ∃ r > 0, ∀ z : ComplexField,
      (S.prodCongr R).symm (unpack z) ∈ closedBall ((S.prodCongr R).symm (u, 0)) r →
        Tendsto (fun n : ℕ => (nativeUpdate τ b κ m)^[n] z) atTop (nhds (realEmbed u)) ∧
        ∀ n : ℕ, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[n] z) ∧
          NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[n] z) := by
  apply native_complex_local_attraction (S.prodCongr R) hu hf hτ0 hτ1
  rw [coordinateDerivative_blocks]
  apply (product_operator_norm_bound _ _).trans_lt
  apply max_lt
  · exact (GroundLocalDynamics.operator_norm_le_rows _ ha hreal).trans_lt ha1
  · exact (GroundLocalDynamics.operator_norm_le_rows _ hc himag).trans_lt hc1

end
end SbtCosmo.Derivation.GroundNativeLocal
