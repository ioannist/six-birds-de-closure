import SbtCosmo.Derivation.GroundNativeIteration

/-! Actual full sixteen-real-coordinate derivative of the unchanged complex
phase-aligned and normalized update near its positive fixed points. -/
namespace SbtCosmo.Derivation.GroundNativeJacobian
noncomputable section
set_option maxHeartbeats 2000000
open Filter GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian
open GroundNativePhase GroundNativeDerivative GroundNativeIteration
open scoped BigOperators ContDiff Topology

theorem stateNormSq_hasFDerivAt_real (u : Field) :
    HasFDerivAt stateNormSq ((2 : ℝ) • realDot u) (u, 0) := by
  have hr := (normSq_hasFDerivAt u).comp (u, (0 : Field))
    (ContinuousLinearMap.fst ℝ Field Field).hasFDerivAt
  have hi := (normSq_hasFDerivAt (0 : Field)).comp (u, (0 : Field))
    (ContinuousLinearMap.snd ℝ Field Field).hasFDerivAt
  convert hr.add hi using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [realDot, dotMap_apply, dot]

theorem stateSqrt_hasFDerivAt_real {u : Field} (hu : normSq u = 1) :
    HasFDerivAt (fun x => Real.sqrt (stateNormSq x)) (realDot u) (u, 0) := by
  have hh := (stateNormSq_hasFDerivAt_real u).sqrt (by rw [stateNormSq_real hu]; norm_num)
  convert hh using 1
  norm_num [stateNormSq_real hu, smul_smul]

theorem stateInvSqrt_hasFDerivAt_real {u : Field} (hu : normSq u = 1) :
    HasFDerivAt (fun x => (Real.sqrt (stateNormSq x))⁻¹) (-realDot u) (u, 0) := by
  have hh := (hasDerivAt_inv (by rw [stateNormSq_real hu]; norm_num : Real.sqrt (stateNormSq (u, (0 : Field))) ≠ 0)).comp_hasFDerivAt
    (u, (0 : Field)) (stateSqrt_hasFDerivAt_real hu)
  simpa only [stateNormSq_real hu, Real.sqrt_one, one_pow, inv_one, neg_smul, one_smul] using hh

def stateProjection (u : Field) : State →L[ℝ] State :=
  (projection u).prodMap (ContinuousLinearMap.id ℝ Field)

theorem normalizeState_hasFDerivAt_real {u : Field} (hu : normSq u = 1) :
    HasFDerivAt normalizeState (stateProjection u) (u, 0) := by
  have hh := (stateInvSqrt_hasFDerivAt_real hu).smul (hasFDerivAt_id (u, (0 : Field)))
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · funext i
    simp [stateProjection, projection, dotMap_apply, realDot_apply,
      stateNormSq_real hu, sub_eq_add_neg]
  · funext i
    simp [stateProjection, stateNormSq_real hu]

def mixedDerivative (b : Field) (κ m : ℝ) (u : Field) : State →L[ℝ] State :=
  (1-m) • ContinuousLinearMap.id ℝ State + m • alignedDerivative b κ u

theorem mixed_hasFDerivAt_real {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (mixed b κ m) (mixedDerivative b κ m u) (u, 0) :=
  ((hasFDerivAt_id (u, (0 : Field))).const_smul (1-m)).add
    ((aligned_hasFDerivAt hu hf).const_smul m)

def imaginaryDerivative (m : ℝ) (u : Field) : Field →L[ℝ] Field :=
  (1-m) • ContinuousLinearMap.id ℝ Field - m • (dotMap u).smulRight u
def fullDerivative (b : Field) (κ m : ℝ) (u : Field) : State →L[ℝ] State :=
  (normalizedJacobian b κ m u).prodMap (imaginaryDerivative m u)

theorem imaginaryDerivative_apply (m : ℝ) (u h : Field) (i : Fin 8) :
    imaginaryDerivative m u h i = (1-m)*h i-m*dot u h*u i := by
  simp [imaginaryDerivative, dotMap_apply]
  ring

theorem fullDerivative_apply (b : Field) (κ m : ℝ) (u : Field) (h : State) :
    fullDerivative b κ m u h =
      (normalizedJacobian b κ m u h.1, imaginaryDerivative m u h.2) := rfl

theorem fullMap_hasFDerivAt_real {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (fullMap b κ m) (fullDerivative b κ m u) (u, 0) := by
  have hn : HasFDerivAt normalizeState (stateProjection u) (mixed b κ m (u, 0)) := by
    rw [mixed_fixed hu hf]
    exact normalizeState_hasFDerivAt_real hu
  have hh := hn.comp (u, (0 : Field)) (mixed_hasFDerivAt_real hu hf)
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · rfl
  · funext i
    simp [fullDerivative, imaginaryDerivative, mixedDerivative, alignedDerivative,
      stateProjection, imagDot_apply, dotMap_apply]
    ring

theorem imaginary_tangent_mode {u h : Field} (m : ℝ) (ht : dot u h = 0) :
    imaginaryDerivative m u h = (1-m) • h := by
  funext i
  rw [imaginaryDerivative_apply, ht]
  simp

theorem imaginary_phase_mode {u : Field} (m : ℝ) (hu : normSq u = 1) :
    imaginaryDerivative m u u = (1-2*m) • u := by
  funext i
  rw [imaginaryDerivative_apply, dot_self, hu]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem half_mixing_imaginary_projection (u : Field) : imaginaryDerivative (1/2) u = (1/2 : ℝ) • projection u := by
  apply ContinuousLinearMap.ext
  intro h
  funext i
  rw [imaginaryDerivative_apply]
  simp [projection_apply]
  ring

def nativePairMap (τ : ℝ) (b : Field) (κ m : ℝ) (x : State) : State :=
  unpack (nativeUpdate τ b κ m (pack x))

theorem nativePairMap_eventual_return {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    nativePairMap τ b κ m =ᶠ[nhds (u, (0 : Field))] fullMap b κ m := by
  filter_upwards [nativeUpdate_near_fixed (m := m) hu hf hτ0 hτ1] with x hx
  have he := congrArg unpack hx.1
  exact he.symm

theorem nativePairMap_smooth_at {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ContDiffAt ℝ ∞ (nativePairMap τ b κ m) (u, 0) :=
  (fullMap_smooth_at hu hf).congr_of_eventuallyEq (nativePairMap_eventual_return hu hf hτ0 hτ1)

/-- Exact native derivative, with both threshold guards earned locally. -/
theorem nativePairMap_hasFDerivAt {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    HasFDerivAt (nativePairMap τ b κ m) (fullDerivative b κ m u) (u, 0) :=
  (fullMap_hasFDerivAt_real hu hf).congr_of_eventuallyEq (nativePairMap_eventual_return hu hf hτ0 hτ1)

theorem nativePairMap_fixed {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    nativePairMap τ b κ m (u, 0) = (u, 0) := by
  have he := (nativePairMap_eventual_return (m := m) hu hf hτ0 hτ1).eq_of_nhds
  rw [he, fullMap_fixed hu hf]

theorem nativePairMap_iterate_return (τ : ℝ) (b : Field) (κ m : ℝ) (x : State) (n : ℕ) :
    pack ((nativePairMap τ b κ m)^[n] x) = (nativeUpdate τ b κ m)^[n] (pack x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change packCLE (packCLE.symm (nativeUpdate τ b κ m (pack ((nativePairMap τ b κ m)^[n] x)))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, ih]

end
end SbtCosmo.Derivation.GroundNativeJacobian
