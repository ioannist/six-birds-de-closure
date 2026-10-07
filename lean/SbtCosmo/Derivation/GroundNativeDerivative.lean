import SbtCosmo.Derivation.GroundNativePhase

/-! Actual first derivative of unchanged complex sourcing and the source's
conjugated phase alignment, in real/imaginary coordinates. -/
namespace SbtCosmo.Derivation.GroundNativeDerivative
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian GroundNativePhase
open scoped BigOperators ContDiff

def pairSourceDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] Field :=
  (sourceDerivative b κ x.1).comp (ContinuousLinearMap.fst ℝ Field Field) +
  (sourceDerivative b κ x.2).comp (ContinuousLinearMap.snd ℝ Field Field)

theorem sourceDerivative_zero_field (b : Field) (κ : ℝ) : sourceDerivative b κ 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro h
  funext i
  simp [sourceDerivative_apply, GroundState.gradient]

theorem pairSource_hasFDerivAt (b : Field) (κ : ℝ) (x : State) :
    HasFDerivAt (pairSource b κ) (pairSourceDerivative b κ x) x := by
  have hr := (sourcePotential_hasFDerivAt b κ x.1).comp x
    (ContinuousLinearMap.fst ℝ Field Field).hasFDerivAt
  have hi := (sourcePotential_hasFDerivAt b κ x.2).comp x
    (ContinuousLinearMap.snd ℝ Field Field).hasFDerivAt
  have hh := hr.add hi |>.sub_const b
  convert hh using 1
  funext y i
  simp only [pairSource, Function.comp_def, sourcePotential, BackgroundSelection.potential,
    Pi.sub_apply, Pi.add_apply]
  ring

def selectedDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] Field :=
  (GroundSmooth.selectorDerivative (pairSource b κ x)).comp (pairSourceDerivative b κ x)

theorem selected_hasFDerivAt (b : Field) (κ : ℝ) (x : State) :
    HasFDerivAt (selected b κ) (selectedDerivative b κ x) x :=
  (GroundSmooth.positiveGround_hasFDerivAt _).comp x (pairSource_hasFDerivAt b κ x)

theorem selected_hasFDerivAt_real (b : Field) (κ : ℝ) (u : Field) :
    HasFDerivAt (selected b κ)
      ((jacobian b κ u).comp (ContinuousLinearMap.fst ℝ Field Field)) (u, 0) := by
  convert selected_hasFDerivAt b κ (u, 0) using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [selectedDerivative, pairSourceDerivative, pairSource_real, sourceDerivative_zero_field,
    jacobian]

def realDot (u : Field) : State →L[ℝ] ℝ := (dotMap u).comp (ContinuousLinearMap.fst ℝ Field Field)
def imagDot (u : Field) : State →L[ℝ] ℝ := (dotMap u).comp (ContinuousLinearMap.snd ℝ Field Field)

theorem realDot_apply (u : Field) (h : State) : realDot u h = dot u h.1 := by simp [realDot, dotMap_apply]
theorem imagDot_apply (u : Field) (h : State) : imagDot u h = dot u h.2 := by simp [imagDot, dotMap_apply]

theorem realOverlap_hasFDerivAt {b u : Field} {κ : ℝ} (hf : groundMap b κ u = u) :
    HasFDerivAt (realOverlap b κ) (realDot u) (u, 0) := by
  have hg (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp (u, (0 : Field))
    (selected_hasFDerivAt_real b κ u)
  have ha (i : Fin 8) := ((ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.fst ℝ Field Field)).hasFDerivAt (x := (u, 0))
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hg i).mul (ha i))
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  have hj := jacobian_tangent b κ u h.1
  rw [hf] at hj
  simp [realDot, dotMap_apply, selected_real, hf, Finset.sum_add_distrib]
  have hj' : (∑ i, u i * jacobian b κ u h.1 i) = 0 := hj
  rw [hj']
  simp [dot]

theorem imagOverlap_hasFDerivAt {b u : Field} {κ : ℝ} (hf : groundMap b κ u = u) :
    HasFDerivAt (imagOverlap b κ) (imagDot u) (u, 0) := by
  have hg (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp (u, (0 : Field))
    (selected_hasFDerivAt_real b κ u)
  have ha (i : Fin 8) := ((ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.snd ℝ Field Field)).hasFDerivAt (x := (u, 0))
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hg i).mul (ha i))
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [imagDot, dotMap_apply, selected_real, hf, dot]

theorem overlapNorm_hasFDerivAt {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (overlapNorm b κ) (realDot u) (u, 0) := by
  obtain ⟨hr, hi, _⟩ := overlap_at_fixed hu hf
  have hh := (((realOverlap_hasFDerivAt hf).pow 2).add
    ((imagOverlap_hasFDerivAt hf).pow 2)).sqrt (by simp [hr, hi])
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [hr, hi]

theorem realFactor_hasFDerivAt {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (fun x => realOverlap b κ x / overlapNorm b κ x)
      (0 : State →L[ℝ] ℝ) (u, 0) := by
  obtain ⟨hr, _, hn⟩ := overlap_at_fixed hu hf
  have hinv := (hasDerivAt_inv (by rw [hn]; norm_num : overlapNorm b κ (u, 0) ≠ 0)).comp_hasFDerivAt
    (u, (0 : Field)) (overlapNorm_hasFDerivAt hu hf)
  have hh := (realOverlap_hasFDerivAt hf).mul hinv
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [hr, hn]

theorem imagFactor_hasFDerivAt {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (fun x => -imagOverlap b κ x / overlapNorm b κ x)
      (-imagDot u) (u, 0) := by
  obtain ⟨_, hi, hn⟩ := overlap_at_fixed hu hf
  have hinv := (hasDerivAt_inv (by rw [hn]; norm_num : overlapNorm b κ (u, 0) ≠ 0)).comp_hasFDerivAt
    (u, (0 : Field)) (overlapNorm_hasFDerivAt hu hf)
  have hh := (imagOverlap_hasFDerivAt hf).neg.mul hinv
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [hi, hn]

def alignedDerivative (b : Field) (κ : ℝ) (u : Field) : State →L[ℝ] State :=
  ((jacobian b κ u).comp (ContinuousLinearMap.fst ℝ Field Field)).prod
    (-(imagDot u).smulRight u)

theorem alignedDerivative_apply (b : Field) (κ : ℝ) (u : Field) (h : State) :
    alignedDerivative b κ u h = (jacobian b κ u h.1, fun i => -dot u h.2 * u i) := by
  apply Prod.ext
  · rfl
  · funext i
    simp [alignedDerivative, imagDot_apply]

/-- The negative imaginary phase term is the unchanged native sign error. -/
theorem aligned_hasFDerivAt {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (aligned b κ) (alignedDerivative b κ u) (u, 0) := by
  have hg := selected_hasFDerivAt_real b κ u
  have hr := (realFactor_hasFDerivAt hu hf).smul hg
  have hi := (imagFactor_hasFDerivAt hu hf).smul hg
  have hh := hr.prodMk hi
  obtain ⟨hreal, him, hn⟩ := overlap_at_fixed hu hf
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · funext i
    simp [alignedDerivative, hreal, him, hn]
  · funext i
    simp [alignedDerivative, selected_real, hf, hreal, him, hn]

end
end SbtCosmo.Derivation.GroundNativeDerivative
