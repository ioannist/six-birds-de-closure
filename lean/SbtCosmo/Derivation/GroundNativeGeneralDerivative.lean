import SbtCosmo.Derivation.GroundNativeJacobian
namespace SbtCosmo.Derivation.GroundNativeGeneralDerivative
noncomputable section
set_option maxHeartbeats 3000000
open GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian GroundNativePhase GroundNativeDerivative GroundNativeIteration
open Filter
open scoped BigOperators Topology

def stateDot (x : State) : State →L[ℝ] ℝ := realDot x.1 + imagDot x.2

theorem stateNormSq_hasFDerivAt (x : State) :
    HasFDerivAt stateNormSq ((2 : ℝ) • stateDot x) x := by
  have hr := (normSq_hasFDerivAt x.1).comp x
    (ContinuousLinearMap.fst ℝ Field Field).hasFDerivAt
  have hi := (normSq_hasFDerivAt x.2).comp x
    (ContinuousLinearMap.snd ℝ Field Field).hasFDerivAt
  convert hr.add hi using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [stateDot, realDot_apply, imagDot_apply, dotMap_apply]

def realOverlapDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] ℝ :=
  (dotMap x.1).comp (selectedDerivative b κ x) + realDot (selected b κ x)
def imagOverlapDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] ℝ :=
  (dotMap x.2).comp (selectedDerivative b κ x) + imagDot (selected b κ x)

theorem realOverlap_hasFDerivAt (b : Field) (κ : ℝ) (x : State) :
    HasFDerivAt (realOverlap b κ) (realOverlapDerivative b κ x) x := by
  have hg (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp x
    (selected_hasFDerivAt b κ x)
  have ha (i : Fin 8) := ((ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.fst ℝ Field Field)).hasFDerivAt (x := x)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hg i).mul (ha i))
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [realOverlapDerivative, realDot_apply, dotMap_apply, dot, Finset.sum_add_distrib]
  ring

theorem imagOverlap_hasFDerivAt (b : Field) (κ : ℝ) (x : State) :
    HasFDerivAt (imagOverlap b κ) (imagOverlapDerivative b κ x) x := by
  have hg (i : Fin 8) := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp x
    (selected_hasFDerivAt b κ x)
  have ha (i : Fin 8) := ((ContinuousLinearMap.proj (R := ℝ) i).comp
    (ContinuousLinearMap.snd ℝ Field Field)).hasFDerivAt (x := x)
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hg i).mul (ha i))
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [imagOverlapDerivative, imagDot_apply, dotMap_apply, dot, Finset.sum_add_distrib]
  ring

def overlapNumeratorDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] ℝ :=
  realOverlap b κ x • realOverlapDerivative b κ x +
  imagOverlap b κ x • imagOverlapDerivative b κ x

def overlapInverseDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] ℝ :=
  -((overlapNorm b κ x)⁻¹)^3 • overlapNumeratorDerivative b κ x

theorem overlapInverse_hasFDerivAt (b : Field) (κ : ℝ) (x : State)
    (hn : 0 < overlapSq b κ x) :
    HasFDerivAt (fun y => (overlapNorm b κ y)⁻¹) (overlapInverseDerivative b κ x) x := by
  have hs := (((realOverlap_hasFDerivAt b κ x).pow 2).add
    ((imagOverlap_hasFDerivAt b κ x).pow 2)).sqrt hn.ne'
  have hp : overlapNorm b κ x ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hh := (hasDerivAt_inv hp).comp_hasFDerivAt x hs
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [overlapInverseDerivative, overlapNumeratorDerivative, overlapNorm, overlapSq]
  field_simp


def realFactorDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] ℝ :=
  (overlapNorm b κ x)⁻¹ • realOverlapDerivative b κ x +
  realOverlap b κ x • overlapInverseDerivative b κ x

def imagFactorDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] ℝ :=
  -((overlapNorm b κ x)⁻¹ • imagOverlapDerivative b κ x) -
  imagOverlap b κ x • overlapInverseDerivative b κ x

theorem realFactor_hasFDerivAt (b : Field) (κ : ℝ) (x : State)
    (hn : 0 < overlapSq b κ x) :
    HasFDerivAt (fun y => realOverlap b κ y / overlapNorm b κ y)
      (realFactorDerivative b κ x) x := by
  have hh := (realOverlap_hasFDerivAt b κ x).mul (overlapInverse_hasFDerivAt b κ x hn)
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [realFactorDerivative]
  ring

theorem imagFactor_hasFDerivAt (b : Field) (κ : ℝ) (x : State)
    (hn : 0 < overlapSq b κ x) :
    HasFDerivAt (fun y => -imagOverlap b κ y / overlapNorm b κ y)
      (imagFactorDerivative b κ x) x := by
  have hh := (imagOverlap_hasFDerivAt b κ x).neg.mul (overlapInverse_hasFDerivAt b κ x hn)
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [imagFactorDerivative]
  ring

def alignedDerivative (b : Field) (κ : ℝ) (x : State) : State →L[ℝ] State :=
  ((realFactorDerivative b κ x).smulRight (selected b κ x) +
    (realOverlap b κ x / overlapNorm b κ x) • selectedDerivative b κ x).prod
  ((imagFactorDerivative b κ x).smulRight (selected b κ x) +
    (-imagOverlap b κ x / overlapNorm b κ x) • selectedDerivative b κ x)

theorem aligned_hasFDerivAt (b : Field) (κ : ℝ) (x : State)
    (hn : 0 < overlapSq b κ x) :
    HasFDerivAt (aligned b κ) (alignedDerivative b κ x) x := by
  simpa only [alignedDerivative, add_comm] using ((realFactor_hasFDerivAt b κ x hn).smul (selected_hasFDerivAt b κ x)).prodMk
    ((imagFactor_hasFDerivAt b κ x hn).smul (selected_hasFDerivAt b κ x))


def stateInverseDerivative (x : State) : State →L[ℝ] ℝ :=
  -((Real.sqrt (stateNormSq x))⁻¹)^3 • stateDot x

theorem stateInverse_hasFDerivAt (x : State) (hn : 0 < stateNormSq x) :
    HasFDerivAt (fun y => (Real.sqrt (stateNormSq y))⁻¹) (stateInverseDerivative x) x := by
  have hs := (stateNormSq_hasFDerivAt x).sqrt hn.ne'
  have hp := (Real.sqrt_pos.mpr hn).ne'
  have hh := (hasDerivAt_inv hp).comp_hasFDerivAt x hs
  convert hh using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [stateInverseDerivative]
  field_simp

def normalizationDerivative (x : State) : State →L[ℝ] State :=
  (Real.sqrt (stateNormSq x))⁻¹ • ContinuousLinearMap.id ℝ State +
  (stateInverseDerivative x).smulRight x

theorem normalizeState_hasFDerivAt (x : State) (hn : 0 < stateNormSq x) :
    HasFDerivAt normalizeState (normalizationDerivative x) x :=
  (stateInverse_hasFDerivAt x hn).smul (hasFDerivAt_id x)

def mixedDerivative (b : Field) (κ m : ℝ) (x : State) : State →L[ℝ] State :=
  (1-m) • ContinuousLinearMap.id ℝ State + m • alignedDerivative b κ x

theorem mixed_hasFDerivAt (b : Field) (κ m : ℝ) (x : State) (hn : 0 < overlapSq b κ x) :
    HasFDerivAt (mixed b κ m) (mixedDerivative b κ m x) x :=
  ((hasFDerivAt_id x).const_smul (1-m)).add ((aligned_hasFDerivAt b κ x hn).const_smul m)

def fullDerivative (b : Field) (κ m : ℝ) (x : State) : State →L[ℝ] State :=
  (normalizationDerivative (mixed b κ m x)).comp (mixedDerivative b κ m x)

theorem fullMap_hasFDerivAt (b : Field) (κ m : ℝ) (x : State)
    (ho : 0 < overlapSq b κ x) (hn : 0 < stateNormSq (mixed b κ m x)) :
    HasFDerivAt (fullMap b κ m) (fullDerivative b κ m x) x :=
  (normalizeState_hasFDerivAt (mixed b κ m x) hn).comp x (mixed_hasFDerivAt b κ m x ho)


theorem realOverlapDerivative_apply (b : Field) (κ : ℝ) (x h : State) :
    realOverlapDerivative b κ x h = dot x.1 (selectedDerivative b κ x h) +
      dot (selected b κ x) h.1 := by simp [realOverlapDerivative, dotMap_apply, realDot_apply]

theorem imagOverlapDerivative_apply (b : Field) (κ : ℝ) (x h : State) :
    imagOverlapDerivative b κ x h = dot x.2 (selectedDerivative b κ x h) +
      dot (selected b κ x) h.2 := by simp [imagOverlapDerivative, dotMap_apply, imagDot_apply]

theorem overlapInverseDerivative_apply (b : Field) (κ : ℝ) (x h : State) :
    overlapInverseDerivative b κ x h = -((overlapNorm b κ x)⁻¹)^3 *
      (realOverlap b κ x * realOverlapDerivative b κ x h +
        imagOverlap b κ x * imagOverlapDerivative b κ x h) := by
  simp [overlapInverseDerivative, overlapNumeratorDerivative]
  ring

theorem alignedDerivative_real_apply (b : Field) (κ : ℝ) (x h : State) (i : Fin 8) :
    (alignedDerivative b κ x h).1 i =
      (realOverlapDerivative b κ x h * (overlapNorm b κ x)⁻¹ +
        realOverlap b κ x * overlapInverseDerivative b κ x h) * selected b κ x i +
      realOverlap b κ x * (overlapNorm b κ x)⁻¹ * selectedDerivative b κ x h i := by
  simp [alignedDerivative, realFactorDerivative, div_eq_mul_inv, mul_comm, mul_assoc]

theorem alignedDerivative_imag_apply (b : Field) (κ : ℝ) (x h : State) (i : Fin 8) :
    (alignedDerivative b κ x h).2 i =
      (-imagOverlapDerivative b κ x h * (overlapNorm b κ x)⁻¹ -
        imagOverlap b κ x * overlapInverseDerivative b κ x h) * selected b κ x i -
      imagOverlap b κ x * (overlapNorm b κ x)⁻¹ * selectedDerivative b κ x h i := by
  simp [alignedDerivative, imagFactorDerivative, div_eq_mul_inv]
  ring

theorem normalizationDerivative_apply (x h : State) :
    normalizationDerivative x h = (Real.sqrt (stateNormSq x))⁻¹ • h +
      (-((Real.sqrt (stateNormSq x))⁻¹)^3 * (dot x.1 h.1+dot x.2 h.2)) • x := by
  simp [normalizationDerivative, stateInverseDerivative, stateDot, realDot_apply, imagDot_apply, mul_add, add_smul]


theorem overlapNorm_continuous (b : Field) (κ : ℝ) : Continuous (overlapNorm b κ) :=
  (((realOverlap_smooth b κ).continuous.pow 2).add ((imagOverlap_smooth b κ).continuous.pow 2)).sqrt

theorem nativePairMap_eventual_return (b : Field) (κ m τ : ℝ) (x : State)
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ x) :
    GroundNativeJacobian.nativePairMap τ b κ m =ᶠ[nhds x] fullMap b κ m := by
  have hm : {y | τ < overlapNorm b κ y} ∈ nhds x :=
    (isOpen_lt continuous_const (overlapNorm_continuous b κ)).mem_nhds ho
  filter_upwards [hm] with y hy
  have hh := fullMap_native_return hτ b κ m y hy
  change unpack (nativeUpdate τ b κ m (pack y)) = fullMap b κ m y
  rw [← hh]
  exact packCLE.symm_apply_apply _

theorem nativePairMap_hasFDerivAt (b : Field) (κ m τ : ℝ) (x : State)
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ x) (hn : 0 < stateNormSq (mixed b κ m x)) :
    HasFDerivAt (GroundNativeJacobian.nativePairMap τ b κ m) (fullDerivative b κ m x) x := by
  have hp : 0 < overlapSq b κ x := by
    have hpos : 0 < overlapNorm b κ x := hτ.trans_lt ho
    exact Real.sqrt_pos.mp hpos
  exact (fullMap_hasFDerivAt b κ m x hp hn).congr_of_eventuallyEq
    (nativePairMap_eventual_return b κ m τ x hτ ho)


end
end SbtCosmo.Derivation.GroundNativeGeneralDerivative
