import SbtCosmo.Derivation.GroundComplex
import SbtCosmo.Derivation.GroundLocalDynamics
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Exact real/imaginary representation of the unchanged Step26 complex source
and its conjugated phase rule. The sign error is retained. The source's real
symmetric diagonalization gives a real ground eigenvector up to a real sign;
we do not assume arbitrary complex phase choices have the same aligned output. -/
namespace SbtCosmo.Derivation.GroundNativePhase
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundSourceJacobian
open scoped BigOperators ContDiff Topology

abbrev State := Field × Field
def pack (x : State) : ComplexField := fun i => ⟨x.1 i, x.2 i⟩
def unpack (z : ComplexField) : State := (fun i => (z i).re, fun i => (z i).im)

def packLE : State ≃ₗ[ℝ] ComplexField where
  toFun := pack
  invFun := unpack
  left_inv x := by rfl
  right_inv z := by funext i; apply Complex.ext <;> rfl
  map_add' x y := by rfl
  map_smul' c x := by funext i; apply Complex.ext <;> simp [pack]

def packCLE : State ≃L[ℝ] ComplexField := packLE.toContinuousLinearEquiv

theorem packCLE_apply (x : State) : packCLE x = pack x := rfl
theorem packCLE_symm_apply (z : ComplexField) : packCLE.symm z = unpack z := rfl

def stateNormSq (x : State) : ℝ := normSq x.1 + normSq x.2
def pairSource (b : Field) (κ : ℝ) (x : State) : Field := fun i =>
  b i + κ * ((GroundState.gradient x.1 i)^2 + (GroundState.gradient x.2 i)^2 + b i*((x.1 i)^2+(x.2 i)^2))
def selected (b : Field) (κ : ℝ) (x : State) : Field := positiveGround (pairSource b κ x)

theorem norm_pack (x : State) : complexNormSq (pack x) = stateNormSq x := by
  simp [complexNormSq_split, stateNormSq, pack]

theorem source_pack (b : Field) (κ : ℝ) (x : State) :
    complexSourcePotential b κ (pack x) = pairSource b κ x := by
  funext i
  simp [complexSourcePotential, complexGradient, pack, pairSource, GroundState.gradient,
    BackgroundSelection.potential, Complex.normSq_apply, pow_two]
  left
  ring

theorem pairSource_real (b : Field) (κ : ℝ) (u : Field) :
    pairSource b κ (u, 0) = sourcePotential b κ u := by
  funext i
  simp [pairSource, sourcePotential, BackgroundSelection.potential, GroundState.gradient]

theorem selected_real (b : Field) (κ : ℝ) (u : Field) :
    selected b κ (u, 0) = groundMap b κ u := by rw [selected, pairSource_real]; rfl

theorem pairSource_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (pairSource b κ) := by
  unfold pairSource GroundState.gradient
  fun_prop

theorem selected_smooth (b : Field) (κ : ℝ) : ContDiff ℝ ∞ (selected b κ) :=
  GroundSmooth.positiveGround_smooth.comp (pairSource_smooth b κ)

def overlap (candidate reference : ComplexField) : ℂ := ∑ i, star (candidate i) * reference i
def nativePhase (τ : ℝ) (candidate reference : ComplexField) : ComplexField :=
  if ‖overlap candidate reference‖ ≤ τ then candidate else
    fun i => Complex.exp ((-Complex.arg (overlap candidate reference) : ℝ) * Complex.I) * candidate i

theorem native_factor (z : ℂ) (hz : z ≠ 0) :
    Complex.exp ((-Complex.arg z : ℝ) * Complex.I) = star z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have he : Complex.exp ((Complex.arg z : ℝ) * Complex.I) = z / (‖z‖ : ℂ) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using Complex.norm_mul_exp_arg_mul_I z
  have hc := congrArg (starRingEnd ℂ) he
  simpa [← Complex.exp_conj] using hc

theorem nativePhase_ratio {τ : ℝ} {candidate reference : ComplexField}
    (hτ : 0 ≤ τ) (ho : τ < ‖overlap candidate reference‖) :
    nativePhase τ candidate reference =
      fun i => (star (overlap candidate reference) / (‖overlap candidate reference‖ : ℂ)) * candidate i := by
  have hn : overlap candidate reference ≠ 0 := norm_pos_iff.mp (hτ.trans_lt ho)
  simp only [nativePhase, not_le.mpr ho, ↓reduceIte, native_factor _ hn]

theorem overlap_neg_left (candidate reference : ComplexField) :
    overlap (-candidate) reference = -overlap candidate reference := by
  simp [overlap, Finset.sum_neg_distrib]

theorem nativePhase_real_sign_invariant {τ : ℝ} {candidate reference : ComplexField}
    (hτ : 0 ≤ τ) (ho : τ < ‖overlap candidate reference‖) :
    nativePhase τ (-candidate) reference = nativePhase τ candidate reference := by
  have ho' : τ < ‖overlap (-candidate) reference‖ := by simpa [overlap_neg_left] using ho
  rw [nativePhase_ratio hτ ho', nativePhase_ratio hτ ho, overlap_neg_left]
  funext i
  simp
  ring

def realOverlap (b : Field) (κ : ℝ) (x : State) : ℝ := dot (selected b κ x) x.1
def imagOverlap (b : Field) (κ : ℝ) (x : State) : ℝ := dot (selected b κ x) x.2
def overlapSq (b : Field) (κ : ℝ) (x : State) : ℝ :=
  (realOverlap b κ x)^2 + (imagOverlap b κ x)^2
def overlapNorm (b : Field) (κ : ℝ) (x : State) : ℝ := Real.sqrt (overlapSq b κ x)
def aligned (b : Field) (κ : ℝ) (x : State) : State :=
  (fun i => realOverlap b κ x / overlapNorm b κ x * selected b κ x i,
   fun i => -imagOverlap b κ x / overlapNorm b κ x * selected b κ x i)

theorem overlap_pair (b : Field) (κ : ℝ) (x : State) :
    overlap (realEmbed (selected b κ x)) (pack x) =
      ⟨realOverlap b κ x, imagOverlap b κ x⟩ := by
  apply Complex.ext <;> simp [overlap, realEmbed, pack, realOverlap, imagOverlap, dot]

theorem overlap_norm_pair (b : Field) (κ : ℝ) (x : State) :
    ‖overlap (realEmbed (selected b κ x)) (pack x)‖ = overlapNorm b κ x := by
  rw [overlap_pair]
  dsimp [overlapNorm, overlapSq]
  rw [← Real.sqrt_sq (norm_nonneg (⟨realOverlap b κ x, imagOverlap b κ x⟩ : ℂ)),
    ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

theorem aligned_native_return (b : Field) (κ : ℝ) (x : State) {τ : ℝ}
    (hτ : 0 ≤ τ) (ho : τ < overlapNorm b κ x) :
    pack (aligned b κ x) = nativePhase τ (realEmbed (selected b κ x)) (pack x) := by
  have ho' : τ < ‖overlap (realEmbed (selected b κ x)) (pack x)‖ := by
    rw [overlap_norm_pair]; exact ho
  rw [nativePhase_ratio hτ ho', overlap_norm_pair, overlap_pair]
  funext i
  apply Complex.ext <;> simp [pack, aligned, realEmbed, Complex.div_re, Complex.div_im]
  all_goals field_simp
  all_goals simp

theorem overlap_at_fixed {b u : Field} {κ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    realOverlap b κ (u, 0) = 1 ∧ imagOverlap b κ (u, 0) = 0 ∧ overlapNorm b κ (u, 0) = 1 := by
  have hr : realOverlap b κ (u, 0) = 1 := by
    simp [realOverlap, selected_real, hf, dot_self, hu]
  have hi : imagOverlap b κ (u, 0) = 0 := by simp [imagOverlap, dot]
  exact ⟨hr, hi, by simp [overlapNorm, overlapSq, hr, hi]⟩

end
end SbtCosmo.Derivation.GroundNativePhase
