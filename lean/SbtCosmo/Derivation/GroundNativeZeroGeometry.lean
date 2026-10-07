import SbtCosmo.Derivation.GroundNativeReflection
import SbtCosmo.Derivation.GroundZeroCouplingOrbit

/-! Exact finite-dimensional geometry of the original complex half-mixing
update at zero coupling, including its unchanged conjugate phase factor. -/
namespace SbtCosmo.Derivation.GroundNativeZeroGeometry
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration
open scoped BigOperators

def realPart (g : Field) (x : State) : ℝ := dot g x.1
def imagPart (g : Field) (x : State) : ℝ := dot g x.2
def radius (g : Field) (x : State) : ℝ := Real.sqrt ((realPart g x)^2 + (imagPart g x)^2)
def mix (g : Field) (x : State) : State :=
  ((1/2 : ℝ) • x.1 + (realPart g x / (2*radius g x)) • g,
   (1/2 : ℝ) • x.2 - (imagPart g x / (2*radius g x)) • g)
def step (g : Field) (x : State) : State := normalizeState (mix g x)

theorem affine_norm (g u : Field) (t s : ℝ) :
    normSq (fun i => t*u i+s*g i) = t^2*normSq u+s^2*normSq g+2*t*s*dot g u := by
  simp only [normSq, dot]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem affine_dot (g u : Field) (t s : ℝ) :
    dot g (fun i => t*u i+s*g i) = t*dot g u+s*normSq g := by
  simp only [dot, normSq]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem decomposition {g : Field} (hg : normSq g = 1) (x : State) :
    normSq (x.1 - (realPart g x) • g) + normSq (x.2 - (imagPart g x) • g) =
      stateNormSq x - (realPart g x)^2 - (imagPart g x)^2 := by
  have hr := affine_norm g x.1 1 (-realPart g x)
  have hi := affine_norm g x.2 1 (-imagPart g x)
  rw [hg] at hr hi
  change normSq (fun i => x.1 i - realPart g x * g i) +
    normSq (fun i => x.2 i - imagPart g x * g i) = _
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hr hi
  rw [hr, hi]
  simp only [stateNormSq, realPart, imagPart]
  ring

theorem overlap_bound {g : Field} (hg : normSq g = 1) (x : State) :
    (realPart g x)^2 + (imagPart g x)^2 ≤ stateNormSq x := by
  have h := add_nonneg (normSq_nonneg (x.1 - (realPart g x) • g))
    (normSq_nonneg (x.2 - (imagPart g x) • g))
  rw [decomposition hg x] at h
  linarith

theorem radius_sq (g : Field) (x : State) :
    (radius g x)^2 = (realPart g x)^2 + (imagPart g x)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem radius_bounds {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) : 0 < radius g x ∧ realPart g x ≤ radius g x ∧ radius g x ≤ 1 := by
  have hs := radius_sq g x
  have hb := overlap_bound hg x
  rw [hx] at hb
  have hn : 0 ≤ radius g x := Real.sqrt_nonneg _
  constructor
  · nlinarith [sq_nonneg (imagPart g x)]
  constructor <;> nlinarith [sq_nonneg (imagPart g x)]

theorem mixed_real {g : Field} (hg : normSq g = 1) (x : State) :
    realPart g (mix g x) = realPart g x * (radius g x + 1) / (2*radius g x) := by
  have h := affine_dot g x.1 (1/2) (realPart g x / (2*radius g x))
  rw [hg] at h
  change dot g (fun i => (1/2)*x.1 i+(realPart g x/(2*radius g x))*g i) = _
  rw [h]
  change (1/2)*realPart g x+(realPart g x/(2*radius g x))*1 = _
  by_cases hr : radius g x = 0
  · have hs := radius_sq g x
    rw [hr] at hs
    have ha : realPart g x = 0 := by nlinarith [sq_nonneg (imagPart g x)]
    simp [ha]
  · field_simp

theorem mixed_norm {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (hr : radius g x ≠ 0) :
    stateNormSq (mix g x) = (1 - radius g x + 2*(realPart g x)^2 / radius g x)/2 := by
  have h1 := affine_norm g x.1 (1/2) (realPart g x / (2*radius g x))
  have h2 := affine_norm g x.2 (1/2) (-imagPart g x / (2*radius g x))
  rw [hg] at h1 h2
  change normSq (fun i => (1/2)*x.1 i+(realPart g x/(2*radius g x))*g i) +
    normSq (fun i => (1/2)*x.2 i-(imagPart g x/(2*radius g x))*g i) = _
  simp only [neg_div, neg_mul, ← sub_eq_add_neg] at h2
  rw [h1,h2]
  have hxx : normSq x.1 + normSq x.2 = 1 := hx
  have hrs := radius_sq g x
  dsimp only [realPart, imagPart] at *
  have hxxr := congrArg (fun t : ℝ => t*(radius g x)^2) hxx
  have hrr := congrArg (fun t : ℝ => 2*radius g x*t) hrs
  field_simp
  nlinarith [hrs, hxxr, hrr]

theorem step_real (g : Field) (x : State) :
    realPart g (step g x) = realPart g (mix g x) / Real.sqrt (stateNormSq (mix g x)) := by
  change dot g ((Real.sqrt (stateNormSq (mix g x)))⁻¹ • (mix g x).1) = _
  rw [show (Real.sqrt (stateNormSq (mix g x)))⁻¹ • (mix g x).1 =
    (fun i => (Real.sqrt (stateNormSq (mix g x)))⁻¹ * (mix g x).1 i) from rfl,
    dot_smul_right]
  dsimp only [realPart]
  ring

theorem step_unit {g : Field} {x : State} (hm : 0 < stateNormSq (mix g x)) :
    stateNormSq (step g x) = 1 := GroundNativeEscape.normalizeState_unit hm

theorem distance_identity {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1) :
    stateNormSq (x - (g, 0)) = 2*(1-realPart g x) := by
  have h := affine_norm g x.1 1 (-1)
  rw [hg] at h
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  change normSq (x.1-g) + normSq (x.2-0) = _
  change normSq (x.1-g) = 1^2*normSq x.1+(-1)^2*1+2*1*(-1)*dot g x.1 at h
  rw [sub_zero, h]
  dsimp only [realPart]
  change normSq x.1 + normSq x.2 = 1 at hx
  linarith

theorem state_norm_bound (x : State) : ‖x‖ ≤ Real.sqrt (stateNormSq x) := by
  rw [Prod.norm_def]
  apply max_le
  · exact (GroundZeroCouplingOrbit.norm_le_sqrt_normSq x.1).trans
      (Real.sqrt_le_sqrt (by dsimp [stateNormSq]; linarith [normSq_nonneg x.2]))
  · exact (GroundZeroCouplingOrbit.norm_le_sqrt_normSq x.2).trans
      (Real.sqrt_le_sqrt (by dsimp [stateNormSq]; linarith [normSq_nonneg x.1]))

theorem selected_zero (b : Field) (x : State) : selected b 0 x = positiveGround b := by
  have hs : pairSource b 0 x = b := by funext i; simp [pairSource]
  rw [selected, hs]

theorem mixed_zero (b : Field) (x : State) : mixed b 0 (1/2) x = mix (positiveGround b) x := by
  have he : overlapNorm b 0 x = radius (positiveGround b) x := by
    simp only [overlapNorm, overlapSq, realOverlap, imagOverlap, selected_zero, radius, realPart, imagPart]
  rw [mixed]
  simp only [aligned, realOverlap, imagOverlap, selected_zero, he]
  apply Prod.ext <;> funext i <;>
    simp [mix, realPart, imagPart]
  all_goals ring

theorem native_return (b : Field) (x : State) {τ : ℝ} (hτ : 0 ≤ τ)
    (ha : τ < radius (positiveGround b) x) :
    pack (step (positiveGround b) x) = nativeUpdate τ b 0 (1/2) (pack x) := by
  have ho : τ < overlapNorm b 0 x := by
    simpa only [overlapNorm, overlapSq, realOverlap, imagOverlap, selected_zero, radius, realPart, imagPart] using ha
  rw [← fullMap_native_return hτ b 0 (1/2) x ho, fullMap, mixed_zero]
  rfl

theorem native_guard_return (b : Field) (x : State) {τ : ℝ} (hτ : 0 ≤ τ)
    (ha : τ < radius (positiveGround b) x)
    (hm : τ < Real.sqrt (stateNormSq (mix (positiveGround b) x))) :
    ActivePhase τ b 0 (pack x) ∧ NativeLegal τ b 0 (1/2) (pack x) := by
  have ho : τ < overlapNorm b 0 x := by
    simpa only [overlapNorm, overlapSq, realOverlap, imagOverlap, selected_zero, radius, realPart, imagPart] using ha
  constructor
  · simpa only [ActivePhase, nativeCandidate_pack, overlap_norm_pair] using ho
  · simpa only [NativeLegal, ← pack_mixed_native hτ b 0 (1/2) x ho, norm_pack, mixed_zero] using hm

end
end SbtCosmo.Derivation.GroundNativeZeroGeometry
