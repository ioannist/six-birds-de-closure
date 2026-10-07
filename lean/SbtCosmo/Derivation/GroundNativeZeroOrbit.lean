import SbtCosmo.Derivation.GroundNativeZeroScalar

/-! Global complex zero-coupling convergence of the unchanged native half update
from positive real overlap, with quantitative decay and all source guards. -/
namespace SbtCosmo.Derivation.GroundNativeZeroOrbit
noncomputable section
set_option maxHeartbeats 4000000
open GroundState GroundBorder GroundNativePhase GroundNativeIteration GroundNativeZeroGeometry
open Filter
open scoped Topology

def rate (g : Field) (x : State) : ℝ := 1-(realPart g x)^2/4

theorem step_estimate {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) :
    stateNormSq (step g x) = 1 ∧ realPart g x ≤ realPart g (step g x) ∧
      1-(realPart g (step g x))^2 ≤ rate g x*(1-(realPart g x)^2) ∧
      realPart g x ≤ Real.sqrt (stateNormSq (mix g x)) := by
  obtain ⟨hr, har, hr1⟩ := radius_bounds hg hx ha
  have hd := mixed_norm hg hx hr.ne'
  obtain ⟨hdp, hda, _⟩ := GroundNativeZeroScalar.mixed_bounds ha har hr1 hd
  have hc : realPart g (step g x) = realPart g x*(radius g x+1)/
      (2*radius g x*Real.sqrt (stateNormSq (mix g x))) := by
    rw [step_real, mixed_real hg]
    rw [div_div]
  exact ⟨step_unit hdp, GroundNativeZeroScalar.coefficient_monotone ha har hr1 hd hc,
    GroundNativeZeroScalar.defect_contraction ha har hr1 hd hc, hda⟩

theorem rate_bounds {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) : 0 ≤ rate g x ∧ rate g x < 1 := by
  have hb := overlap_bound hg x
  rw [hx] at hb
  dsimp only [rate]
  constructor <;> nlinarith [sq_nonneg (imagPart g x)]

theorem orbit_unit_overlap {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) (n : ℕ) :
    stateNormSq ((step g)^[n] x) = 1 ∧ realPart g x ≤ realPart g ((step g)^[n] x) := by
  induction n with
  | zero => exact ⟨hx, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hs := step_estimate hg ih.1 (ha.trans_le ih.2)
    exact ⟨hs.1, ih.2.trans hs.2.1⟩

theorem orbit_defect_bound {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) (n : ℕ) :
    0 ≤ 1-(realPart g ((step g)^[n] x))^2 ∧
      1-(realPart g ((step g)^[n] x))^2 ≤ (rate g x)^n*(1-(realPart g x)^2) := by
  have hn (j : ℕ) : 0 ≤ 1-(realPart g ((step g)^[j] x))^2 := by
    have h := overlap_bound hg ((step g)^[j] x)
    rw [(orbit_unit_overlap hg hx ha j).1] at h
    nlinarith [sq_nonneg (imagPart g ((step g)^[j] x))]
  induction n with
  | zero => exact ⟨hn 0, by simp⟩
  | succ n ih =>
    refine ⟨hn (n+1), ?_⟩
    have hi := orbit_unit_overlap hg hx ha n
    have hs := (step_estimate hg hi.1 (ha.trans_le hi.2)).2.2.1
    have hrate : rate g ((step g)^[n] x) ≤ rate g x := by
      dsimp only [rate]
      nlinarith [hi.2]
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ rate g ((step g)^[n] x)*(1-(realPart g ((step g)^[n] x))^2) := hs
      _ ≤ rate g x*(1-(realPart g ((step g)^[n] x))^2) :=
        mul_le_mul_of_nonneg_right hrate ih.1
      _ ≤ rate g x*((rate g x)^n*(1-(realPart g x)^2)) :=
        mul_le_mul_of_nonneg_left ih.2 (rate_bounds hg hx ha).1
      _ = _ := by rw [pow_succ]; ring

theorem orbit_distance_bound {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) (n : ℕ) :
    ‖(step g)^[n] x - (g, 0)‖ ≤ Real.sqrt (2*((rate g x)^n*(1-(realPart g x)^2))) := by
  have hi := orbit_unit_overlap hg hx ha n
  have hb := orbit_defect_bound hg hx ha n
  have hrad := radius_bounds hg hi.1 (ha.trans_le hi.2)
  have har : realPart g ((step g)^[n] x) ≤ 1 := hrad.2.1.trans hrad.2.2
  apply (state_norm_bound _).trans
  apply Real.sqrt_le_sqrt
  rw [distance_identity hg hi.1]
  have ha' := ha.trans_le hi.2
  nlinarith [hb.2]

theorem orbit_converges {g : Field} {x : State} (hg : normSq g = 1) (hx : stateNormSq x = 1)
    (ha : 0 < realPart g x) :
    Tendsto (fun n : ℕ => (step g)^[n] x) atTop (nhds (g, (0 : Field))) := by
  have hq := rate_bounds hg hx ha
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1 hq.2).mul_const (1-(realPart g x)^2)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hp.const_mul 2)
  have ht : Tendsto (fun n : ℕ => ‖(step g)^[n] x-(g,0)‖) atTop (nhds 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (orbit_distance_bound hg hx ha)
      (by simpa only [Function.comp_def, mul_zero, zero_mul, Real.sqrt_zero] using hs)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

theorem orbit_native_guards (b : Field) {x : State} {τ : ℝ} (hx : stateNormSq x = 1)
    (hτ : 0 ≤ τ) (ha : τ < realPart (positiveGround b) x) (n : ℕ) :
    ActivePhase τ b 0 (pack ((step (positiveGround b))^[n] x)) ∧
      NativeLegal τ b 0 (1/2) (pack ((step (positiveGround b))^[n] x)) := by
  have hg := (positiveGround_spec b).2.1
  have hp := hτ.trans_lt ha
  have hi := orbit_unit_overlap hg hx hp n
  have hr := radius_bounds hg hi.1 (hp.trans_le hi.2)
  have hs := step_estimate hg hi.1 (hp.trans_le hi.2)
  exact native_guard_return b _ hτ (ha.trans_le (hi.2.trans hr.2.1)) (ha.trans_le (hi.2.trans hs.2.2.2))

theorem orbit_native_return (b : Field) {x : State} {τ : ℝ} (hx : stateNormSq x = 1)
    (hτ : 0 ≤ τ) (ha : τ < realPart (positiveGround b) x) (n : ℕ) :
    pack ((step (positiveGround b))^[n] x) = (nativeUpdate τ b 0 (1/2))^[n] (pack x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hi := orbit_unit_overlap (positiveGround_spec b).2.1 hx (hτ.trans_lt ha) n
    have hr := radius_bounds (positiveGround_spec b).2.1 hi.1 ((hτ.trans_lt ha).trans_le hi.2)
    rw [native_return b _ hτ (ha.trans_le (hi.2.trans hr.2.1)), ih]

/-- Every unit complex initial field with real ground overlap above the source
threshold converges to the actual positive ground, with all native guards. -/
theorem actual_positive_zero_convergence (b : Field) {z : ComplexField} {τ : ℝ}
    (hz : complexNormSq z = 1) (hτ : 0 ≤ τ) (ha : τ < realPart (positiveGround b) (unpack z)) :
    Tendsto (fun n : ℕ => (nativeUpdate τ b 0 (1/2))^[n] z) atTop (nhds (realEmbed (positiveGround b))) ∧
      ∀ n : ℕ, ActivePhase τ b 0 ((nativeUpdate τ b 0 (1/2))^[n] z) ∧
        NativeLegal τ b 0 (1/2) ((nativeUpdate τ b 0 (1/2))^[n] z) := by
  have he : pack (unpack z) = z := packCLE.apply_symm_apply z
  have hx : stateNormSq (unpack z) = 1 := by rw [← norm_pack, he, hz]
  have hr (n : ℕ) : pack ((step (positiveGround b))^[n] (unpack z)) = (nativeUpdate τ b 0 (1/2))^[n] z := by
    simpa only [he] using orbit_native_return b hx hτ ha n
  refine ⟨?_, fun n => ?_⟩
  · have ht := packCLE.continuous.continuousAt.tendsto.comp
      (orbit_converges (positiveGround_spec b).2.1 hx (hτ.trans_lt ha))
    simpa only [Function.comp_def, packCLE_apply, hr] using ht
  · simpa only [hr] using orbit_native_guards b hx hτ ha n

theorem actual_negative_zero_convergence (b : Field) {z : ComplexField} {τ : ℝ}
    (hz : complexNormSq z = 1) (hτ : 0 ≤ τ) (ha : τ < -realPart (positiveGround b) (unpack z)) :
    Tendsto (fun n : ℕ => (nativeUpdate τ b 0 (1/2))^[n] z) atTop (nhds (realEmbed (-positiveGround b))) ∧
      ∀ n : ℕ, ActivePhase τ b 0 ((nativeUpdate τ b 0 (1/2))^[n] z) ∧
        NativeLegal τ b 0 (1/2) ((nativeUpdate τ b 0 (1/2))^[n] z) := by
  have hp : τ < realPart (positiveGround b) (unpack (-z)) := by
    simpa [GroundNativeZeroGeometry.realPart, GroundBorder.dot, GroundNativePhase.unpack, Finset.sum_neg_distrib] using ha
  have hn : complexNormSq (-z) = 1 := by rw [GroundNativeReflection.complexNormSq_neg, hz]
  obtain ⟨ht, hg⟩ := actual_positive_zero_convergence b hn hτ hp
  have he (n : ℕ) : (nativeUpdate τ b 0 (1/2))^[n] z = -((nativeUpdate τ b 0 (1/2))^[n] (-z)) := by
    simpa only [neg_neg] using GroundNativeReflection.native_iterate_neg b 0 (1/2) (-z) hτ n (fun j _ => (hg j).1)
  refine ⟨?_, fun n => ?_⟩
  · simpa only [← he, ← GroundNativeReflection.realEmbed_neg] using ht.neg
  · rw [he]
    exact ⟨(GroundNativeReflection.activePhase_neg_iff τ b 0 _).mpr (hg n).1,
      (GroundNativeReflection.nativeLegal_neg_iff b 0 (1/2) _ hτ (hg n).1).mpr (hg n).2⟩

end
end SbtCosmo.Derivation.GroundNativeZeroOrbit
