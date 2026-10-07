import SbtCosmo.Derivation.GroundRootCertificate

/-! Global positive-real convergence of the actual zero-coupling normalized
iteration for EVERY real background, including nonconstant ones. No derivative,
spectral bound, approximate root or iteration budget is supplied. -/
namespace SbtCosmo.Derivation.GroundZeroCouplingOrbit
noncomputable section
set_option maxHeartbeats 2000000
open Filter GroundState GroundBorder GroundSourceJacobian GroundNormalizedJacobian
open scoped BigOperators Topology

def step (g : Field) (m : ℝ) : Field → Field := normalizedRelaxed (fun _ => g) m
def gap (g u : Field) : ℝ := 1 - dot g u

theorem distance_identity {g u : Field} (hg : normSq g = 1) (hu : normSq u = 1) :
    normSq (u-g) = 2 * gap g u := by
  have he : normSq (u-g) = normSq u + normSq g - 2 * dot g u := by
    simp only [normSq, dot, Pi.sub_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hu, hg]
  unfold gap
  ring

theorem gap_nonnegative {g u : Field} (hg : normSq g = 1) (hu : normSq u = 1) :
    0 ≤ gap g u := by
  have h := normSq_nonneg (u-g)
  rw [distance_identity hg hu] at h
  linarith

theorem dot_nonnegative {g u : Field} (hg : ∀ i, 0 ≤ g i) (hu : ∀ i, 0 ≤ u i) :
    0 ≤ dot g u := Finset.sum_nonneg (fun i _ => mul_nonneg (hg i) (hu i))

theorem convex_norm_identity {g u : Field} (hg : normSq g = 1) (hu : normSq u = 1)
    (m : ℝ) : normSq (relaxed (fun _ => g) m u) = 1-m*(1-m)*normSq (u-g) := by
  have he : normSq (relaxed (fun _ => g) m u) =
      (1-m)*normSq u + m*normSq g - m*(1-m)*normSq (u-g) := by
    simp only [normSq, relaxed, Pi.sub_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hu, hg]
  ring

theorem convex_norm_le_one {g u : Field} (hg : normSq g = 1) (hu : normSq u = 1)
    {m : ℝ} (hm : m ∈ Set.Icc 0 1) : normSq (relaxed (fun _ => g) m u) ≤ 1 := by
  rw [convex_norm_identity hg hu]
  have hp := mul_nonneg (mul_nonneg hm.1 (sub_nonneg.mpr hm.2)) (normSq_nonneg (u-g))
  linarith

theorem relaxed_positive {g u : Field} (hg : ∀ i, 0 < g i) (hu : ∀ i, 0 ≤ u i)
    {m : ℝ} (hm : m ∈ Set.Ioc 0 1) (i : Fin 8) :
    0 < relaxed (fun _ => g) m u i :=
  add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hm.2) (hu i)) (mul_pos hm.1 (hg i))

theorem relaxed_norm_positive {g u : Field} (hg : ∀ i, 0 < g i) (hu : ∀ i, 0 ≤ u i)
    {m : ℝ} (hm : m ∈ Set.Ioc 0 1) : 0 < normSq (relaxed (fun _ => g) m u) := by
  have hpos := relaxed_positive hg hu hm (0 : Fin 8)
  have hn := normSq_nonneg (relaxed (fun _ => g) m u)
  apply lt_of_le_of_ne hn
  intro hz
  have he := normSq_zero_iff _ |>.mp hz.symm
  have hi := congrFun he (0 : Fin 8)
  change relaxed (fun _ => g) m u 0 = 0 at hi
  linarith

theorem normalize_unit {w : Field} (hw : 0 < normSq w) :
    normSq (GroundNormalizedJacobian.normalize w) = 1 := by
  have hs := Real.sq_sqrt hw.le
  change (∑ i, (w i / Real.sqrt (normSq w))^2) = 1
  simp only [div_pow, hs, ← Finset.sum_div]
  exact div_self hw.ne'

theorem step_unit_positive {g u : Field} (hg : ∀ i, 0 < g i) (hu : ∀ i, 0 ≤ u i)
    {m : ℝ} (hm : m ∈ Set.Ioc 0 1) :
    normSq (step g m u) = 1 ∧ ∀ i, 0 < step g m u i := by
  have hn := relaxed_norm_positive hg hu hm
  refine ⟨normalize_unit hn, fun i => ?_⟩
  exact div_pos (relaxed_positive hg hu hm i) (Real.sqrt_pos.mpr hn)

/-- Positive convex mixing keeps the actual map defined and positive for all
backgrounds and couplings. This is an invariant, not a convergence theorem. -/
theorem native_step_unit_positive (b : Field) (κ : ℝ) {u : Field} {m : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hm : m ∈ Set.Ioc 0 1) :
    normSq (normalizedRelaxed (groundMap b κ) m u) = 1 ∧
      ∀ i, 0 < normalizedRelaxed (groundMap b κ) m u i :=
  step_unit_positive (positiveGround_spec (sourcePotential b κ u)).1 hu hm

theorem native_orbit_unit_nonnegative (b : Field) (κ : ℝ) {u : Field} {m : ℝ}
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) (hm : m ∈ Set.Ioc 0 1) (n : ℕ) :
    normSq ((normalizedRelaxed (groundMap b κ) m)^[n] u) = 1 ∧
      ∀ i, 0 ≤ (normalizedRelaxed (groundMap b κ) m)^[n] u i := by
  induction n with
  | zero => exact ⟨hu, hup⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := native_step_unit_positive b κ ih.2 hm
    exact ⟨hh.1, fun i => (hh.2 i).le⟩

theorem dot_relaxed {g u : Field} (hg : normSq g = 1) (m : ℝ) :
    dot g (relaxed (fun _ => g) m u) = (1-m)*dot g u + m := by
  have he : dot g (relaxed (fun _ => g) m u) = (1-m)*dot g u + m*dot g g := by
    simp only [dot, relaxed]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, dot_self, hg]
  ring

theorem dot_step {g u : Field} (hg : normSq g = 1) (m : ℝ) :
    dot g (step g m u) = ((1-m)*dot g u+m) / Real.sqrt (normSq (relaxed (fun _ => g) m u)) := by
  rw [← dot_relaxed hg m]
  simp [dot, step, normalizedRelaxed, mul_div_assoc, Finset.sum_div]

theorem gap_step_bound {g u : Field} (hg : normSq g = 1) (hu : normSq u = 1)
    (hgp : ∀ i, 0 < g i) (hup : ∀ i, 0 ≤ u i) {m : ℝ} (hm : m ∈ Set.Ioc 0 1) :
    0 ≤ gap g (step g m u) ∧ gap g (step g m u) ≤ (1-m)*gap g u := by
  have hunit := step_unit_positive hgp hup hm
  have hn := relaxed_norm_positive hgp hup hm
  have hr := Real.sqrt_pos.mpr hn
  have hr1 : Real.sqrt (normSq (relaxed (fun _ => g) m u)) ≤ 1 :=
    Real.sqrt_le_one.mpr (convex_norm_le_one hg hu ⟨hm.1.le, hm.2⟩)
  have hd := dot_nonnegative (fun i => (hgp i).le) hup
  have hnum : 0 ≤ (1-m)*dot g u+m :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hm.2) hd) hm.1.le
  have hmul := mul_le_of_le_one_right hnum hr1
  have hdiv : (1-m)*dot g u+m ≤
      ((1-m)*dot g u+m)/Real.sqrt (normSq (relaxed (fun _ => g) m u)) :=
    (le_div_iff₀ hr).mpr hmul
  refine ⟨gap_nonnegative hg hunit.1, ?_⟩
  unfold gap
  rw [dot_step hg]
  nlinarith

theorem orbit_unit_nonnegative {g u : Field} (hg : ∀ i, 0 < g i)
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) {m : ℝ} (hm : m ∈ Set.Ioc 0 1) (n : ℕ) :
    normSq ((step g m)^[n] u) = 1 ∧ ∀ i, 0 ≤ (step g m)^[n] u i := by
  induction n with
  | zero => exact ⟨hu, hup⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_unit_positive hg ih.2 hm
    exact ⟨hh.1, fun i => (hh.2 i).le⟩

theorem orbit_gap_bound {g u : Field} (hg : normSq g = 1) (hgp : ∀ i, 0 < g i)
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) {m : ℝ} (hm : m ∈ Set.Ioc 0 1) (n : ℕ) :
    0 ≤ gap g ((step g m)^[n] u) ∧ gap g ((step g m)^[n] u) ≤ (1-m)^n * gap g u := by
  induction n with
  | zero => simpa using gap_nonnegative hg hu
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hl := orbit_unit_nonnegative hgp hu hup hm n
    have hb := gap_step_bound hg hl.1 hgp hl.2 hm
    refine ⟨hb.1, hb.2.trans ?_⟩
    calc
      (1-m)*gap g ((step g m)^[n] u) ≤ (1-m)*((1-m)^n*gap g u) :=
        mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hm.2)
      _ = (1-m)^(n+1)*gap g u := by rw [pow_succ]; ring

theorem norm_le_sqrt_normSq (w : Field) : ‖w‖ ≤ Real.sqrt (normSq w) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)

theorem orbit_distance_bound {g u : Field} (hg : normSq g = 1) (hgp : ∀ i, 0 < g i)
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) {m : ℝ} (hm : m ∈ Set.Ioc 0 1) (n : ℕ) :
    ‖(step g m)^[n] u - g‖ ≤ Real.sqrt (2*((1-m)^n*gap g u)) := by
  have hn := orbit_unit_nonnegative hgp hu hup hm n
  have hb := orbit_gap_bound hg hgp hu hup hm n
  apply (norm_le_sqrt_normSq _).trans
  apply Real.sqrt_le_sqrt
  rw [distance_identity hg hn.1]
  linarith

theorem orbit_converges {g u : Field} (hg : normSq g = 1) (hgp : ∀ i, 0 < g i)
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) {m : ℝ} (hm : m ∈ Set.Ioc 0 1) :
    Tendsto (fun n : ℕ => (step g m)^[n] u) atTop (nhds g) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hm.2)
    (show 1-m < 1 by linarith [hm.1])).mul_const (gap g u)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hp.const_mul 2)
  have ht : Tendsto (fun n : ℕ => ‖(step g m)^[n] u-g‖) atTop (nhds 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (orbit_distance_bound hg hgp hu hup hm)
      (by simpa only [Function.comp_def, mul_zero, zero_mul, Real.sqrt_zero] using hs)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

/-- Original zero-coupling source, arbitrary background, all nonnegative unit
initial fields, every positive convex mixing fraction. -/
theorem actual_zero_coupling_global_convergence (b : Field) {u : Field} {m : ℝ}
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) (hm : m ∈ Set.Ioc 0 1) :
    Tendsto (fun n : ℕ => (normalizedRelaxed (groundMap b 0) m)^[n] u)
      atTop (nhds (positiveGround b)) := by
  have hf : groundMap b 0 = fun _ => positiveGround b := by
    funext w
    exact zero_coupling_groundMap b w
  rw [hf]
  exact orbit_converges (positiveGround_spec b).2.1 (positiveGround_spec b).1 hu hup hm

theorem actual_zero_coupling_distance_bound (b : Field) {u : Field} {m : ℝ}
    (hu : normSq u = 1) (hup : ∀ i, 0 ≤ u i) (hm : m ∈ Set.Ioc 0 1) (n : ℕ) :
    ‖(normalizedRelaxed (groundMap b 0) m)^[n] u - positiveGround b‖ ≤
      Real.sqrt (2*((1-m)^n*gap (positiveGround b) u)) := by
  have hf : groundMap b 0 = fun _ => positiveGround b := by
    funext w
    exact zero_coupling_groundMap b w
  rw [hf]
  exact orbit_distance_bound (positiveGround_spec b).2.1 (positiveGround_spec b).1 hu hup hm n

end
end SbtCosmo.Derivation.GroundZeroCouplingOrbit
