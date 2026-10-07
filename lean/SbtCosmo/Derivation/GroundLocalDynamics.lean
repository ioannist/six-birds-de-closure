import SbtCosmo.Derivation.GroundRootCertificate
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Actual nonlinear local attraction from an actual normalized derivative bound.
The coordinate change is a fixed linear equivalence, not a modified iteration.
The spectral/coordinate norm bound is explicit; numerical certificates are not
silently promoted to Lean proofs. -/
namespace SbtCosmo.Derivation.GroundLocalDynamics
noncomputable section
set_option maxHeartbeats 2000000
open Filter NNReal Metric GroundState GroundBorder GroundSourceJacobian
open GroundNormalizedJacobian
open scoped Topology ContDiff BigOperators

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem lipschitz_fixed_ball_invariant {f : E → E} {u : E} {r : ℝ} {q : ℝ≥0}
    (hr : 0 ≤ r) (hq : q ≤ 1) (hf : f u = u)
    (hl : LipschitzOnWith q f (closedBall u r)) :
    Set.MapsTo f (closedBall u r) (closedBall u r) := by
  intro x hx
  have hd := hl.dist_le_mul x hx u (mem_closedBall_self hr)
  rw [hf] at hd
  change dist (f x) u ≤ r
  have hm : (q : ℝ) * dist x u ≤ dist x u :=
    mul_le_of_le_one_left (dist_nonneg) (by exact_mod_cast hq)
  exact hd.trans (hm.trans hx)

omit [NormedSpace ℝ E] in
theorem lipschitz_fixed_orbit_bound {f : E → E} {u y : E} {r : ℝ} {q : ℝ≥0}
    (hr : 0 ≤ r) (hq : q ≤ 1) (hf : f u = u)
    (hl : LipschitzOnWith q f (closedBall u r)) (hy : y ∈ closedBall u r) (n : ℕ) :
    f^[n] y ∈ closedBall u r ∧ dist (f^[n] y) u ≤ (q : ℝ)^n * dist y u := by
  have hm := lipschitz_fixed_ball_invariant hr hq hf hl
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨hm ih.1, ?_⟩
    have hd := hl.dist_le_mul (f^[n] y) ih.1 u (mem_closedBall_self hr)
    rw [hf] at hd
    calc
      dist (f (f^[n] y)) u ≤ (q : ℝ) * dist (f^[n] y) u := hd
      _ ≤ (q : ℝ) * ((q : ℝ)^n * dist y u) := mul_le_mul_of_nonneg_left ih.2 q.coe_nonneg
      _ = (q : ℝ)^(n+1) * dist y u := by rw [pow_succ]; ring

omit [NormedSpace ℝ E] in
theorem lipschitz_fixed_orbit_converges {f : E → E} {u y : E} {r : ℝ} {q : ℝ≥0}
    (hr : 0 ≤ r) (hq : q < 1) (hf : f u = u)
    (hl : LipschitzOnWith q f (closedBall u r)) (hy : y ∈ closedBall u r) :
    Tendsto (fun n : ℕ => f^[n] y) atTop (nhds u) := by
  have hb := lipschitz_fixed_orbit_bound hr hq.le hf hl hy
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one q.coe_nonneg
    (show (q : ℝ) < 1 by exact_mod_cast hq)).mul_const (dist y u)
  have hd : Tendsto (fun n : ℕ => dist (f^[n] y) u) atTop (nhds 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hb n).2) (by simpa using hg)
  exact tendsto_iff_dist_tendsto_zero.mpr hd

/-- C1 regularity and a strict derivative norm bound earn a nonlinear basin. -/
theorem c1_fixed_local_attraction {f : E → E} {u : E}
    (hc : ContDiffAt ℝ 1 f u) (hf : f u = u) (hd : ‖fderiv ℝ f u‖ < 1) :
    ∃ r > 0, ∃ q : ℝ≥0, q < 1 ∧
      Set.MapsTo f (closedBall u r) (closedBall u r) ∧
      ∀ y ∈ closedBall u r,
        Tendsto (fun n : ℕ => f^[n] y) atTop (nhds u) ∧
        ∀ n : ℕ, dist (f^[n] y) u ≤ (q : ℝ)^n * dist y u := by
  have hd' : ‖fderiv ℝ f u‖₊ < (1 : ℝ≥0) := by exact_mod_cast hd
  obtain ⟨q, hlow, hhigh⟩ := exists_between hd'
  obtain ⟨t, ht, hl⟩ := hc.exists_lipschitzOnWith_of_nnnorm_lt q hlow
  obtain ⟨r, hr, hrt⟩ := nhds_basis_closedBall.mem_iff.mp ht
  have hl' := hl.mono hrt
  refine ⟨r, hr, q, hhigh, lipschitz_fixed_ball_invariant hr.le hhigh.le hf hl', ?_⟩
  intro y hy
  exact ⟨lipschitz_fixed_orbit_converges hr.le hhigh hf hl' hy,
    fun n => (lipschitz_fixed_orbit_bound hr.le hhigh.le hf hl' hy n).2⟩

end General

theorem normSq_smooth : ContDiff ℝ ∞ normSq := by
  unfold normSq
  fun_prop

theorem normalize_smooth_at {u : Field} (hu : 0 < normSq u) :
    ContDiffAt ℝ ∞ normalize u := by
  have hs := normSq_smooth.contDiffAt.sqrt hu.ne'
  have hi := hs.inv (Real.sqrt_pos.mpr hu).ne'
  have hh := hi.smul (contDiffAt_id (x := u))
  convert hh using 1
  funext w i
  simp [GroundNormalizedJacobian.normalize, div_eq_mul_inv, mul_comm]

theorem relaxed_smooth (b : Field) (κ m : ℝ) :
    ContDiff ℝ ∞ (relaxed (groundMap b κ) m) := by
  exact (contDiff_id.const_smul (1-m)).add ((groundMap_smooth b κ).const_smul m)

theorem relaxed_fixed {b u : Field} {κ m : ℝ} (hf : groundMap b κ u = u) :
    relaxed (groundMap b κ) m u = u := by
  funext i
  simp only [relaxed, hf]
  ring

theorem normalized_smooth_at {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    ContDiffAt ℝ ∞ (normalizedRelaxed (groundMap b κ) m) u := by
  have hr := relaxed_fixed (m := m) hf
  have hn : ContDiffAt ℝ ∞ normalize (relaxed (groundMap b κ) m u) := by
    rw [hr]
    apply normalize_smooth_at
    rw [hu]
    norm_num
  exact hn.comp u (relaxed_smooth b κ m).contDiffAt

/-- The energy coordinate of a certified positive root is the actual selected
ground energy, so its entire border is the existing selector's border. -/
theorem positive_root_groundPair_return {b : Field} {κ : ℝ} {x : Point}
    (hz : GroundRootCertificate.residual b κ x = 0) (hp : ∀ i, 0 < x.1 i) :
    groundPair (sourcePotential b κ x.1) = x := by
  obtain ⟨hg, hf⟩ := GroundRootCertificate.positive_root_return hz hp
  change positiveGround (sourcePotential b κ x.1) = x.1 at hf
  have he1 := hg.2.1 (0 : Fin 8)
  have he2 := (positiveGround_spec (sourcePotential b κ x.1)).2.2.1 (0 : Fin 8)
  rw [hf] at he2
  have he : energy (sourcePotential b κ x.1) x.1 = x.2 :=
    mul_right_cancel₀ (hp 0).ne' (he2.symm.trans he1)
  apply Prod.ext
  · exact hf
  · simpa only [groundPair, hf] using he

/-- Any solution of the actual root's sourced bordered linear equation returns
to the actual ground-map Jacobian; a computed matrix cannot stand in for it. -/
theorem positive_root_jacobian_return {b : Field} {κ : ℝ} {x : Point}
    (hz : GroundRootCertificate.residual b κ x = 0) (hp : ∀ i, 0 < x.1 i)
    (h : Field) {y : Point}
    (hy : border (sourcePotential b κ x.1) x.1 x.2 y =
      (fun i => -sourceDerivative b κ x.1 h i * x.1 i, 0)) :
    y.1 = jacobian b κ x.1 h := by
  have hpair := positive_root_groundPair_return hz hp
  have hground : positiveGround (sourcePotential b κ x.1) = x.1 :=
    congrArg Prod.fst hpair
  have hy' : border (sourcePotential b κ x.1)
      (groundPair (sourcePotential b κ x.1)).1 (groundPair (sourcePotential b κ x.1)).2 y =
      (fun i => -sourceDerivative b κ x.1 h i * positiveGround (sourcePotential b κ x.1) i, 0) := by
    simpa only [hpair, hground] using hy
  have he := GroundSmooth.pairDerivative_unique _ _ hy'
  exact congrArg Prod.fst he

def coordinateMap (S : Field ≃L[ℝ] Field) (b : Field) (κ m : ℝ) (x : Field) : Field :=
  S.symm (normalizedRelaxed (groundMap b κ) m (S x))

def coordinateJacobian (S : Field ≃L[ℝ] Field) (b : Field) (κ m : ℝ)
    (u : Field) : Field →L[ℝ] Field :=
  S.symm.toContinuousLinearMap.comp ((normalizedJacobian b κ m u).comp S.toContinuousLinearMap)

def column (j : Fin 8) : Field := Pi.single j 1

theorem linear_action_entries (L : Field →L[ℝ] Field) (h : Field) (i : Fin 8) :
    L h i = ∑ j, L (column j) i * h j := by
  conv_lhs => rw [pi_eq_sum_univ' h]
  simp [column, map_sum, mul_comm]

/-- The exact row sums checked by the interval checker bound the actual operator
norm for the finite-field sup norm; this bridge is not a spectral assumption. -/
theorem operator_norm_le_rows (L : Field →L[ℝ] Field) {q : ℝ} (hq : 0 ≤ q)
    (hb : ∀ i, (∑ j, |L (column j) i|) ≤ q) : ‖L‖ ≤ q := by
  apply L.opNorm_le_bound hq
  intro h
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg h))).mpr
  intro i
  rw [Real.norm_eq_abs, linear_action_entries]
  calc
    |∑ j, L (column j) i * h j| ≤ ∑ j, |L (column j) i * h j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |L (column j) i| * ‖h‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm h j
    _ = (∑ j, |L (column j) i|) * ‖h‖ := by rw [Finset.sum_mul]
    _ ≤ q * ‖h‖ := mul_le_mul_of_nonneg_right (hb i) (norm_nonneg h)

theorem coordinate_fixed (S : Field ≃L[ℝ] Field) {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    coordinateMap S b κ m (S.symm u) = S.symm u := by
  simp [coordinateMap, normalizedRelaxed_fixes _ m hf hu]

theorem coordinate_smooth_at (S : Field ≃L[ℝ] Field) {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    ContDiffAt ℝ ∞ (coordinateMap S b κ m) (S.symm u) := by
  have hc : ContDiffAt ℝ ∞ (normalizedRelaxed (groundMap b κ) m) (S (S.symm u)) := by
    simpa using normalized_smooth_at (m := m) hu hf
  exact S.symm.contDiff.contDiffAt.comp _ (hc.comp _ S.contDiff.contDiffAt)

theorem coordinate_hasFDerivAt (S : Field ≃L[ℝ] Field) {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) :
    HasFDerivAt (coordinateMap S b κ m) (coordinateJacobian S b κ m u) (S.symm u) := by
  have hd : HasFDerivAt (normalizedRelaxed (groundMap b κ) m)
      (normalizedJacobian b κ m u) (S (S.symm u)) := by
    simpa using normalized_hasFDerivAt (m := m) hu hf
  exact S.symm.toContinuousLinearMap.hasFDerivAt.comp _
    (hd.comp _ S.toContinuousLinearMap.hasFDerivAt)

theorem coordinate_iterate_return (S : Field ≃L[ℝ] Field) (b : Field) (κ m : ℝ)
    (x : Field) (n : ℕ) :
    S ((coordinateMap S b κ m)^[n] x) =
      (normalizedRelaxed (groundMap b κ) m)^[n] (S x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp [coordinateMap, ih]

/-- All directions of the actual real iteration converge in an earned local
coordinate ball. The norm bound is on the actual, already constructed derivative. -/
theorem actual_local_attraction (S : Field ≃L[ℝ] Field) {b u : Field} {κ m : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u)
    (hd : ‖coordinateJacobian S b κ m u‖ < 1) :
    ∃ r > 0, ∃ q : ℝ≥0, q < 1 ∧ ∀ y : Field,
      S.symm y ∈ closedBall (S.symm u) r →
        Tendsto (fun n : ℕ => (normalizedRelaxed (groundMap b κ) m)^[n] y)
          atTop (nhds u) ∧
        ∀ n : ℕ, dist (S.symm ((normalizedRelaxed (groundMap b κ) m)^[n] y)) (S.symm u) ≤
          (q : ℝ)^n * dist (S.symm y) (S.symm u) := by
  have hc : ContDiffAt ℝ 1 (coordinateMap S b κ m) (S.symm u) :=
    (coordinate_smooth_at S hu hf).of_le (by simp)
  have hd' : ‖fderiv ℝ (coordinateMap S b κ m) (S.symm u)‖ < 1 := by
    rw [(coordinate_hasFDerivAt S hu hf).fderiv]
    exact hd
  obtain ⟨r, hr, q, hq, _, horbit⟩ :=
    c1_fixed_local_attraction hc (coordinate_fixed S hu hf) hd'
  refine ⟨r, hr, q, hq, fun y hy => ?_⟩
  obtain ⟨ht, hb⟩ := horbit (S.symm y) hy
  have hreturn (n : ℕ) : S ((coordinateMap S b κ m)^[n] (S.symm y)) =
      (normalizedRelaxed (groundMap b κ) m)^[n] y := by
    simpa using coordinate_iterate_return S b κ m (S.symm y) n
  refine ⟨?_, fun n => ?_⟩
  · have hh := S.continuous.continuousAt.tendsto.comp ht
    simpa only [Function.comp_def, hreturn, S.apply_symm_apply] using hh
  · have hn := congrArg S.symm (hreturn n)
    have hn' : (coordinateMap S b κ m)^[n] (S.symm y) =
        S.symm ((normalizedRelaxed (groundMap b κ) m)^[n] y) := by
      simpa only [S.symm_apply_apply] using hn
    rw [← hn']
    exact hb n

theorem actual_local_attraction_of_rows (S : Field ≃L[ℝ] Field) {b u : Field} {κ m q : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ i, (∑ j, |coordinateJacobian S b κ m u (column j) i|) ≤ q) :
    ∃ r > 0, ∀ y : Field, S.symm y ∈ closedBall (S.symm u) r →
      Tendsto (fun n : ℕ => (normalizedRelaxed (groundMap b κ) m)^[n] y) atTop (nhds u) := by
  obtain ⟨r, hr, _, _, ho⟩ := actual_local_attraction S hu hf
    ((operator_norm_le_rows _ hq hb).trans_lt hq1)
  exact ⟨r, hr, fun y hy => (ho y hy).1⟩

end
end SbtCosmo.Derivation.GroundLocalDynamics
