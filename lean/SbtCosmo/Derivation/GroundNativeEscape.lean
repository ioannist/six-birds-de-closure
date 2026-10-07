import SbtCosmo.Derivation.GroundNativeLocal

/-! Nonlinear escape of the unchanged native complex map from arbitrarily close
unit inputs. Actual C-infinity smoothness, the derivative and legality are earned.
A real expanding eigenmode and the coordinate norm gap remain explicit linear
hypotheses; no nonlinear remainder or escape verdict is supplied. -/
namespace SbtCosmo.Derivation.GroundNativeEscape
noncomputable section
open Filter Metric NNReal
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem c2_quadratic_remainder {f : E → E} {u : E}
    (hc : ContDiffAt ℝ 2 f u) :
    ∃ r > 0, ∃ K : ℝ≥0, ∀ x ∈ closedBall u r,
      ‖f x - f u - (fderiv ℝ f u) (x-u)‖ ≤ (K : ℝ)*‖x-u‖^2 := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) u := hc.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hKt⟩ := hd.exists_lipschitzOnWith
  have hdiff : ∀ᶠ x in nhds u, DifferentiableAt ℝ f x := by
    filter_upwards [hc.eventually (by norm_num)] with x hx
    exact hx.differentiableAt (by norm_num)
  obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.mp (inter_mem ht hdiff)
  refine ⟨r, hr, K, ?_⟩
  intro x hx
  let g : E → E := fun y => f y - f u - (fderiv ℝ f u) (y-u)
  let s : Set E := closedBall u ‖x-u‖
  have hs : s ⊆ closedBall u r := by
    exact closedBall_subset_closedBall (by simpa only [mem_closedBall, dist_eq_norm] using hx)
  have hu : u ∈ s := mem_closedBall_self (norm_nonneg _)
  have hxs : x ∈ s := by simp only [s, mem_closedBall, dist_eq_norm, le_refl]
  have hg : ∀ y ∈ s,
      HasFDerivWithinAt g (fderiv ℝ f y - fderiv ℝ f u) s y := by
    intro y hy
    have hy' := hrs (hs hy)
    have h1 := hy'.2.hasFDerivAt.sub_const (f u)
    have h2 := (fderiv ℝ f u).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const u)
    simpa only [g, ContinuousLinearMap.comp_id] using (h1.sub h2).hasFDerivWithinAt
  have hb : ∀ y ∈ s, ‖fderiv ℝ f y - fderiv ℝ f u‖ ≤ (K : ℝ)*‖x-u‖ := by
    intro y hy
    have h := (lipschitzOnWith_iff_norm_sub_le.mp hKt) (hrs (hs hy)).1 (hrs (hs hu)).1
    have hyb : ‖y-u‖ ≤ ‖x-u‖ := by simpa only [s, mem_closedBall, dist_eq_norm] using hy
    exact h.trans (mul_le_mul_of_nonneg_left hyb K.coe_nonneg)
  have h := (convex_closedBall u ‖x-u‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hb hu hxs
  simpa only [g, sub_self, map_zero, sub_zero, pow_two, mul_assoc] using h

theorem quadratic_tracking_step {f : E → E} {L : E →L[ℝ] E}
    {x y : E} {α K A M R : ℝ}
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hsmall : A*α ≤ 1) (hrate : 4*K + M*A ≤ A*R^2)
    (hL : ‖L‖ ≤ M) (hy : ‖y‖ ≤ α) (he : ‖x-y‖ ≤ A*α^2)
    (hrem : ‖f x - L x‖ ≤ K*‖x‖^2) :
    ‖x‖ ≤ 2*α ∧ ‖f x - L y‖ ≤ A*(α*R)^2 := by
  have hx : ‖x‖ ≤ 2*α := by
    have ht : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
      have hh := norm_add_le (x-y) y
      simpa only [sub_add_cancel] using hh
    have hh : A*α^2 ≤ α := by nlinarith [mul_le_mul_of_nonneg_right hsmall hα]
    linarith
  refine ⟨hx, ?_⟩
  have hsq : ‖x‖^2 ≤ (2*α)^2 := by nlinarith [norm_nonneg x]
  have hlinear : ‖L (x-y)‖ ≤ M*(A*α^2) := by
    exact (L.le_opNorm _).trans (mul_le_mul hL he (norm_nonneg _) hM)
  have hid : f x - L y = (f x - L x) + L (x-y) := by
    rw [map_sub]
    abel
  calc
    ‖f x - L y‖ = ‖(f x - L x) + L (x-y)‖ := congrArg norm hid
    _ ≤ ‖f x - L x‖ + ‖L (x-y)‖ := norm_add_le _ _
    _ ≤ K*‖x‖^2 + M*(A*α^2) := add_le_add hrem hlinear
    _ ≤ K*(2*α)^2 + M*(A*α^2) := add_le_add (mul_le_mul_of_nonneg_left hsq hK) le_rfl
    _ ≤ A*(α*R)^2 := by nlinarith [mul_le_mul_of_nonneg_right hrate (sq_nonneg α)]

theorem quadratic_tracking {f : E → E} {L : E →L[ℝ] E}
    {y : ℕ → E} {δ K A M R r : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hR : 1 ≤ R) (hsmall : A*r ≤ 1) (hend : δ*R^N ≤ r)
    (hrate : 4*K + M*A ≤ A*R^2) (hL : ‖L‖ ≤ M)
    (hy : ∀ k, ‖y k‖ ≤ δ*R^k) (hynext : ∀ k, y (k+1) = L (y k))
    (hrem : ∀ x, ‖x‖ ≤ 2*r → ‖f x - L x‖ ≤ K*‖x‖^2) :
    ∀ k ≤ N, ‖f^[k] (y 0) - y k‖ ≤ A*(δ*R^k)^2 ∧
      ‖f^[k] (y 0)‖ ≤ 2*(δ*R^k) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hamp : ∀ k ≤ N, δ*R^k ≤ r := by
    intro k hk
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hk) hδ).trans hend
  have hnorm : ∀ k ≤ N, ∀ x : E, ‖x-y k‖ ≤ A*(δ*R^k)^2 → ‖x‖ ≤ 2*(δ*R^k) := by
    intro k hk x he
    have hα : 0 ≤ δ*R^k := mul_nonneg hδ (pow_nonneg hR0 _)
    have hs : A*(δ*R^k) ≤ 1 := (mul_le_mul_of_nonneg_left (hamp k hk) hA).trans hsmall
    have ht : ‖x‖ ≤ ‖x-y k‖ + ‖y k‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-y k) (y k)
    have hh : A*(δ*R^k)^2 ≤ δ*R^k := by
      nlinarith [mul_le_mul_of_nonneg_right hs hα]
    linarith [hy k]
  intro k
  induction k with
  | zero =>
    intro hk
    have he : ‖f^[0] (y 0) - y 0‖ ≤ A*(δ*R^0)^2 := by
      simp only [Function.iterate_zero, id_eq, sub_self, norm_zero]
      exact mul_nonneg hA (sq_nonneg _)
    exact ⟨he, hnorm 0 hk _ he⟩
  | succ k ih =>
    intro hk
    have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
    obtain ⟨he, hn⟩ := ih hk'
    have hα : 0 ≤ δ*R^k := mul_nonneg hδ (pow_nonneg hR0 _)
    have hs : A*(δ*R^k) ≤ 1 := (mul_le_mul_of_nonneg_left (hamp k hk') hA).trans hsmall
    have hb : ‖f^[k] (y 0)‖ ≤ 2*r := hn.trans (mul_le_mul_of_nonneg_left (hamp k hk') (by norm_num))
    have ht := (quadratic_tracking_step hα hK hM hs hrate hL (hy k) he (hrem _ hb)).2
    have he' : ‖f^[k+1] (y 0) - y (k+1)‖ ≤ A*(δ*R^(k+1))^2 := by
      simpa only [Function.iterate_succ_apply', hynext, pow_succ, mul_assoc] using ht
    exact ⟨he', hnorm (k+1) hk _ he'⟩

theorem eigenmode_tracking {f : E → E} {L : E →L[ℝ] E}
    {h : E} {ℓ δ K A M r : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hℓ : 1 ≤ |ℓ|) (hsmall : A*r ≤ 1) (hend : δ*|ℓ|^N ≤ r)
    (hrate : 4*K + M*A ≤ A*|ℓ|^2) (hL : ‖L‖ ≤ M)
    (hh : ‖h‖ = 1) (heigen : L h = ℓ • h)
    (hrem : ∀ x, ‖x‖ ≤ 2*r → ‖f x - L x‖ ≤ K*‖x‖^2) :
    (∀ k ≤ N, ‖f^[k] (δ • h) - (δ*ℓ^k) • h‖ ≤ A*(δ*|ℓ|^k)^2 ∧
      ‖f^[k] (δ • h)‖ ≤ 2*(δ*|ℓ|^k)) ∧
    δ*|ℓ|^N - A*(δ*|ℓ|^N)^2 ≤ ‖f^[N] (δ • h)‖ := by
  let y : ℕ → E := fun k => (δ*ℓ^k) • h
  have hy : ∀ k, ‖y k‖ = δ*|ℓ|^k := by
    intro k
    simp only [y, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hδ, hh, mul_one]
  have hnext : ∀ k, y (k+1) = L (y k) := by
    intro k
    simp only [y, map_smul, heigen, smul_smul, pow_succ, mul_assoc]
  have ht := quadratic_tracking hδ hK hA hM hℓ hsmall hend hrate hL (fun k => (hy k).le) hnext hrem
  have hy0 : y 0 = δ • h := by simp only [y, pow_zero, mul_one]
  rw [hy0] at ht
  refine ⟨ht, ?_⟩
  have hn : ‖y N‖ ≤ ‖f^[N] (δ • h) - y N‖ + ‖f^[N] (δ • h)‖ := by
    have hv := norm_add_le (y N - f^[N] (δ • h)) (f^[N] (δ • h))
    rw [sub_add_cancel, norm_sub_rev] at hv
    exact hv
  rw [hy N] at hn
  linarith [(ht N le_rfl).1]

theorem finite_eigenmode_escape {f : E → E} {L : E →L[ℝ] E}
    {h : E} {ℓ K A M s : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hℓ : 1 < |ℓ|) (hs : 0 < s) (hsmall : A*s ≤ 1/2)
    (hrate : 4*K + M*A ≤ A*|ℓ|^2) (hL : ‖L‖ ≤ M)
    (hh : ‖h‖ = 1) (heigen : L h = ℓ • h)
    (hrem : ∀ x, ‖x‖ ≤ 2*s → ‖f x - L x‖ ≤ K*‖x‖^2) (N : ℕ) :
    s/2 ≤ ‖f^[N] ((s/|ℓ|^N) • h)‖ ∧
      (∀ k ≤ N, ‖f^[k] ((s/|ℓ|^N) • h)‖ ≤ 2*s) := by
  have hR : 0 < |ℓ| := lt_trans zero_lt_one hℓ
  have hδ : 0 ≤ s/|ℓ|^N := div_nonneg hs.le (pow_nonneg hR.le _)
  have hvalue : (s/|ℓ|^N)*|ℓ|^N = s := div_mul_cancel₀ s (pow_ne_zero _ hR.ne')
  have ht := eigenmode_tracking hδ hK hA hM hℓ.le (hsmall.trans (by norm_num))
    (le_of_eq hvalue) hrate hL hh heigen hrem
  rw [hvalue] at ht
  constructor
  · have hb : A*s^2 ≤ s/2 := by
      nlinarith [mul_le_mul_of_nonneg_right hsmall hs.le]
    linarith [ht.2]
  · intro k hk
    have hamp : (s/|ℓ|^N)*|ℓ|^k ≤ s := by
      have hb := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ.le hk) hδ
      rw [hvalue] at hb
      exact hb
    exact (ht.1 k hk).2.trans (mul_le_mul_of_nonneg_left hamp (by norm_num))

theorem arbitrarily_close_eigenmode_escape {f : E → E} {L : E →L[ℝ] E}
    {h : E} {ℓ K A M s : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hℓ : 1 < |ℓ|) (hs : 0 < s) (hsmall : A*s ≤ 1/2)
    (hrate : 4*K + M*A ≤ A*|ℓ|^2) (hL : ‖L‖ ≤ M)
    (hh : ‖h‖ = 1) (heigen : L h = ℓ • h)
    (hrem : ∀ x, ‖x‖ ≤ 2*s → ‖f x - L x‖ ≤ K*‖x‖^2) :
    ∀ ε > 0, ∃ x : E, ∃ N : ℕ, 1 ≤ N ∧ ‖x‖ < ε ∧
      s/2 ≤ ‖f^[N] x‖ ∧ ∀ k ≤ N, ‖f^[k] x‖ ≤ 2*s := by
  intro ε hε
  have hR : 0 < |ℓ| := lt_trans zero_lt_one hℓ
  have hi0 : 0 ≤ |ℓ|⁻¹ := inv_nonneg.mpr hR.le
  have hi1 : |ℓ|⁻¹ < 1 := (inv_lt_one₀ hR).mpr hℓ
  have ht : Tendsto (fun n : ℕ => s/|ℓ|^n) atTop (nhds 0) := by
    have hp := (tendsto_const_nhds (x := s)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1)
    simpa only [inv_pow, div_eq_mul_inv, mul_zero] using hp
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ s/|ℓ|^N < ε := by
    exact (eventually_ge_atTop 1).and (ht.eventually (gt_mem_nhds hε))
  obtain ⟨N, hN, hclose⟩ := hev.exists
  refine ⟨(s/|ℓ|^N) • h, N, hN, ?_, ?_⟩
  · simpa only [norm_smul, Real.norm_eq_abs, hh, mul_one,
      abs_of_nonneg (div_nonneg hs.le (pow_nonneg hR.le _))] using hclose
  · exact finite_eigenmode_escape hK hA hM hℓ hs hsmall hrate hL hh heigen hrem N

theorem c2_eigenmode_escape {f : E → E} {L : E →L[ℝ] E}
    {h : E} {ℓ : ℝ} (hc : ContDiffAt ℝ 2 f 0) (hf : f 0 = 0)
    (hd : HasFDerivAt f L 0) (hh : ‖h‖ = 1) (heigen : L h = ℓ • h)
    (hℓ : 1 < |ℓ|) (hgap : ‖L‖ < |ℓ|^2) :
    ∃ s > 0, ∀ ε > 0, ∃ x : E, ∃ N : ℕ, 1 ≤ N ∧ ‖x‖ < ε ∧
      s/2 ≤ ‖f^[N] x‖ ∧ ∀ k ≤ N, ‖f^[k] x‖ ≤ 2*s := by
  obtain ⟨r, hr, K, hrem⟩ := c2_quadratic_remainder hc
  let M := ‖L‖
  let A := (4*(K : ℝ)+1)/(|ℓ|^2-M)
  have hden : 0 < |ℓ|^2-M := sub_pos.mpr hgap
  have hA : 0 < A := div_pos (by positivity) hden
  have hrate : 4*(K : ℝ) + M*A ≤ A*|ℓ|^2 := by
    have heq : A*(|ℓ|^2-M) = 4*(K : ℝ)+1 := div_mul_cancel₀ _ hden.ne'
    nlinarith
  let s := min (r/2) (1/(2*A))
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsr : 2*s ≤ r := by
    have hb : s ≤ r/2 := min_le_left _ _
    linarith
  have hsmall : A*s ≤ 1/2 := by
    have hb : s ≤ 1/(2*A) := min_le_right _ _
    have hm : s*(2*A) ≤ 1 := (le_div_iff₀ (by positivity)).mp hb
    nlinarith
  have hrem' : ∀ x, ‖x‖ ≤ 2*s → ‖f x - L x‖ ≤ (K : ℝ)*‖x‖^2 := by
    intro x hx
    have hx' : x ∈ closedBall (0 : E) r := by
      simpa only [mem_closedBall, dist_zero_right] using hx.trans hsr
    have ht := hrem x hx'
    simpa only [hf, sub_zero, hd.fderiv] using ht
  exact ⟨s, hs, arbitrarily_close_eigenmode_escape K.coe_nonneg hA.le (norm_nonneg L)
    hℓ hs hsmall hrate le_rfl hh heigen hrem'⟩

theorem c2_eigenmode_escape_within {f : E → E} {L : E →L[ℝ] E}
    {h : E} {ℓ B : ℝ} (hc : ContDiffAt ℝ 2 f 0) (hf : f 0 = 0)
    (hd : HasFDerivAt f L 0) (hh : ‖h‖ = 1) (heigen : L h = ℓ • h)
    (hℓ : 1 < |ℓ|) (hgap : ‖L‖ < |ℓ|^2) (hB : 0 < B) :
    ∃ s > 0, 2*s ≤ B ∧ ∀ ε > 0, ∃ x : E, ∃ N : ℕ, 1 ≤ N ∧ ‖x‖ < ε ∧
      s/2 ≤ ‖f^[N] x‖ ∧ ∀ k ≤ N, ‖f^[k] x‖ ≤ 2*s := by
  obtain ⟨r, hr, K, hrem⟩ := c2_quadratic_remainder hc
  let M := ‖L‖
  let A := (4*(K : ℝ)+1)/(|ℓ|^2-M)
  have hden : 0 < |ℓ|^2-M := sub_pos.mpr hgap
  have hA : 0 < A := div_pos (by positivity) hden
  have hrate : 4*(K : ℝ) + M*A ≤ A*|ℓ|^2 := by
    have heq : A*(|ℓ|^2-M) = 4*(K : ℝ)+1 := div_mul_cancel₀ _ hden.ne'
    nlinarith
  let s := min (min (r/2) (B/2)) (1/(2*A))
  have hs : 0 < s := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hsr : 2*s ≤ r := by
    have hb : s ≤ r/2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hsB : 2*s ≤ B := by
    have hb : s ≤ B/2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hsmall : A*s ≤ 1/2 := by
    have hb : s ≤ 1/(2*A) := min_le_right _ _
    have hm : s*(2*A) ≤ 1 := (le_div_iff₀ (by positivity)).mp hb
    nlinarith
  have hrem' : ∀ x, ‖x‖ ≤ 2*s → ‖f x - L x‖ ≤ (K : ℝ)*‖x‖^2 := by
    intro x hx
    have hx' : x ∈ closedBall (0 : E) r := by
      simpa only [mem_closedBall, dist_zero_right] using hx.trans hsr
    have ht := hrem x hx'
    simpa only [hf, sub_zero, hd.fderiv] using ht
  exact ⟨s, hs, hsB, arbitrarily_close_eigenmode_escape K.coe_nonneg hA.le (norm_nonneg L)
    hℓ hs hsmall hrate le_rfl hh heigen hrem'⟩

theorem c2_eigenmode_output_escape {f : E → E} {L : E →L[ℝ] E}
    {h : E} {ℓ B : ℝ} {P : E → Prop}
    (hc : ContDiffAt ℝ 2 f 0) (hf : f 0 = 0)
    (hd : HasFDerivAt f L 0) (hh : ‖h‖ = 1) (heigen : L h = ℓ • h)
    (hℓ : 1 < |ℓ|) (hgap : ‖L‖ < |ℓ|^2) (hB : 0 < B)
    (hP : ∀ x, ‖x‖ ≤ B → P (f x)) :
    ∃ s > 0, ∀ ε > 0, ∃ z : E, ∃ N : ℕ, ‖z‖ < ε ∧ P z ∧
      s/2 ≤ ‖f^[N] z‖ ∧ ∀ k ≤ N, ‖f^[k] z‖ ≤ B := by
  obtain ⟨s, hs, hsB, hes⟩ := c2_eigenmode_escape_within hc hf hd hh heigen hℓ hgap hB
  refine ⟨s, hs, ?_⟩
  intro ε hε
  have ht : {x | ‖f x‖ < ε} ∈ nhds (0 : E) := by
    have hv := hc.continuousAt.eventually (show ball (0 : E) ε ∈ nhds (f 0) by
      rw [hf]
      exact ball_mem_nhds _ hε)
    simpa only [mem_ball, dist_zero_right] using hv
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨x, N, hN, hx, hout, hstay⟩ := hes δ hδ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hxB : ‖x‖ ≤ B := by
    simpa only [Function.iterate_zero, id_eq] using (hstay 0 (by omega)).trans hsB
  refine ⟨f x, n, ?_, hP x hxB, ?_, ?_⟩
  · exact hball (by simpa only [mem_ball, dist_zero_right] using hx)
  · simpa only [Function.iterate_succ_apply] using hout
  · intro k hk
    have hb := (hstay (k+1) (by omega)).trans hsB
    simpa only [Function.iterate_succ_apply] using hb

open SbtCosmo.Derivation GroundState GroundNativePhase GroundNativeIteration
open scoped BigOperators

theorem stateNormSq_smul (a : ℝ) (x : State) :
    stateNormSq (a • x) = a^2 * stateNormSq x := by
  change (∑ i, (a*x.1 i)^2) + (∑ i, (a*x.2 i)^2) =
    a^2*((∑ i, (x.1 i)^2) + (∑ i, (x.2 i)^2))
  simp only [mul_pow, ← Finset.mul_sum, mul_add]

theorem normalizeState_unit {x : State} (hx : 0 < stateNormSq x) :
    stateNormSq (normalizeState x) = 1 := by
  rw [normalizeState, stateNormSq_smul, inv_pow, Real.sq_sqrt hx.le]
  exact inv_mul_cancel₀ hx.ne'

theorem complexNormalize_unit {z : ComplexField} (hz : 0 < complexNormSq z) :
    complexNormSq (complexNormalize z) = 1 := by
  have hp : pack (unpack z) = z := by funext i; exact Complex.eta (z i)
  have hx : 0 < stateNormSq (unpack z) := by rw [← norm_pack, hp]; exact hz
  have hh := normalizeState_unit hx
  rw [← norm_pack, pack_normalizeState, hp] at hh
  exact hh

theorem nativeUpdate_unit {z : ComplexField} {τ κ m : ℝ} {b : Field}
    (hτ : 0 ≤ τ) (hz : NativeLegal τ b κ m z) :
    complexNormSq (nativeUpdate τ b κ m z) = 1 := by
  exact complexNormalize_unit (Real.sqrt_pos.mp (hτ.trans_lt hz))

open GroundNativeJacobian GroundNativeLocal GroundSourceJacobian

def displacementMap (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field) (κ m : ℝ)
    (u : Field) (x : State) : State :=
  coordinateMap T τ b κ m (T.symm (u, 0) + x) - T.symm (u, 0)

theorem displacement_fixed (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    displacementMap T τ b κ m u 0 = 0 := by
  simp only [displacementMap, add_zero, coordinate_fixed T hu hf hτ0 hτ1, sub_self]

theorem displacement_smooth (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    ContDiffAt ℝ ∞ (displacementMap T τ b κ m u) 0 := by
  have hc : ContDiffAt ℝ ∞ (coordinateMap T τ b κ m) (T.symm (u, 0) + 0) := by
    simpa only [add_zero] using coordinate_smooth_at T hu hf hτ0 hτ1
  exact (hc.comp _ (contDiffAt_const.add contDiffAt_id)).sub contDiffAt_const

theorem displacement_hasFDerivAt (T : State ≃L[ℝ] State) {b u : Field} {κ m τ : ℝ}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    HasFDerivAt (displacementMap T τ b κ m u)
      (coordinateDerivative T b κ m u) 0 := by
  have hd : HasFDerivAt (coordinateMap T τ b κ m) (coordinateDerivative T b κ m u)
      (T.symm (u, 0) + 0) := by
    simpa only [add_zero] using coordinate_hasFDerivAt T hu hf hτ0 hτ1
  have hh := (hd.comp 0 ((hasFDerivAt_const (T.symm (u, 0)) (0 : State)).add (hasFDerivAt_id (0 : State)))).sub_const (T.symm (u, 0))
  simpa only [zero_add, ContinuousLinearMap.comp_id] using hh

theorem displacement_iterate_return (T : State ≃L[ℝ] State) (τ : ℝ) (b : Field)
    (κ m : ℝ) (u : Field) (x : State) (n : ℕ) :
    T (T.symm (u, 0) + (displacementMap T τ b κ m u)^[n] x) =
      (nativePairMap τ b κ m)^[n] (T (T.symm (u, 0) + x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [displacementMap, add_sub_cancel, coordinateMap, T.apply_symm_apply, ih]

theorem native_complex_local_escape (T : State ≃L[ℝ] State) {b u : Field}
    {κ m τ ℓ : ℝ} {v : State}
    (hu : normSq u = 1) (hf : groundMap b κ u = u) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hv : ‖v‖ = 1) (heigen : coordinateDerivative T b κ m u v = ℓ • v)
    (hℓ : 1 < |ℓ|) (hgap : ‖coordinateDerivative T b κ m u‖ < |ℓ|^2) :
    ∃ s > 0, ∀ ε > 0, ∃ z : ComplexField, ∃ N : ℕ,
      complexNormSq z = 1 ∧ ‖T.symm (unpack z) - T.symm (u, 0)‖ < ε ∧
      s/2 ≤ ‖T.symm (unpack ((nativeUpdate τ b κ m)^[N] z)) - T.symm (u, 0)‖ ∧
      ∀ k ≤ N, ActivePhase τ b κ ((nativeUpdate τ b κ m)^[k] z) ∧
        NativeLegal τ b κ m ((nativeUpdate τ b κ m)^[k] z) := by
  let a : State := T.symm (u, 0)
  let f : State → State := displacementMap T τ b κ m u
  have hregion : {x : State | T (a+x) ∈ NativeRegion τ b κ m} ∈ nhds 0 := by
    have hc : ContinuousAt (fun x : State => T (a+x)) 0 :=
      T.continuous.continuousAt.comp (continuousAt_const.add continuousAt_id)
    have hs : NativeRegion τ b κ m ∈ nhds (T (a+0)) := by
      simpa only [a, add_zero, T.apply_symm_apply] using native_region_near_fixed hu hf hτ0 hτ1
    exact hc.eventually hs
  obtain ⟨B, hB, hBr⟩ := nhds_basis_closedBall.mem_iff.mp hregion
  have hr : ∀ x : State, ‖x‖ ≤ B → T (a+x) ∈ NativeRegion τ b κ m := by
    intro x hx
    apply hBr
    simpa only [mem_closedBall, dist_zero_right] using hx
  have hP : ∀ x : State, ‖x‖ ≤ B → complexNormSq (pack (T (a+f x))) = 1 := by
    intro x hx
    have hn := displacement_iterate_return T τ b κ m u x 1
    simp only [Function.iterate_one] at hn
    change T (a + f x) = nativePairMap τ b κ m (T (a+x)) at hn
    rw [hn]
    have hp := nativePairMap_iterate_return τ b κ m (T (a+x)) 1
    simp only [Function.iterate_one] at hp
    rw [hp]
    exact nativeUpdate_unit hτ0 (hr x hx).2
  have hc2 : ContDiffAt ℝ 2 f 0 := (displacement_smooth T hu hf hτ0 hτ1).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨s, hs, hes⟩ := c2_eigenmode_output_escape
    (P := fun x : State => complexNormSq (pack (T (a+x))) = 1) hc2
    (displacement_fixed T hu hf hτ0 hτ1) (displacement_hasFDerivAt T hu hf hτ0 hτ1)
    hv heigen hℓ hgap hB hP
  refine ⟨s, hs, ?_⟩
  intro ε hε
  obtain ⟨x, N, hx, hp, hout, hstay⟩ := hes ε hε
  let z : ComplexField := pack (T (a+x))
  have hi : ∀ k, T.symm (unpack ((nativeUpdate τ b κ m)^[k] z)) - a = f^[k] x := by
    intro k
    have hp := nativePairMap_iterate_return τ b κ m (T (a+x)) k
    change pack ((nativePairMap τ b κ m)^[k] (T (a+x))) = (nativeUpdate τ b κ m)^[k] z at hp
    rw [← hp, ← displacement_iterate_return T τ b κ m u x k]
    change T.symm (T (a+f^[k] x)) - a = f^[k] x
    simp only [T.symm_apply_apply, add_sub_cancel_left]
  refine ⟨z, N, hp, ?_, ?_, ?_⟩
  · simpa only [a, Function.iterate_zero, id_eq] using (show ‖T.symm (unpack z) - a‖ < ε by rw [← Function.iterate_zero_apply (nativeUpdate τ b κ m) z, hi]; exact hx)
  · simpa only [a] using (show s/2 ≤ ‖T.symm (unpack ((nativeUpdate τ b κ m)^[N] z)) - a‖ by rw [hi]; exact hout)
  · intro k hk
    have hrk := hr (f^[k] x) (hstay k hk)
    have hip := congrArg (fun w => T (a+w)) (hi k)
    simp only [add_sub_cancel, T.apply_symm_apply] at hip
    rw [← hip] at hrk
    exact hrk

end
end SbtCosmo.Derivation.GroundNativeEscape
