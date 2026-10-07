import SbtCosmo.Derivation.ClosurePrice
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Scalar convex budget pricing from the actual infimum value and its derivative.
No dual certificate, value-support inequality or convexity of the value is assumed. -/
namespace SbtCosmo.Derivation.ConvexClosurePrice
noncomputable section
open Set Filter
open scoped Topology

variable {E : Type*}

def feasibleCosts (A : Set E) (J energy : E → ℝ) (B : ℝ) : Set ℝ :=
  {r | ∃ x ∈ A, energy x ≤ B ∧ J x = r}

def budgetValue (A : Set E) (J energy : E → ℝ) (B : ℝ) : ℝ :=
  sInf (feasibleCosts A J energy B)

/-- Ordinary primal optimality, not a dual or stationarity premise. -/
structure PrimalOptimum (A : Set E) (J energy : E → ℝ) (B : ℝ) (star : E) : Prop where
  member : star ∈ A
  feasible : energy star ≤ B
  optimal : ∀ x ∈ A, energy x ≤ B → J star ≤ J x

theorem feasible_costs_mono (A : Set E) (J energy : E → ℝ) :
    Monotone (feasibleCosts A J energy) := by
  intro B C hBC r
  rintro ⟨x, hx, he, hJ⟩
  exact ⟨x, hx, he.trans hBC, hJ⟩

theorem value_le_candidate {A : Set E} {J energy : E → ℝ} {B : ℝ}
    (hbb : BddBelow (feasibleCosts A J energy B)) {x : E} (hx : x ∈ A) (he : energy x ≤ B) :
    budgetValue A J energy B ≤ J x :=
  csInf_le hbb ⟨x, hx, he, rfl⟩

theorem optimum_value {A : Set E} {J energy : E → ℝ} {B : ℝ} {star : E}
    (h : PrimalOptimum A J energy B star) : budgetValue A J energy B = J star := by
  apply le_antisymm
  · apply value_le_candidate (x := star) ?_ h.member h.feasible
    refine ⟨J star, ?_⟩
    rintro r ⟨x, hx, he, rfl⟩
    exact h.optimal x hx he
  · apply le_csInf (show (feasibleCosts A J energy B).Nonempty from ⟨J star, star, h.member, h.feasible, rfl⟩)
    rintro r ⟨x, hx, he, rfl⟩
    exact h.optimal x hx he

/-- The infimum is meaningful only under explicit nonempty/bounded-below guards. -/
theorem value_isGLB {A : Set E} {J energy : E → ℝ} {B : ℝ}
    (hne : (feasibleCosts A J energy B).Nonempty)
    (hbb : BddBelow (feasibleCosts A J energy B)) :
    IsGLB (feasibleCosts A J energy B) (budgetValue A J energy B) := isGLB_csInf hne hbb

/-- A local right-hand comparison earns an upper bound on the derivative. -/
theorem derivative_le_of_right_support {f : ℝ → ℝ} {d k : ℝ} (hd : HasDerivAt f d 0)
    (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ f 0 + k*t) : d ≤ k := by
  have ht := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  apply le_of_tendsto ht
  filter_upwards [hbound, self_mem_nhdsWithin] with t hb ht
  rw [slope_def_field]
  simp only [sub_zero]
  apply (div_le_iff₀ ht).mpr
  linarith

/-- Earned global Lagrangian minimization, feasibility and complementarity. -/
structure DualCertificate (A : Set E) (J energy : E → ℝ) (B price : ℝ) (star : E) : Prop where
  nonnegative : 0 ≤ price
  member : star ∈ A
  feasible : energy star ≤ B
  complementarity : price*(energy star-B) = 0
  global_minimum : ∀ x ∈ A, J star ≤ J x + price*(energy x-B)

section Convex
variable [AddCommGroup E] [Module ℝ E]

/-- Convex primal mixing yields the global price-support inequality from a local value derivative. -/
theorem derivative_global_support {A : Set E} {J energy : E → ℝ} {B d lo hi : ℝ} {star : E}
    (hJ : ConvexOn ℝ A J) (he : ConvexOn ℝ A energy)
    (hstar : PrimalOptimum A J energy B star)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, (feasibleCosts A J energy T).Nonempty ∧ BddBelow (feasibleCosts A J energy T))
    (hd : HasDerivAt (budgetValue A J energy) d B) :
    ∀ x ∈ A, J star + d*(energy x-B) ≤ J x := by
  intro x hx
  let gap := energy x-B
  let path := fun t : ℝ => B+t*gap
  have hpath : HasDerivAt path gap 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const gap).const_add B using 1
    simp
  have hv : HasDerivAt (fun t : ℝ => budgetValue A J energy (path t)) (d*gap) 0 := by
    have h0 : path 0 = B := by simp [path]
    rw [← h0] at hd
    exact hd.comp 0 hpath
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), path t ∈ Ioo lo hi := by
    have ht : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 B) := by
      simpa [path] using hpath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht (isOpen_Ioo.mem_nhds hB)
  have hone : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      budgetValue A J energy (path t) ≤ budgetValue A J energy (path 0) + (J x-J star)*t := by
    filter_upwards [hnear, hone, self_mem_nhdsWithin] with t hT ht htp
    have hs : 0 ≤ 1-t := by linarith
    have ha : 1-t+t = (1 : ℝ) := by ring
    have hm : (1-t) • star + t • x ∈ A := hJ.1 hstar.member hx hs htp.le ha
    have henergy := he.2 hstar.member hx hs htp.le ha
    have hbudget := mul_le_mul_of_nonneg_left hstar.feasible hs
    have hfeas : energy ((1-t) • star + t • x) ≤ path t := by
      dsimp [path, gap]
      simp only [smul_eq_mul] at henergy
      nlinarith
    have hvle := value_le_candidate (hfinite (path t) hT).2 hm hfeas
    have hobj := hJ.2 hstar.member hx hs htp.le ha
    rw [show path 0 = B by simp [path], optimum_value hstar]
    simp only [smul_eq_mul] at hobj
    nlinarith
  have hp := derivative_le_of_right_support hv hbound
  dsimp [gap] at hp
  linarith

/-- Strict sensitivity of the actual infimum forces activity; it need not be assumed. -/
theorem strict_sensitivity_forces_activity {A : Set E} {J energy : E → ℝ} {B d lo hi : ℝ} {star : E}
    (hJ : ConvexOn ℝ A J) (he : ConvexOn ℝ A energy)
    (hstar : PrimalOptimum A J energy B star) (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, (feasibleCosts A J energy T).Nonempty ∧ BddBelow (feasibleCosts A J energy T))
    (hd : HasDerivAt (budgetValue A J energy) d B) (hs : d < 0) : energy star = B := by
  have hg := derivative_global_support hJ he hstar hB hfinite hd star hstar.member
  have hf := hstar.feasible
  nlinarith

/-- A positive scalar certificate is constructed as minus the actual value derivative. -/
theorem positive_price_certificate {A : Set E} {J energy : E → ℝ} {B d lo hi : ℝ} {star : E}
    (hJ : ConvexOn ℝ A J) (he : ConvexOn ℝ A energy)
    (hstar : PrimalOptimum A J energy B star)
    (hB : B ∈ Ioo lo hi)
    (hfinite : ∀ T ∈ Ioo lo hi, (feasibleCosts A J energy T).Nonempty ∧ BddBelow (feasibleCosts A J energy T))
    (hd : HasDerivAt (budgetValue A J energy) d B) (hs : d < 0) :
    ∃ price : ℝ, price = -d ∧ 0 < price ∧ DualCertificate A J energy B price star := by
  have hactive := strict_sensitivity_forces_activity hJ he hstar hB hfinite hd hs
  refine ⟨-d, rfl, by linarith, ?_⟩
  refine ⟨by linarith, hstar.member, hstar.feasible, ?_, ?_⟩
  · rw [hactive]
    ring
  · intro x hx
    have h := derivative_global_support hJ he hstar hB hfinite hd x hx
    nlinarith

end Convex

/-- Dual global support returns actual primal optimality. -/
theorem certificate_primal_optimum {A : Set E} {J energy : E → ℝ} {B p : ℝ} {star : E}
    (h : DualCertificate A J energy B p star) : PrimalOptimum A J energy B star := by
  refine ⟨h.member, h.feasible, ?_⟩
  intro x hx he
  have hg := h.global_minimum x hx
  have hp := mul_nonpos_of_nonneg_of_nonpos h.nonnegative (sub_nonpos.mpr he)
  linarith

def lagrangian (J energy : E → ℝ) (B price : ℝ) (x : E) : ℝ := J x+price*(energy x-B)

def dualValue (A : Set E) (J energy : E → ℝ) (B price : ℝ) : ℝ :=
  sInf ((lagrangian J energy B price) '' A)

theorem certificate_lagrangian_minimum {A : Set E} {J energy : E → ℝ} {B p : ℝ} {star : E}
    (h : DualCertificate A J energy B p star) :
    lagrangian J energy B p star = J star ∧ IsMinOn (lagrangian J energy B p) A star := by
  have he : lagrangian J energy B p star = J star := by
    unfold lagrangian
    rw [h.complementarity, add_zero]
  exact ⟨he, fun x hx => by rw [he]; exact h.global_minimum x hx⟩

/-- The constructed dual infimum has actual lower-bound and nonempty guards. -/
theorem certificate_dual_isGLB {A : Set E} {J energy : E → ℝ} {B p : ℝ} {star : E}
    (h : DualCertificate A J energy B p star) :
    IsGLB ((lagrangian J energy B p) '' A) (dualValue A J energy B p) := by
  apply isGLB_csInf (show ((lagrangian J energy B p) '' A).Nonempty from ⟨_, star, h.member, rfl⟩)
  refine ⟨J star, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact h.global_minimum x hx

/-- Finite competing dual values obey weak duality; no empty/unbounded infimum default is used. -/
theorem weak_duality {A : Set E} {J energy : E → ℝ} {B q : ℝ} {star : E}
    (h : PrimalOptimum A J energy B star) (hq : 0 ≤ q)
    (hbb : BddBelow ((lagrangian J energy B q) '' A)) :
    dualValue A J energy B q ≤ budgetValue A J energy B := by
  rw [optimum_value h]
  have hc := csInf_le hbb (show lagrangian J energy B q star ∈
      (lagrangian J energy B q) '' A from ⟨star, h.member, rfl⟩)
  have hp := mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr h.feasible)
  dsimp [dualValue, lagrangian] at *
  linarith

/-- Actual infimum dual value attains the actual primal infimum: no dual gap. -/
theorem certificate_strong_duality {A : Set E} {J energy : E → ℝ} {B p : ℝ} {star : E}
    (h : DualCertificate A J energy B p star) :
    dualValue A J energy B p = budgetValue A J energy B := by
  rw [optimum_value (certificate_primal_optimum h)]
  have hm := certificate_lagrangian_minimum h
  apply le_antisymm
  · apply csInf_le (show BddBelow ((lagrangian J energy B p) '' A) from ?_)
      (show J star ∈ (lagrangian J energy B p) '' A from ⟨star, h.member, hm.1⟩)
    refine ⟨J star, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact h.global_minimum x hx
  · apply le_csInf (show ((lagrangian J energy B p) '' A).Nonempty from ⟨_, star, h.member, rfl⟩)
    rintro r ⟨x, hx, rfl⟩
    exact h.global_minimum x hx

/-- Any earned dual certificate supplies an actual budget value support bound. -/
theorem certificate_value_support {A : Set E} {J energy : E → ℝ} {B p T : ℝ} {star : E}
    (h : DualCertificate A J energy B p star) (hne : (feasibleCosts A J energy T).Nonempty) :
    budgetValue A J energy B - p*(T-B) ≤ budgetValue A J energy T := by
  rw [optimum_value (certificate_primal_optimum h)]
  apply le_csInf hne
  rintro r ⟨x, hx, he, rfl⟩
  have hg := h.global_minimum x hx
  have hp := mul_le_mul_of_nonneg_left he h.nonnegative
  nlinarith

/-- Every dual price agrees with the derivative when that actual derivative exists. -/
theorem certificate_price_identification {A : Set E} {J energy : E → ℝ} {B p d lo hi : ℝ} {star : E}
    (h : DualCertificate A J energy B p star) (hB : B ∈ Ioo lo hi)
    (hne : ∀ T ∈ Ioo lo hi, (feasibleCosts A J energy T).Nonempty)
    (hd : HasDerivAt (budgetValue A J energy) d B) : p = -d := by
  have hm : IsLocalMin (fun T => budgetValue A J energy T+p*T) B := by
    filter_upwards [isOpen_Ioo.mem_nhds hB] with T hT
    have hs := certificate_value_support h (hne T hT)
    linarith
  have hz := hm.hasDerivAt_eq_zero (hd.add ((hasDerivAt_id B).const_mul p))
  linarith

end
end SbtCosmo.Derivation.ConvexClosurePrice
