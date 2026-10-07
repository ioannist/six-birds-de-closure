import SbtCosmo.Derivation.GroundState
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Maps.Proper.Basic

/-!
Construction of the positive ground vector of the actual eight-site Hamiltonian
for every supplied potential. This is the linear spectral child needed by the
nonlinear fixed-point theorem; a self-consistent vector is not assumed here.
-/
namespace SbtCosmo.Derivation.GroundState

noncomputable section
open scoped BigOperators

def unitFields : Set Field := {u | normSq u = 1}

theorem normSq_abs (u : Field) : normSq (fun i => |u i|) = normSq u := by
  simp [normSq]

theorem abs_edge_energy_le (a b : ℝ) : (|a| - |b|) ^ 2 ≤ (a - b) ^ 2 := by
  have h : a * b ≤ |a| * |b| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [sq_abs a, sq_abs b]

theorem energy_abs_le (v u : Field) : energy v (fun i => |u i|) ≤ energy v u := by
  rw [energy_identity, energy_identity]
  simp only [sq_abs]
  apply add_le_add
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => abs_edge_energy_le (u (next i)) (u i)) (by norm_num)
  · exact le_rfl

theorem normSq_homogeneous (u : Field) (c : ℝ) :
    normSq (fun i => c * u i) = c ^ 2 * normSq u := by
  simp [normSq, mul_pow, Finset.mul_sum]

theorem energy_homogeneous (v u : Field) (c : ℝ) :
    energy v (fun i => c * u i) = c ^ 2 * energy v u := by
  simp [energy, hamiltonian, next, prev, Fin.sum_univ_succ]
  ring

theorem normSq_nonneg (u : Field) : 0 ≤ normSq u := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem normSq_zero_iff (u : Field) : normSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    have hs : (u i) ^ 2 ≤ normSq u :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    have : (u i) ^ 2 = 0 := le_antisymm (hs.trans_eq h) (sq_nonneg _)
    simpa using this
  · intro h
    simp [h, normSq]

theorem continuous_normSq : Continuous normSq := by
  unfold normSq
  fun_prop

theorem continuous_energy (v : Field) : Continuous (energy v) := by
  unfold energy hamiltonian
  fun_prop

theorem unitFields_compact : IsCompact unitFields := by
  have hc : IsClosed unitFields := isClosed_eq continuous_normSq continuous_const
  apply (isCompact_closedBall (0 : Field) 1).of_isClosed_subset hc
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  have hs : (u i) ^ 2 ≤ normSq u :=
    Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  change normSq u = 1 at hu
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (u i), abs_nonneg (u i)]

theorem unitFields_nonempty : unitFields.Nonempty := ⟨uniform, uniform_normalized⟩

theorem exists_nonnegative_minimizer (v : Field) :
    ∃ u : Field, normSq u = 1 ∧ (∀ i, 0 ≤ u i) ∧ IsMinOn (energy v) unitFields u := by
  obtain ⟨u, hu, hm⟩ := unitFields_compact.exists_isMinOn
    unitFields_nonempty (continuous_energy v).continuousOn
  refine ⟨fun i => |u i|, ?_, fun i => abs_nonneg (u i), ?_⟩
  · exact (normSq_abs u).trans hu
  · intro w hw
    exact (energy_abs_le v u).trans (hm hw)

def nativeMatrix (v : Field) : Matrix (Fin 8) (Fin 8) ℝ := fun i j =>
  if i = j then 1 + v i else if j = prev i ∨ j = next i then -1 / 2 else 0

theorem nativeMatrix_mulVec (v u : Field) : (nativeMatrix v).mulVec u = hamiltonian v u := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, nativeMatrix, hamiltonian, next, prev, Fin.sum_univ_succ] <;>
    ring

theorem nativeMatrix_hermitian (v : Field) : (nativeMatrix v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeMatrix, Matrix.conjTranspose_apply, next, prev]

abbrev EuclideanField := EuclideanSpace ℝ (Fin 8)

def nativeOperator (v : Field) : EuclideanField →L[ℝ] EuclideanField :=
  (Matrix.toEuclideanLin (nativeMatrix v)).toContinuousLinearMap

theorem nativeOperator_selfAdjoint (v : Field) : IsSelfAdjoint (nativeOperator v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isHermitian_iff_isSymmetric.mp (nativeMatrix_hermitian v)

theorem euclidean_normSq (u : EuclideanField) : ‖u‖ ^ 2 = normSq u.ofLp := by
  simp [PiLp.norm_sq_eq_of_L2, normSq, Real.norm_eq_abs]

theorem nativeOperator_energy (v : Field) (u : EuclideanField) :
    (nativeOperator v).reApplyInnerSelf u = energy v u.ofLp := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, nativeOperator,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct,
    nativeMatrix_mulVec, RCLike.re_to_real, star_trivial]
  rfl

theorem minimizer_eigen {v u : Field} (hu : normSq u = 1)
    (hm : IsMinOn (energy v) unitFields u) :
    ∀ i, hamiltonian v u i = energy v u * u i := by
  let x : EuclideanField := WithLp.toLp 2 u
  have hx : ‖x‖ = 1 := by
    have hs : ‖x‖ ^ 2 = 1 := by simpa [x, euclidean_normSq] using hu
    nlinarith [norm_nonneg x]
  have hmin : IsMinOn (nativeOperator v).reApplyInnerSelf (Metric.sphere 0 ‖x‖) x := by
    intro y hy
    change (nativeOperator v).reApplyInnerSelf x ≤ (nativeOperator v).reApplyInnerSelf y
    rw [nativeOperator_energy, nativeOperator_energy]
    apply hm
    change normSq y.ofLp = 1
    rw [← euclidean_normSq]
    have hy' : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right, hx] using hy
    rw [hy']
    norm_num
  have he := (nativeOperator_selfAdjoint v).eq_smul_self_of_isLocalExtrOn (Or.inl hmin.localize)
  have hq : (nativeOperator v).rayleighQuotient x = energy v u := by
    simp [ContinuousLinearMap.rayleighQuotient, nativeOperator_energy, x, hx]
  rw [hq] at he
  intro i
  have hi := congrArg (fun y : EuclideanField => y i) he
  simpa [nativeOperator, Matrix.toLpLin_apply, nativeMatrix_mulVec, x] using hi

theorem minimizer_lower_bound {v u : Field}
    (hm : IsMinOn (energy v) unitFields u) (w : Field) :
    energy v u * normSq w ≤ energy v w := by
  by_cases hw : w = 0
  · simp [hw, normSq, energy, hamiltonian]
  have hpos : 0 < normSq w :=
    lt_of_le_of_ne (normSq_nonneg w) (fun h => hw ((normSq_zero_iff w).mp h.symm))
  let c : ℝ := (Real.sqrt (normSq w))⁻¹
  have hs : c ^ 2 * normSq w = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hpos.le]
    exact inv_mul_cancel₀ hpos.ne'
  have hn : (fun i => c * w i) ∈ unitFields := by
    change normSq (fun i => c * w i) = 1
    rw [normSq_homogeneous, hs]
  have he := hm hn
  change energy v u ≤ energy v (fun i => c * w i) at he
  rw [energy_homogeneous] at he
  have hf := mul_le_mul_of_nonneg_right he (normSq_nonneg w)
  have hf' : c ^ 2 * energy v w * normSq w = energy v w := by
    calc
      _ = (c ^ 2 * normSq w) * energy v w := by ring
      _ = energy v w := by rw [hs, one_mul]
  rwa [hf'] at hf

/-- The positive ground witness is constructed for every supplied real potential. -/
theorem exists_positive_ground (v : Field) :
    ∃ u : Field, (∀ i, 0 < u i) ∧ IsGround v u (energy v u) := by
  obtain ⟨u, hu, hn, hm⟩ := exists_nonnegative_minimizer v
  have he := minimizer_eigen hu hm
  exact ⟨u, normalized_nonnegative_eigen_positive hn he hu,
    hu, he, minimizer_lower_bound hm⟩

theorem ground_energy {v u : Field} {e : ℝ} (hg : IsGround v u e) : energy v u = e := by
  have h : energy v u = e * normSq u := by
    unfold energy normSq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg.2.1 i]
    ring
  simpa [hg.1] using h

theorem ground_values_equal {v u w : Field} {e f : ℝ}
    (hu : IsGround v u e) (hw : IsGround v w f) : e = f := by
  have h1 := hu.2.2 w
  have h2 := hw.2.2 u
  rw [hw.1, ground_energy hw, mul_one] at h1
  rw [hu.1, ground_energy hu, mul_one] at h2
  exact le_antisymm h1 h2

/-- Minimum positive coordinate ratio and actual cycle connectivity force equality. -/
theorem positive_ground_unique {v u w : Field} {e f : ℝ}
    (hu : IsGround v u e) (hw : IsGround v w f)
    (hpu : ∀ i, 0 < u i) (hpw : ∀ i, 0 < w i) : u = w := by
  have hef := ground_values_equal hu hw
  subst f
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image
    (fun j : Fin 8 => u j / w j) Finset.univ_nonempty
  let c : ℝ := u i / w i
  let z : Field := fun j => u j - c * w j
  have hc : 0 < c := div_pos (hpu i) (hpw i)
  have hz : ∀ j, 0 ≤ z j := by
    intro j
    have hr := hi j (Finset.mem_univ j)
    have hm : c * w j ≤ u j := (le_div_iff₀ (hpw j)).mp hr
    exact sub_nonneg.mpr hm
  have hez : ∀ j, hamiltonian v z j = e * z j := by
    intro j
    have he1 := hu.2.1 j
    have he2 := hw.2.1 j
    dsimp [z, hamiltonian] at *
    linear_combination he1 - c * he2
  have hzi : z i = 0 := by
    dsimp [z, c]
    rw [div_mul_cancel₀ _ (hpw i).ne', sub_self]
  have hzall := nonnegative_eigen_zero_forces_all_zero hz hez hzi
  have hp : u = fun j => c * w j := by
    funext j
    have h := hzall j
    exact sub_eq_zero.mp h
  have hc2 : c ^ 2 = 1 := by
    have hn := hu.1
    rw [hp, normSq_homogeneous, hw.1, mul_one] at hn
    exact hn
  have hc1 : c = 1 := by nlinarith
  simpa [hc1] using hp

def positiveGround (v : Field) : Field := (exists_positive_ground v).choose

theorem positiveGround_spec (v : Field) :
    (∀ i, 0 < positiveGround v i) ∧ IsGround v (positiveGround v) (energy v (positiveGround v)) :=
  (exists_positive_ground v).choose_spec

theorem positiveGround_minimizer (v : Field) :
    IsMinOn (energy v) unitFields (positiveGround v) := by
  intro w hw
  have h := (positiveGround_spec v).2.2.2 w
  change normSq w = 1 at hw
  simpa [hw] using h

def nonnegativeUnitFields : Set Field := unitFields ∩ {u | ∀ i, 0 ≤ u i}

theorem nonnegativeUnitFields_compact : IsCompact nonnegativeUnitFields := by
  apply unitFields_compact.of_isClosed_subset
  · apply IsClosed.inter (isClosed_eq continuous_normSq continuous_const)
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (continuous_apply i)
  · exact Set.inter_subset_left

def groundSection (v : Field) : nonnegativeUnitFields :=
  ⟨positiveGround v, (positiveGround_spec v).2.1, fun i => (positiveGround_spec v).1 i |>.le⟩

theorem nonnegative_minimizer_unique {v : Field} {u : nonnegativeUnitFields}
    (hm : IsMinOn (energy v) unitFields u.val) : u = groundSection v := by
  have hn := u.property.1
  have he := minimizer_eigen hn hm
  have hg : IsGround v u.val (energy v u.val) := ⟨hn, he, minimizer_lower_bound hm⟩
  apply Subtype.ext
  exact positive_ground_unique hg (positiveGround_spec v).2
    (normalized_nonnegative_eigen_positive u.property.2 he hn) (positiveGround_spec v).1

theorem continuous_joint_energy : Continuous (fun p : Field × Field => energy p.1 p.2) := by
  unfold energy hamiltonian
  fun_prop

/-- A closed minimizing graph with compact range proves selector continuity. -/
theorem continuous_groundSection : Continuous groundSection := by
  letI : CompactSpace nonnegativeUnitFields := isCompact_iff_compactSpace.mp nonnegativeUnitFields_compact
  apply continuous_iff_isClosed.mpr
  intro C hC
  have hmin : IsClosed {p : Field × nonnegativeUnitFields |
      IsMinOn (energy p.1) unitFields p.2.val} := by
    change IsClosed {p : Field × nonnegativeUnitFields |
      ∀ w : Field, w ∈ unitFields → energy p.1 p.2.val ≤ energy p.1 w}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro w
    apply isClosed_iInter
    intro _
    apply isClosed_le
    · exact continuous_joint_energy.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    · exact continuous_joint_energy.comp (continuous_fst.prodMk continuous_const)
  have heq : groundSection ⁻¹' C = Prod.fst ''
      ({p : Field × nonnegativeUnitFields | p.2 ∈ C} ∩
        {p | IsMinOn (energy p.1) unitFields p.2.val}) := by
    ext v
    constructor
    · intro hv
      exact ⟨(v, groundSection v), ⟨hv, positiveGround_minimizer v⟩, rfl⟩
    · rintro ⟨⟨v', u⟩, ⟨huC, hm⟩, hv⟩
      change v' = v at hv
      subst v'
      change u ∈ C at huC
      have hu : u = groundSection v := nonnegative_minimizer_unique hm
      rwa [hu] at huC
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ ((hC.preimage continuous_snd).inter hmin)

theorem continuous_positiveGround : Continuous positiveGround :=
  continuous_subtype_val.comp continuous_groundSection

end
end SbtCosmo.Derivation.GroundState
