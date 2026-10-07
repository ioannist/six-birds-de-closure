import SbtCosmo.Derivation.BackgroundSelection
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
The actual eight-site Step26 cycle Hamiltonian on real fields. This file
constructs exact ground-state fixed points for every constant background and
every real coupling. It proves positivity of every normalized nonnegative
eigenvector, and distinguishes fixed points from stability under relaxation.
The all-background selector and Brouwer construction are mechanized in the
downstream GroundSelector, GroundFixedPoint and GroundComplex modules.
-/
namespace SbtCosmo.Derivation.GroundState

noncomputable section

open scoped BigOperators

abbrev Field := Fin 8 → ℝ

def next (i : Fin 8) : Fin 8 := i + 1
def prev (i : Fin 8) : Fin 8 := i + 7

def gradient (u : Field) (i : Fin 8) : ℝ := (u (next i) - u (prev i)) / 2

def hamiltonian (v u : Field) (i : Fin 8) : ℝ :=
  (1 + v i) * u i - (u (prev i) + u (next i)) / 2

def normSq (u : Field) : ℝ := ∑ i, (u i) ^ 2
def energy (v u : Field) : ℝ := ∑ i, u i * hamiltonian v u i
def kineticEnergy (u : Field) : ℝ := (∑ i, (u (next i) - u i) ^ 2) / 2

def sourcePotential (b : Field) (κ : ℝ) (u : Field) : Field := fun i =>
  BackgroundSelection.potential (b i) κ ((u i) ^ 2) ((gradient u i) ^ 2)

def IsGround (v u : Field) (e : ℝ) : Prop :=
  normSq u = 1 ∧ (∀ i, hamiltonian v u i = e * u i) ∧
    ∀ w : Field, e * normSq w ≤ energy v w

def IsSelfConsistentGround (b : Field) (κ : ℝ) (u : Field) : Prop :=
  ∃ e, IsGround (sourcePotential b κ u) u e

/-- Direct finite sum identity for the original cycle, including the wrap edge. -/
theorem energy_identity (v u : Field) :
    energy v u = kineticEnergy u + ∑ i, v i * (u i) ^ 2 := by
  simp [energy, kineticEnergy, hamiltonian, next, prev, Fin.sum_univ_succ]
  ring

theorem kineticEnergy_nonneg (u : Field) : 0 ≤ kineticEnergy u := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)

theorem constant_potential_lower_bound (c : ℝ) (u : Field) :
    c * normSq u ≤ energy (fun _ => c) u := by
  rw [energy_identity]
  have he : (∑ i : Fin 8, c * (u i) ^ 2) = c * normSq u := by
    simp [normSq, Finset.mul_sum]
  rw [he]
  linarith [kineticEnergy_nonneg u]

def uniform : Field := fun _ => Real.sqrt (1 / 8)

theorem uniform_positive (i : Fin 8) : 0 < uniform i := by
  exact Real.sqrt_pos.2 (by norm_num)

theorem uniform_sq (i : Fin 8) : (uniform i) ^ 2 = 1 / 8 := by
  exact Real.sq_sqrt (by norm_num)

theorem uniform_normalized : normSq uniform = 1 := by
  simp [normSq, uniform_sq]

theorem uniform_gradient (i : Fin 8) : gradient uniform i = 0 := by
  simp [gradient, uniform]

theorem constant_source_potential (b κ : ℝ) :
    sourcePotential (fun _ => b) κ uniform = fun _ => b + κ * b / 8 := by
  funext i
  simp [sourcePotential, BackgroundSelection.potential, uniform_gradient, uniform_sq]
  ring

theorem uniform_eigen (c : ℝ) (i : Fin 8) :
    hamiltonian (fun _ => c) uniform i = c * uniform i := by
  simp [hamiltonian, uniform]
  ring

theorem uniform_ground (c : ℝ) : IsGround (fun _ => c) uniform c := by
  exact ⟨uniform_normalized, uniform_eigen c, constant_potential_lower_bound c⟩

/-- All real backgrounds and couplings in this constructed constant sector. -/
theorem constant_background_fixed_point (b κ : ℝ) :
    IsSelfConsistentGround (fun _ => b) κ uniform := by
  refine ⟨b + κ * b / 8, ?_⟩
  rw [constant_source_potential]
  exact uniform_ground _

/-- There is no existence boundary in this sector, even at negative coupling. -/
theorem all_constant_parameters_admitted :
    ∀ b κ : ℝ, ∃ u : Field, IsSelfConsistentGround (fun _ => b) κ u := by
  exact fun b κ => ⟨uniform, constant_background_fixed_point b κ⟩

/-- Existence of a self-consistent ground state cannot select the background. -/
theorem constant_background_no_forced_value (κ : ℝ) :
    ¬ ∃ c : ℝ, BackgroundSelection.ForcesValue
      (fun b : ℝ => IsSelfConsistentGround (fun _ => b) κ uniform) (fun b => b) c := by
  apply BackgroundSelection.two_admitted_values_not_forced
    (fun b : ℝ => IsSelfConsistentGround (fun _ => b) κ uniform) (fun b => b)
    (constant_background_fixed_point 0 κ) (constant_background_fixed_point 1 κ)
  norm_num

theorem zero_entry_forces_next_zero {v u : Field} {e : ℝ}
    (hn : ∀ j, 0 ≤ u j) (he : ∀ j, hamiltonian v u j = e * u j)
    {i : Fin 8} (hi : u i = 0) : u (next i) = 0 := by
  have h := he i
  simp only [hamiltonian, hi, mul_zero, zero_sub] at h
  have hp := hn (prev i)
  have hq := hn (next i)
  linarith

/-- Connectivity of the actual eight-site cycle, with no sign assumptions on v. -/
theorem nonnegative_eigen_zero_forces_all_zero {v u : Field} {e : ℝ}
    (hn : ∀ j, 0 ≤ u j) (he : ∀ j, hamiltonian v u j = e * u j)
    {i : Fin 8} (hi : u i = 0) : ∀ j, u j = 0 := by
  have h0 : u (i + 0) = 0 := by simpa using hi
  have h1 : u (i + 1) = 0 := by simpa [next] using zero_entry_forces_next_zero hn he hi
  have h2 : u (i + 2) = 0 := by
    simpa [next, add_assoc] using zero_entry_forces_next_zero hn he h1
  have h3 : u (i + 3) = 0 := by
    simpa [next, add_assoc] using zero_entry_forces_next_zero hn he h2
  have h4 : u (i + 4) = 0 := by
    simpa [next, add_assoc] using zero_entry_forces_next_zero hn he h3
  have h5 : u (i + 5) = 0 := by
    simpa [next, add_assoc] using zero_entry_forces_next_zero hn he h4
  have h6 : u (i + 6) = 0 := by
    simpa [next, add_assoc] using zero_entry_forces_next_zero hn he h5
  have h7 : u (i + 7) = 0 := by
    simpa [next, add_assoc] using zero_entry_forces_next_zero hn he h6
  have hall : ∀ k : Fin 8, u (i + k) = 0 := by
    intro k
    fin_cases k <;> assumption
  intro j
  simpa using hall (j - i)

theorem normalized_nonnegative_eigen_positive {v u : Field} {e : ℝ}
    (hn : ∀ j, 0 ≤ u j) (he : ∀ j, hamiltonian v u j = e * u j)
    (hu : normSq u = 1) : ∀ j, 0 < u j := by
  intro j
  by_contra h
  have hj : u j = 0 := le_antisymm (le_of_not_gt h) (hn j)
  have hz := nonnegative_eigen_zero_forces_all_zero hn he hj
  have : normSq u = 0 := by simp [normSq, hz]
  linarith

def relaxed (f : Field → Field) (m : ℝ) (u : Field) : Field :=
  fun i => (1 - m) * u i + m * f u i

/-- The affine relaxation before native normalization preserves all fixed points. -/
theorem relaxed_fixed_iff (f : Field → Field) {m : ℝ} (hm : m ≠ 0) (u : Field) :
    relaxed f m u = u ↔ f u = u := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    change (1 - m) * u i + m * f u i = u i at hi
    have hz : m * (f u i - u i) = 0 := by nlinarith
    have := (mul_eq_zero.mp hz).resolve_left hm
    linarith
  · intro h
    funext i
    simp only [relaxed, h]
    ring

def normalizedRelaxed (f : Field → Field) (m : ℝ) (u : Field) : Field :=
  fun i => relaxed f m u i / Real.sqrt (normSq (relaxed f m u))

/-- The actual normalization does not destroy an existing unit fixed point. -/
theorem normalizedRelaxed_fixes (f : Field → Field) (m : ℝ) {u : Field}
    (hf : f u = u) (hu : normSq u = 1) : normalizedRelaxed f m u = u := by
  have hr : relaxed f m u = u := by
    funext i
    simp only [relaxed, hf]
    ring
  funext i
  simp [normalizedRelaxed, hr, hu]

/-- A real tangent eigenvalue is shifted by damping; this is a scalar law. -/
theorem relaxed_real_mode_stable_iff {m t : ℝ} (hm : 0 < m) :
    |(1 - m) + m * t| < 1 ↔ 1 - 2 / m < t ∧ t < 1 := by
  rw [abs_lt]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · have hd : (1 - 2 / m) * m = m - 2 := by field_simp
      have hp : (1 - 2 / m) * m < t * m := by nlinarith
      nlinarith
    · nlinarith
  · rintro ⟨hl, hu⟩
    have hp := mul_lt_mul_of_pos_right hl hm
    have hd : (1 - 2 / m) * m = m - 2 := by field_simp
    constructor <;> nlinarith

theorem unstable_mode_stabilized_by_damping :
    ¬ |(-2 : ℝ)| < 1 ∧ |(1 - (1 / 2 : ℝ)) + (1 / 2 : ℝ) * (-2)| < 1 := by
  norm_num

end
end SbtCosmo.Derivation.GroundState
