import SbtCosmo.Derivation.GroundFixedPoint
import SbtCosmo.Derivation.GroundSimple

/-! The positive real fixed point returns to the original complex field domain. -/
namespace SbtCosmo.Derivation.GroundState

noncomputable section
open scoped BigOperators

abbrev ComplexField := Fin 8 → ℂ

def realEmbed (u : Field) : ComplexField := fun i => (u i : ℂ)
def complexGradient (z : ComplexField) (i : Fin 8) : ℂ :=
  (z (next i) - z (prev i)) / 2
def complexHamiltonian (v : Field) (z : ComplexField) (i : Fin 8) : ℂ :=
  (1 + (v i : ℂ)) * z i - (z (prev i) + z (next i)) / 2
def complexNormSq (z : ComplexField) : ℝ := ∑ i, Complex.normSq (z i)
def complexEnergy (v : Field) (z : ComplexField) : ℝ :=
  (∑ i, star (z i) * complexHamiltonian v z i).re
def complexSourcePotential (b : Field) (κ : ℝ) (z : ComplexField) : Field := fun i =>
  BackgroundSelection.potential (b i) κ (Complex.normSq (z i)) (Complex.normSq (complexGradient z i))

theorem complexHamiltonian_re (v : Field) (z : ComplexField) (i : Fin 8) :
    (complexHamiltonian v z i).re = hamiltonian v (fun j => (z j).re) i := by
  simp [complexHamiltonian, hamiltonian]

theorem complexHamiltonian_im (v : Field) (z : ComplexField) (i : Fin 8) :
    (complexHamiltonian v z i).im = hamiltonian v (fun j => (z j).im) i := by
  simp [complexHamiltonian, hamiltonian]

theorem complexNormSq_split (z : ComplexField) :
    complexNormSq z = normSq (fun i => (z i).re) + normSq (fun i => (z i).im) := by
  simp [complexNormSq, normSq, Complex.normSq_apply, pow_two, Finset.sum_add_distrib]

theorem complexEnergy_split (v : Field) (z : ComplexField) :
    complexEnergy v z = energy v (fun i => (z i).re) + energy v (fun i => (z i).im) := by
  simp [complexEnergy, energy, Complex.mul_re, complexHamiltonian_re,
    complexHamiltonian_im, Finset.sum_add_distrib]

/-- Real ground minimality controls every complex competitor, not only real tests. -/
theorem complex_ground_lower_bound {v u : Field} {e : ℝ}
    (hg : IsGround v u e) (z : ComplexField) : e * complexNormSq z ≤ complexEnergy v z := by
  rw [complexNormSq_split, complexEnergy_split, mul_add]
  exact add_le_add (hg.2.2 _) (hg.2.2 _)

theorem realEmbed_normalized {u : Field} (hu : normSq u = 1) : complexNormSq (realEmbed u) = 1 := by
  simpa [complexNormSq, realEmbed, Complex.normSq_apply, normSq, pow_two] using hu

theorem realEmbed_eigen {v u : Field} {e : ℝ} (hg : IsGround v u e) (i : Fin 8) :
    complexHamiltonian v (realEmbed u) i = (e : ℂ) * realEmbed u i := by
  apply Complex.ext
  · simpa [complexHamiltonian_re, realEmbed] using hg.2.1 i
  · simp [complexHamiltonian_im, realEmbed, hamiltonian]

theorem complexSourcePotential_realEmbed (b : Field) (κ : ℝ) (u : Field) :
    complexSourcePotential b κ (realEmbed u) = sourcePotential b κ u := by
  funext i
  simp [complexSourcePotential, sourcePotential, complexGradient, gradient, realEmbed,
    Complex.normSq_apply, BackgroundSelection.potential, pow_two]
  left
  ring

/-- Complexification introduces no additional lowest-eigenvalue directions. -/
theorem complex_lowest_eigen_span {v u : Field} {e : ℝ} (hg : IsGround v u e)
    {z : ComplexField}
    (hz : ∀ i, complexHamiltonian v z i = (e : ℂ) * z i) :
    ∃ c : ℂ, z = fun i => c * realEmbed u i := by
  have hre : ∀ i, hamiltonian v (fun j => (z j).re) i = e * (z i).re := by
    intro i
    simpa [complexHamiltonian_re] using congrArg Complex.re (hz i)
  have him : ∀ i, hamiltonian v (fun j => (z j).im) i = e * (z i).im := by
    intro i
    simpa [complexHamiltonian_im] using congrArg Complex.im (hz i)
  obtain ⟨a, ha⟩ := real_lowest_eigen_span hg hre
  obtain ⟨b, hb⟩ := real_lowest_eigen_span hg him
  refine ⟨⟨a, b⟩, ?_⟩
  funext i
  apply Complex.ext
  · simpa [realEmbed] using congrFun ha i
  · simpa [realEmbed] using congrFun hb i

/-- Exact self-consistency and ground energy in the native complex domain. -/
theorem exists_native_complex_ground (b : Field) (κ : ℝ) :
    ∃ z : ComplexField, complexNormSq z = 1 ∧
      ∃ e : ℝ, (∀ i, complexHamiltonian (complexSourcePotential b κ z) z i = (e : ℂ) * z i) ∧
        ∀ w : ComplexField, e * complexNormSq w ≤ complexEnergy (complexSourcePotential b κ z) w := by
  obtain ⟨u, _, e, hg⟩ := exists_selfConsistent_ground b κ
  refine ⟨realEmbed u, realEmbed_normalized hg.1, e, ?_, ?_⟩
  · intro i
    rw [complexSourcePotential_realEmbed]
    exact realEmbed_eigen hg i
  · intro w
    rw [complexSourcePotential_realEmbed]
    exact complex_ground_lower_bound hg w

end
end SbtCosmo.Derivation.GroundState
