import SbtCosmo.Derivation.GroundParameterTube

/-! The nine-coordinate product sup norm used by the actual root certificates.
Coordinate matrices return to continuous linear maps on Field times energy;
row sums bound that actual operator norm, with no norm substitution. -/
namespace SbtCosmo.Derivation.GroundPointCoordinates
noncomputable section
set_option maxHeartbeats 2000000
open GroundState GroundBorder GroundRootCertificate
open scoped BigOperators

abbrev Vector := Fin 9 → ℝ
def coord (x : Point) : Vector := Fin.lastCases x.2 x.1
def fromCoord (v : Vector) : Point := (fun i => v i.castSucc, v (Fin.last 8))
def column (j : Fin 9) : Point := fromCoord (Pi.single j 1)

theorem coord_fromCoord (v : Vector) : coord (fromCoord v) = v := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp only [coord, fromCoord, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fromCoord_coord (x : Point) : fromCoord (coord x) = x := by
  apply Prod.ext <;> simp only [coord, fromCoord, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem coord_norm_le (x : Point) (j : Fin 9) : |coord x j| ≤ ‖x‖ := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [coord, Fin.lastCases_last, Prod.norm_def, Real.norm_eq_abs] using le_max_right ‖x.1‖ ‖x.2‖
  · have hi : |coord x i.castSucc| ≤ ‖x.1‖ := by
      simpa only [coord, Fin.lastCases_castSucc, Real.norm_eq_abs] using norm_le_pi_norm x.1 i
    exact hi.trans
      (by rw [Prod.norm_def]; exact le_max_left _ _)

theorem norm_le_coordinates {x : Point} {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ j, |coord x j| ≤ q) : ‖x‖ ≤ q := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg hq).mpr
    intro i
    simpa only [coord, Fin.lastCases_castSucc, Real.norm_eq_abs] using h i.castSucc
  · simpa only [coord, Fin.lastCases_last, Real.norm_eq_abs] using h (Fin.last 8)

theorem coord_column (i j : Fin 9) : coord (column j) i = if i = j then 1 else 0 := by
  simp [column, coord_fromCoord, Pi.single_apply]

theorem coord_sum (s : Finset (Fin 9)) (f : Fin 9 → Point) (j : Fin 9) :
    coord (∑ i ∈ s, f i) j = ∑ i ∈ s, coord (f i) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp only [coord, Fin.lastCases_last, Fin.lastCases_castSucc, Prod.fst_sum,
      Prod.snd_sum, Finset.sum_apply]

theorem coord_smul (c : ℝ) (x : Point) (j : Fin 9) : coord (c • x) j = c * coord x j := by
  refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp only [coord, Fin.lastCases_last, Fin.lastCases_castSucc, Prod.smul_fst,
      Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem coord_add (x y : Point) (j : Fin 9) : coord (x+y) j = coord x j + coord y j := by
  refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp only [coord, Fin.lastCases_last, Fin.lastCases_castSucc, Prod.fst_add, Prod.snd_add, Pi.add_apply]

theorem coord_sub (x y : Point) (j : Fin 9) : coord (x-y) j = coord x j - coord y j := by
  refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp only [coord, Fin.lastCases_last, Fin.lastCases_castSucc, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]

theorem point_expansion (x : Point) : x = ∑ j, coord x j • column j := by
  apply_fun coord
  · funext i
    simp only [coord_sum, coord_smul, coord_column]
    simp
  · intro x y h
    exact (fromCoord_coord x).symm.trans ((congrArg fromCoord h).trans (fromCoord_coord y))

theorem linear_action_entries (L : Point →L[ℝ] Point) (x : Point) (i : Fin 9) :
    coord (L x) i = ∑ j, coord (L (column j)) i * coord x j := by
  conv_lhs => rw [point_expansion x]
  simp only [map_sum, map_smul, coord_sum, coord_smul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem operator_norm_le_rows (L : Point →L[ℝ] Point) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ i, (∑ j, |coord (L (column j)) i|) ≤ q) : ‖L‖ ≤ q := by
  apply L.opNorm_le_bound hq
  intro x
  apply norm_le_coordinates (mul_nonneg hq (norm_nonneg x))
  intro i
  rw [linear_action_entries]
  calc
    |∑ j, coord (L (column j)) i * coord x j| ≤ ∑ j, |coord (L (column j)) i * coord x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |coord (L (column j)) i| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (coord_norm_le x j) (abs_nonneg _)
    _ = (∑ j, |coord (L (column j)) i|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ q * ‖x‖ := mul_le_mul_of_nonneg_right (h i) (norm_nonneg x)

def matrixLM (A : Matrix (Fin 9) (Fin 9) ℝ) : Point →ₗ[ℝ] Point where
  toFun x := ∑ j, coord x j • fromCoord (fun i => A i j)
  map_add' x y := by
    simp only [coord_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [coord_smul, mul_smul, Finset.smul_sum, RingHom.id_apply]

def matrixMap (A : Matrix (Fin 9) (Fin 9) ℝ) : Point →L[ℝ] Point :=
  (matrixLM A).toContinuousLinearMap

theorem matrixMap_apply (A : Matrix (Fin 9) (Fin 9) ℝ) (x : Point) (i : Fin 9) :
    coord (matrixMap A x) i = ∑ j, A i j * coord x j := by
  change coord (∑ j, coord x j • fromCoord (fun i => A i j)) i = _
  simp only [coord_sum, coord_smul, coord_fromCoord]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end SbtCosmo.Derivation.GroundPointCoordinates
