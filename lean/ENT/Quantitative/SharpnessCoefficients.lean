module

public import ENT.Basic.Coefficients
public import ENT.Basic.ProjectionConvolution
public import ENT.Basic.ProjectionDensity
public import ENT.Entropy.LawInvariance
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.FieldSimp

/-! The explicit nonflat directions used for the upper bound on the optimal
stability coefficient. The density and entropy statements concern the actual
continuous-uniform projection laws, including the zero final coefficient. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ENT.Quantitative
noncomputable section

/-- In dimension `m + 1`, retain the normalized diagonal in the first `m`
coordinates and set the last coefficient to zero. -/
def oneZeroCoefficients (m : ℕ) : Fin (m + 1) → ℝ :=
  Fin.snoc (diagonal m) 0

@[simp] theorem oneZeroCoefficients_castSucc (m : ℕ) (i : Fin m) :
    oneZeroCoefficients m i.castSucc = diagonal m i := by
  simp [oneZeroCoefficients]

@[simp] theorem oneZeroCoefficients_last (m : ℕ) :
    oneZeroCoefficients m (Fin.last m) = 0 := by
  simp [oneZeroCoefficients]

theorem oneZeroCoefficients_isUnit {m : ℕ} (hm : 0 < m) :
    IsUnit (oneZeroCoefficients m) := by
  simpa [IsUnit, Fin.sum_univ_castSucc] using isUnit_diagonal hm

theorem oneZeroCoefficients_not_isDiagonal {m : ℕ} :
    ¬ IsDiagonal (oneZeroCoefficients m) := by
  intro h
  have hlast := h (Fin.last m)
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  have hz : (0 : ℝ) = (m + 1 : ℝ)⁻¹ := by
    simpa only [oneZeroCoefficients_last, zero_pow (by decide : 2 ≠ 0),
      Nat.cast_add, Nat.cast_one] using hlast
  exact (inv_ne_zero hm) hz.symm

theorem oneZeroCoefficients_deficit {m : ℕ} (hm : 0 < m) :
    deficit (oneZeroCoefficients m) = 1 / ((m : ℝ) * (m + 1 : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
  rw [deficit_eq_sum_pow_four_sub_inv (by omega) (oneZeroCoefficients_isUnit hm)]
  rw [Fin.sum_univ_castSucc]
  simp only [oneZeroCoefficients_castSucc, oneZeroCoefficients_last,
    zero_pow (by decide : 4 ≠ 0), add_zero]
  have hfour : ∀ i : Fin m, (diagonal m i) ^ 4 = ((m : ℝ)⁻¹) ^ 2 := by
    intro i
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, diagonal_sq]
  simp only [hfour, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

theorem oneZeroCoefficients_deficit_pos {m : ℕ} (hm : 0 < m) :
    0 < deficit (oneZeroCoefficients m) := by
  rw [oneZeroCoefficients_deficit hm]
  positivity

theorem projectionLaw_snoc_zero {m : ℕ} (a : Fin m → ℝ) :
    projectionLaw (Fin.snoc a 0) = projectionLaw a := by
  rw [projectionLaw_eq_conv_remove (Fin.snoc a 0) (Fin.last m)]
  have hrem : removeCoefficient (Fin.snoc a 0) (Fin.last m) = a := by
    funext i
    simp [removeCoefficient]
  rw [hrem]
  simp

theorem oneZeroCoefficients_law (m : ℕ) :
    projectionLaw (oneZeroCoefficients m) = projectionLaw (diagonal m) :=
  projectionLaw_snoc_zero _

/-- An entropy value defined using an actual finite-entropy density bundle. -/
def projectionEntropy {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) : ℝ :=
  (projectionFiniteEntropyDensity a ha).entropy

/-- The entropy of the normalized continuous-uniform sum. Dimension zero is
assigned zero solely to make a sequence; every semantic theorem assumes `n > 0`. -/
def diagonalEntropy (n : ℕ) : ℝ :=
  if hn : 0 < n then projectionEntropy (diagonal n) (isUnit_diagonal hn) else 0

theorem projectionEntropy_eq {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a)
    (p : FiniteEntropyDensity (projectionLaw a)) :
    projectionEntropy a ha = p.entropy :=
  (projectionFiniteEntropyDensity a ha).entropy_eq p

theorem diagonalEntropy_eq {n : ℕ} (hn : 0 < n)
    (q : FiniteEntropyDensity (projectionLaw (diagonal n))) :
    diagonalEntropy n = q.entropy := by
  rw [diagonalEntropy, dif_pos hn]
  exact projectionEntropy_eq _ _ q

theorem oneZeroCoefficients_entropy {m : ℕ} (hm : 0 < m) :
    projectionEntropy (oneZeroCoefficients m) (oneZeroCoefficients_isUnit hm) =
      diagonalEntropy m := by
  let p := projectionFiniteEntropyDensity (oneZeroCoefficients m)
    (oneZeroCoefficients_isUnit hm)
  have h := diagonalEntropy_eq hm (p.transport (oneZeroCoefficients_law m))
  change p.entropy = diagonalEntropy m
  simpa only [FiniteEntropyDensity.entropy_transport] using h.symm

theorem oneZeroCoefficients_normalized_gap {m : ℕ} (hm : 0 < m) :
    (m + 1 : ℝ) * (diagonalEntropy (m + 1) -
        projectionEntropy (oneZeroCoefficients m) (oneZeroCoefficients_isUnit hm)) /
      deficit (oneZeroCoefficients m) =
    (m + 1 : ℝ)^2 * (m : ℝ) * (diagonalEntropy (m + 1) - diagonalEntropy m) := by
  rw [oneZeroCoefficients_entropy hm, oneZeroCoefficients_deficit hm]
  simp only [div_eq_mul_inv, one_mul, inv_inv]
  ring

end
end ENT.Quantitative
