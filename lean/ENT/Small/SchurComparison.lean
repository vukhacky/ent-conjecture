module

public import ENT.Small.OcticMoments
public import ENT.Comparison.CompactBalancing
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp

/-! The manuscript's small-dimensional Schur comparison, proved by the
exact gain under pair averaging. The argument includes equal and zero
weights without dividing by their difference. -/

@[expose] public section
set_option autoImplicit false
open Set
open scoped BigOperators

namespace ENT.Small
noncomputable section
open ENT.Comparison

def powerObjective {n : ℕ} (A B C D : ℝ) (w : Fin n → ℝ) : ℝ :=
  -A * powerSum w 2 + B * powerSum w 3 + C * (powerSum w 2) ^ 2 - D * powerSum w 4

theorem simplex_pair_bounds {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ weightSimplex n) (i j : Fin n) (hij : i ≠ j) :
    w i + w j ≤ 1 ∧
      powerSum w 2 ≤ (w i + w j) ^ 2 - 2 * (w i * w j) + (1 - (w i + w j)) ^ 2 := by
  let T := (Finset.univ.erase i).erase j
  have hsum (f : Fin n → ℝ) : (∑ k ∈ T, f k) = (∑ k, f k) - f i - f j := by
    unfold T
    rw [Finset.sum_erase_eq_sub (by simp [hij.symm]),
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have hs : (∑ k ∈ T, w k) = 1 - w i - w j := by rw [hsum, hw.2]
  have hs0 : 0 ≤ ∑ k ∈ T, w k := Finset.sum_nonneg fun k _ => hw.1 k
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := T) (f := w)
    (fun k _ => hw.1 k)
  rw [hsum, hs] at hsq
  constructor
  · linarith
  · unfold powerSum
    nlinarith

theorem powerObjective_pair_gain {n : ℕ} (A B C D : ℝ) (w : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    powerObjective A B C D (balanceWeights w i j) - powerObjective A B C D w =
      (w i - w j) ^ 2 / 4 *
        (2 * A - 3 * B * (w i + w j) - 4 * C * powerSum w 2 +
          3 * D * (w i + w j) ^ 2 + (C + D / 2) * (w i - w j) ^ 2) := by
  unfold powerObjective powerSum
  rw [sum_apply_balanceWeights w i j hij (fun x => x ^ 2),
    sum_apply_balanceWeights w i j hij (fun x => x ^ 3),
    sum_apply_balanceWeights w i j hij (fun x => x ^ 4)]
  ring

theorem pair_gain_bracket_nonneg {A B C D x y p : ℝ}
    (hC : 0 ≤ C) (hDC : D ≤ 2 * C)
    (hA0 : 4 * C ≤ 2 * A) (hA1 : 3 * B + 4 * C - 4 * D ≤ 2 * A)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1)
    (hp : p ≤ (x + y) ^ 2 - 2 * (x * y) + (1 - (x + y)) ^ 2) :
    0 ≤ 2 * A - 3 * B * (x + y) - 4 * C * p +
      3 * D * (x + y) ^ 2 + (C + D / 2) * (x - y) ^ 2 := by
  have hs0 : 0 ≤ x + y := add_nonneg hx hy
  have hs1 : 0 ≤ 1 - (x + y) := sub_nonneg.mpr hxy
  have hM0 : 0 ≤ 2 * A - 4 * C := sub_nonneg.mpr hA0
  have hM1 : 0 ≤ 2 * A - (3 * B + 4 * C - 4 * D) := sub_nonneg.mpr hA1
  have hcoeff : 0 ≤ 8 * C - 4 * D := by linarith
  have hcoeff2 : 0 ≤ C - D / 2 := by linarith
  have hdiff : 0 ≤ (x + y) ^ 2 - 2 * (x * y) + (1 - (x + y)) ^ 2 - p :=
    sub_nonneg.mpr hp
  calc
    _ = (1 - (x + y)) * (2 * A - 4 * C) +
        (x + y) * (2 * A - (3 * B + 4 * C - 4 * D)) +
        (8 * C - 4 * D) * ((x + y) * (1 - (x + y)) + x * y) +
        (C - D / 2) * (x - y) ^ 2 +
        4 * C * ((x + y) ^ 2 - 2 * (x * y) + (1 - (x + y)) ^ 2 - p) := by ring
    _ ≥ 0 := by positivity

theorem powerObjective_pair_balancing {n : ℕ} {A B C D : ℝ}
    (hC : 0 ≤ C) (hDC : D ≤ 2 * C)
    (hA0 : 4 * C ≤ 2 * A) (hA1 : 3 * B + 4 * C - 4 * D ≤ 2 * A)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) (i j : Fin n) (hij : i ≠ j) :
    powerObjective A B C D w ≤ powerObjective A B C D (balanceWeights w i j) := by
  apply sub_nonneg.mp
  rw [powerObjective_pair_gain A B C D w i j hij]
  have hb := simplex_pair_bounds hw i j hij
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (pair_gain_bracket_nonneg hC hDC hA0 hA1 (hw.1 i) (hw.1 j) hb.1 hb.2)

theorem powerObjective_le_flat {n : ℕ} (hn : 0 < n) {A B C D : ℝ}
    (hC : 0 ≤ C) (hDC : D ≤ 2 * C)
    (hA0 : 4 * C ≤ 2 * A) (hA1 : 3 * B + 4 * C - 4 * D ≤ 2 * A)
    (w : Fin n → ℝ) (hw : w ∈ weightSimplex n) :
    powerObjective A B C D w ≤ powerObjective A B C D (flatWeights n) := by
  apply le_flat_of_pair_balancing hn (powerObjective A B C D) _
    (powerObjective_pair_balancing hC hDC hA0 hA1) w hw
  apply Continuous.continuousOn
  unfold powerObjective powerSum
  fun_prop

def octicA (c₂ c₃ c₄ : ℝ) : ℝ := (6 / 5 : ℝ) * c₂ + 18 * c₃ + 252 * c₄
def octicB (c₃ c₄ : ℝ) : ℝ := (48 / 7 : ℝ) * c₃ + 192 * c₄
def octicC (c₄ : ℝ) : ℝ := (252 / 5 : ℝ) * c₄
def octicD (c₄ : ℝ) : ℝ := (432 / 5 : ℝ) * c₄

theorem powerSum_flat_two {n : ℕ} (hn : 0 < n) :
    powerSum (flatWeights n) 2 = (n : ℝ)⁻¹ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [powerSum, flatWeights, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The octic moment comparison from the manuscript's Schur criterion.
The proof uses exact pair gains and compactness, including boundary weights. -/
theorem small_schur_moment_comparison {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) (c₁ c₂ c₃ c₄ lam : ℝ)
    (hD : 0 < octicD c₄) (hDC : octicD c₄ < 2 * octicC c₄)
    (hA0 : 4 * octicC c₄ ≤ 2 * (octicA c₂ c₃ c₄ - lam))
    (hA1 : 3 * octicB c₃ c₄ + 4 * octicC c₄ - 4 * octicD c₄ ≤
      2 * (octicA c₂ c₃ c₄ - lam)) :
    lam * deficit a ≤
      (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw (diagonal n)) -
      (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw a) := by
  have hC : 0 ≤ octicC c₄ := by linarith
  have hw : (fun i => (a i) ^ 2) ∈ weightSimplex n := ⟨fun i => sq_nonneg _, ha⟩
  have h := powerObjective_le_flat hn hC hDC.le hA0 hA1 _ hw
  have hobj (w : Fin n → ℝ) :
      powerObjective (octicA c₂ c₃ c₄ - lam) (octicB c₃ c₄) (octicC c₄) (octicD c₄) w =
        octicWeightExpression c₁ c₂ c₃ c₄ w - (c₁ + 3 * c₂ + 15 * c₃ + 105 * c₄) +
          lam * powerSum w 2 := by
    unfold powerObjective octicWeightExpression octicA octicB octicC octicD
    ring
  rw [hobj, hobj, powerSum_flat_two hn] at h
  have hdiag : (fun i : Fin n => (diagonal n i) ^ 2) = flatWeights n :=
    funext (diagonal_sq n)
  rw [octicPolynomial_expectation _ (isUnit_diagonal hn),
    octicPolynomial_expectation a ha, hdiag]
  have hdef : deficit a = powerSum (fun i => (a i) ^ 2) 2 - (n : ℝ)⁻¹ := by
    rw [deficit_eq_sum_pow_four_sub_inv hn ha]
    simp only [powerSum, ← pow_mul]
  rw [hdef]
  linarith

end
end ENT.Small
