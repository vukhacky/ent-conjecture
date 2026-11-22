module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-! The unnormalized Bernstein coefficients are computed in blocks. Their coefficient identities yield the corresponding polynomial identity. -/

@[expose] public section
set_option autoImplicit false

open Polynomial
open scoped BigOperators

namespace ENT.Certificate.BlockBernstein

noncomputable section

def bernsteinPolynomial (D : ℕ) (B : List ℤ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (D + 1),
    C (B[j]?.getD 0) * X ^ j * (1 - X) ^ (D - j)

theorem coeff_one_sub_X_pow (m i : ℕ) :
    ((1 - X : Polynomial ℤ) ^ m).coeff i =
      (-1 : ℤ) ^ i * (Nat.choose m i : ℤ) := by
  induction m generalizing i with
  | zero => cases i <;> simp [Polynomial.coeff_one]
  | succ m ih =>
      cases i with
      | zero => simp [pow_succ, mul_sub, ih]
      | succ i =>
          rw [pow_succ, mul_sub, mul_one, coeff_sub, coeff_mul_X, ih, ih]
          simp only [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          ring

theorem coeff_basis (D j i : ℕ) (b : ℤ) :
    (C b * X ^ j * (1 - X) ^ (D - j) : Polynomial ℤ).coeff i =
      if j ≤ i then b * (-1 : ℤ) ^ (i - j) * (Nat.choose (D - j) (i - j) : ℤ)
      else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hji : j ≤ i
  · simp [hji, coeff_one_sub_X_pow, mul_assoc]
  · simp [hji]

theorem coeff_bernsteinPolynomial_of_le (D : ℕ) (B : List ℤ) (i : ℕ)
    (hi : i ≤ D) :
    (bernsteinPolynomial D B).coeff i =
      ∑ j ∈ Finset.range (i + 1),
        B[j]?.getD 0 * (-1 : ℤ) ^ (i - j) * (Nat.choose (D - j) (i - j) : ℤ) := by
  classical
  rw [bernsteinPolynomial, finsetSum_coeff]
  calc
    ∑ j ∈ Finset.range (D + 1),
        (C (B[j]?.getD 0) * X ^ j * (1 - X) ^ (D - j) : Polynomial ℤ).coeff i
      = ∑ j ∈ Finset.range (i + 1),
        (C (B[j]?.getD 0) * X ^ j * (1 - X) ^ (D - j) : Polynomial ℤ).coeff i := by
          symm
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hi))
          intro j _ hnot
          have hji : ¬ j ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hnot
          rw [coeff_basis, if_neg hji]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [coeff_basis, if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

theorem coeff_bernsteinPolynomial_eq_zero (D : ℕ) (B : List ℤ) (i : ℕ)
    (hi : D < i) : (bernsteinPolynomial D B).coeff i = 0 := by
  classical
  rw [bernsteinPolynomial, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjD : j ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hji : j ≤ i := hjD.trans hi.le
  have hchoose : Nat.choose (D - j) (i - j) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  rw [coeff_basis, if_pos hji, hchoose, Nat.cast_zero, mul_zero]

theorem natDegree_bernsteinPolynomial_le (D : ℕ) (B : List ℤ) :
    (bernsteinPolynomial D B).natDegree ≤ D := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact coeff_bernsteinPolynomial_eq_zero D B i hi

theorem eval₂_bernsteinPolynomial (D : ℕ) (B : List ℤ) (x : ℝ) :
    (bernsteinPolynomial D B).eval₂ (Int.castRingHom ℝ) x =
      ∑ j ∈ Finset.range (D + 1),
        (B[j]?.getD 0 : ℝ) * x ^ j * (1 - x) ^ (D - j) := by
  rw [bernsteinPolynomial, eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval₂_mul, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  rfl

theorem eval₂_bernsteinPolynomial_nonneg (D : ℕ) (B : List ℤ)
    (hB : ∀ b ∈ B, 0 ≤ b) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (bernsteinPolynomial D B).eval₂ (Int.castRingHom ℝ) x := by
  rw [eval₂_bernsteinPolynomial]
  apply Finset.sum_nonneg
  intro j _
  have hb : (0 : ℤ) ≤ B[j]?.getD 0 := by
    by_cases hj : j < B.length
    · rw [List.getElem?_eq_getElem hj, Option.getD_some]
      exact hB B[j] (List.getElem_mem hj)
    · rw [List.getElem?_eq_none (by omega)]
      simp
  exact mul_nonneg (mul_nonneg (Int.cast_nonneg hb) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

theorem eq_bernsteinPolynomial_of_coeff (D : ℕ) (B : List ℤ)
    (q : Polynomial ℤ)
    (htail : ∀ i, D < i → q.coeff i = 0)
    (hcoeff : ∀ i, i ≤ D → q.coeff i =
      ∑ j ∈ Finset.range (i + 1),
        B[j]?.getD 0 * (-1 : ℤ) ^ (i - j) * (Nat.choose (D - j) (i - j) : ℤ)) :
    q = bernsteinPolynomial D B := by
  ext i
  by_cases hi : i ≤ D
  · rw [hcoeff i hi, coeff_bernsteinPolynomial_of_le D B i hi]
  · rw [htail i (by omega), coeff_bernsteinPolynomial_eq_zero D B i (by omega)]

theorem eval₂_nonneg_of_coeff (D : ℕ) (B : List ℤ) (q : Polynomial ℤ)
    (htail : ∀ i, D < i → q.coeff i = 0)
    (hcoeff : ∀ i, i ≤ D → q.coeff i =
      ∑ j ∈ Finset.range (i + 1),
        B[j]?.getD 0 * (-1 : ℤ) ^ (i - j) * (Nat.choose (D - j) (i - j) : ℤ))
    (hB : ∀ b ∈ B, 0 ≤ b) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ q.eval₂ (Int.castRingHom ℝ) x := by
  rw [eq_bernsteinPolynomial_of_coeff D B q htail hcoeff]
  exact eval₂_bernsteinPolynomial_nonneg D B hB x hx0 hx1

end
end ENT.Certificate.BlockBernstein
