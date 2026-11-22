module

public import ENT.Certificate.KroneckerBounds
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Polynomial.Basic

/-! Positive-coefficient transform for compact exact interval certificates.
For degree at most d, T_d(q)(z) = (z+1)^d q(z/(z+1)).
The final coefficient equals q(1), so no endpoint limiting assumption is
needed when transferring coefficient positivity to the closed unit interval. -/

@[expose] public section
set_option autoImplicit false
open Polynomial
open scoped BigOperators

namespace ENT.Quantitative.PositiveTransform
noncomputable section

def transform (d : ℕ) (q : Polynomial ℤ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (d + 1), C (q.coeff i) * X ^ i * (X + 1) ^ (d - i)

theorem coeff_basis (d i j : ℕ) (a : ℤ) :
    (C a * X ^ i * (X + 1) ^ (d - i) : Polynomial ℤ).coeff j =
      if i ≤ j then a * (Nat.choose (d - i) (j - i) : ℤ) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hij : i ≤ j
  · simp only [hij, if_true, coeff_X_add_one_pow]
  · simp only [hij, if_false, mul_zero]

theorem coeff_transform (d : ℕ) (q : Polynomial ℤ) (j : ℕ) :
    (transform d q).coeff j = ∑ i ∈ Finset.range (d + 1),
      if i ≤ j then q.coeff i * (Nat.choose (d - i) (j - i) : ℤ) else 0 := by
  simp only [transform, finsetSum_coeff, coeff_basis]

theorem natDegree_transform_le (d : ℕ) (q : Polynomial ℤ) :
    (transform d q).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_transform]
  apply Finset.sum_eq_zero
  intro i hi
  have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [if_pos (hid.trans hj.le), Nat.choose_eq_zero_of_lt (by omega),
    Nat.cast_zero, mul_zero]

theorem coeff_natAbs_le (d : ℕ) (q : Polynomial ℤ) (M : ℕ)
    (hM : ∀ i, (q.coeff i).natAbs ≤ M) (j : ℕ) :
    ((transform d q).coeff j).natAbs ≤ (d + 1) * M * 2 ^ d := by
  rw [coeff_transform]
  calc
    (∑ i ∈ Finset.range (d + 1),
        if i ≤ j then q.coeff i * (Nat.choose (d - i) (j - i) : ℤ) else 0).natAbs ≤
      ∑ i ∈ Finset.range (d + 1),
        (if i ≤ j then q.coeff i * (Nat.choose (d - i) (j - i) : ℤ) else 0).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (d + 1), M * 2 ^ d := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hij : i ≤ j
      · rw [if_pos hij, Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.mul_le_mul (hM i) ((Nat.choose_le_two_pow _ _).trans
          (Nat.pow_le_pow_right (by decide) (Nat.sub_le d i)))
      · simp only [if_neg hij, Int.natAbs_zero, Nat.zero_le]
    _ = _ := by simp [Nat.mul_assoc]

theorem eval₂_transform (d : ℕ) (q : Polynomial ℤ) (z : ℝ) :
    (transform d q).eval₂ (Int.castRingHom ℝ) z =
      ∑ i ∈ Finset.range (d + 1), (q.coeff i : ℝ) * z ^ i * (z + 1) ^ (d - i) := by
  simp only [transform, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow,
    eval₂_X, eval₂_add, eval₂_one, Int.coe_castRingHom]

theorem eval₂_transform_identity (d : ℕ) (q : Polynomial ℤ)
    (hd : q.natDegree ≤ d) (z : ℝ) (hz : z + 1 ≠ 0) :
    (transform d q).eval₂ (Int.castRingHom ℝ) z =
      (z + 1) ^ d * q.eval₂ (Int.castRingHom ℝ) (z / (z + 1)) := by
  rw [eval₂_transform, eval₂_eq_sum_range' (Int.castRingHom ℝ) (by omega : q.natDegree < d + 1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_sub₀ (z + 1) hz (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), div_pow]
  simp only [Int.coe_castRingHom, div_eq_mul_inv]
  ring

theorem eval_map_real_identity (d : ℕ) (q : Polynomial ℤ)
    (hd : q.natDegree ≤ d) (z : ℝ) (hz : 1 + z ≠ 0) :
    ((transform d q).map (Int.castRingHom ℝ)).eval z =
      (1 + z) ^ d * (q.map (Int.castRingHom ℝ)).eval (z / (1 + z)) := by
  simp only [eval_map, add_comm 1 z] at hz ⊢
  exact eval₂_transform_identity d q hd z hz

theorem top_coeff_eq_eval_one (d : ℕ) (q : Polynomial ℤ) (hd : q.natDegree ≤ d) :
    (transform d q).coeff d = q.eval 1 := by
  rw [coeff_transform, eval_eq_sum_range' (by omega : q.natDegree < d + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [if_pos hid, Nat.choose_self, Nat.cast_one, one_pow, mul_one]

theorem eval₂_nonneg_of_coeff_nonneg (p : Polynomial ℤ)
    (hcoeff : ∀ i, 0 ≤ p.coeff i) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ p.eval₂ (Int.castRingHom ℝ) z := by
  rw [eval₂_eq_sum_range]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Int.cast_nonneg (hcoeff i)) (pow_nonneg hz i)

theorem nonneg_on_unitInterval (d : ℕ) (q : Polynomial ℤ)
    (hd : q.natDegree ≤ d) (hcoeff : ∀ i, 0 ≤ (transform d q).coeff i)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ q.eval₂ (Int.castRingHom ℝ) x := by
  rcases eq_or_lt_of_le hx1 with rfl | hxlt
  · have h := hcoeff d
    rw [top_coeff_eq_eval_one d q hd] at h
    rw [eval₂_at_one]
    exact Int.cast_nonneg h
  · let z := x / (1 - x)
    have hz : 0 ≤ z := div_nonneg hx0 (sub_nonneg.mpr hx1)
    have hz1 : 0 < z + 1 := by linarith
    have hxdiv : z / (z + 1) = x := by
      dsimp [z]
      field_simp
      <;> ring
    have h := eval₂_nonneg_of_coeff_nonneg (transform d q) hcoeff z hz
    rw [eval₂_transform_identity d q hd z hz1.ne', hxdiv] at h
    exact nonneg_of_mul_nonneg_right h (pow_pos hz1 d)

end
end ENT.Quantitative.PositiveTransform
