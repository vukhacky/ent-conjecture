module

public import ENT.Statement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Elementary facts about ENT's normalized coefficients and deficit. -/

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace ENT

theorem diagonal_sq (n : ℕ) (i : Fin n) :
    (diagonal n i) ^ 2 = (n : ℝ)⁻¹ := by
  simp [diagonal, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem isDiagonal_diagonal (n : ℕ) : IsDiagonal (diagonal n) :=
  diagonal_sq n

theorem isUnit_diagonal {n : ℕ} (hn : 0 < n) : IsUnit (diagonal n) := by
  unfold IsUnit
  simp only [diagonal_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

theorem isUnit_abs_iff {n : ℕ} (a : Fin n → ℝ) :
    IsUnit (fun i => |a i|) ↔ IsUnit a := by
  simp only [IsUnit, sq_abs]

theorem isDiagonal_abs_iff {n : ℕ} (a : Fin n → ℝ) :
    IsDiagonal (fun i => |a i|) ↔ IsDiagonal a := by
  simp only [IsDiagonal, sq_abs]

theorem isUnit_two_swap_iff (a : Fin 2 → ℝ) :
    IsUnit (fun i => a i.rev) ↔ IsUnit a := by
  simp only [IsUnit, Fin.sum_univ_two,
    show (0 : Fin 2).rev = 1 by decide, show (1 : Fin 2).rev = 0 by decide]
  rw [add_comm]

theorem isDiagonal_two_swap_iff (a : Fin 2 → ℝ) :
    IsDiagonal (fun i => a i.rev) ↔ IsDiagonal a := by
  constructor
  · intro h i
    simpa only [Fin.rev_rev] using h i.rev
  · intro h i
    exact h i.rev

theorem isDiagonal_two_iff_eq_of_nonneg {a : Fin 2 → ℝ} (ha : IsUnit a)
    (h0 : 0 ≤ a 0) (h1 : 0 ≤ a 1) : IsDiagonal a ↔ a 0 = a 1 := by
  constructor
  · intro h
    apply (sq_eq_sq₀ h0 h1).mp
    exact (h 0).trans (h 1).symm
  · intro h
    have hsum : (a 0) ^ 2 + (a 1) ^ 2 = 1 := by
      simpa only [IsUnit, Fin.sum_univ_two] using ha
    rw [← h] at hsum
    have hs : (a 0) ^ 2 = (2 : ℝ)⁻¹ := by
      norm_num
      nlinarith
    intro i
    fin_cases i
    · exact hs
    · simpa [h] using hs

theorem first_pos_of_isUnit_nonneg_ordered {a : Fin 2 → ℝ} (ha : IsUnit a)
    (h0 : 0 ≤ a 0) (h1 : 0 ≤ a 1) (horder : a 1 ≤ a 0) : 0 < a 0 := by
  have hsum : (a 0) ^ 2 + (a 1) ^ 2 = 1 := by
    simpa only [IsUnit, Fin.sum_univ_two] using ha
  by_contra hn
  have hz0 : a 0 = 0 := le_antisymm (le_of_not_gt hn) h0
  have hz1 : a 1 = 0 := by linarith
  simp only [hz0, hz1, zero_pow (by decide : 2 ≠ 0), zero_add, zero_ne_one] at hsum

theorem isDiagonal_iff_abs {n : ℕ} (a : Fin n → ℝ) :
    IsDiagonal a ↔ ∀ i, |a i| = diagonal n i := by
  constructor
  · intro h i
    have hc : 0 ≤ diagonal n i := by
      unfold diagonal
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    apply (sq_eq_sq₀ (abs_nonneg (a i)) hc).mp
    rw [sq_abs, h i, diagonal_sq]
  · intro h i
    have hs := congrArg (fun x : ℝ => x ^ 2) (h i)
    simpa only [sq_abs, diagonal_sq] using hs

theorem deficit_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ deficit a := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg ((a i) ^ 2 - (n : ℝ)⁻¹)

theorem deficit_eq_zero_iff {n : ℕ} (a : Fin n → ℝ) :
    deficit a = 0 ↔ IsDiagonal a := by
  constructor
  · intro h i
    have hi : ((a i) ^ 2 - (n : ℝ)⁻¹) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg ((a j) ^ 2 - (n : ℝ)⁻¹))).mp h i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    rw [h i, sub_self, zero_pow (by decide : 2 ≠ 0)]

theorem deficit_eq_sum_pow_four_sub_inv {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : IsUnit a) :
    deficit a = (∑ i, (a i) ^ 4) - (n : ℝ)⁻¹ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hcancel : (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  calc
    deficit a = ∑ i, ((a i) ^ 4 - 2 * (n : ℝ)⁻¹ * (a i) ^ 2 + ((n : ℝ)⁻¹) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (a i) ^ 4) - 2 * (n : ℝ)⁻¹ * (∑ i, (a i) ^ 2) +
        (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (∑ i, (a i) ^ 4) - (n : ℝ)⁻¹ := by
      rw [ha, hcancel]
      ring

theorem isDiagonal_of_isUnit_one {a : Fin 1 → ℝ} (ha : IsUnit a) :
    IsDiagonal a := by
  intro i
  fin_cases i
  simpa [IsUnit] using ha

theorem isUnit_one_iff {a : Fin 1 → ℝ} :
    IsUnit a ↔ a 0 = 1 ∨ a 0 = -1 := by
  simp only [IsUnit, Fin.sum_univ_one]
  constructor
  · intro h
    have hprod : (a 0 - 1) * (a 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> rw [h] <;> norm_num

end ENT
