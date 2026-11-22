module

public import ENT.Certificate.Contract
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Pascal's identity in finite-difference form, over exact real sums. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ENT.Spline

theorem alternating_pascal_sum (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n + 2), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * f j) =
      (∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * f j) -
      (∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * f (j + 1)) := by
  have hfirst :
      (∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * f j) =
        (∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1) : ℝ) * f (j + 1)) + f 0 := by
    rw [Finset.sum_range_succ' (fun j => (-1 : ℝ) ^ j * (n.choose j : ℝ) * f j) n]
    rw [Finset.sum_range_succ]
    simp
  have hpascal (j : ℕ) :
      (-1 : ℝ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℝ) * f (j + 1) =
        (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1) : ℝ) * f (j + 1) -
        (-1 : ℝ) ^ j * (n.choose j : ℝ) * f (j + 1) := by
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
    ring
  rw [show n + 2 = (n + 1) + 1 by omega,
    Finset.sum_range_succ' (fun j => (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * f j)]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
  simp_rw [hpascal]
  rw [Finset.sum_sub_distrib, hfirst]
  ring

end ENT.Spline
