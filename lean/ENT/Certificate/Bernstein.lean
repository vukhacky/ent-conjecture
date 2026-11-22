module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Nonnegativity in the unnormalized Bernstein basis follows from the coefficient identity and the signs of the coefficients. -/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ENT.Certificate

noncomputable section

/-- The unnormalized basis uses no binomial coefficient. -/
def bernsteinEval (d : ℕ) (b : Fin (d + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin (d + 1), b j * x ^ (j : ℕ) * (1 - x) ^ (d - (j : ℕ))

theorem bernsteinEval_nonneg (d : ℕ) (b : Fin (d + 1) → ℝ)
    (hb : ∀ j, 0 ≤ b j) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinEval d b x := by
  unfold bernsteinEval
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (hb j) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

/-- Soundness does not depend on the code that proposed the coefficients. -/
theorem bernstein_identity_nonneg (d : ℕ) (b : Fin (d + 1) → ℝ)
    (f : ℝ → ℝ) (hid : ∀ x, f x = bernsteinEval d b x)
    (hb : ∀ j, 0 ≤ b j) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ f x := by
  rw [hid x]
  exact bernsteinEval_nonneg d b hb x hx0 hx1

/-- A positive rescaling of a checked unit-interval polynomial gives a
certificate on the half-cell. The source identity is checked for all x. -/
theorem halfCell_nonneg (f g : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hid : ∀ x, g x = c * f (x / 2))
    (hg : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ g x)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) : 0 ≤ f s := by
  have hunit0 : 0 ≤ 2 * s := mul_nonneg (by norm_num) hs0
  have hunit1 : 2 * s ≤ 1 := by linarith
  have h := hg (2 * s) hunit0 hunit1
  rw [hid (2 * s)] at h
  have hcancel : 2 * s / 2 = s := by ring
  rw [hcancel] at h
  exact nonneg_of_mul_nonneg_right h hc

end
end ENT.Certificate
