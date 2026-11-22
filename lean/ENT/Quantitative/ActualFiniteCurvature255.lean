module

public import ENT.FiniteCurvature149
public import ENT.Quantitative.LargeCurvature150
public import ENT.Spline.Symmetry
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Curvature of the diagonal density, from cell certificates in dimensions 7–149 and the analytic estimate from dimension 150. -/

@[expose] public section
set_option autoImplicit false
open Set

namespace ENT.Quantitative
noncomputable section

theorem deriv_odd_of_even {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have he : (fun y => f (-y)) = f := funext hf
  have h := deriv_comp_neg f x
  rw [he] at h
  linarith

theorem deriv_even_of_odd {f : ℝ → ℝ} (hf : Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have he : (fun y => f (-y)) = -f := funext hf
  have h := deriv_comp_neg f x
  rw [he, deriv.neg] at h
  linarith

theorem third_deriv_zero_of_even {f : ℝ → ℝ} (hf : Function.Even f) :
    deriv (deriv (deriv f)) 0 = 0 :=
  Spline.deriv_zero_of_even _ (deriv_even_of_odd (deriv_odd_of_even hf))

theorem diagonalPotential_third_deriv_zero (n : ℕ) (hn : 2 ≤ n) :
    deriv (deriv (deriv (Spline.diagonalSplinePotential n))) 0 = 0 :=
  third_deriv_zero_of_even (Spline.diagonalSplinePotential_even n hn)

theorem actual_curvature_ge_seven {n : ℕ} (hn : 7 ≤ n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    (7 / (n : ℝ)) * x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x := by
  by_cases hsmall : n ≤ 149
  · exact diagonal_density_curvature_seven_through_149 hn hsmall x hx0 hx1
  · rcases eq_or_lt_of_le hx0 with rfl | hx0
    · rw [diagonalPotential_third_deriv_zero n (by omega), mul_zero]
    · exact large_curvature_ge_150 (by omega) x ⟨hx0, hx1⟩

/-- The lower curvature bound on the dimension range of Theorem 3.1. -/
theorem actual_curvature_seven_through_255 {n : ℕ} (hn0 : 7 ≤ n) (_hn1 : n ≤ 255)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    (7 / (n : ℝ)) * x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x :=
  actual_curvature_ge_seven hn0 x hx0 hx1

/-- The same range statement explicitly names the actual probability density. -/
theorem actual_density_curvature_seven_through_255 {n : ℕ} (hn0 : 7 ≤ n) (hn1 : n ≤ 255)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    (7 / (n : ℝ)) * x ≤ deriv (deriv (deriv
      (fun y => -Real.log ((Spline.diagonalFiniteEntropyDensity n (by omega)).density y)))) x :=
  actual_curvature_seven_through_255 hn0 hn1 x hx0 hx1

end
end ENT.Quantitative
