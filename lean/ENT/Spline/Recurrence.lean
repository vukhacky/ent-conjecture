module

public import ENT.Spline.Global
public import ENT.Spline.BinomialDifference
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Exact integral recurrence for the global spline density, for n≥2. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace ENT.Spline

noncomputable section

def antiderivativeSpline (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ j * (n.choose j : ℝ) * positivePower n (t - (j : ℝ))

theorem antiderivativeSpline_hasDerivAt (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (antiderivativeSpline n) (unnormalizedSpline n x) x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hterm (j : ℕ) :
      HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ j * (n.choose j : ℝ) *
          positivePower n (y - (j : ℝ)))
        ((-1 : ℝ) ^ j * (n.choose j : ℝ) *
          ((n : ℝ) * positivePower (n - 1) (x - (j : ℝ)))) x := by
    have h := (positivePower_hasDerivAt n hn (x - (j : ℝ))).comp x
      ((hasDerivAt_id x).sub_const (j : ℝ))
    convert h.const_mul ((-1 : ℝ) ^ j * (n.choose j : ℝ)) using 1 <;> first | rfl | simp
  have hsum := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun j _ => hterm j)
  convert hsum.const_mul ((n : ℝ)⁻¹) using 1
  · rfl
  · unfold unnormalizedSpline
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hn0]

theorem antiderivativeSpline_window (n : ℕ) (t : ℝ) :
    antiderivativeSpline n t - antiderivativeSpline n (t - 1) =
      (n : ℝ)⁻¹ * unnormalizedSpline (n + 1) t := by
  have hshift (j : ℕ) :
      positivePower n (t - 1 - (j : ℝ)) = positivePower n (t - ((j + 1 : ℕ) : ℝ)) := by
    congr 1
    push_cast
    ring
  unfold antiderivativeSpline
  simp_rw [hshift]
  rw [← mul_sub, ← alternating_pascal_sum n (fun j => positivePower n (t - (j : ℝ)))]
  simp only [unnormalizedSpline, Nat.add_sub_cancel]

theorem integral_unnormalizedSpline_window (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    (∫ y in (t - 1)..t, unnormalizedSpline n y) =
      (n : ℝ)⁻¹ * unnormalizedSpline (n + 1) t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => antiderivativeSpline_hasDerivAt n hn x)
    ((continuous_unnormalizedSpline n).intervalIntegrable (t - 1) t)]
  exact antiderivativeSpline_window n t

theorem unitSumSplineDensity_window (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    (∫ y in (t - 1)..t, unitSumSplineDensity n y) = unitSumSplineDensity (n + 1) t := by
  unfold unitSumSplineDensity
  rw [intervalIntegral.integral_const_mul, integral_unnormalizedSpline_window n hn]
  have hfact : (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
  simp only [Nat.add_sub_cancel]
  rw [hfact, mul_inv]
  ring

end
end ENT.Spline
