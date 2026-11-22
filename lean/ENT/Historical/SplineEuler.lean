module

public import ENT.Spline.DensityLaw
public import ENT.Spline.Recurrence
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.LinearCombination

/-! Euler recurrence for cardinal splines and the monotone normalized
simplex-slice volume. This is an analytic route to the capped-simplex
likelihood-ratio comparison, valid globally across every spline knot. -/

@[expose] public section
set_option autoImplicit false
open Set
open scoped BigOperators

namespace ENT.Spline
noncomputable section

theorem positivePower_mul_predecessor (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    x * positivePower m x = positivePower (m+1) x := by
  by_cases hx : 0 ≤ x
  · simp only [positivePower, max_eq_right hx, pow_succ]
    ring
  · simp [positivePower, max_eq_left (le_of_not_ge hx), zero_pow (by omega : m ≠ 0)]

theorem unnormalizedSpline_succ_hasDerivAt (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    HasDerivAt (unnormalizedSpline (m+1))
      (∑ j ∈ Finset.range (m+2), (-1:ℝ)^j * ((m+1).choose j:ℝ) *
        ((m:ℝ) * positivePower (m-1) (x-(j:ℝ)))) x := by
  have hterm (j : ℕ) :
      HasDerivAt (fun y : ℝ => (-1:ℝ)^j * ((m+1).choose j:ℝ) * positivePower m (y-(j:ℝ)))
        ((-1:ℝ)^j * ((m+1).choose j:ℝ) *
          ((m:ℝ) * positivePower (m-1) (x-(j:ℝ)))) x := by
    have h := (positivePower_hasDerivAt m hm (x-(j:ℝ))).comp x
      ((hasDerivAt_id x).sub_const (j:ℝ))
    convert h.const_mul ((-1:ℝ)^j * ((m+1).choose j:ℝ)) using 1 <;> first | rfl | simp
  unfold unnormalizedSpline
  simpa only [Nat.add_sub_cancel, Nat.add_assoc] using
    HasDerivAt.fun_sum (u := Finset.range (m+2)) (fun j _ => hterm j)

theorem unnormalizedSpline_euler (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    (m:ℝ)*unnormalizedSpline (m+1) x - x*deriv (unnormalizedSpline (m+1)) x =
      (m:ℝ)*((m:ℝ)+1)*unnormalizedSpline m (x-1) := by
  rw [(unnormalizedSpline_succ_hasDerivAt m hm x).deriv]
  unfold unnormalizedSpline
  simp only [Nat.add_sub_cancel]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm (j : ℕ) :
      (m:ℝ)*((-1:ℝ)^j*((m+1).choose j:ℝ)*positivePower m (x-(j:ℝ))) -
        x*((-1:ℝ)^j*((m+1).choose j:ℝ)*((m:ℝ)*positivePower (m-1) (x-(j:ℝ)))) =
      -(m:ℝ)*(j:ℝ)*(-1:ℝ)^j*((m+1).choose j:ℝ)*positivePower (m-1) (x-(j:ℝ)) := by
    have he := positivePower_mul_predecessor (m-1) (by omega) (x-(j:ℝ))
    rw [show m-1+1=m by omega] at he
    rw [←he]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hc : ((m+1).choose (j+1):ℝ)*((j:ℝ)+1) = ((m:ℝ)+1)*(m.choose j:ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq m j).symm
  have hx : x-((j+1:ℕ):ℝ) = x-1-(j:ℝ) := by push_cast; ring
  rw [hx, pow_succ, Nat.cast_add, Nat.cast_one]
  linear_combination (m:ℝ)*(-1:ℝ)^j*positivePower (m-1) (x-1-(j:ℝ)) * hc

theorem unitSumSplineDensity_euler_succ (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    (m:ℝ)*unitSumSplineDensity (m+1) x - x*deriv (unitSumSplineDensity (m+1)) x =
      ((m:ℝ)+1)*unitSumSplineDensity m (x-1) := by
  have hd := (unnormalizedSpline_succ_hasDerivAt m hm x).const_mul
    ((Nat.factorial m:ℝ)⁻¹)
  have hd' : deriv (unitSumSplineDensity (m+1)) x =
      (Nat.factorial m:ℝ)⁻¹ * deriv (unnormalizedSpline (m+1)) x := by
    rw [(unnormalizedSpline_succ_hasDerivAt m hm x).deriv]
    unfold unitSumSplineDensity
    simpa only [Nat.add_sub_cancel] using hd.deriv
  rw [hd', unitSumSplineDensity, unitSumSplineDensity, Nat.add_sub_cancel]
  have he := unnormalizedSpline_euler m hm x
  have hf : (Nat.factorial m:ℝ) = (m:ℝ)*(Nat.factorial (m-1):ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : m ≠ 0)).symm
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hf0 : (Nat.factorial (m-1):ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m-1)
  rw [hf]
  field_simp
  nlinarith [he]

theorem unitSumSplineDensity_euler (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    ((n:ℝ)-1)*unitSumSplineDensity n x - x*deriv (unitSumSplineDensity n) x =
      (n:ℝ)*unitSumSplineDensity (n-1) (x-1) := by
  have h := unitSumSplineDensity_euler_succ (n-1) (by omega) x
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, sub_add_cancel] using h

end
end ENT.Spline
