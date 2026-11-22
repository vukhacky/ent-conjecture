module

public import ENT.Spline.DensityProperties
public import ENT.Spline.Normalization

/-! Regularity and bounded support of the standardized spline density. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Spline

noncomputable section

theorem continuous_diagonalSplineDensity (n : ℕ) : Continuous (diagonalSplineDensity n) :=
  continuous_const.mul ((continuous_unitSumSplineDensity n).comp
    ((continuous_const.sub (continuous_const.mul continuous_id)).div_const 2))

theorem diagonalSplineDensity_nonneg (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ diagonalSplineDensity n x :=
  mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
    (unitSumSplineDensity_nonneg n hn _)

theorem diagonalSplineDensity_le (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    diagonalSplineDensity n x ≤ Real.sqrt (n : ℝ) / 2 := by
  unfold diagonalSplineDensity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (unitSumSplineDensity_le_one n hn _)
    (div_nonneg (Real.sqrt_nonneg (n : ℝ)) (by norm_num : (0 : ℝ) ≤ 2))

theorem diagonalSplineDensity_eq_zero_of_not_mem (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : x ∉ Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    diagonalSplineDensity n x = 0 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hr2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn'.le
  have hx' : x < -Real.sqrt (n : ℝ) ∨ Real.sqrt (n : ℝ) < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  have ht : ((n : ℝ) - Real.sqrt (n : ℝ) * x) / 2 ∉ Icc 0 (n : ℝ) := by
    intro hmem
    rcases hx' with hx' | hx'
    · have hm := mul_lt_mul_of_pos_left hx' hr
      nlinarith [hmem.2, hr2]
    · have hm := mul_lt_mul_of_pos_left hx' hr
      nlinarith [hmem.1, hr2]
  unfold diagonalSplineDensity
  rw [unitSumSplineDensity_eq_zero_of_not_mem n hn _ ht, mul_zero]

theorem hasCompactSupport_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    HasCompactSupport (diagonalSplineDensity n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) isCompact_Icc
  intro x hx
  by_contra hnot
  exact hx (diagonalSplineDensity_eq_zero_of_not_mem n hn x hnot)

theorem integrable_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    Integrable (diagonalSplineDensity n) volume :=
  (continuous_diagonalSplineDensity n).integrable_of_hasCompactSupport
    (hasCompactSupport_diagonalSplineDensity n hn)

end
end ENT.Spline
