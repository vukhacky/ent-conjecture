module

public import ENT.Spline.Symmetry
public import ENT.Spline.DensityLaw

/-! Exact vanishing at support endpoints and full probability mass in the
open support of the diagonal spline density. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter

namespace ENT.Spline

noncomputable section

theorem unitSumSplineDensity_zero (n : ℕ) (hn : 2 ≤ n) : unitSumSplineDensity n 0 = 0 := by
  unfold unitSumSplineDensity unnormalizedSpline
  have hpow : n - 1 ≠ 0 := by omega
  have hsum : ∑ j ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ j * (n.choose j : ℝ) * positivePower (n - 1) (0 - (j : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : (0 : ℝ) - (j : ℝ) ≤ 0 := sub_nonpos.mpr (Nat.cast_nonneg j)
    simp only [positivePower, max_eq_left hj, zero_pow hpow, mul_zero]
  rw [hsum, mul_zero]

theorem unitSumSplineDensity_right_endpoint (n : ℕ) (hn : 2 ≤ n) :
    unitSumSplineDensity n (n : ℝ) = 0 := by
  have h := unitSumSplineDensity_reflection n hn 0
  simpa only [sub_zero, unitSumSplineDensity_zero n hn] using h

theorem diagonalSplineDensity_right_endpoint (n : ℕ) (hn : 2 ≤ n) :
    diagonalSplineDensity n (Real.sqrt (n : ℝ)) = 0 := by
  have hr : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  unfold diagonalSplineDensity
  rw [hr, sub_self, zero_div, unitSumSplineDensity_zero n hn, mul_zero]

theorem diagonalSplineDensity_left_endpoint (n : ℕ) (hn : 2 ≤ n) :
    diagonalSplineDensity n (-Real.sqrt (n : ℝ)) = 0 := by
  rw [diagonalSplineDensity_even n hn, diagonalSplineDensity_right_endpoint n hn]

theorem diagonalSplineDensity_eq_zero_of_not_mem_interior (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : x ∉ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    diagonalSplineDensity n x = 0 := by
  by_cases hclosed : x ∈ Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))
  · have hx' : x ≤ -Real.sqrt (n : ℝ) ∨ Real.sqrt (n : ℝ) ≤ x := by
      simpa only [mem_Ioo, not_and_or, not_lt] using hx
    rcases hx' with hlo | hhi
    · rw [le_antisymm hlo hclosed.1]
      exact diagonalSplineDensity_left_endpoint n hn
    · rw [le_antisymm hclosed.2 hhi]
      exact diagonalSplineDensity_right_endpoint n hn
  · exact diagonalSplineDensity_eq_zero_of_not_mem n hn x hclosed

theorem diagonalSplineDensity_pos_iff (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    0 < diagonalSplineDensity n x ↔ x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  constructor
  · intro hp
    by_contra hx
    rw [diagonalSplineDensity_eq_zero_of_not_mem_interior n hn x hx] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · exact diagonalSplineDensity_pos n hn x

theorem ae_mem_diagonalSplineSupport (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ x ∂projectionLaw (diagonal n), x ∈ Ioo (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  rw [diagonalSplineDensity_law n hn]
  apply (ae_withDensity_iff (continuous_diagonalSplineDensity n).measurable.ennreal_ofReal).mpr
  exact Filter.Eventually.of_forall (fun x hnonzero => by
    by_contra hx
    apply hnonzero
    rw [diagonalSplineDensity_eq_zero_of_not_mem_interior n hn x hx, ENNReal.ofReal_zero])

end
end ENT.Spline
