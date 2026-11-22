module

public import ENT.Small.FourAnalysis

/-! The actual n=4 local constants in the unit-sum coordinates used by exact
weighted-log quadrature. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small
noncomputable section

theorem diagonalSplineDensity_four_reflected (s : ℝ) :
    Spline.diagonalSplineDensity 4 (1 - s) = Spline.unitSumSplineDensity 4 (1 + s) := by
  unfold Spline.diagonalSplineDensity
  norm_num only [Nat.cast_ofNat]
  rw [sqrt_four_eq_two, show (2 : ℝ) / 2 = 1 by norm_num, one_mul]
  congr 1
  ring

theorem fourJ3_eq_unitSum_log_integral :
    fourJ3 = ∫ s in (0 : ℝ)..1, -Real.log (Spline.unitSumSplineDensity 4 (1 + s)) := by
  calc
    _ = ∫ s in (0 : ℝ)..1, Spline.diagonalSplinePotential 4 (1 - s) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := Spline.diagonalSplinePotential 4) (a := 0) (b := 1) 1
      simpa only [sub_self, sub_zero, fourJ3] using h.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [Spline.diagonalSplinePotential]
      rw [diagonalSplineDensity_four_reflected]

theorem fourJ2_eq_unitSum_log_integral :
    fourJ2 = ∫ s in (0 : ℝ)..1, -s * Real.log (Spline.unitSumSplineDensity 4 (1 + s)) := by
  calc
    _ = ∫ s in (0 : ℝ)..1, (1 - (1 - s)) * Spline.diagonalSplinePotential 4 (1 - s) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => (1 - x) * Spline.diagonalSplinePotential 4 x) (a := 0) (b := 1) 1
      simpa only [sub_self, sub_zero, fourJ2] using h.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [Spline.diagonalSplinePotential]
      rw [diagonalSplineDensity_four_reflected]
      ring

end
end ENT.Small
