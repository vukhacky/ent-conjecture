module

public import ENT.Spline.DensityLaw
public import ENT.Spline.Symmetry
public import ENT.Certificate.EdgeCell
public import Mathlib.Tactic.FieldSimp

/-! The two polynomial pieces of the genuine three-dimensional diagonal density. -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Small

noncomputable section

theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by positivity

theorem sqrt_three_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem inv_sqrt_three_pos : 0 < (Real.sqrt (3 : ℝ))⁻¹ := inv_pos.mpr sqrt_three_pos

theorem inv_sqrt_three_sq : ((Real.sqrt (3 : ℝ))⁻¹) ^ 2 = 1 / 3 := by
  rw [inv_pow, sqrt_three_sq]
  norm_num

theorem inv_sqrt_three_lt_one : (Real.sqrt (3 : ℝ))⁻¹ < 1 := by
  nlinarith [inv_sqrt_three_sq, inv_sqrt_three_pos]

theorem sqrt_three_mul_inv : Real.sqrt (3 : ℝ) * (Real.sqrt (3 : ℝ))⁻¹ = 1 :=
  mul_inv_cancel₀ sqrt_three_pos.ne'

theorem sqrt_three_eq_three_inv : Real.sqrt (3 : ℝ) = 3 * (Real.sqrt (3 : ℝ))⁻¹ := by
  field_simp
  exact sqrt_three_sq

theorem unitSumSplineDensity_three_left {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Spline.unitSumSplineDensity 3 x = x ^ 2 / 2 := by
  have h := Spline.unnormalizedSpline_eq_piece 3 0 (by norm_num) (by norm_num) x hx.1 hx.2
  norm_num only [Nat.cast_zero, zero_add] at h
  rw [Spline.unitSumSplineDensity, h, Certificate.splinePiece_edge]
  norm_num
  ring

theorem unitSumSplineDensity_three_middle {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    Spline.unitSumSplineDensity 3 x = (-2 * x ^ 2 + 6 * x - 3) / 2 := by
  have h := Spline.unnormalizedSpline_eq_piece 3 1 (by norm_num) (by norm_num) (x - 1)
    (by linarith [hx.1]) (by linarith [hx.2])
  norm_num only [Nat.cast_one, add_sub_cancel] at h
  rw [Spline.unitSumSplineDensity, h]
  norm_num [Certificate.splinePiece, Finset.sum_range_succ, Nat.choose]
  ring

theorem diagonalSplineDensity_three_center {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (Real.sqrt (3 : ℝ))⁻¹) :
    Spline.diagonalSplineDensity 3 x = (3 * Real.sqrt (3 : ℝ) / 8) * (1 - x ^ 2) := by
  have hxmul : Real.sqrt (3 : ℝ) * x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hx.2 sqrt_three_pos.le
    rwa [sqrt_three_mul_inv] at h
  have ht : ((3 : ℝ) - Real.sqrt (3 : ℝ) * x) / 2 ∈ Icc (1 : ℝ) 2 := by
    constructor <;> nlinarith [mul_nonneg sqrt_three_pos.le hx.1]
  unfold Spline.diagonalSplineDensity
  norm_num only [Nat.cast_ofNat]
  rw [unitSumSplineDensity_three_middle ht]
  have h3 : Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt (3 : ℝ) := by
    rw [pow_succ, sqrt_three_sq]
  ring_nf
  rw [h3]
  ring

theorem diagonalSplineDensity_three_outer {x : ℝ}
    (hx : x ∈ Icc (Real.sqrt (3 : ℝ))⁻¹ (Real.sqrt (3 : ℝ))) :
    Spline.diagonalSplineDensity 3 x =
      (3 * Real.sqrt (3 : ℝ) / 16) * (Real.sqrt (3 : ℝ) - x) ^ 2 := by
  have hlo : 1 ≤ Real.sqrt (3 : ℝ) * x := by
    have h := mul_le_mul_of_nonneg_left hx.1 sqrt_three_pos.le
    rwa [sqrt_three_mul_inv] at h
  have hhi : Real.sqrt (3 : ℝ) * x ≤ 3 := by
    have h := mul_le_mul_of_nonneg_left hx.2 sqrt_three_pos.le
    simpa only [← pow_two, sqrt_three_sq] using h
  have ht : ((3 : ℝ) - Real.sqrt (3 : ℝ) * x) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  unfold Spline.diagonalSplineDensity
  norm_num only [Nat.cast_ofNat]
  rw [unitSumSplineDensity_three_left ht]
  have h3 : Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt (3 : ℝ) := by
    rw [pow_succ, sqrt_three_sq]
  ring_nf
  rw [sqrt_three_sq, h3]
  ring

theorem diagonalSplineDensity_three_at_cut :
    Spline.diagonalSplineDensity 3 (Real.sqrt (3 : ℝ))⁻¹ = Real.sqrt (3 : ℝ) / 4 := by
  rw [diagonalSplineDensity_three_center ⟨inv_sqrt_three_pos.le, le_rfl⟩, inv_sqrt_three_sq]
  ring

end
end ENT.Small
