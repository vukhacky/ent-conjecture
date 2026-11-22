module

public import ENT.Small.ThreeDensity
public import ENT.Small.LogIntegrals
public import ENT.Small.EndpointLog
public import ENT.Small.EnclosuresThree

/-! Exact entropy and unweighted potential integrals for the actual dimension-three
Lebesgue density. Endpoint logarithms are handled through interval integrability. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

private theorem inv_sqrt_three_pow_four : ((Real.sqrt (3 : ℝ))⁻¹) ^ 4 = 1 / 9 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, inv_sqrt_three_sq]
  norm_num

private theorem log_sqrt_three_quarter :
    -Real.log (Real.sqrt (3 : ℝ) / 4) = threeV := by
  unfold threeV
  rw [← Real.log_inv]
  congr 1
  field_simp

private theorem three_center_cut :
    (3 * Real.sqrt (3 : ℝ) / 8) * (1 - ((Real.sqrt (3 : ℝ))⁻¹) ^ 2) =
      Real.sqrt (3 : ℝ) / 4 := by
  rw [inv_sqrt_three_sq]
  ring

private theorem three_outer_cut :
    (3 * Real.sqrt (3 : ℝ) / 16) * (2 * (Real.sqrt (3 : ℝ))⁻¹) ^ 2 =
      Real.sqrt (3 : ℝ) / 4 := by
  rw [mul_pow, inv_sqrt_three_sq]
  ring

private theorem sqrt_three_sub_inv :
    Real.sqrt (3 : ℝ) - (Real.sqrt (3 : ℝ))⁻¹ = 2 * (Real.sqrt (3 : ℝ))⁻¹ := by
  linarith [sqrt_three_eq_three_inv]

private theorem three_center_algebra (s r L A : ℝ) (hs : s = 3 * r) (hr : r ^ 2 = 1 / 3) :
    (3 * s / 8) * ((r - r ^ 3 / 3) * L + 2 * r ^ 3 / 9 - 4 * r / 3 + (4 / 3) * A) =
      L / 3 - 17 / 36 + (s / 2) * A := by
  have hr4 : r ^ 4 = 1 / 9 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hr]; norm_num
  rw [hs]
  ring_nf
  rw [hr, hr4]
  ring

private theorem three_outer_algebra (s r L : ℝ) (hs : s = 3 * r) (hr : r ^ 2 = 1 / 3) :
    (3 * s / 16) * (2 * r) ^ 3 / 3 * L - 2 * (3 * s / 16) * (2 * r) ^ 3 / 9 =
      L / 6 - 1 / 9 := by
  have hr4 : r ^ 4 = 1 / 9 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hr]; norm_num
  rw [hs]
  ring_nf
  rw [hr4]
  ring

theorem three_entropy_center_integral :
    (∫ x in 0..(Real.sqrt (3 : ℝ))⁻¹,
      Spline.diagonalSplineDensity 3 x * Real.log (Spline.diagonalSplineDensity 3 x)) =
        Real.log (Real.sqrt (3 : ℝ) / 4) / 3 - 17 / 36 +
          (Real.sqrt (3 : ℝ) / 2) * Real.artanh (Real.sqrt (3 : ℝ))⁻¹ := by
  calc
    _ = ∫ x in 0..(Real.sqrt (3 : ℝ))⁻¹,
        ((3 * Real.sqrt (3 : ℝ) / 8) * (1 - x ^ 2)) *
          Real.log ((3 * Real.sqrt (3 : ℝ) / 8) * (1 - x ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le inv_sqrt_three_pos.le] at hx
      dsimp only
      rw [diagonalSplineDensity_three_center hx]
    _ = _ := by
      rw [integral_quadratic_cap_mul_log (by positivity) inv_sqrt_three_pos.le
        inv_sqrt_three_lt_one, three_center_cut]
      exact three_center_algebra _ _ _ _ sqrt_three_eq_three_inv inv_sqrt_three_sq

theorem three_entropy_outer_integral :
    (∫ x in (Real.sqrt (3 : ℝ))⁻¹..Real.sqrt (3 : ℝ),
      Spline.diagonalSplineDensity 3 x * Real.log (Spline.diagonalSplineDensity 3 x)) =
        Real.log (Real.sqrt (3 : ℝ) / 4) / 6 - 1 / 9 := by
  have hrR : (Real.sqrt (3 : ℝ))⁻¹ ≤ Real.sqrt (3 : ℝ) := by
    linarith [sqrt_three_eq_three_inv, inv_sqrt_three_pos]
  calc
    _ = ∫ x in (Real.sqrt (3 : ℝ))⁻¹..Real.sqrt (3 : ℝ),
        ((3 * Real.sqrt (3 : ℝ) / 16) * (Real.sqrt (3 : ℝ) - x) ^ 2) *
          Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * (Real.sqrt (3 : ℝ) - x) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hrR] at hx
      dsimp only
      rw [diagonalSplineDensity_three_outer hx]
    _ = ∫ x in 0..2 * (Real.sqrt (3 : ℝ))⁻¹,
        ((3 * Real.sqrt (3 : ℝ) / 16) * x ^ 2) *
          Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * x ^ 2) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun y : ℝ => ((3 * Real.sqrt (3 : ℝ) / 16) * y ^ 2) *
          Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * y ^ 2))
        (a := (Real.sqrt (3 : ℝ))⁻¹) (b := Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))
      simpa only [sub_self, sqrt_three_sub_inv] using h
    _ = _ := by
      rw [integral_scaled_square_mul_log (by positivity) (by positivity), three_outer_cut]
      exact three_outer_algebra _ _ _ sqrt_three_eq_three_inv inv_sqrt_three_sq

/-- This is the entropy of the genuine diagonal law, not an independently chosen formula. -/
theorem diagonalFiniteEntropyDensity_three_entropy :
    (Spline.diagonalFiniteEntropyDensity 3 (by norm_num)).entropy = threeH := by
  let f : ℝ → ℝ := fun x => Spline.diagonalSplineDensity 3 x *
    Real.log (Spline.diagonalSplineDensity 3 x)
  have hf : Continuous f := Real.continuous_mul_log.comp (Spline.continuous_diagonalSplineDensity 3)
  have hw : (∫ x, f x) = 2 * ∫ x in 0..Real.sqrt (3 : ℝ), f x := by
    apply integral_even_of_bounded_support sqrt_three_pos.le hf
    · intro x
      simp only [f, Spline.diagonalSplineDensity_even 3 (by norm_num) x]
    · intro x hx
      simp only [f, Spline.diagonalSplineDensity_eq_zero_of_not_mem 3 (by norm_num) x hx, zero_mul]
  change -(∫ x, f x) = threeH
  rw [hw, ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (Real.sqrt (3 : ℝ))⁻¹)
    (hf.intervalIntegrable (Real.sqrt (3 : ℝ))⁻¹ (Real.sqrt (3 : ℝ)))]
  change - (2 * ((∫ x in 0..(Real.sqrt (3 : ℝ))⁻¹,
    Spline.diagonalSplineDensity 3 x * Real.log (Spline.diagonalSplineDensity 3 x)) +
    (∫ x in (Real.sqrt (3 : ℝ))⁻¹..Real.sqrt (3 : ℝ),
    Spline.diagonalSplineDensity 3 x * Real.log (Spline.diagonalSplineDensity 3 x)))) = _
  rw [three_entropy_center_integral, three_entropy_outer_integral, threeH_eq]
  have hv := log_sqrt_three_quarter
  unfold threeScaledArtanh threeR
  simp only [one_div]
  rw [← hv]
  ring

theorem three_potential_center_integral :
    (∫ x in 0..threeR, Spline.diagonalSplinePotential 3 x) = threeJ := by
  have hR : threeR = (Real.sqrt (3 : ℝ))⁻¹ := by simp only [threeR, one_div]
  rw [hR]
  calc
    _ = ∫ x in 0..(Real.sqrt (3 : ℝ))⁻¹,
        -Real.log ((3 * Real.sqrt (3 : ℝ) / 8) * (1 - x ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le inv_sqrt_three_pos.le] at hx
      dsimp [Spline.diagonalSplinePotential]
      rw [diagonalSplineDensity_three_center hx]
    _ = _ := by
      rw [integral_neg_log_quadratic_cap (by positivity) inv_sqrt_three_pos.le
        inv_sqrt_three_lt_one, three_center_cut]
      unfold threeJ
      rw [hR]
      rw [← log_sqrt_three_quarter]
      ring

theorem three_potential_outer_integral :
    (∫ x in threeR..Real.sqrt (3 : ℝ), Spline.diagonalSplinePotential 3 x) =
      2 * threeR * (threeV + 2) := by
  have hR : threeR = (Real.sqrt (3 : ℝ))⁻¹ := by simp only [threeR, one_div]
  have hrR : threeR ≤ Real.sqrt (3 : ℝ) := by
    rw [hR]
    linarith [sqrt_three_eq_three_inv, inv_sqrt_three_pos]
  calc
    _ = ∫ x in threeR..Real.sqrt (3 : ℝ),
        -Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * (Real.sqrt (3 : ℝ) - x) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hrR] at hx
      dsimp [Spline.diagonalSplinePotential]
      rw [diagonalSplineDensity_three_outer (by simpa only [hR] using hx)]
    _ = ∫ x in 0..2 * (Real.sqrt (3 : ℝ))⁻¹,
        -Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * x ^ 2) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun y : ℝ => -Real.log ((3 * Real.sqrt (3 : ℝ) / 16) * y ^ 2))
        (a := (Real.sqrt (3 : ℝ))⁻¹) (b := Real.sqrt (3 : ℝ)) (Real.sqrt (3 : ℝ))
      simpa only [hR, sub_self, sqrt_three_sub_inv] using h
    _ = _ := by
      rw [integral_neg_log_scaled_square (by positivity) (by positivity), three_outer_cut, hR]
      rw [← log_sqrt_three_quarter]
      ring

theorem three_potential_full_integral :
    (∫ x in 0..Real.sqrt (3 : ℝ), Spline.diagonalSplinePotential 3 x) = threeF2R := by
  have hi : Integrable (Spline.diagonalSplinePotential 3) :=
    (integrable_log_diagonalSplineDensity 3 (by norm_num)).neg
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := 0) (b := threeR))
    (hi.intervalIntegrable (a := threeR) (b := Real.sqrt (3 : ℝ))),
    three_potential_center_integral, three_potential_outer_integral]
  rfl

end
end ENT.Small
