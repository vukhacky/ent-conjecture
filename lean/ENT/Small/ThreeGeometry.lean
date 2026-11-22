module

public import ENT.Small.LocalThresholds

/-! Exact centered cubic geometry and Taylor-error bounds in dimension three. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem three_center_shift_bounds (a : Fin 3 → ℝ) (ha : IsUnit a)
    (ha0 : ∀ i, 0 ≤ a i) (hu : centeredEnergy a ≤ 1 / 100) :
    coefficientMean a - threeR ≤ -threeR * centeredEnergy a / 2 ∧
      |coefficientMean a - threeR| ≤ 3 * centeredEnergy a / 10 := by
  have hu0 := centeredEnergy_nonneg a
  have hm0 := coefficientMean_nonneg a ha0
  have hm := three_mean_le_r a ha ha0
  have hunit := centeredEnergy_add_mean_sq (by decide : 0 < 3) a
  rw [ha] at hunit
  norm_num at hunit
  have hmlo : (57 : ℝ) / 100 ≤ coefficientMean a := by nlinarith
  have hsum : (10 : ℝ) / 9 ≤ coefficientMean a + threeR := by
    linarith [threeR_bounds.1]
  have hid : (coefficientMean a - threeR) ^ 2 +
      2 * threeR * (coefficientMean a - threeR) +
      threeR ^ 2 * centeredEnergy a = 0 := by
    rw [threeR_sq]
    nlinarith [threeR_sq]
  constructor
  · apply (mul_le_mul_iff_left₀ (show 0 < 2 * threeR by linarith [threeR_pos])).mp
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hm)]
    have hp := mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hsum)
    nlinarith [threeR_sq]

theorem three_zero_sum_discriminant (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) :
    perturbationEnergy z ^ 3 - 54 * (z 0 * z 1 * z 2) ^ 2 =
      2 * (z 0 - z 1) ^ 2 * (z 1 - z 2) ^ 2 * (z 2 - z 0) ^ 2 := by
  have hz2 : z 2 = -z 0 - z 1 := by
    simp only [Fin.sum_univ_three] at hz
    linarith
  simp only [perturbationEnergy, Fin.sum_univ_three, hz2]
  ring

theorem three_zero_sum_product_bound (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hu : perturbationEnergy z = ρ ^ 2) :
    |z 0 * z 1 * z 2| ≤ ρ ^ 3 / 7 := by
  have hdisc := three_zero_sum_discriminant z hz
  have hpos : 0 ≤ 2 * (z 0 - z 1) ^ 2 * (z 1 - z 2) ^ 2 * (z 2 - z 0) ^ 2 := by
    positivity
  rw [hu] at hdisc
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ ρ ^ 3 / 7)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (z 0 * z 1 * z 2)]

theorem three_zero_sum_cube (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) :
    ∑ i, z i ^ 3 = 3 * (z 0 * z 1 * z 2) := by
  have hz2 : z 2 = -z 0 - z 1 := by
    simp only [Fin.sum_univ_three] at hz
    linarith
  simp only [Fin.sum_univ_three, hz2]
  ring

theorem three_zero_sum_fourth (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) :
    ∑ i, z i ^ 4 = perturbationEnergy z ^ 2 / 2 := by
  have hz2 : z 2 = -z 0 - z 1 := by
    simp only [Fin.sum_univ_three] at hz
    linarith
  simp only [perturbationEnergy, Fin.sum_univ_three, hz2]
  ring

theorem three_shift_fourth_identity (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) (d : ℝ) :
    ∑ i, (d - 2 * z i) ^ 4 = 3 * d ^ 4 + 24 * d ^ 2 * perturbationEnergy z -
      96 * d * (z 0 * z 1 * z 2) + 8 * perturbationEnergy z ^ 2 := by
  have hz2 : z 2 = -z 0 - z 1 := by
    simp only [Fin.sum_univ_three] at hz
    linarith
  simp only [perturbationEnergy, Fin.sum_univ_three, hz2]
  ring

theorem three_shift_product (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0) (m : ℝ) :
    (m + z 0) * (m + z 1) * (m + z 2) =
      m ^ 3 - m * perturbationEnergy z / 2 + z 0 * z 1 * z 2 := by
  have hz2 : z 2 = -z 0 - z 1 := by
    simp only [Fin.sum_univ_three] at hz
    linarith
  simp only [perturbationEnergy, Fin.sum_univ_three, hz2]
  ring

theorem three_small_shift_bound {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10)
    (hd : |d| ≤ 3 * ρ ^ 2 / 10) : |d| ≤ ρ / 30 := by
  have h := mul_nonneg hρ0 (show 0 ≤ 1 / 10 - ρ by linarith)
  nlinarith

theorem three_coordinate_rational_bound (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hu : perturbationEnergy z = ρ ^ 2) (i : Fin 3) :
    |z i| ≤ 5 * ρ / 6 := by
  have h := zero_sum_coordinate_sq_bound z hz i
  rw [hu] at h
  norm_num at h
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 5 * ρ / 6)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg ρ]

theorem three_taylor_argument_bound (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10)
    (hu : perturbationEnergy z = ρ ^ 2) (hd : |d| ≤ 3 * ρ ^ 2 / 10)
    (i : Fin 3) : |d - 2 * z i| ≤ 17 * ρ / 10 := by
  have hzbound := three_coordinate_rational_bound z hz hρ0 hu i
  have hdbound := three_small_shift_bound hρ0 hρ hd
  have htriangle := abs_sub d (2 * z i)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htriangle
  linarith

theorem three_taylor_fourth_sum_bound (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10)
    (hu : perturbationEnergy z = ρ ^ 2) (hd : |d| ≤ 3 * ρ ^ 2 / 10) :
    ∑ i, (d - 2 * z i) ^ 4 ≤ 9 * ρ ^ 4 := by
  have hdsmall := three_small_shift_bound hρ0 hρ hd
  have hdsq := pow_le_pow_left₀ (abs_nonneg d) hdsmall 2
  have hdfour := pow_le_pow_left₀ (abs_nonneg d) hdsmall 4
  simp only [sq_abs] at hdsq
  have hdsq' : d ^ 2 ≤ ρ ^ 2 / 900 := by nlinarith [sq_abs d]
  have hdfour' : d ^ 4 ≤ ρ ^ 4 / 810000 := by
    rw [show |d| ^ 4 = d ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs]
      ring] at hdfour
    nlinarith
  have hdp : |d * (z 0 * z 1 * z 2)| ≤ ρ ^ 4 / 210 := by
    rw [abs_mul]
    have h := mul_le_mul hdsmall (three_zero_sum_product_bound z hz hρ0 hu)
      (abs_nonneg _) (by positivity : 0 ≤ ρ / 30)
    nlinarith
  have hdsqmul := mul_le_mul_of_nonneg_right hdsq' (sq_nonneg ρ)
  rw [three_shift_fourth_identity z hz d, hu]
  have hp := neg_abs_le (d * (z 0 * z 1 * z 2))
  nlinarith [pow_nonneg hρ0 4]

theorem three_taylor_error_bound (z : Fin 3 → ℝ) (hz : ∑ i, z i = 0)
    {ρ d E M : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 10)
    (hu : perturbationEnergy z = ρ ^ 2) (hd : |d| ≤ 3 * ρ ^ 2 / 10)
    (hM0 : 0 ≤ M) (hM : M ≤ 17 * ρ / 10)
    (hE : E ≤ (1 / 20 : ℝ) * M * (∑ i, (d - 2 * z i) ^ 4)) :
    E ≤ 153 * ρ ^ 5 / 200 := by
  have hs := three_taylor_fourth_sum_bound z hz hρ0 hρ hu hd
  have hs0 : 0 ≤ ∑ i, (d - 2 * z i) ^ 4 := by positivity
  have hp := mul_le_mul hM hs hs0 (by positivity : 0 ≤ 17 * ρ / 10)
  nlinarith

end
end ENT.Small
