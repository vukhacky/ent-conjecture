module

public import ENT.Pang.FourierLogJet
public import ENT.Pang.DerivativeIntegralBounds

/-! From the proved Fourier averages to the actual derivative ratios. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

theorem inverse_two_pi_eq_fourierScale_sq :
    (2 * Real.pi)⁻¹ = (1 / Real.sqrt (2 * Real.pi)) ^ 2 := by
  rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]

theorem probabilityFourier_integral_eq_average (f : ℝ → ℝ) :
    (2 * Real.pi)⁻¹ * (∫ u, f u) =
      (1 / Real.sqrt (2 * Real.pi)) * fourierAverage f := by
  rw [inverse_two_pi_eq_fourierScale_sq, fourierAverage]
  ring

theorem abs_tiltStandardMoment_three_pos {t : ℝ} (ht : 0 < t) :
    0 < |tiltStandardMoment t 3| :=
  abs_pos.mpr (ne_of_lt (pang_tilt_moment_bounds ht).2.1.2)

theorem sumSin_eq_normalized {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    sumSin n t u = (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ)) *
      normalizedSumSin n t u := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hm : |tiltStandardMoment t 3| ≠ 0 := (abs_tiltStandardMoment_three_pos ht).ne'
  unfold normalizedSumSin
  field_simp

theorem integral_pow_mul_sumSin_eq_normalized {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∫ u : ℝ, u ^ k * sumSin n t u) =
      (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ)) *
        ∫ u : ℝ, u ^ k * normalizedSumSin n t u := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    change u ^ k * sumSin n t u =
      (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ)) * (u ^ k * normalizedSumSin n t u)
    rw [sumSin_eq_normalized hn ht]
    ring

def skewFourierCoefficient (n : ℕ) (t : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ))

theorem skewFourierCoefficient_pos {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    0 < skewFourierCoefficient n t :=
  mul_pos fourierScale_pos (div_pos (abs_tiltStandardMoment_three_pos ht)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))

theorem standardizedDensity_zero_eq_average {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 2 < n) :
    standardizedDensity n t 0 =
      (1 / Real.sqrt (2 * Real.pi)) * fourierAverage (sumCos n t) := by
  have h := iteratedDeriv_standardizedDensity_at_zero ht (k := 0) hn
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h
  simp_rw [← sumCos_eq_re ht] at h
  exact h.trans (probabilityFourier_integral_eq_average _)

theorem deriv_standardizedDensity_zero_eq_average {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 3 < n) :
    deriv (standardizedDensity n t) 0 = skewFourierCoefficient n t *
      fourierAverage (fun u => u * normalizedSumSin n t u) := by
  have h := iteratedDeriv_standardizedDensity_at_zero ht (k := 1) hn
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, fourierMultiplier_one_re] at h
  simp_rw [← sumSin_eq_im ht] at h
  rw [show (fun u : ℝ => u * sumSin n t u) = (fun u => u ^ 1 * sumSin n t u) by simp,
    integral_pow_mul_sumSin_eq_normalized (by omega) ht] at h
  rw [h]
  simp only [pow_one, skewFourierCoefficient, fourierAverage]
  rw [inverse_two_pi_eq_fourierScale_sq]
  ring

theorem secondDeriv_standardizedDensity_zero_eq_average {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 4 < n) :
    iteratedDeriv 2 (standardizedDensity n t) 0 =
      -(1 / Real.sqrt (2 * Real.pi)) * fourierAverage (fun u => u ^ 2 * sumCos n t u) := by
  have h := iteratedDeriv_standardizedDensity_at_zero ht (k := 2) hn
  simp_rw [fourierMultiplier_two_re, ← sumCos_eq_re ht] at h
  rw [integral_neg, mul_neg, probabilityFourier_integral_eq_average] at h
  simpa only [neg_mul] using h

theorem thirdDeriv_standardizedDensity_zero_eq_average {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 5 < n) :
    iteratedDeriv 3 (standardizedDensity n t) 0 = -skewFourierCoefficient n t *
      fourierAverage (fun u => u ^ 3 * normalizedSumSin n t u) := by
  have h := iteratedDeriv_standardizedDensity_at_zero ht (k := 3) hn
  simp_rw [fourierMultiplier_three_re, ← sumSin_eq_im ht] at h
  rw [integral_neg, integral_pow_mul_sumSin_eq_normalized (by omega) ht] at h
  rw [h]
  simp only [skewFourierCoefficient, fourierAverage]
  rw [inverse_two_pi_eq_fourierScale_sq]
  ring

theorem deriv_standardizedDensity_zero_pos {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) : 0 < deriv (standardizedDensity n t) 0 := by
  rw [deriv_standardizedDensity_zero_eq_average ht (by omega)]
  exact mul_pos (skewFourierCoefficient_pos (by omega) ht) (fourierAverage_firstSine_pos ht hn)

theorem standardizedDensity_second_ratio_lt {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) :
    -iteratedDeriv 2 (standardizedDensity n t) 0 / standardizedDensity n t 0 < 21 / 19 := by
  rw [secondDeriv_standardizedDensity_zero_eq_average ht (by omega),
    standardizedDensity_zero_eq_average ht (by omega)]
  simp only [neg_mul, neg_neg]
  rw [mul_div_mul_left _ _ fourierScale_pos.ne']
  have hc := fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  apply (div_lt_iff₀ hc0).mpr
  nlinarith [fourierAverage_secondCos_lt ht hn]

theorem standardizedDensity_first_ratio_sq_le {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) :
    (deriv (standardizedDensity n t) 0) ^ 2 / (standardizedDensity n t 0) ^ 2 ≤
      (4 / (n : ℝ)) * (20 / 19) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs := Real.sqrt_pos.mpr hnR
  have hc := fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  have hA := fourierAverage_firstSine_pos ht hn
  have hA1 := fourierAverage_firstSine_lt ht hn
  have hratio : 0 ≤ fourierAverage (fun u => u * normalizedSumSin n t u) /
      fourierAverage (sumCos n t) := div_nonneg hA.le hc0.le
  have hratioBound : fourierAverage (fun u => u * normalizedSumSin n t u) /
      fourierAverage (sumCos n t) ≤ 20 / 19 := by
    apply (div_le_iff₀ hc0).mpr
    nlinarith
  have hskew : |tiltStandardMoment t 3| / Real.sqrt (n : ℝ) ≤ 2 / Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_right (abs_tiltStandardMoment_three_le_two ht) hs.le
  have hbound := mul_le_mul hskew hratioBound hratio (by positivity : 0 ≤ 2 / Real.sqrt (n : ℝ))
  have hsq := pow_le_pow_left₀ (mul_nonneg (div_nonneg (abs_nonneg _) hs.le) hratio) hbound 2
  have heq : deriv (standardizedDensity n t) 0 / standardizedDensity n t 0 =
      (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ)) *
        (fourierAverage (fun u => u * normalizedSumSin n t u) / fourierAverage (sumCos n t)) := by
    rw [deriv_standardizedDensity_zero_eq_average ht (by omega),
      standardizedDensity_zero_eq_average ht (by omega), skewFourierCoefficient]
    field_simp
  rw [← div_pow, heq]
  calc
    _ ≤ (2 / Real.sqrt (n : ℝ) * (20 / 19)) ^ 2 := hsq
    _ = (4 / (n : ℝ)) * (20 / 19) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hnR.le]
      norm_num

theorem standardizedDensity_lowerDerivativeBracket_lt {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) :
    lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0)
      (iteratedDeriv 2 (standardizedDensity n t) 0) < 7 / 2 :=
  lowerDerivativeBracket_lt_of_ratios hn
    (standardizedDensity_second_ratio_lt ht hn) (standardizedDensity_first_ratio_sq_le ht hn)

theorem standardizedDensity_signed_derivative_eq {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 5 < n) :
    iteratedDeriv 3 (standardizedDensity n t) 0 +
      (7 / 2) * deriv (standardizedDensity n t) 0 =
        -skewFourierCoefficient n t *
          fourierAverage (fun u => u * (u ^ 2 - 7 / 2) * normalizedSumSin n t u) := by
  have h3 := integrable_pow_mul_normalizedSumSin ht (k := 3) hn
  have h1 : Integrable (fun u : ℝ => u * normalizedSumSin n t u) := by
    simpa only [pow_one] using integrable_pow_mul_normalizedSumSin ht (k := 1) (by omega : 1 + 2 < n)
  have heq : (fun u : ℝ => u * (u ^ 2 - 7 / 2) * normalizedSumSin n t u) =
      (fun u => u ^ 3 * normalizedSumSin n t u -
        (7 / 2) * (u * normalizedSumSin n t u)) := by funext u; ring
  rw [heq, fourierAverage_sub h3 (h1.const_mul _), fourierAverage_const_mul,
    thirdDeriv_standardizedDensity_zero_eq_average ht hn,
    deriv_standardizedDensity_zero_eq_average ht (by omega)]
  ring

end
end ENT.Pang
