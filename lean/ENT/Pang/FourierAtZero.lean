module

public import ENT.Pang.FourierDerivatives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The four genuine density derivatives at zero, as positive-halfline integrals. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

theorem integral_even_eq_two_mul_Ioi {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2 * ∫ x in Ioi 0, f x := by
  have hfun : (fun x : ℝ => (Ioi (0 : ℝ)).indicator f (-x)) =
      (Iio (0 : ℝ)).indicator f := by
    funext x
    by_cases hx : x < 0
    · have hneg : -x ∈ Ioi (0 : ℝ) := by simpa using neg_pos.mpr hx
      rw [indicator_of_mem hneg, indicator_of_mem hx, heven]
    · have hneg : -x ∉ Ioi (0 : ℝ) := by simpa using not_lt.mpr (neg_nonpos.mpr (le_of_not_gt hx))
      rw [indicator_of_notMem hneg, indicator_of_notMem hx]
  have h := Measure.integral_comp_mul_left ((Ioi (0 : ℝ)).indicator f) (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  rw [hfun, integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi] at h
  have hsplit := intervalIntegral.integral_Iio_add_Ici (b := (0 : ℝ))
    hf.integrableOn hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi] at hsplit
  linarith

theorem sumCos_neg (n : ℕ) (t u : ℝ) : sumCos n t (-u) = sumCos n t u := by
  simp only [sumCos, neg_mul, Real.cos_neg]

theorem sumSin_neg (n : ℕ) (t u : ℝ) : sumSin n t (-u) = -sumSin n t u := by
  simp only [sumSin, neg_mul, Real.sin_neg, integral_neg]

theorem integrable_pow_mul_sumCos {t : ℝ} (ht : 0 < t) {n k : ℕ}
    (hn : k + 2 < n) : Integrable (fun u : ℝ => u ^ k * sumCos n t u) := by
  have h := (integrable_pow_smul_charFun_standardizedSumLaw ht hn).re
  convert h using 1
  funext u
  rw [sumCos_eq_re ht]
  simp only [Complex.smul_re, smul_eq_mul, RCLike.re_to_complex]

theorem integrable_pow_mul_sumSin {t : ℝ} (ht : 0 < t) {n k : ℕ}
    (hn : k + 2 < n) : Integrable (fun u : ℝ => u ^ k * sumSin n t u) := by
  have h := (integrable_pow_smul_charFun_standardizedSumLaw ht hn).im
  convert h using 1
  funext u
  rw [sumSin_eq_im ht]
  simp only [Complex.smul_im, smul_eq_mul, RCLike.im_to_complex]

theorem iteratedDeriv_standardizedDensity_at_zero {t : ℝ} (ht : 0 < t)
    {n k : ℕ} (hn : k + 2 < n) :
    iteratedDeriv k (standardizedDensity n t) 0 =
      (2 * Real.pi)⁻¹ * ∫ u : ℝ,
        ((-Complex.I * (u : ℂ)) ^ k * charFun (standardizedSumLaw n t) u).re := by
  rw [iteratedDeriv_standardizedDensity ht hn]
  change (((2 * Real.pi)⁻¹ : ℝ) •
    ∫ u, fourierDerivativeIntegrand (charFun (standardizedSumLaw n t)) k 0 u).re = _
  rw [Complex.smul_re, smul_eq_mul]
  have h := (integral_re (integrable_fourierDerivativeIntegrand ht hn 0)).symm
  simp only [RCLike.re_to_complex] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [fourierDerivativeIntegrand, probabilityFourierKernel, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

theorem fourierMultiplier_one_re (u : ℝ) (z : ℂ) :
    ((-Complex.I * (u : ℂ)) ^ 1 * z).re = u * z.im := by
  simp [Complex.mul_re, Complex.mul_im]

theorem fourierMultiplier_two_re (u : ℝ) (z : ℂ) :
    ((-Complex.I * (u : ℂ)) ^ 2 * z).re = -(u ^ 2 * z.re) := by
  simp [pow_two, Complex.mul_re, Complex.mul_im]

theorem fourierMultiplier_three_re (u : ℝ) (z : ℂ) :
    ((-Complex.I * (u : ℂ)) ^ 3 * z).re = -(u ^ 3 * z.im) := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]

theorem standardizedDensity_zero_integral {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 2 < n) :
    standardizedDensity n t 0 = Real.pi⁻¹ * ∫ u in Ioi 0, sumCos n t u := by
  have h := iteratedDeriv_standardizedDensity_at_zero ht (k := 0) hn
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h
  simp_rw [← sumCos_eq_re ht] at h
  rw [h, integral_even_eq_two_mul_Ioi
    (by simpa only [pow_zero, one_mul] using integrable_pow_mul_sumCos ht (k := 0) hn)
    (sumCos_neg n t)]
  field_simp

theorem deriv_standardizedDensity_zero_integral {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 3 < n) :
    deriv (standardizedDensity n t) 0 = Real.pi⁻¹ * ∫ u in Ioi 0, u * sumSin n t u := by
  have h := iteratedDeriv_standardizedDensity_at_zero ht (k := 1) hn
  simp only [iteratedDeriv_one] at h
  simp_rw [fourierMultiplier_one_re, ← sumSin_eq_im ht] at h
  rw [h, integral_even_eq_two_mul_Ioi
    (by simpa only [pow_one] using integrable_pow_mul_sumSin ht (k := 1) hn)
    (fun u => by rw [sumSin_neg]; ring)]
  field_simp

theorem secondDeriv_standardizedDensity_zero_integral {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 4 < n) :
    iteratedDeriv 2 (standardizedDensity n t) 0 =
      -Real.pi⁻¹ * ∫ u in Ioi 0, u ^ 2 * sumCos n t u := by
  rw [iteratedDeriv_standardizedDensity_at_zero ht hn]
  simp_rw [fourierMultiplier_two_re, ← sumCos_eq_re ht]
  rw [integral_neg, integral_even_eq_two_mul_Ioi (integrable_pow_mul_sumCos ht hn)
    (fun u => by rw [sumCos_neg]; ring)]
  field_simp

theorem thirdDeriv_standardizedDensity_zero_integral {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 5 < n) :
    iteratedDeriv 3 (standardizedDensity n t) 0 =
      -Real.pi⁻¹ * ∫ u in Ioi 0, u ^ 3 * sumSin n t u := by
  rw [iteratedDeriv_standardizedDensity_at_zero ht hn]
  simp_rw [fourierMultiplier_three_re, ← sumSin_eq_im ht]
  rw [integral_neg, integral_even_eq_two_mul_Ioi (integrable_pow_mul_sumSin ht hn)
    (fun u => by rw [sumSin_neg]; ring)]
  field_simp

end
end ENT.Pang
