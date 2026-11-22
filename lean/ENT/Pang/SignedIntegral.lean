module

public import ENT.Pang.ErrorIntegral
public import ENT.Pang.CurvatureAlgebra

/-! Positivity of the actual signed Fourier integral in Pang Proposition 4.8. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def signedGaussianWeight (u : ℝ) : ℝ :=
  (u ^ 2 - 7 / 2) * (u ^ 4 / 6) * gaussianWeight u

def signedFourierIntegrand (n : ℕ) (t u : ℝ) : ℝ :=
  u * (u ^ 2 - 7 / 2) * normalizedSumSin n t u

def signedLowerModel (n : ℕ) (u : ℝ) : ℝ :=
  signedGaussianWeight u -
  (1 / 20 : ℝ) * pangSmall.indicator (fun v => smallLeadingPolynomial v * gaussianWeight v) u -
  (1 / (n : ℝ)) * positiveErrorWeight n u -
  (1 / 6 : ℝ) * (pangTail n).indicator
    (fun v => v ^ 6 * (gaussianWeight v + pangEnvelope n v)) u

theorem signedFourierIntegrand_eq (n : ℕ) (t u : ℝ) :
    signedFourierIntegrand n t u = (u ^ 2 - 7 / 2) * (u * normalizedSumSin n t u) := by
  unfold signedFourierIntegrand
  ring

theorem signedGaussianWeight_eq_neg (u : ℝ) :
    signedGaussianWeight u = -smallLeadingPolynomial u * gaussianWeight u := by
  unfold signedGaussianWeight smallLeadingPolynomial
  ring

theorem signed_integrand_small_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 150 ≤ n) {u : ℝ} (hu : u ∈ pangSmall) :
    signedGaussianWeight u - (1 / 20 : ℝ) *
      (smallLeadingPolynomial u * gaussianWeight u) ≤ signedFourierIntegrand n t u := by
  have hupper := (abs_le.mp (abs_mul_normalizedSumSin_le ht (by omega : 0 < n) u)).2
  have hc := sub_nonneg.mpr (sq_le_of_mem_pangSmall hu)
  have h := mul_le_mul_of_nonneg_left hupper hc
  have he : (7 / 2 - u ^ 2) * ((1 / 6 : ℝ) * (u ^ 4 * pangEnvelope n u)) =
      smallLeadingPolynomial u * pangEnvelope n u := by unfold smallLeadingPolynomial; ring
  rw [he] at h
  have hr := mul_le_mul_of_nonneg_left
    (pangEnvelope_small_lt_gaussian hn (sq_le_of_mem_pangSmall hu)).le
    (smallLeadingPolynomial_nonneg hu)
  change smallLeadingPolynomial u * pangEnvelope n u ≤
    smallLeadingPolynomial u * ((21 : ℝ) / 20 * gaussianWeight u) at hr
  rw [signedGaussianWeight_eq_neg, signedFourierIntegrand_eq]
  nlinarith

theorem signed_integrand_middle_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : u ∉ pangSmall) (hut : u ∉ pangTail n) :
    signedGaussianWeight u - (1 / (n : ℝ)) * pangErrorWeight n u ≤
      signedFourierIntegrand n t u := by
  have hlocal := mul_normalizedSumSin_local_lower ht hn
    (local_frequency_condition hn (le_of_not_gt hut))
  have hc : 0 ≤ u ^ 2 - 7 / 2 := sub_nonneg.mpr (sq_gt_of_not_mem_pangSmall hu).le
  have h := mul_le_mul_of_nonneg_left hlocal hc
  convert h using 1 <;> simp only [signedGaussianWeight, pangErrorWeight, signedFourierIntegrand] <;> ring

theorem signed_integrand_tail_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : u ∉ pangSmall) :
    signedGaussianWeight u - (1 / (n : ℝ)) * pangErrorWeight n u -
      (1 / 6 : ℝ) * (u ^ 6 * (gaussianWeight u + pangEnvelope n u)) ≤
        signedFourierIntegrand n t u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 ≤ u ^ 2 - 7 / 2 := sub_nonneg.mpr (sq_gt_of_not_mem_pangSmall hu).le
  have h := mul_le_mul_of_nonneg_left
    (abs_le.mp (abs_mul_normalizedSumSin_le ht hn u)).1 hc
  have he : 0 ≤ pangErrorWeight n u := by
    have hp := positiveErrorWeight_nonneg hn u
    simpa only [positiveErrorWeight, indicator_of_mem (show u ∈ pangSmallᶜ from hu)] using hp
  have herr : 0 ≤ (1 / (n : ℝ)) * pangErrorWeight n u := by positivity
  have hg := mul_nonneg (show 0 ≤ u ^ 4 by positivity) (gaussianWeight_pos u).le
  have hr := mul_nonneg (show 0 ≤ u ^ 4 by positivity) (pangEnvelope_pos hn u).le
  unfold signedGaussianWeight
  rw [signedFourierIntegrand_eq]
  nlinarith

theorem signedLowerModel_le {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 150 ≤ n) (u : ℝ) : signedLowerModel n u ≤ signedFourierIntegrand n t u := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have htail : 0 ≤ (pangTail n).indicator
      (fun v => v ^ 6 * (gaussianWeight v + pangEnvelope n v)) u := by
    by_cases hut : u ∈ pangTail n
    · rw [indicator_of_mem hut]
      exact mul_nonneg (by positivity) (combinedWeight_nonneg hn0 u)
    · rw [indicator_of_notMem hut]
  unfold signedLowerModel
  by_cases hu : u ∈ pangSmall
  · rw [indicator_of_mem hu, positiveErrorWeight,
      indicator_of_notMem (show u ∉ pangSmallᶜ from fun h => h hu), mul_zero, sub_zero]
    have h := signed_integrand_small_lower ht hn hu
    linarith
  · rw [indicator_of_notMem hu, mul_zero, sub_zero, positiveErrorWeight,
      indicator_of_mem (show u ∈ pangSmallᶜ from hu)]
    by_cases hut : u ∈ pangTail n
    · rw [indicator_of_mem hut]
      exact signed_integrand_tail_lower ht hn0 hu
    · rw [indicator_of_notMem hut, mul_zero, sub_zero]
      exact signed_integrand_middle_lower ht hn0 hu hut

theorem integrable_signedGaussianWeight : Integrable signedGaussianWeight := by
  have h := ((integrable_pow_mul_gaussianWeight 6).const_mul (1 / 6 : ℝ)).sub
    ((integrable_pow_mul_gaussianWeight 4).const_mul (7 / 12 : ℝ))
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => by
    simp only [Pi.sub_apply, signedGaussianWeight]
    ring)

theorem fourierAverage_signedGaussianWeight : fourierAverage signedGaussianWeight = 3 / 4 := by
  have he : signedGaussianWeight = (fun u =>
      (1 / 6 : ℝ) * (u ^ 6 * gaussianWeight u) - (7 / 12 : ℝ) * (u ^ 4 * gaussianWeight u)) := by
    funext u
    unfold signedGaussianWeight
    ring
  rw [he, fourierAverage_sub ((integrable_pow_mul_gaussianWeight 6).const_mul _)
    ((integrable_pow_mul_gaussianWeight 4).const_mul _)]
  simp only [fourierAverage_const_mul]
  change (1 / 6 : ℝ) * gaussianMoment 3 - (7 / 12 : ℝ) * gaussianMoment 2 = _
  rw [gaussianMoment_three, gaussianMoment_two]
  norm_num

theorem integrable_signedFourierIntegrand {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 5 < n) : Integrable (signedFourierIntegrand n t) := by
  have h := (integrable_pow_mul_normalizedSumSin ht (k := 3) hn).sub
    ((integrable_pow_mul_normalizedSumSin ht (n := n) (k := 1) (by omega)).const_mul (7 / 2 : ℝ))
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => by
    simp only [Pi.sub_apply, signedFourierIntegrand]
    ring)

theorem integrable_signedLowerModel {n : ℕ} (hn : 14 < n) : Integrable (signedLowerModel n) := by
  have hsmall : Integrable (pangSmall.indicator
      (fun u => smallLeadingPolynomial u * gaussianWeight u)) :=
    integrable_indicator_pangSmall_of_continuous (by
      unfold smallLeadingPolynomial gaussianWeight; fun_prop)
  exact ((integrable_signedGaussianWeight.sub (hsmall.const_mul _)).sub
    ((integrable_positiveErrorWeight hn).const_mul _)).sub
    (((integrable_pow_mul_combinedWeight (k := 6) (by omega)).indicator
      (measurableSet_pangTail n)).const_mul _)

theorem fourierAverage_signedLowerModel {n : ℕ} (hn : 14 < n) :
    fourierAverage (signedLowerModel n) = 3 / 4 -
      (1 / 20 : ℝ) * fourierAverage (pangSmall.indicator
        (fun u => smallLeadingPolynomial u * gaussianWeight u)) -
      (1 / (n : ℝ)) * fourierAverage (positiveErrorWeight n) -
      (1 / 6 : ℝ) * normalizedTailMoment n 3 := by
  have h0 := integrable_signedGaussianWeight
  have h1 := (integrable_indicator_pangSmall_of_continuous (show Continuous
      (fun u => smallLeadingPolynomial u * gaussianWeight u) by
        unfold smallLeadingPolynomial gaussianWeight; fun_prop)).const_mul (1 / 20 : ℝ)
  have h2 := (integrable_positiveErrorWeight hn).const_mul (1 / (n : ℝ))
  have h3 := ((integrable_pow_mul_combinedWeight (n := n) (k := 6) (by omega)).indicator
    (measurableSet_pangTail n)).const_mul (1 / 6 : ℝ)
  have ha := fourierAverage_sub ((h0.sub h1).sub h2) h3
  have hb := fourierAverage_sub (h0.sub h1) h2
  have hc := fourierAverage_sub h0 h1
  simp only [Pi.sub_def] at ha hb hc
  unfold signedLowerModel
  rw [ha, hb, hc]
  simp only [fourierAverage_const_mul]
  rw [fourierAverage_signedGaussianWeight,
    show (fun u : ℝ => u ^ 6 * (gaussianWeight u + pangEnvelope n u)) =
      (fun u => u ^ (2 * 3) * (gaussianWeight u + pangEnvelope n u)) by rfl,
    fourierAverage_tail]

/-- Proposition 4.8, as a positive normalized integral of the actual characteristic function. -/
theorem pang_signed_integral_pos {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n) :
    0 < fourierAverage (fun u => u * (u ^ 2 - 7 / 2) * normalizedSumSin n t u) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := fourierAverage_mono (integrable_signedLowerModel (by omega))
    (integrable_signedFourierIntegrand ht (by omega)) (signedLowerModel_le ht hn)
  rw [fourierAverage_signedLowerModel (by omega)] at h
  have herr := mul_lt_mul_of_pos_left (pang_error_integral_lt hn)
    (show 0 < 1 / (n : ℝ) by positivity)
  rw [show (1 / (n : ℝ)) * 80 = 80 / (n : ℝ) by ring] at herr
  have hs := small_leading_gaussian_bound
  have htail := normalizedTailMoment_order6_lt hn
  have hm := signedIntegralMargin_pos hn
  change 0 < fourierAverage (signedFourierIntegrand n t)
  nlinarith

end
end ENT.Pang
