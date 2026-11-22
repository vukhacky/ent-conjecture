module

public import ENT.Quantitative.Fourier150ErrorIntegral
public import ENT.Pang.CurvatureAlgebra

/-! Positivity of the actual signed Fourier integral in Pang Proposition 4.8. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Quantitative.Threshold150
open ENT.Pang

noncomputable section

theorem pangEnvelope_quant_small_lt_gaussian {n : ℕ} (hn : 150≤n) {u : ℝ}
    (hu : u^2≤16/5) : pangEnvelope n u<(103:ℝ)/100*gaussianWeight u := by
  have hnR : (150:ℝ)≤n := by exact_mod_cast hn
  have hb : 0<1+u^2/(n:ℝ) := by positivity
  have hlog : Real.log (1+u^2/(n:ℝ)) * (-((n:ℝ)-1)/2)+u^2/2≤52/1875 := by
    apply (pangEnvelope_log_exponent_le (by omega : 1≤n) u).trans
    have he : u^2/(2*(n:ℝ))+u^4/(4*(n:ℝ))=(2*u^2+u^4)/(4*(n:ℝ)) := by ring
    rw [he]
    apply (div_le_iff₀ (show 0<4*(n:ℝ) by positivity)).mpr
    have hp := pow_le_pow_left₀ (sq_nonneg u) hu 2
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  have hx : Real.exp (52/1875:ℝ)<103/100 := by
    have h := Real.exp_bound_div_one_sub_of_interval' (by norm_num : (0:ℝ)<52/1875)
      (by norm_num : (52:ℝ)/1875<1)
    norm_num at h ⊢
    linarith
  unfold pangEnvelope gaussianWeight
  rw [Real.rpow_def_of_pos hb]
  calc
    Real.exp (Real.log (1+u^2/(n:ℝ)) * (-((n:ℝ)-1)/2)) =
        Real.exp (Real.log (1+u^2/(n:ℝ)) * (-((n:ℝ)-1)/2)+u^2/2)*Real.exp (-u^2/2) := by
      rw [←Real.exp_add]; congr 1; ring
    _<_ := mul_lt_mul_of_pos_right (he.trans_lt hx) (Real.exp_pos _)

def signedGaussianWeight (u : ℝ) : ℝ :=
  (u ^ 2 - 16 / 5) * (u ^ 4 / 6) * gaussianWeight u

def signedFourierIntegrand (n : ℕ) (t u : ℝ) : ℝ :=
  u * (u ^ 2 - 16 / 5) * normalizedSumSin n t u

def signedLowerModel (n : ℕ) (t u : ℝ) : ℝ :=
  signedGaussianWeight u -
  (3 / 100 : ℝ) * quantSmall.indicator (fun v => quantSmallLeadingPolynomial v * gaussianWeight v) u -
  (1 / (n : ℝ)) * positiveErrorWeight n t u -
  (1 / 6 : ℝ) * (pangTail n).indicator
    (fun v => v ^ 6 * (gaussianWeight v + pangEnvelope n v)) u

theorem signedFourierIntegrand_eq (n : ℕ) (t u : ℝ) :
    signedFourierIntegrand n t u = (u ^ 2 - 16 / 5) * (u * normalizedSumSin n t u) := by
  unfold signedFourierIntegrand
  ring

theorem signedGaussianWeight_eq_neg (u : ℝ) :
    signedGaussianWeight u = -quantSmallLeadingPolynomial u * gaussianWeight u := by
  unfold signedGaussianWeight quantSmallLeadingPolynomial
  ring

theorem signed_integrand_small_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 150 ≤ n) {u : ℝ} (hu : u ∈ quantSmall) :
    signedGaussianWeight u - (3 / 100 : ℝ) *
      (quantSmallLeadingPolynomial u * gaussianWeight u) ≤ signedFourierIntegrand n t u := by
  have hupper := (abs_le.mp (abs_mul_normalizedSumSin_le ht (by omega : 0 < n) u)).2
  have hc := sub_nonneg.mpr (sq_le_of_mem_quantSmall hu)
  have h := mul_le_mul_of_nonneg_left hupper hc
  have he : (16 / 5 - u ^ 2) * ((1 / 6 : ℝ) * (u ^ 4 * pangEnvelope n u)) =
      quantSmallLeadingPolynomial u * pangEnvelope n u := by unfold quantSmallLeadingPolynomial; ring
  rw [he] at h
  have hr := mul_le_mul_of_nonneg_left
    (pangEnvelope_quant_small_lt_gaussian hn (sq_le_of_mem_quantSmall hu)).le
    (quantSmallLeadingPolynomial_nonneg hu)
  change quantSmallLeadingPolynomial u * pangEnvelope n u ≤
    quantSmallLeadingPolynomial u * ((103 : ℝ) / 100 * gaussianWeight u) at hr
  rw [signedGaussianWeight_eq_neg, signedFourierIntegrand_eq]
  nlinarith

theorem signed_integrand_middle_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : u ∉ quantSmall) (hut : u ∉ pangTail n) :
    signedGaussianWeight u - (1 / (n : ℝ)) * pangErrorWeight n t u ≤
      signedFourierIntegrand n t u := by
  have hlocal := mul_normalizedSumSin_local_lower_skew ht hn
    (local_frequency_condition hn (le_of_not_gt hut))
  have hc : 0 ≤ u ^ 2 - 16 / 5 := sub_nonneg.mpr (sq_gt_of_not_mem_quantSmall hu).le
  have h := mul_le_mul_of_nonneg_left hlocal hc
  convert h using 1 <;> simp only [signedGaussianWeight, pangErrorWeight, signedFourierIntegrand] <;> ring

theorem signed_integrand_tail_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : u ∉ quantSmall) :
    signedGaussianWeight u - (1 / (n : ℝ)) * pangErrorWeight n t u -
      (1 / 6 : ℝ) * (u ^ 6 * (gaussianWeight u + pangEnvelope n u)) ≤
        signedFourierIntegrand n t u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 ≤ u ^ 2 - 16 / 5 := sub_nonneg.mpr (sq_gt_of_not_mem_quantSmall hu).le
  have h := mul_le_mul_of_nonneg_left
    (abs_le.mp (abs_mul_normalizedSumSin_le ht hn u)).1 hc
  have he : 0 ≤ pangErrorWeight n t u := by
    have hp := positiveErrorWeight_nonneg hn t u
    simpa only [positiveErrorWeight, indicator_of_mem (show u ∈ quantSmallᶜ from hu)] using hp
  have herr : 0 ≤ (1 / (n : ℝ)) * pangErrorWeight n t u := by positivity
  have hg := mul_nonneg (show 0 ≤ u ^ 4 by positivity) (gaussianWeight_pos u).le
  have hr := mul_nonneg (show 0 ≤ u ^ 4 by positivity) (pangEnvelope_pos hn u).le
  unfold signedGaussianWeight
  rw [signedFourierIntegrand_eq]
  nlinarith

theorem signedLowerModel_le {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 150 ≤ n) (u : ℝ) : signedLowerModel n t u ≤ signedFourierIntegrand n t u := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have htail : 0 ≤ (pangTail n).indicator
      (fun v => v ^ 6 * (gaussianWeight v + pangEnvelope n v)) u := by
    by_cases hut : u ∈ pangTail n
    · rw [indicator_of_mem hut]
      exact mul_nonneg (by positivity) (combinedWeight_nonneg hn0 u)
    · rw [indicator_of_notMem hut]
  unfold signedLowerModel
  by_cases hu : u ∈ quantSmall
  · rw [indicator_of_mem hu, positiveErrorWeight,
      indicator_of_notMem (show u ∉ quantSmallᶜ from fun h => h hu), mul_zero, sub_zero]
    have h := signed_integrand_small_lower ht hn hu
    linarith
  · rw [indicator_of_notMem hu, mul_zero, sub_zero, positiveErrorWeight,
      indicator_of_mem (show u ∈ quantSmallᶜ from hu)]
    by_cases hut : u ∈ pangTail n
    · rw [indicator_of_mem hut]
      exact signed_integrand_tail_lower ht hn0 hu
    · rw [indicator_of_notMem hut, mul_zero, sub_zero]
      exact signed_integrand_middle_lower ht hn0 hu hut

theorem integrable_signedGaussianWeight : Integrable signedGaussianWeight := by
  have h := ((integrable_pow_mul_gaussianWeight 6).const_mul (1 / 6 : ℝ)).sub
    ((integrable_pow_mul_gaussianWeight 4).const_mul (8 / 15 : ℝ))
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => by
    simp only [Pi.sub_apply, signedGaussianWeight]
    ring)

theorem fourierAverage_signedGaussianWeight : fourierAverage signedGaussianWeight = 9 / 10 := by
  have he : signedGaussianWeight = (fun u =>
      (1 / 6 : ℝ) * (u ^ 6 * gaussianWeight u) - (8 / 15 : ℝ) * (u ^ 4 * gaussianWeight u)) := by
    funext u
    unfold signedGaussianWeight
    ring
  rw [he, fourierAverage_sub ((integrable_pow_mul_gaussianWeight 6).const_mul _)
    ((integrable_pow_mul_gaussianWeight 4).const_mul _)]
  simp only [fourierAverage_const_mul]
  change (1 / 6 : ℝ) * gaussianMoment 3 - (8 / 15 : ℝ) * gaussianMoment 2 = _
  rw [gaussianMoment_three, gaussianMoment_two]
  norm_num

theorem integrable_signedFourierIntegrand {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 5 < n) : Integrable (signedFourierIntegrand n t) := by
  have h := (integrable_pow_mul_normalizedSumSin ht (k := 3) hn).sub
    ((integrable_pow_mul_normalizedSumSin ht (n := n) (k := 1) (by omega)).const_mul (16 / 5 : ℝ))
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => by
    simp only [Pi.sub_apply, signedFourierIntegrand]
    ring)

theorem integrable_signedLowerModel {n : ℕ} (hn : 14 < n) (t : ℝ) : Integrable (signedLowerModel n t) := by
  have hsmall : Integrable (quantSmall.indicator
      (fun u => quantSmallLeadingPolynomial u * gaussianWeight u)) :=
    integrable_indicator_quantSmall_of_continuous (by
      unfold quantSmallLeadingPolynomial gaussianWeight; fun_prop)
  exact ((integrable_signedGaussianWeight.sub (hsmall.const_mul _)).sub
    ((integrable_positiveErrorWeight hn t).const_mul _)).sub
    (((integrable_pow_mul_combinedWeight (k := 6) (by omega)).indicator
      (measurableSet_pangTail n)).const_mul _)

theorem fourierAverage_signedLowerModel {n : ℕ} (hn : 14 < n) (t : ℝ) :
    fourierAverage (signedLowerModel n t) = 9 / 10 -
      (3 / 100 : ℝ) * fourierAverage (quantSmall.indicator
        (fun u => quantSmallLeadingPolynomial u * gaussianWeight u)) -
      (1 / (n : ℝ)) * fourierAverage (positiveErrorWeight n t) -
      (1 / 6 : ℝ) * normalizedTailMoment n 3 := by
  have h0 := integrable_signedGaussianWeight
  have h1 := (integrable_indicator_quantSmall_of_continuous (show Continuous
      (fun u => quantSmallLeadingPolynomial u * gaussianWeight u) by
        unfold quantSmallLeadingPolynomial gaussianWeight; fun_prop)).const_mul (3 / 100 : ℝ)
  have h2 := (integrable_positiveErrorWeight hn t).const_mul (1 / (n : ℝ))
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

theorem quant_signed_integral_lower {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 150≤n) :
    (7/10:ℝ)-(13/150)*skewSquared t <
      fourierAverage (fun u=>u*(u^2-16/5)*normalizedSumSin n t u) := by
  have hnR : (150:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have h := fourierAverage_mono (integrable_signedLowerModel (by omega) t)
    (integrable_signedFourierIntegrand ht (by omega)) (signedLowerModel_le ht hn)
  rw [fourierAverage_signedLowerModel (by omega) t] at h
  have herr := mul_lt_mul_of_pos_left (quant_error_integral_lt hn ht)
    (show 0<1/(n:ℝ) by positivity)
  have hdiv : (1/(n:ℝ))*(131/5+13*skewSquared t)≤131/750+(13/150)*skewSquared t := by
    have hd := div_le_div_of_nonneg_left (show (0:ℝ)≤131/5+13*skewSquared t by
      linarith [skewSquared_nonneg t]) (by norm_num : (0:ℝ)<150) hnR
    convert hd using 1 <;> ring
  have hs := mul_lt_mul_of_pos_left small_leading_gaussian_bound (by norm_num : (0:ℝ)<3/100)
  have htail := threshold150_tail_order6_le hn
  change (7/10:ℝ)-(13/150)*skewSquared t<fourierAverage (signedFourierIntegrand n t)
  linarith

end
end ENT.Quantitative.Threshold150
