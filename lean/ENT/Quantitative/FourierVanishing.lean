module

public import ENT.Quantitative.FourierSignedIntegral
public import ENT.Pang.DerivativeIntegralBounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform Fourier error bounds which vanish with dimension. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem vanishing_small_envelope {n : ℕ} (hn : 256≤n) {u : ℝ}
    (hu : u^2≤31/10) :
    pangEnvelope n u < (1+6/(n:ℝ))*gaussianWeight u := by
  have hnR : (256:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hb : 0<1+u^2/(n:ℝ) := by positivity
  have hlog : Real.log (1+u^2/(n:ℝ)) * (-((n:ℝ)-1)/2)+u^2/2 ≤ 77/(16*(n:ℝ)) := by
    apply (pangEnvelope_log_exponent_le (by omega : 1≤n) u).trans
    have he : u^2/(2*(n:ℝ))+u^4/(4*(n:ℝ)) = (2*u^2+u^4)/(4*(n:ℝ)) := by ring
    rw [he]
    have hp := pow_le_pow_left₀ (sq_nonneg u) hu 2
    apply (div_le_iff₀ (by positivity : 0<4*(n:ℝ))).mpr
    field_simp
    nlinarith
  have hxpos : (0:ℝ)<77/(16*(n:ℝ)) := by positivity
  have hxlt : (77:ℝ)/(16*(n:ℝ))<1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hex := Real.exp_bound_div_one_sub_of_interval' hxpos hxlt
  have hrat : (1:ℝ)/(1-77/(16*(n:ℝ))) ≤ 1+6/(n:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0<1-77/(16*(n:ℝ)))).mpr
    field_simp
    nlinarith
  have he := (Real.exp_le_exp.mpr hlog).trans_lt (hex.trans_le hrat)
  unfold pangEnvelope gaussianWeight
  rw [Real.rpow_def_of_pos hb]
  calc
    Real.exp (Real.log (1+u^2/(n:ℝ)) * (-((n:ℝ)-1)/2)) =
      Real.exp (Real.log (1+u^2/(n:ℝ)) * (-((n:ℝ)-1)/2)+u^2/2)*Real.exp (-u^2/2) := by
        rw [←Real.exp_add]; congr 1; ring
    _ < _ := mul_lt_mul_of_pos_right he (Real.exp_pos _)

def vanishingSignedLowerModel (n : ℕ) (u : ℝ) : ℝ :=
  signedGaussianWeight u -
  (6/(n:ℝ))*quantSmall.indicator (fun v => quantSmallLeadingPolynomial v*gaussianWeight v) u -
  (1/(n:ℝ))*positiveErrorWeight n u -
  (1/6:ℝ)*(pangTail n).indicator (fun v => v^6*(gaussianWeight v+pangEnvelope n v)) u

theorem vanishing_signed_small_lower {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n)
    {u : ℝ} (hu : u∈quantSmall) :
    signedGaussianWeight u-(6/(n:ℝ))*(quantSmallLeadingPolynomial u*gaussianWeight u) ≤
      signedFourierIntegrand n t u := by
  have hupper := (abs_le.mp (abs_mul_normalizedSumSin_le ht (by omega : 0<n) u)).2
  have hc := sub_nonneg.mpr (sq_le_of_mem_quantSmall hu)
  have h := mul_le_mul_of_nonneg_left hupper hc
  have he : (31/10-u^2)*((1/6:ℝ)*(u^4*pangEnvelope n u)) =
      quantSmallLeadingPolynomial u*pangEnvelope n u := by unfold quantSmallLeadingPolynomial; ring
  rw [he] at h
  have hr := mul_le_mul_of_nonneg_left
    (vanishing_small_envelope hn (sq_le_of_mem_quantSmall hu)).le
    (quantSmallLeadingPolynomial_nonneg hu)
  rw [signedGaussianWeight_eq_neg, signedFourierIntegrand_eq]
  nlinarith

theorem vanishingSignedLowerModel_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) (u : ℝ) :
    vanishingSignedLowerModel n u ≤ signedFourierIntegrand n t u := by
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn0
  have htail : 0≤(pangTail n).indicator
      (fun v=>v^6*(gaussianWeight v+pangEnvelope n v)) u := by
    by_cases hut : u∈pangTail n
    · rw [indicator_of_mem hut]
      exact mul_nonneg (by positivity) (combinedWeight_nonneg hn0 u)
    · rw [indicator_of_notMem hut]
  unfold vanishingSignedLowerModel
  by_cases hu : u∈quantSmall
  · rw [indicator_of_mem hu, positiveErrorWeight,
      indicator_of_notMem (show u∉quantSmallᶜ from fun h=>h hu), mul_zero, sub_zero]
    linarith [vanishing_signed_small_lower ht hn hu]
  · rw [indicator_of_notMem hu, mul_zero, sub_zero, positiveErrorWeight,
      indicator_of_mem (show u∈quantSmallᶜ from hu)]
    by_cases hut : u∈pangTail n
    · rw [indicator_of_mem hut]
      exact signed_integrand_tail_lower ht hn0 hu
    · rw [indicator_of_notMem hut, mul_zero, sub_zero]
      exact signed_integrand_middle_lower ht hn0 hu hut

theorem integrable_vanishingSignedLowerModel {n : ℕ} (hn : 14<n) :
    Integrable (vanishingSignedLowerModel n) := by
  have hs : Integrable (quantSmall.indicator
      (fun u => quantSmallLeadingPolynomial u*gaussianWeight u)) :=
    integrable_indicator_quantSmall_of_continuous (by
      unfold quantSmallLeadingPolynomial gaussianWeight; fun_prop)
  exact ((integrable_signedGaussianWeight.sub (hs.const_mul _)).sub
    ((integrable_positiveErrorWeight hn).const_mul _)).sub
    (((integrable_pow_mul_combinedWeight (k:=6) (by omega)).indicator
      (measurableSet_pangTail n)).const_mul _)

theorem fourierAverage_vanishingSignedLowerModel {n : ℕ} (hn : 14<n) :
    fourierAverage (vanishingSignedLowerModel n) = 19/20 -
      (6/(n:ℝ))*fourierAverage (quantSmall.indicator
        (fun u => quantSmallLeadingPolynomial u*gaussianWeight u)) -
      (1/(n:ℝ))*fourierAverage (positiveErrorWeight n) -
      (1/6:ℝ)*normalizedTailMoment n 3 := by
  have h0 := integrable_signedGaussianWeight
  have h1 := (integrable_indicator_quantSmall_of_continuous (show Continuous
      (fun u => quantSmallLeadingPolynomial u*gaussianWeight u) by
        unfold quantSmallLeadingPolynomial gaussianWeight; fun_prop)).const_mul (6/(n:ℝ))
  have h2 := (integrable_positiveErrorWeight hn).const_mul (1/(n:ℝ))
  have h3 := ((integrable_pow_mul_combinedWeight (n:=n) (k:=6) (by omega)).indicator
    (measurableSet_pangTail n)).const_mul (1/6:ℝ)
  have ha := fourierAverage_sub ((h0.sub h1).sub h2) h3
  have hb := fourierAverage_sub (h0.sub h1) h2
  have hc := fourierAverage_sub h0 h1
  simp only [Pi.sub_def] at ha hb hc
  unfold vanishingSignedLowerModel
  rw [ha,hb,hc]
  simp only [fourierAverage_const_mul]
  rw [fourierAverage_signedGaussianWeight,
    show (fun u : ℝ=>u^6*(gaussianWeight u+pangEnvelope n u)) =
      (fun u=>u^(2*3)*(gaussianWeight u+pangEnvelope n u)) by rfl,
    fourierAverage_tail]

def signedIntegralLower (n : ℕ) : ℝ :=
  19/20 - (6/(n:ℝ))*(2/5) - (1/(n:ℝ))*(70623/1000) -
    ((4/(n:ℝ))^3*(10395+12969))/6

theorem signedIntegralLower_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) :
    signedIntegralLower n ≤ fourierAverage (fun u=>u*(u^2-31/10)*normalizedSumSin n t u) := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have h := fourierAverage_mono (integrable_vanishingSignedLowerModel (by omega))
    (integrable_signedFourierIntegrand ht (by omega)) (vanishingSignedLowerModel_le ht hn)
  rw [fourierAverage_vanishingSignedLowerModel (by omega)] at h
  have hs := mul_le_mul_of_nonneg_left small_leading_gaussian_bound.le (by positivity : 0≤6/(n:ℝ))
  have he := mul_le_mul_of_nonneg_left (quant_error_integral_lt hn).le (by positivity : 0≤1/(n:ℝ))
  have ht0 := normalizedTailMoment_le (n:=n) (k:=3) (q:=6) (by omega) (by omega)
  rw [gaussianMoment_six] at ht0
  have hm : envelopeMoment n 6 ≤ 12969 := by
    apply (envelopeMoment_le_at256 hn 6 (by norm_num)).trans
    norm_num [momentMajorant]
  have ht1 := mul_le_mul_of_nonneg_left (add_le_add_left hm 10395)
    (by positivity : 0≤(4/(n:ℝ))^3)
  change signedIntegralLower n ≤ fourierAverage (signedFourierIntegrand n t)
  unfold signedIntegralLower
  norm_num only [Nat.reduceSub] at ht0
  linarith

def firstSineLower (n : ℕ) : ℝ := 1/2-457/(36*(n:ℝ))

theorem firstSineLower_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) :
    firstSineLower n ≤ fourierAverage (fun u=>u*normalizedSumSin n t u) := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hi : Integrable (fun u=>u*normalizedSumSin n t u) := by
    simpa using integrable_pow_mul_normalizedSumSin ht (k:=1) (by omega : 1+2<n)
  have h := fourierAverage_mono (integrable_firstSineLowerModel (by omega)) hi
    (firstSineLowerModel_le ht (by omega))
  rw [fourierAverage_firstSineLowerModel (by omega)] at h
  have h10 := div_le_div_of_nonneg_right (envelopeMoment_order10_lt (by omega : 150≤n)).le
    (by positivity : 0≤216*(n:ℝ))
  have htail := div_le_div_of_nonneg_right (normalizedTailMoment_order4_lt (by omega : 150≤n)).le
    (by norm_num : (0:ℝ)≤6)
  have he : (11:ℝ)/(4*(n:ℝ))+5/(2*(n:ℝ))+1500/(216*(n:ℝ))+(3/(n:ℝ))/6 =
      457/(36*(n:ℝ)) := by ring
  unfold firstSineLower
  linarith

def parameterSignedLower (n : ℕ) (c : ℝ) : ℝ :=
  signedIntegralLower n+(31/10-c)*firstSineLower n

theorem parameterSignedLower_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n)
    {c : ℝ} (hc : c≤31/10) :
    parameterSignedLower n c ≤ fourierAverage (fun u=>u*(u^2-c)*normalizedSumSin n t u) := by
  have h1 := integrable_pow_mul_normalizedSumSin ht (n:=n) (k:=1) (by omega : 1+2<n)
  have h1' : Integrable (fun u=>u*normalizedSumSin n t u) := by simpa using h1
  have h3 := integrable_signedFourierIntegrand ht (by omega : 5<n)
  have he : (fun u : ℝ=>u*(u^2-c)*normalizedSumSin n t u) =
      (fun u=>signedFourierIntegrand n t u+(31/10-c)*(u*normalizedSumSin n t u)) := by
    funext u; unfold signedFourierIntegrand; ring
  rw [he, fourierAverage_add h3 (h1'.const_mul _), fourierAverage_const_mul]
  exact add_le_add (signedIntegralLower_le ht hn)
    (mul_le_mul_of_nonneg_left (firstSineLower_le ht hn) (by linarith))

end
end ENT.Quantitative
