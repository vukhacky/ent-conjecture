module

public import ENT.Pang.FourierAverage
public import ENT.Pang.SmallEnvelope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact polynomial control of the small-interval corrections in Pang Appendix B. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def pangSmallRadius : ℝ := Real.sqrt (7 / 2)
def pangSmall : Set ℝ := Icc (-pangSmallRadius) pangSmallRadius

theorem pangSmallRadius_pos : 0 < pangSmallRadius := by unfold pangSmallRadius; positivity
theorem pangSmallRadius_sq : pangSmallRadius ^ 2 = 7 / 2 := Real.sq_sqrt (by norm_num)
theorem pangSmallRadius_lt_two : pangSmallRadius < 2 := by
  have h := pangSmallRadius_sq
  nlinarith [pangSmallRadius_pos]

theorem sq_le_of_mem_pangSmall {u : ℝ} (hu : u ∈ pangSmall) : u ^ 2 ≤ 7 / 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg u) (abs_le.mpr hu) 2
  rwa [sq_abs, pangSmallRadius_sq] at h

theorem sq_gt_of_not_mem_pangSmall {u : ℝ} (hu : u ∉ pangSmall) : 7 / 2 < u ^ 2 := by
  have h : pangSmallRadius < |u| := lt_of_not_ge (by simpa only [pangSmall, mem_Icc, abs_le] using hu)
  have hs := pow_lt_pow_left₀ h pangSmallRadius_pos.le (by norm_num : 2 ≠ 0)
  rwa [pangSmallRadius_sq, sq_abs] at hs

theorem measurableSet_pangSmall : MeasurableSet pangSmall := measurableSet_Icc

theorem fourierScale_lt_half : 1 / Real.sqrt (2 * Real.pi) < (1 : ℝ) / 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_gt_three
  have hsqrt : (2 : ℝ) < Real.sqrt (2 * Real.pi) := by nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  exact one_div_lt_one_div_of_lt (by norm_num) hsqrt

theorem gaussianWeight_le_one (u : ℝ) : gaussianWeight u ≤ 1 := by
  unfold gaussianWeight
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])

theorem pangEnvelope_le_one {n : ℕ} (hn : 1 ≤ n) (u : ℝ) : pangEnvelope n u ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have h : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
    linarith
  · linarith

theorem integral_pangSmall_even_pow (k : ℕ) :
    (∫ u in pangSmall, u ^ (2 * k)) =
      2 * pangSmallRadius * (7 / 2 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ) := by
  have ha : -pangSmallRadius ≤ pangSmallRadius := by linarith [pangSmallRadius_pos]
  unfold pangSmall
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
    integral_pow]
  have hp : pangSmallRadius ^ (2 * k) = (7 / 2 : ℝ) ^ k := by
    rw [pow_mul, pangSmallRadius_sq]
  have hneg : (-pangSmallRadius) ^ (2 * k) = pangSmallRadius ^ (2 * k) := by
    simp only [pow_mul, neg_sq]
  rw [pow_add, pow_add, pow_one, pow_one, hneg, hp]
  push_cast
  ring

def smallLeadingPolynomial (u : ℝ) : ℝ := (7 / 2 - u ^ 2) * u ^ 4 / 6

def smallErrorPolynomial (u : ℝ) : ℝ :=
  (7 / 2 - u ^ 2) * ((11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8 +
    (1 / 216 : ℝ) * u ^ 10)

theorem smallLeadingPolynomial_nonneg {u : ℝ} (hu : u ∈ pangSmall) :
    0 ≤ smallLeadingPolynomial u := by
  unfold smallLeadingPolynomial
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (sq_le_of_mem_pangSmall hu)) (by positivity)) (by norm_num)

theorem smallErrorPolynomial_nonneg {u : ℝ} (hu : u ∈ pangSmall) :
    0 ≤ smallErrorPolynomial u := by
  unfold smallErrorPolynomial
  exact mul_nonneg (sub_nonneg.mpr (sq_le_of_mem_pangSmall hu)) (by positivity)

theorem integrableOn_pangSmall_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f pangSmall := hf.continuousOn.integrableOn_Icc

theorem integrable_indicator_pangSmall_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (pangSmall.indicator f) :=
  (integrableOn_pangSmall_of_continuous hf).integrable_indicator measurableSet_pangSmall

theorem integral_smallLeadingPolynomial :
    (∫ u in pangSmall, smallLeadingPolynomial u) = (49 / 60 : ℝ) * pangSmallRadius := by
  have h4 : IntegrableOn (fun u : ℝ => (7 / 12 : ℝ) * u ^ 4) pangSmall :=
    integrableOn_pangSmall_of_continuous (by fun_prop)
  have h6 : IntegrableOn (fun u : ℝ => (1 / 6 : ℝ) * u ^ 6) pangSmall :=
    integrableOn_pangSmall_of_continuous (by fun_prop)
  have he : smallLeadingPolynomial =
      (fun u : ℝ => (7 / 12 : ℝ) * u ^ 4 - (1 / 6 : ℝ) * u ^ 6) := by
    funext u
    unfold smallLeadingPolynomial
    ring
  rw [he, integral_sub h4 h6, integral_const_mul, integral_const_mul,
    show (∫ u in pangSmall, u ^ 4) = 2 * pangSmallRadius * (7 / 2 : ℝ) ^ 2 / 5
      by simpa using integral_pangSmall_even_pow 2,
    show (∫ u in pangSmall, u ^ 6) = 2 * pangSmallRadius * (7 / 2 : ℝ) ^ 3 / 7
      by simpa using integral_pangSmall_even_pow 3]
  ring

theorem integral_smallErrorPolynomial :
    (∫ u in pangSmall, smallErrorPolynomial u) =
      (6153077 / 2471040 : ℝ) * pangSmallRadius := by
  have h6 : IntegrableOn (fun u : ℝ => (77 / 120 : ℝ) * u ^ 6) pangSmall :=
    integrableOn_pangSmall_of_continuous (by fun_prop)
  have h8 : IntegrableOn (fun u : ℝ => (1 / 10 : ℝ) * u ^ 8) pangSmall :=
    integrableOn_pangSmall_of_continuous (by fun_prop)
  have h10 : IntegrableOn (fun u : ℝ => (23 / 3024 : ℝ) * u ^ 10) pangSmall :=
    integrableOn_pangSmall_of_continuous (by fun_prop)
  have h12 : IntegrableOn (fun u : ℝ => (1 / 216 : ℝ) * u ^ 12) pangSmall :=
    integrableOn_pangSmall_of_continuous (by fun_prop)
  have he : smallErrorPolynomial = (fun u : ℝ =>
      (77 / 120 : ℝ) * u ^ 6 - (1 / 10 : ℝ) * u ^ 8 -
      (23 / 3024 : ℝ) * u ^ 10 - (1 / 216 : ℝ) * u ^ 12) := by
    funext u
    unfold smallErrorPolynomial
    ring
  have ha := integral_sub ((h6.sub h8).sub h10) h12
  have hb := integral_sub (h6.sub h8) h10
  have hc := integral_sub h6 h8
  simp only [Pi.sub_def] at ha hb hc
  rw [he, ha, hb, hc]
  simp only [integral_const_mul]
  rw [show (∫ u in pangSmall, u ^ 6) = 2 * pangSmallRadius * (7 / 2 : ℝ) ^ 3 / 7
      by simpa using integral_pangSmall_even_pow 3,
    show (∫ u in pangSmall, u ^ 8) = 2 * pangSmallRadius * (7 / 2 : ℝ) ^ 4 / 9
      by simpa using integral_pangSmall_even_pow 4,
    show (∫ u in pangSmall, u ^ 10) = 2 * pangSmallRadius * (7 / 2 : ℝ) ^ 5 / 11
      by simpa using integral_pangSmall_even_pow 5,
    show (∫ u in pangSmall, u ^ 12) = 2 * pangSmallRadius * (7 / 2 : ℝ) ^ 6 / 13
      by simpa using integral_pangSmall_even_pow 6]
  ring

theorem fourierAverage_smallLeadingPolynomial_lt :
    fourierAverage (pangSmall.indicator smallLeadingPolynomial) < 1 := by
  rw [fourierAverage, integral_indicator measurableSet_pangSmall,
    integral_smallLeadingPolynomial]
  have h := mul_lt_mul_of_pos_right fourierScale_lt_half
    (show 0 < (49 / 60 : ℝ) * pangSmallRadius from mul_pos (by norm_num) pangSmallRadius_pos)
  nlinarith [pangSmallRadius_lt_two]

theorem fourierAverage_smallErrorPolynomial_lt :
    fourierAverage (pangSmall.indicator smallErrorPolynomial) < 3 := by
  rw [fourierAverage, integral_indicator measurableSet_pangSmall,
    integral_smallErrorPolynomial]
  have h := mul_lt_mul_of_pos_right fourierScale_lt_half
    (show 0 < (6153077 / 2471040 : ℝ) * pangSmallRadius from
      mul_pos (by norm_num) pangSmallRadius_pos)
  nlinarith [pangSmallRadius_lt_two]

theorem small_leading_gaussian_bound :
    fourierAverage (pangSmall.indicator
      (fun u => smallLeadingPolynomial u * gaussianWeight u)) < 1 := by
  apply (fourierAverage_mono
    (integrable_indicator_pangSmall_of_continuous (by
      unfold smallLeadingPolynomial gaussianWeight; fun_prop))
    (integrable_indicator_pangSmall_of_continuous (by
      unfold smallLeadingPolynomial; fun_prop)) ?_).trans_lt fourierAverage_smallLeadingPolynomial_lt
  intro u
  by_cases hu : u ∈ pangSmall
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    exact mul_le_of_le_one_right (smallLeadingPolynomial_nonneg hu) (gaussianWeight_le_one u)
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]

def smallErrorWeight (n : ℕ) (u : ℝ) : ℝ :=
  (7 / 2 - u ^ 2) * (((11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8) *
    gaussianWeight u + (1 / 216 : ℝ) * u ^ 10 * pangEnvelope n u)

theorem smallErrorWeight_le {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : u ∈ pangSmall) :
    smallErrorWeight n u ≤ smallErrorPolynomial u := by
  unfold smallErrorWeight smallErrorPolynomial
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (sq_le_of_mem_pangSmall hu))
  have hg := mul_le_of_le_one_right
    (show 0 ≤ (11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8 by positivity) (gaussianWeight_le_one u)
  have hr := mul_le_of_le_one_right (show 0 ≤ (1 / 216 : ℝ) * u ^ 10 by positivity)
    (pangEnvelope_le_one hn u)
  linarith

theorem small_error_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    fourierAverage (pangSmall.indicator (smallErrorWeight n)) < 3 := by
  have hn0 : 0 < n := by omega
  have hc : Continuous (smallErrorWeight n) := by
    unfold smallErrorWeight
    apply (continuous_const.sub (continuous_id.pow 2)).mul
    apply Continuous.add
    · exact ((continuous_const.mul (continuous_id.pow 6)).add
        (continuous_const.mul (continuous_id.pow 8))).mul continuous_gaussianWeight
    · exact (continuous_const.mul (continuous_id.pow 10)).mul (continuous_pangEnvelope hn0)
  apply (fourierAverage_mono (integrable_indicator_pangSmall_of_continuous hc)
    (integrable_indicator_pangSmall_of_continuous (by
      unfold smallErrorPolynomial; fun_prop)) ?_).trans_lt fourierAverage_smallErrorPolynomial_lt
  intro u
  by_cases hu : u ∈ pangSmall
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    exact smallErrorWeight_le (by omega) hu
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]

end
end ENT.Pang
