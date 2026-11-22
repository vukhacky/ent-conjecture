module

public import ENT.Pang.FourierAverage
public import ENT.Pang.SmallEnvelope
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Quantitative refinement at the split c=31/10.
 Exact polynomial control of the small-interval corrections in Pang Appendix B. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Quantitative
open ENT.Pang

noncomputable section

def quantSmallRadius : ℝ := Real.sqrt (31 / 10)
def quantSmall : Set ℝ := Icc (-quantSmallRadius) quantSmallRadius

theorem quantSmallRadius_pos : 0 < quantSmallRadius := by unfold quantSmallRadius; positivity
theorem quantSmallRadius_sq : quantSmallRadius ^ 2 = 31 / 10 := Real.sq_sqrt (by norm_num)
theorem quantSmallRadius_lt_bound : quantSmallRadius < 1761/1000 := by
  have h := quantSmallRadius_sq
  nlinarith [quantSmallRadius_pos]

theorem sq_le_of_mem_quantSmall {u : ℝ} (hu : u ∈ quantSmall) : u ^ 2 ≤ 31 / 10 := by
  have h := pow_le_pow_left₀ (abs_nonneg u) (abs_le.mpr hu) 2
  rwa [sq_abs, quantSmallRadius_sq] at h

theorem sq_gt_of_not_mem_quantSmall {u : ℝ} (hu : u ∉ quantSmall) : 31 / 10 < u ^ 2 := by
  have h : quantSmallRadius < |u| := lt_of_not_ge (by simpa only [quantSmall, mem_Icc, abs_le] using hu)
  have hs := pow_lt_pow_left₀ h quantSmallRadius_pos.le (by norm_num : 2 ≠ 0)
  rwa [quantSmallRadius_sq, sq_abs] at hs

theorem measurableSet_quantSmall : MeasurableSet quantSmall := measurableSet_Icc

theorem fourierScale_lt_two_fifths : 1 / Real.sqrt (2 * Real.pi) < (2 : ℝ) / 5 := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hp := Real.pi_gt_d2
  have hsqrt : (5 : ℝ)/2 < Real.sqrt (2 * Real.pi) := by
    nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
  have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<5/2) hsqrt
  exact lt_of_lt_of_eq h (by norm_num)

theorem gaussianWeight_le_one (u : ℝ) : gaussianWeight u ≤ 1 := by
  unfold gaussianWeight
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])

theorem pangEnvelope_le_one {n : ℕ} (hn : 1 ≤ n) (u : ℝ) : pangEnvelope n u ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have h : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
    linarith
  · linarith

theorem integral_quantSmall_even_pow (k : ℕ) :
    (∫ u in quantSmall, u ^ (2 * k)) =
      2 * quantSmallRadius * (31 / 10 : ℝ) ^ k / ((2 * k + 1 : ℕ) : ℝ) := by
  have ha : -quantSmallRadius ≤ quantSmallRadius := by linarith [quantSmallRadius_pos]
  unfold quantSmall
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
    integral_pow]
  have hp : quantSmallRadius ^ (2 * k) = (31 / 10 : ℝ) ^ k := by
    rw [pow_mul, quantSmallRadius_sq]
  have hneg : (-quantSmallRadius) ^ (2 * k) = quantSmallRadius ^ (2 * k) := by
    simp only [pow_mul, neg_sq]
  rw [pow_add, pow_add, pow_one, pow_one, hneg, hp]
  push_cast
  ring

def quantSmallLeadingPolynomial (u : ℝ) : ℝ := (31 / 10 - u ^ 2) * u ^ 4 / 6

def quantSmallErrorPolynomial (u : ℝ) : ℝ :=
  (31 / 10 - u ^ 2) * ((11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8 +
    (1 / 216 : ℝ) * u ^ 10)

theorem quantSmallLeadingPolynomial_nonneg {u : ℝ} (hu : u ∈ quantSmall) :
    0 ≤ quantSmallLeadingPolynomial u := by
  unfold quantSmallLeadingPolynomial
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr (sq_le_of_mem_quantSmall hu)) (by positivity)) (by norm_num)

theorem quantSmallErrorPolynomial_nonneg {u : ℝ} (hu : u ∈ quantSmall) :
    0 ≤ quantSmallErrorPolynomial u := by
  unfold quantSmallErrorPolynomial
  exact mul_nonneg (sub_nonneg.mpr (sq_le_of_mem_quantSmall hu)) (by positivity)

theorem integrableOn_quantSmall_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f quantSmall := hf.continuousOn.integrableOn_Icc

theorem integrable_indicator_quantSmall_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (quantSmall.indicator f) :=
  (integrableOn_quantSmall_of_continuous hf).integrable_indicator measurableSet_quantSmall

theorem integral_quantSmallLeadingPolynomial :
    (∫ u in quantSmall, quantSmallLeadingPolynomial u) = (29791 / 52500 : ℝ) * quantSmallRadius := by
  have h4 : IntegrableOn (fun u : ℝ => (31 / 60 : ℝ) * u ^ 4) quantSmall :=
    integrableOn_quantSmall_of_continuous (by fun_prop)
  have h6 : IntegrableOn (fun u : ℝ => (1 / 6 : ℝ) * u ^ 6) quantSmall :=
    integrableOn_quantSmall_of_continuous (by fun_prop)
  have he : quantSmallLeadingPolynomial =
      (fun u : ℝ => (31 / 60 : ℝ) * u ^ 4 - (1 / 6 : ℝ) * u ^ 6) := by
    funext u
    unfold quantSmallLeadingPolynomial
    ring
  rw [he, integral_sub h4 h6, integral_const_mul, integral_const_mul,
    show (∫ u in quantSmall, u ^ 4) = 2 * quantSmallRadius * (31 / 10 : ℝ) ^ 2 / 5
      by simpa using integral_quantSmall_even_pow 2,
    show (∫ u in quantSmall, u ^ 6) = 2 * quantSmallRadius * (31 / 10 : ℝ) ^ 3 / 7
      by simpa using integral_quantSmall_even_pow 3]
  ring

theorem integral_quantSmallErrorPolynomial :
    (∫ u in quantSmall, quantSmallErrorPolynomial u) =
      (2400231079 / 1638000000 : ℝ) * quantSmallRadius := by
  have h6 : IntegrableOn (fun u : ℝ => (341 / 600 : ℝ) * u ^ 6) quantSmall :=
    integrableOn_quantSmall_of_continuous (by fun_prop)
  have h8 : IntegrableOn (fun u : ℝ => (23 / 210 : ℝ) * u ^ 8) quantSmall :=
    integrableOn_quantSmall_of_continuous (by fun_prop)
  have h10 : IntegrableOn (fun u : ℝ => (143 / 15120 : ℝ) * u ^ 10) quantSmall :=
    integrableOn_quantSmall_of_continuous (by fun_prop)
  have h12 : IntegrableOn (fun u : ℝ => (1 / 216 : ℝ) * u ^ 12) quantSmall :=
    integrableOn_quantSmall_of_continuous (by fun_prop)
  have he : quantSmallErrorPolynomial = (fun u : ℝ =>
      (341 / 600 : ℝ) * u ^ 6 - (23 / 210 : ℝ) * u ^ 8 -
      (143 / 15120 : ℝ) * u ^ 10 - (1 / 216 : ℝ) * u ^ 12) := by
    funext u
    unfold quantSmallErrorPolynomial
    ring
  have ha := integral_sub ((h6.sub h8).sub h10) h12
  have hb := integral_sub (h6.sub h8) h10
  have hc := integral_sub h6 h8
  simp only [Pi.sub_def] at ha hb hc
  rw [he, ha, hb, hc]
  simp only [integral_const_mul]
  rw [show (∫ u in quantSmall, u ^ 6) = 2 * quantSmallRadius * (31 / 10 : ℝ) ^ 3 / 7
      by simpa using integral_quantSmall_even_pow 3,
    show (∫ u in quantSmall, u ^ 8) = 2 * quantSmallRadius * (31 / 10 : ℝ) ^ 4 / 9
      by simpa using integral_quantSmall_even_pow 4,
    show (∫ u in quantSmall, u ^ 10) = 2 * quantSmallRadius * (31 / 10 : ℝ) ^ 5 / 11
      by simpa using integral_quantSmall_even_pow 5,
    show (∫ u in quantSmall, u ^ 12) = 2 * quantSmallRadius * (31 / 10 : ℝ) ^ 6 / 13
      by simpa using integral_quantSmall_even_pow 6]
  ring

theorem fourierAverage_quantSmallLeadingPolynomial_lt :
    fourierAverage (quantSmall.indicator quantSmallLeadingPolynomial) < 2/5 := by
  rw [fourierAverage, integral_indicator measurableSet_quantSmall,
    integral_quantSmallLeadingPolynomial]
  have h := mul_lt_mul_of_pos_right fourierScale_lt_two_fifths
    (show 0 < (29791 / 52500 : ℝ) * quantSmallRadius from mul_pos (by norm_num) quantSmallRadius_pos)
  nlinarith [quantSmallRadius_lt_bound]

theorem fourierAverage_quantSmallErrorPolynomial_lt :
    fourierAverage (quantSmall.indicator quantSmallErrorPolynomial) < 11/10 := by
  rw [fourierAverage, integral_indicator measurableSet_quantSmall,
    integral_quantSmallErrorPolynomial]
  have h := mul_lt_mul_of_pos_right fourierScale_lt_two_fifths
    (show 0 < (2400231079 / 1638000000 : ℝ) * quantSmallRadius from
      mul_pos (by norm_num) quantSmallRadius_pos)
  nlinarith [quantSmallRadius_lt_bound]

theorem small_leading_gaussian_bound :
    fourierAverage (quantSmall.indicator
      (fun u => quantSmallLeadingPolynomial u * gaussianWeight u)) < 2/5 := by
  apply (fourierAverage_mono
    (integrable_indicator_quantSmall_of_continuous (by
      unfold quantSmallLeadingPolynomial gaussianWeight; fun_prop))
    (integrable_indicator_quantSmall_of_continuous (by
      unfold quantSmallLeadingPolynomial; fun_prop)) ?_).trans_lt fourierAverage_quantSmallLeadingPolynomial_lt
  intro u
  by_cases hu : u ∈ quantSmall
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    exact mul_le_of_le_one_right (quantSmallLeadingPolynomial_nonneg hu) (gaussianWeight_le_one u)
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]

def quantSmallErrorWeight (n : ℕ) (u : ℝ) : ℝ :=
  (31 / 10 - u ^ 2) * (((11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8) *
    gaussianWeight u + (1 / 216 : ℝ) * u ^ 10 * pangEnvelope n u)

theorem quantSmallErrorWeight_le {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : u ∈ quantSmall) :
    quantSmallErrorWeight n u ≤ quantSmallErrorPolynomial u := by
  unfold quantSmallErrorWeight quantSmallErrorPolynomial
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (sq_le_of_mem_quantSmall hu))
  have hg := mul_le_of_le_one_right
    (show 0 ≤ (11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8 by positivity) (gaussianWeight_le_one u)
  have hr := mul_le_of_le_one_right (show 0 ≤ (1 / 216 : ℝ) * u ^ 10 by positivity)
    (pangEnvelope_le_one hn u)
  linarith

theorem small_error_integral_bound {n : ℕ} (hn : 150 ≤ n) :
    fourierAverage (quantSmall.indicator (quantSmallErrorWeight n)) < 11/10 := by
  have hn0 : 0 < n := by omega
  have hc : Continuous (quantSmallErrorWeight n) := by
    unfold quantSmallErrorWeight
    apply (continuous_const.sub (continuous_id.pow 2)).mul
    apply Continuous.add
    · exact ((continuous_const.mul (continuous_id.pow 6)).add
        (continuous_const.mul (continuous_id.pow 8))).mul continuous_gaussianWeight
    · exact (continuous_const.mul (continuous_id.pow 10)).mul (continuous_pangEnvelope hn0)
  apply (fourierAverage_mono (integrable_indicator_quantSmall_of_continuous hc)
    (integrable_indicator_quantSmall_of_continuous (by
      unfold quantSmallErrorPolynomial; fun_prop)) ?_).trans_lt fourierAverage_quantSmallErrorPolynomial_lt
  intro u
  by_cases hu : u ∈ quantSmall
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    exact quantSmallErrorWeight_le (by omega) hu
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]

end
end ENT.Quantitative
