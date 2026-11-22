module

public import ENT.Quantitative.FourierRatios
public import ENT.Quantitative.LangevinSharp

/-! Quantitative curvature for the actual diagonal convolution density. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem standardizedDensity_signed_derivative_eq_any {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 5<n) (c : ℝ) :
    iteratedDeriv 3 (standardizedDensity n t) 0 + c*deriv (standardizedDensity n t) 0 =
      -skewFourierCoefficient n t *
        fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) := by
  have h3 := integrable_pow_mul_normalizedSumSin ht (k:=3) hn
  have h1 : Integrable (fun u : ℝ => u*normalizedSumSin n t u) := by
    simpa using integrable_pow_mul_normalizedSumSin ht (k:=1) (by omega : 1+2<n)
  have heq : (fun u : ℝ => u*(u^2-c)*normalizedSumSin n t u) =
      (fun u => u^3*normalizedSumSin n t u - c*(u*normalizedSumSin n t u)) := by
    funext u; ring
  rw [heq, fourierAverage_sub h3 (h1.const_mul _), fourierAverage_const_mul,
    thirdDeriv_standardizedDensity_zero_eq_average ht hn,
    deriv_standardizedDensity_zero_eq_average ht (by omega)]
  ring

theorem standardizedPotential_third_deriv_lower {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) {c d : ℝ}
    (hbracket : lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0) (iteratedDeriv 2 (standardizedDensity n t) 0) ≤ c)
    (haverage : d ≤ fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) /
      fourierAverage (sumCos n t)) :
    (|tiltStandardMoment t 3|/Real.sqrt (n:ℝ))*d ≤
      iteratedDeriv 3 (standardizedPotential n t) 0 := by
  have hw := standardizedDensity_zero_pos (by omega : 2≤n) ht
  have hw1 := deriv_standardizedDensity_zero_pos ht hn
  have hratio := div_nonneg hw1.le hw.le
  have hb := mul_le_mul_of_nonneg_left hbracket hratio
  have hsigned := standardizedDensity_signed_derivative_eq_any ht (by omega : 5<n) c
  have hlower : skewFourierCoefficient n t *
      fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) /
      standardizedDensity n t 0 ≤ iteratedDeriv 3 (standardizedPotential n t) 0 := by
    rw [standardizedPotential_third_deriv_eq_neg_logThirdExpression (by omega) ht,
      logThirdExpression_eq _ _ _ _ hw.ne']
    have he : (iteratedDeriv 3 (standardizedDensity n t) 0 +
        c*deriv (standardizedDensity n t) 0)/standardizedDensity n t 0 =
        iteratedDeriv 3 (standardizedDensity n t) 0/standardizedDensity n t 0 +
          (deriv (standardizedDensity n t) 0/standardizedDensity n t 0)*c := by ring
    rw [hsigned] at he
    simp only [neg_mul, neg_div] at he
    linarith
  have heq : skewFourierCoefficient n t *
      fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) /
      standardizedDensity n t 0 =
      (|tiltStandardMoment t 3|/Real.sqrt (n:ℝ)) *
        (fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) /
          fourierAverage (sumCos n t)) := by
    rw [standardizedDensity_zero_eq_average ht (by omega), skewFourierCoefficient]
    field_simp
  rw [heq] at hlower
  exact (mul_le_mul_of_nonneg_left haverage (by positivity)).trans hlower

theorem diagonalPotential_tilt_quantitative_lower {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) {c d : ℝ} (hd : 0<d)
    (hbracket : lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0) (iteratedDeriv 2 (standardizedDensity n t) 0) ≤ c)
    (haverage : d ≤ fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) /
      fourierAverage (sumCos n t)) :
    ((54/5:ℝ)*d/(n:ℝ))*(Real.sqrt (n:ℝ)*tiltMean t) <
      iteratedDeriv 3 (Spline.diagonalSplinePotential n) (Real.sqrt (n:ℝ)*tiltMean t) := by
  have hv := tiltVariance_pos ht
  have hm := tiltMean_pos ht
  have hs := Real.sqrt_pos.mpr hv
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hnS := Real.sqrt_pos.mpr hnR
  have hstd := standardizedPotential_third_deriv_lower ht hn hbracket haverage
  have hvpow : (Real.sqrt (tiltVariance t)^3)^2 = tiltVariance t^3 := by
    rw [← pow_mul, mul_comm 3 2, pow_mul, Real.sq_sqrt hv.le]
  have hscalar := sharp_langevin_ratio ht
  have hscalar' := mul_lt_mul_of_pos_right hscalar
    (show 0 < (tiltMean t/Real.sqrt (n:ℝ))*d by positivity)
  have hmu : |tiltStandardMoment t 3| =
      -tiltThirdCumulant t/(Real.sqrt (tiltVariance t)^3) := by
    rw [tiltStandardMoment_three ht, abs_of_neg (tiltSkewness_neg ht), tiltSkewness]
    ring
  have he1 : (54/5:ℝ)*((tiltMean t/Real.sqrt (n:ℝ))*d) =
      ((54/5:ℝ)*d/(n:ℝ))*(Real.sqrt (n:ℝ)*tiltMean t) := by
    field_simp [hnR.ne', hnS.ne']
    nlinarith [Real.sq_sqrt hnR.le]
  have he2 : (-tiltThirdCumulant t/(tiltMean t*tiltVariance t^3)) *
      ((tiltMean t/Real.sqrt (n:ℝ))*d) =
      (Real.sqrt (tiltVariance t)^3)⁻¹ *
        ((|tiltStandardMoment t 3|/Real.sqrt (n:ℝ))*d) := by
    rw [hmu]
    have hs3 := pow_ne_zero 3 hs.ne'
    have h6 : Real.sqrt (tiltVariance t)^6 = tiltVariance t^3 := by
      calc
        _ = (Real.sqrt (tiltVariance t)^3)^2 := by ring
        _ = _ := hvpow
    field_simp [hm.ne', hv.ne', hs3, hnS.ne']
    rw [h6]
  rw [he1, he2] at hscalar'
  rw [diagonalPotential_third_deriv_tilt (by omega) ht]
  exact hscalar'.trans_le (mul_le_mul_of_nonneg_left hstd (by positivity))

theorem quant_signed_average_ratio_gt {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 256≤n) :
    (163/250:ℝ)/(509/506) <
      fourierAverage (fun u => u*(u^2-31/10)*normalizedSumSin n t u) /
        fourierAverage (sumCos n t) := by
  have hc := quant_fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  apply (lt_div_iff₀ hc0).mpr
  have hupper := quant_fourierAverage_sumCos_le ht hn
  have hlower := quant_signed_integral_lower ht hn
  linarith

/-- The manuscript's explicit quantitative large-dimensional bound, for the actual density. -/
theorem large_curvature_gt_256 {n : ℕ} (hn : 256≤n) :
    ∀ x ∈ Ioo (0:ℝ) (Real.sqrt (n:ℝ)),
      (7/(n:ℝ))*x < deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x := by
  intro x hx
  obtain ⟨t, ht, _⟩ := existsUnique_tiltCenter (by omega : 0<n) hx
  have h := diagonalPotential_tilt_quantitative_lower ht.1 (by omega : 150≤n)
    (c:=31/10) (d:=(163/250)/(509/506)) (by norm_num)
    (quant_standardizedDensity_lowerDerivativeBracket_lt ht.1 hn).le
    (quant_signed_average_ratio_gt ht.1 hn).le
  rw [ht.2] at h
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hcoeff : (7:ℝ)/(n:ℝ) < ((54/5)*((163/250)/(509/506)))/(n:ℝ) :=
    div_lt_div_of_pos_right (by norm_num) hnR
  have h' := (mul_lt_mul_of_pos_right hcoeff hx.1).trans h
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h'

theorem large_curvature_ge_256 {n : ℕ} (hn : 256≤n) :
    ∀ x ∈ Ioo (0:ℝ) (Real.sqrt (n:ℝ)),
      (7/(n:ℝ))*x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x :=
  fun x hx => (large_curvature_gt_256 hn x hx).le

end
end ENT.Quantitative
