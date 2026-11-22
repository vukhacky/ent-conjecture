module

public import ENT.Quantitative.FourierRatios

/-! Fourier derivative-ratio estimates for dimensions at least 150. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem cosineMajorantLower_at150 {n : ℕ} (hn : 150 ≤ n) :
    (9850:ℝ)/10000 < cosineMajorantLower n := by
  have hnR : (150:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hm3 : momentMajorant n 3 ≤ 17131/1000 := by
    have h := momentMajorant_antitone (by norm_num : 16≤150) hn 3 (by norm_num)
    norm_num [momentMajorant] at h ⊢
    linarith
  have h1 : (3:ℝ)/(7*(n:ℝ)) ≤ 3/(7*150) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : momentMajorant n 3/(12*(n:ℝ)) ≤ (17131/1000)/(12*150) :=
    (div_le_div_of_nonneg_right hm3 (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
  have h4 : (4:ℝ)/(n:ℝ) ≤ 4/150 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have htail : (4/(n:ℝ))^3*(15+momentMajorant n 3) ≤ (4/150:ℝ)^3*(15+17131/1000) :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) h4 3) (by linarith)
      (by linarith [momentMajorant_pos (by omega : 16≤n) 3 (by norm_num)]) (by norm_num)
  unfold cosineMajorantLower
  linarith

theorem threshold150_fourierAverage_sumCos_gt {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 150≤n) :
    (9850:ℝ)/10000 < fourierAverage (sumCos n t) :=
  (cosineMajorantLower_at150 hn).trans_le (cosineMajorantLower_le ht (by omega))

theorem threshold150_fourierAverage_sumCos_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 150≤n) :
    fourierAverage (sumCos n t) ≤ 99/98 := by
  have h := (fourierAverage_sumCos_le_majorant ht (by omega : 16≤n)).trans
    (momentMajorant_antitone (by norm_num : 16≤150) hn 0 (by norm_num))
  norm_num [momentMajorant] at h ⊢
  exact h

theorem threshold150_fourierAverage_secondCos_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 150≤n) :
    fourierAverage (fun u => u^2*sumCos n t u) ≤ 26/25 := by
  have h := (fourierAverage_secondCos_le_majorant ht (by omega : 16≤n)).trans
    (momentMajorant_antitone (by norm_num : 16≤150) hn 1 (by norm_num))
  norm_num [momentMajorant] at h ⊢
  linarith

theorem threshold150_fourierAverage_firstSine_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 150≤n) :
    fourierAverage (fun u => u*normalizedSumSin n t u) ≤ (13/4)/6 := by
  have h := fourierAverage_firstSine_le_majorant ht (by omega : 16≤n)
  have hm := momentMajorant_antitone (by norm_num : 16≤150) hn 2 (by norm_num)
  norm_num [momentMajorant] at hm h
  linarith

theorem threshold150_standardizedDensity_second_ratio_le {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) :
    -iteratedDeriv 2 (standardizedDensity n t) 0 / standardizedDensity n t 0 ≤
      (26/25)/(9850/10000) := by
  rw [secondDeriv_standardizedDensity_zero_eq_average ht (by omega),
    standardizedDensity_zero_eq_average ht (by omega)]
  simp only [neg_mul, neg_neg]
  rw [mul_div_mul_left _ _ fourierScale_pos.ne']
  have hc := threshold150_fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  apply (div_le_iff₀ hc0).mpr
  have h2 := threshold150_fourierAverage_secondCos_le ht hn
  linarith

theorem threshold150_standardizedDensity_first_ratio_sq_le {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) :
    (deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2 ≤
      (4/(n:ℝ))*((13/4)/(6*(9850/10000)))^2 := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hs := Real.sqrt_pos.mpr hnR
  have hc := threshold150_fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  have hA := fourierAverage_firstSine_pos ht (by omega : 150≤n)
  have hA1 := threshold150_fourierAverage_firstSine_le ht hn
  have hratio : 0 ≤ fourierAverage (fun u => u*normalizedSumSin n t u) /
      fourierAverage (sumCos n t) := div_nonneg hA.le hc0.le
  have hratioBound : fourierAverage (fun u => u*normalizedSumSin n t u) /
      fourierAverage (sumCos n t) ≤ (13/4)/(6*(9850/10000)) := by
    apply (div_le_iff₀ hc0).mpr
    linarith
  have hskew := div_le_div_of_nonneg_right (abs_tiltStandardMoment_three_le_two ht) hs.le
  have hbound := mul_le_mul hskew hratioBound hratio
    (by positivity : 0≤2/Real.sqrt (n:ℝ))
  have hsq := pow_le_pow_left₀ (mul_nonneg (div_nonneg (abs_nonneg _) hs.le) hratio) hbound 2
  have heq : deriv (standardizedDensity n t) 0 / standardizedDensity n t 0 =
      (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ)) *
        (fourierAverage (fun u => u * normalizedSumSin n t u) / fourierAverage (sumCos n t)) := by
    rw [deriv_standardizedDensity_zero_eq_average ht (by omega),
      standardizedDensity_zero_eq_average ht (by omega), skewFourierCoefficient]
    field_simp
  rw [← div_pow, heq]
  calc
    _ ≤ (2/Real.sqrt (n:ℝ)*((13/4)/(6*(9850/10000))))^2 := hsq
    _ = (4/(n:ℝ))*((13/4)/(6*(9850/10000)))^2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hnR.le]
      norm_num

theorem threshold150_standardizedDensity_lowerDerivativeBracket_lt {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) :
    lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0)
      (iteratedDeriv 2 (standardizedDensity n t) 0) < 16/5 := by
  have h1 := threshold150_standardizedDensity_first_ratio_sq_le ht hn
  have h2 := threshold150_standardizedDensity_second_ratio_le ht hn
  have hnR : (150:ℝ)≤n := by exact_mod_cast hn
  have hd : (4:ℝ)/(n:ℝ) ≤ 4/150 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have h1' := h1.trans (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
  unfold lowerDerivativeBracket
  have he1 : 2*(deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2 =
      2*((deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2) := by ring
  have he2 : -(3*iteratedDeriv 2 (standardizedDensity n t) 0)/standardizedDensity n t 0 =
      3*(-iteratedDeriv 2 (standardizedDensity n t) 0/standardizedDensity n t 0) := by ring
  rw [he1, he2]
  linarith

end
end ENT.Quantitative
