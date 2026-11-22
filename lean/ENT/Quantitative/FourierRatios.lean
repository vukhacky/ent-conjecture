module

public import ENT.Quantitative.FourierSignedIntegral
public import ENT.Pang.FourierRatios

/-! Quantitative Fourier mass and derivative ratios at the fixed threshold 256. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem fourierAverage_sumCos_le_majorant {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 16 ≤ n) :
    fourierAverage (sumCos n t) ≤ momentMajorant n 0 := by
  have hi : Integrable (sumCos n t) := by
    simpa using integrable_pow_mul_sumCos ht (k:=0) (by omega : 0+2<n)
  have hj : Integrable (pangEnvelope n) := by
    simpa using integrable_pow_mul_pangEnvelope (n:=n) (k:=0) (by omega : 0+2<n)
  have h := fourierAverage_mono hi hj
    (fun u => (abs_le.mp (abs_sumCos_le ht (by omega : 0<n) u)).2)
  have hm : fourierAverage (pangEnvelope n) ≤ momentMajorant n 0 := by
    simpa [fourierAverage, envelopeMoment] using envelopeMoment_le_majorant hn 0 (by norm_num)
  exact h.trans hm

theorem fourierAverage_secondCos_le_majorant {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 16 ≤ n) :
    fourierAverage (fun u => u^2*sumCos n t u) ≤ momentMajorant n 1 := by
  have h := fourierAverage_mono
    (integrable_pow_mul_sumCos ht (k:=2) (by omega : 2+2<n))
    (integrable_pow_mul_pangEnvelope (n:=n) (k:=2) (by omega : 2+2<n))
    (fun u => mul_le_mul_of_nonneg_left
      (abs_le.mp (abs_sumCos_le ht (by omega : 0<n) u)).2 (sq_nonneg u))
  exact h.trans (envelopeMoment_le_majorant hn 1 (by norm_num))

theorem fourierAverage_firstSine_le_majorant {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 16 ≤ n) :
    fourierAverage (fun u => u*normalizedSumSin n t u) ≤ momentMajorant n 2/6 := by
  have hi : Integrable (fun u => u*normalizedSumSin n t u) := by
    simpa using integrable_pow_mul_normalizedSumSin ht (k:=1) (by omega : 1+2<n)
  have h := fourierAverage_mono hi
    ((integrable_pow_mul_pangEnvelope (n:=n) (k:=4) (by omega : 4+2<n)).const_mul (1/6:ℝ))
    (fun u => (abs_le.mp (abs_mul_normalizedSumSin_le ht (by omega : 0<n) u)).2)
  rw [fourierAverage_const_mul] at h
  change fourierAverage (fun u => u*normalizedSumSin n t u) ≤ (1/6:ℝ)*envelopeMoment n 2 at h
  nlinarith [envelopeMoment_le_majorant hn 2 (by norm_num)]

def cosineMajorantLower (n : ℕ) : ℝ :=
  1 - 3/(7*(n:ℝ)) - momentMajorant n 3/(12*(n:ℝ)) -
    (4/(n:ℝ))^3*(15+momentMajorant n 3)

theorem cosineMajorantLower_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 16 ≤ n) :
    cosineMajorantLower n ≤ fourierAverage (sumCos n t) := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hi : Integrable (sumCos n t) := by
    simpa using integrable_pow_mul_sumCos ht (k:=0) (by omega : 0+2<n)
  have h := fourierAverage_mono (integrable_cosineLowerModel (by omega)) hi
    (cosineLowerModel_le ht (by omega))
  rw [fourierAverage_cosineLowerModel (by omega)] at h
  have h6 := div_le_div_of_nonneg_right (envelopeMoment_le_majorant hn 3 (by norm_num))
    (by positivity : 0 ≤ 12*(n:ℝ))
  have ht0 := normalizedTailMoment_le (n:=n) (k:=0) (q:=3) (by omega) (by omega)
  norm_num only [Nat.sub_zero, gaussianMoment_three] at ht0
  have ht1 := mul_le_mul_of_nonneg_left
    (add_le_add_left (envelopeMoment_le_majorant hn 3 (by norm_num)) 15)
    (by positivity : 0 ≤ (4/(n:ℝ))^3)
  unfold cosineMajorantLower
  linarith

theorem cosineMajorantLower_at256 {n : ℕ} (hn : 256 ≤ n) :
    (9929:ℝ)/10000 < cosineMajorantLower n := by
  have hnR : (256:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hm3 : momentMajorant n 3 ≤ 16203/1000 := by
    have h := momentMajorant_antitone (by norm_num : 16≤256) hn 3 (by norm_num)
    norm_num [momentMajorant] at h ⊢
    linarith
  have h1 : (3:ℝ)/(7*(n:ℝ)) ≤ 3/(7*256) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : momentMajorant n 3/(12*(n:ℝ)) ≤ (16203/1000)/(12*256) :=
    (div_le_div_of_nonneg_right hm3 (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
  have h4 : (4:ℝ)/(n:ℝ) ≤ 4/256 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have htail : (4/(n:ℝ))^3*(15+momentMajorant n 3) ≤ (4/256:ℝ)^3*(15+16203/1000) :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) h4 3) (by linarith)
      (by linarith [momentMajorant_pos (by omega : 16≤n) 3 (by norm_num)]) (by norm_num)
  unfold cosineMajorantLower
  linarith

theorem quant_fourierAverage_sumCos_gt {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) :
    (9929:ℝ)/10000 < fourierAverage (sumCos n t) :=
  (cosineMajorantLower_at256 hn).trans_le (cosineMajorantLower_le ht (by omega))

theorem quant_fourierAverage_sumCos_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) :
    fourierAverage (sumCos n t) ≤ 509/506 := by
  have h := (fourierAverage_sumCos_le_majorant ht (by omega : 16≤n)).trans
    (momentMajorant_antitone (by norm_num : 16≤256) hn 0 (by norm_num))
  norm_num [momentMajorant] at h ⊢
  exact h

theorem quant_fourierAverage_secondCos_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) :
    fourierAverage (fun u => u^2*sumCos n t u) ≤ 10219/10000 := by
  have h := (fourierAverage_secondCos_le_majorant ht (by omega : 16≤n)).trans
    (momentMajorant_antitone (by norm_num : 16≤256) hn 1 (by norm_num))
  norm_num [momentMajorant] at h ⊢
  linarith

theorem quant_fourierAverage_firstSine_le {t : ℝ} (ht : 0<t) {n : ℕ} (hn : 256≤n) :
    fourierAverage (fun u => u*normalizedSumSin n t u) ≤ (157/50)/6 := by
  have h := fourierAverage_firstSine_le_majorant ht (by omega : 16≤n)
  have hm := momentMajorant_antitone (by norm_num : 16≤256) hn 2 (by norm_num)
  norm_num [momentMajorant] at hm h
  linarith

theorem quant_standardizedDensity_second_ratio_le {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 256≤n) :
    -iteratedDeriv 2 (standardizedDensity n t) 0 / standardizedDensity n t 0 ≤
      (10219/10000)/(9929/10000) := by
  rw [secondDeriv_standardizedDensity_zero_eq_average ht (by omega),
    standardizedDensity_zero_eq_average ht (by omega)]
  simp only [neg_mul, neg_neg]
  rw [mul_div_mul_left _ _ fourierScale_pos.ne']
  have hc := quant_fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  apply (div_le_iff₀ hc0).mpr
  have h2 := quant_fourierAverage_secondCos_le ht hn
  linarith

theorem quant_standardizedDensity_first_ratio_sq_le {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 256≤n) :
    (deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2 ≤
      (4/(n:ℝ))*((157/50)/(6*(9929/10000)))^2 := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hs := Real.sqrt_pos.mpr hnR
  have hc := quant_fourierAverage_sumCos_gt ht hn
  have hc0 : 0 < fourierAverage (sumCos n t) := by linarith
  have hA := fourierAverage_firstSine_pos ht (by omega : 150≤n)
  have hA1 := quant_fourierAverage_firstSine_le ht hn
  have hratio : 0 ≤ fourierAverage (fun u => u*normalizedSumSin n t u) /
      fourierAverage (sumCos n t) := div_nonneg hA.le hc0.le
  have hratioBound : fourierAverage (fun u => u*normalizedSumSin n t u) /
      fourierAverage (sumCos n t) ≤ (157/50)/(6*(9929/10000)) := by
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
    _ ≤ (2/Real.sqrt (n:ℝ)*((157/50)/(6*(9929/10000))))^2 := hsq
    _ = (4/(n:ℝ))*((157/50)/(6*(9929/10000)))^2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hnR.le]
      norm_num

theorem quant_standardizedDensity_lowerDerivativeBracket_lt {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 256≤n) :
    lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0)
      (iteratedDeriv 2 (standardizedDensity n t) 0) < 31/10 := by
  have h1 := quant_standardizedDensity_first_ratio_sq_le ht hn
  have h2 := quant_standardizedDensity_second_ratio_le ht hn
  have hnR : (256:ℝ)≤n := by exact_mod_cast hn
  have hd : (4:ℝ)/(n:ℝ) ≤ 4/256 :=
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
