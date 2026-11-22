module

public import ENT.Quantitative.FourierRatios

/-! Dimension-dependent bounds tend to their Gaussian values. -/

@[expose] public section
set_option autoImplicit false
open Filter
open scoped Topology
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem tendsto_momentMajorant (k : ℕ) :
    Tendsto (fun n : ℕ => momentMajorant n k) atTop (𝓝 (gaussianCap k)) := by
  induction k with
  | zero =>
    have h := tendsto_add_mul_div_add_mul_atTop_nhds (-3:ℝ) (-6) 2 (d:=2) (by norm_num)
    convert h using 1 <;> norm_num [momentMajorant, gaussianCap]
    funext n
    ring
  | succ k ih =>
    have h := tendsto_add_mul_div_add_mul_atTop_nhds (0:ℝ) (-2*(k:ℝ)-4)
      ((2*k+1:ℕ):ℝ) (d:=1) (by norm_num)
    have hm := h.mul ih
    convert hm using 1 <;> simp only [momentMajorant, gaussianCap, div_one]
    funext n
    congr 1
    congr 1 <;> ring

theorem tendsto_const_div_dimension (a : ℝ) :
    Tendsto (fun n : ℕ => a/(n:ℝ)) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul a

theorem tendsto_cosineMajorantLower :
    Tendsto cosineMajorantLower atTop (𝓝 1) := by
  have h6 : Tendsto (fun n : ℕ => momentMajorant n 3) atTop (𝓝 15) := by
    convert tendsto_momentMajorant 3 using 1 <;> norm_num [gaussianCap]
  have h1 := tendsto_const_div_dimension (3/7)
  have h2 := h6.mul (tendsto_const_div_dimension (1/12))
  have h3 := ((tendsto_const_div_dimension 4).pow 3).mul ((tendsto_const_nhds (x:=(15:ℝ))).add h6)
  have h := (((tendsto_const_nhds (x:=(1:ℝ))).sub h1).sub h2).sub h3
  convert h using 1
  · funext n
    unfold cosineMajorantLower
    ring
  · norm_num

def derivativeBracketMajorant (n : ℕ) : ℝ :=
  3*momentMajorant n 1/cosineMajorantLower n +
    (8/(n:ℝ))*(momentMajorant n 2/(6*cosineMajorantLower n))^2

theorem tendsto_derivativeBracketMajorant :
    Tendsto derivativeBracketMajorant atTop (𝓝 3) := by
  have h1 : Tendsto (fun n : ℕ => momentMajorant n 1) atTop (𝓝 1) := by
    convert tendsto_momentMajorant 1 using 1 <;> norm_num [gaussianCap]
  have h2 : Tendsto (fun n : ℕ => momentMajorant n 2) atTop (𝓝 3) := by
    convert tendsto_momentMajorant 2 using 1 <;> norm_num [gaussianCap]
  have ha := (h1.const_mul 3).div tendsto_cosineMajorantLower (by norm_num : (1:ℝ)≠0)
  have hb := (tendsto_const_div_dimension 8).mul
    ((h2.div (tendsto_cosineMajorantLower.const_mul 6) (by norm_num : (6:ℝ)*1≠0)).pow 2)
  convert ha.add hb using 1
  · rfl
  · norm_num

theorem standardizedDensity_lowerDerivativeBracket_le_majorant {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 256≤n) :
    lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0)
      (iteratedDeriv 2 (standardizedDensity n t) 0) ≤ derivativeBracketMajorant n := by
  have hA := cosineMajorantLower_le ht (by omega : 16≤n)
  have hA0 : 0<cosineMajorantLower n := lt_trans (by norm_num) (cosineMajorantLower_at256 hn)
  have hc0 : 0<fourierAverage (sumCos n t) := hA0.trans_le hA
  have hm1 := (momentMajorant_pos (by omega : 16≤n) 1 (by norm_num)).le
  have hm2 := (momentMajorant_pos (by omega : 16≤n) 2 (by norm_num)).le
  have h2 : -iteratedDeriv 2 (standardizedDensity n t) 0/standardizedDensity n t 0 ≤
      momentMajorant n 1/cosineMajorantLower n := by
    rw [secondDeriv_standardizedDensity_zero_eq_average ht (by omega),
      standardizedDensity_zero_eq_average ht (by omega)]
    simp only [neg_mul, neg_neg]
    rw [mul_div_mul_left _ _ fourierScale_pos.ne']
    exact (div_le_div_of_nonneg_right (fourierAverage_secondCos_le_majorant ht (by omega)) hc0.le).trans
      (div_le_div_of_nonneg_left hm1 hA0 hA)
  have hfirst0 := (fourierAverage_firstSine_pos ht (by omega : 150≤n)).le
  have hratio0 : 0≤fourierAverage (fun u=>u*normalizedSumSin n t u)/fourierAverage (sumCos n t) :=
    div_nonneg hfirst0 hc0.le
  have hratio : fourierAverage (fun u=>u*normalizedSumSin n t u)/fourierAverage (sumCos n t) ≤
      momentMajorant n 2/(6*cosineMajorantLower n) := by
    calc
      _ ≤ (momentMajorant n 2/6)/fourierAverage (sumCos n t) :=
        div_le_div_of_nonneg_right (fourierAverage_firstSine_le_majorant ht (by omega)) hc0.le
      _ ≤ (momentMajorant n 2/6)/cosineMajorantLower n :=
        div_le_div_of_nonneg_left (by positivity) hA0 hA
      _ = _ := by ring
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hs := Real.sqrt_pos.mpr hnR
  have hskew := div_le_div_of_nonneg_right (abs_tiltStandardMoment_three_le_two ht) hs.le
  have hbound := mul_le_mul hskew hratio hratio0 (by positivity : 0≤2/Real.sqrt (n:ℝ))
  have hsq := pow_le_pow_left₀ (mul_nonneg (div_nonneg (abs_nonneg _) hs.le) hratio0) hbound 2
  have heq : deriv (standardizedDensity n t) 0 / standardizedDensity n t 0 =
      (|tiltStandardMoment t 3| / Real.sqrt (n : ℝ)) *
        (fourierAverage (fun u => u * normalizedSumSin n t u) / fourierAverage (sumCos n t)) := by
    rw [deriv_standardizedDensity_zero_eq_average ht (by omega),
      standardizedDensity_zero_eq_average ht (by omega), skewFourierCoefficient]
    field_simp
  have h1 : (deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2 ≤
      (4/(n:ℝ))*(momentMajorant n 2/(6*cosineMajorantLower n))^2 := by
    rw [← div_pow, heq]
    calc
      _ ≤ (2/Real.sqrt (n:ℝ)*(momentMajorant n 2/(6*cosineMajorantLower n)))^2 := hsq
      _ = _ := by rw [mul_pow, div_pow, Real.sq_sqrt hnR.le]; norm_num
  unfold lowerDerivativeBracket derivativeBracketMajorant
  have he1 : 2*(deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2 =
      2*((deriv (standardizedDensity n t) 0)^2/(standardizedDensity n t 0)^2) := by ring
  have he2 : -(3*iteratedDeriv 2 (standardizedDensity n t) 0)/standardizedDensity n t 0 =
      3*(-iteratedDeriv 2 (standardizedDensity n t) 0/standardizedDensity n t 0) := by ring
  rw [he1, he2]
  calc
    _ ≤ 3*(momentMajorant n 1/cosineMajorantLower n)+
        2*((4/(n:ℝ))*(momentMajorant n 2/(6*cosineMajorantLower n))^2) :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
        (mul_le_mul_of_nonneg_left h1 (by norm_num))
    _ = _ := by ring

end
end ENT.Quantitative
