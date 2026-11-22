module

public import ENT.Quantitative.LargeCurvature
public import ENT.Quantitative.Fourier150Ratios
public import ENT.Quantitative.Fourier150SignedIntegral
public import ENT.Quantitative.LangevinStrong

/-! The 7/n curvature bound for n ≥ 150, from squared-skewness Fourier remainders, an order-20 tail estimate and a scalar inequality. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

theorem diagonalPotential_tilt_lower_of_scalar {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) {c d r : ℝ} (hd : 0<d)
    (hr : r < -tiltThirdCumulant t/(tiltMean t*tiltVariance t^3))
    (hbracket : lowerDerivativeBracket (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0) (iteratedDeriv 2 (standardizedDensity n t) 0) ≤ c)
    (haverage : d ≤ fourierAverage (fun u => u*(u^2-c)*normalizedSumSin n t u) /
      fourierAverage (sumCos n t)) :
    (r*d/(n:ℝ))*(Real.sqrt (n:ℝ)*tiltMean t) <
      iteratedDeriv 3 (Spline.diagonalSplinePotential n) (Real.sqrt (n:ℝ)*tiltMean t) := by
  have hv := tiltVariance_pos ht
  have hm := tiltMean_pos ht
  have hs := Real.sqrt_pos.mpr hv
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hnS := Real.sqrt_pos.mpr hnR
  have hstd := standardizedPotential_third_deriv_lower ht hn hbracket haverage
  have hvpow : (Real.sqrt (tiltVariance t)^3)^2 = tiltVariance t^3 := by
    rw [← pow_mul, mul_comm 3 2, pow_mul, Real.sq_sqrt hv.le]
  have hscalar := hr
  have hscalar' := mul_lt_mul_of_pos_right hscalar
    (show 0 < (tiltMean t/Real.sqrt (n:ℝ))*d by positivity)
  have hmu : |tiltStandardMoment t 3| =
      -tiltThirdCumulant t/(Real.sqrt (tiltVariance t)^3) := by
    rw [tiltStandardMoment_three ht, abs_of_neg (tiltSkewness_neg ht), tiltSkewness]
    ring
  have he1 : r*((tiltMean t/Real.sqrt (n:ℝ))*d) =
      (r*d/(n:ℝ))*(Real.sqrt (n:ℝ)*tiltMean t) := by
    field_simp [hnR.ne', hnS.ne']
    rw [Real.sq_sqrt hnR.le]
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

theorem threshold150_signed_average_ratio_gt {t : ℝ} (ht : 0<t)
    {n : ℕ} (hn : 150≤n) :
    ((7/10:ℝ)-(13/150)*skewSquared t)/(99/98) <
      fourierAverage (fun u=>u*(u^2-16/5)*normalizedSumSin n t u)/fourierAverage (sumCos n t) := by
  have hc := threshold150_fourierAverage_sumCos_gt ht hn
  have hc0 : 0<fourierAverage (sumCos n t) := by linarith
  have hq := skewSquared_le_four ht
  have hd : 0<((7/10:ℝ)-(13/150)*skewSquared t)/(99/98) := by
    apply div_pos _ (by norm_num)
    linarith
  apply (lt_div_iff₀ hc0).mpr
  have hu := mul_le_mul_of_nonneg_left (threshold150_fourierAverage_sumCos_le ht hn) hd.le
  have he : (((7/10:ℝ)-(13/150)*skewSquared t)/(99/98))*(99/98) =
      (7/10:ℝ)-(13/150)*skewSquared t := by ring
  rw [he] at hu
  exact hu.trans_lt (Threshold150.quant_signed_integral_lower ht hn)

theorem threshold150_scalar_margin {t : ℝ} (ht : 0<t) :
    7 < (54/5+3*skewSquared t)*(((7/10:ℝ)-(13/150)*skewSquared t)/(99/98)) := by
  have hq0 := skewSquared_nonneg t
  have hq4 := skewSquared_le_four ht
  have hquad := mul_nonneg hq0 (sub_nonneg.mpr hq4)
  rw [←mul_div_assoc]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<99/98)).mpr
  nlinarith

/-- Actual diagonal potential curvature in every dimension at least 150. -/
theorem large_curvature_gt_150 {n : ℕ} (hn : 150≤n) :
    ∀ x∈Ioo (0:ℝ) (Real.sqrt (n:ℝ)),
      (7/(n:ℝ))*x < deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x := by
  intro x hx
  obtain ⟨t,ht,_⟩ := existsUnique_tiltCenter (by omega : 0<n) hx
  have hd : 0<((7/10:ℝ)-(13/150)*skewSquared t)/(99/98) := by
    apply div_pos _ (by norm_num)
    linarith [skewSquared_le_four ht.1]
  have h := diagonalPotential_tilt_lower_of_scalar ht.1 hn hd (strong_langevin_ratio ht.1)
    (threshold150_standardizedDensity_lowerDerivativeBracket_lt ht.1 hn).le
    (threshold150_signed_average_ratio_gt ht.1 hn).le
  rw [ht.2] at h
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hcoeff := div_lt_div_of_pos_right (threshold150_scalar_margin ht.1) hnR
  have h' := (mul_lt_mul_of_pos_right hcoeff hx.1).trans h
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h'

theorem large_curvature_ge_150 {n : ℕ} (hn : 150≤n) :
    ∀ x∈Ioo (0:ℝ) (Real.sqrt (n:ℝ)),
      (7/(n:ℝ))*x ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x :=
  fun x hx=>(large_curvature_gt_150 hn x hx).le

end
end ENT.Quantitative
