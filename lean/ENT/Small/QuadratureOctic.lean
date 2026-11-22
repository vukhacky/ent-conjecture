module

public import ENT.Small.QuadratureCertificate
public import ENT.Small.OcticParameters
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Monotonicity and analytic tails for the four actual octic approximants. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section

open Quadrature Certificate

theorem hasDerivAt_octicPolynomial (c₁ c₂ c₃ c₄ x : ℝ) :
    HasDerivAt (octicPolynomial c₁ c₂ c₃ c₄)
      (2*c₁*x + 4*c₂*x^3 + 6*c₃*x^5 + 8*c₄*x^7) x := by
  have h := (((((hasDerivAt_id x).pow 2).const_mul c₁).add
    (((hasDerivAt_id x).pow 4).const_mul c₂)).add
    (((hasDerivAt_id x).pow 6).const_mul c₃)).add
    (((hasDerivAt_id x).pow 8).const_mul c₄)
  convert h using 1
  · funext y
    rfl
  · norm_num
    ring

theorem octicPolynomial_monotoneOn {c₁ c₂ c₃ c₄ : ℝ}
    (h1 : 0 ≤ c₁) (h4 : 0 < c₄) (hdisc : 9*c₃^2 ≤ 32*c₂*c₄) :
    MonotoneOn (octicPolynomial c₁ c₂ c₃ c₄) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (show Continuous (octicPolynomial c₁ c₂ c₃ c₄) by unfold octicPolynomial; fun_prop).continuousOn
    (fun x _ => (hasDerivAt_octicPolynomial c₁ c₂ c₃ c₄ x).hasDerivWithinAt)
  intro x hx
  have hx0 : 0 ≤ x := (interior_subset hx)
  have hq : 0 ≤ 2*c₂ + 3*c₃*x^2 + 4*c₄*x^4 := by
    have he : 16*c₄*(2*c₂ + 3*c₃*x^2 + 4*c₄*x^4) =
        (8*c₄*x^2 + 3*c₃)^2 + (32*c₂*c₄ - 9*c₃^2) := by ring
    have hs := sq_nonneg (8*c₄*x^2 + 3*c₃)
    have hp : 0 ≤ 16*c₄*(2*c₂ + 3*c₃*x^2 + 4*c₄*x^4) := by linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < 16*c₄)).mp hp
  have he : 2*c₁*x + 4*c₂*x^3 + 6*c₃*x^5 + 8*c₄*x^7 =
      2*c₁*x + 2*x^3*(2*c₂ + 3*c₃*x^2 + 4*c₄*x^4) := by ring
  rw [he]
  positivity

theorem exp_neg_twenty_four_le : Real.exp (-24 : ℝ) ≤ 1 / (2:ℝ)^24 := by
  have h2 : (2:ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 24
  have he : Real.exp (24:ℝ) = Real.exp (1:ℝ)^24 := by
    simpa using Real.exp_natCast_mul 24 (1:ℝ)
  rw [←he] at hp
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) hp

theorem even_integral_eq_two_mul_Ioi {f : ℝ → ℝ} (hf : Integrable f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2 * ∫ x in Ioi 0, f x := by
  have hfun : (fun x : ℝ => (Ioi (0 : ℝ)).indicator f (-x)) =
      (Iio (0 : ℝ)).indicator f := by
    funext x
    by_cases hx : x < 0
    · have hneg : -x ∈ Ioi (0 : ℝ) := by simpa using neg_pos.mpr hx
      rw [indicator_of_mem hneg, indicator_of_mem hx, heven]
    · have hneg : -x ∉ Ioi (0 : ℝ) := by simpa using not_lt.mpr (neg_nonpos.mpr (le_of_not_gt hx))
      rw [indicator_of_notMem hneg, indicator_of_notMem hx]
  have h := Measure.integral_comp_mul_left ((Ioi (0 : ℝ)).indicator f) (-1)
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  rw [hfun, integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi] at h
  have hsplit := intervalIntegral.integral_Iio_add_Ici (b := (0 : ℝ))
    hf.integrableOn hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi] at hsplit
  linarith

theorem W3_eq_rationalPolynomial : W3 = rationalPolynomial W3IntegerCoeffs W3Denominator := by
  funext x
  norm_num [W3, octicPolynomial, rationalPolynomial, W3IntegerCoeffs, W3Denominator,
    eval, List.foldr]
  <;> ring

theorem W3_monotoneOn : MonotoneOn W3 (Ici 0) := by
  apply octicPolynomial_monotoneOn <;> norm_num

theorem W3_rational_monotoneOn :
    MonotoneOn (rationalPolynomial W3IntegerCoeffs W3Denominator) (Ici 0) := by
  rw [← W3_eq_rationalPolynomial]
  exact W3_monotoneOn

theorem W3_even (x : ℝ) : W3 (-x) = W3 x := by
  unfold W3 octicPolynomial
  ring

theorem W3_tail_tangent (x : ℝ) (hx : (7/2:ℝ) ≤ x) :
    W3 (7/2:ℝ) + 50 * (x - (7/2:ℝ)) ≤ W3 x := by
  have hy : 0 ≤ x - (7/2:ℝ) := sub_nonneg.mpr hx
  have he : W3 x - W3 (7/2:ℝ) - 50*(x - (7/2:ℝ)) =
      (14141943/1600000:ℝ)*(x - (7/2:ℝ))^1 + (110686703/1600000:ℝ)*(x - (7/2:ℝ))^2 + (18702229/400000:ℝ)*(x - (7/2:ℝ))^3 + (3062867/160000:ℝ)*(x - (7/2:ℝ))^4 + (483161/100000:ℝ)*(x - (7/2:ℝ))^5 + (73543/100000:ℝ)*(x - (7/2:ℝ))^6 + (1547/25000:ℝ)*(x - (7/2:ℝ))^7 + (221/100000:ℝ)*(x - (7/2:ℝ))^8 := by
    unfold W3 octicPolynomial
    ring
  have hp : 0 ≤ W3 x - W3 (7/2:ℝ) - 50*(x - (7/2:ℝ)) := by
    rw [he]
    positivity
  linarith

theorem W3_tail_integral_le :
    (∫ x in Ioi (7/2:ℝ), Real.exp (-W3 x)) ≤ 1 / (50 * (2:ℝ)^24) := by
  have ht := exp_tail_integral_le (by norm_num : (0:ℝ) < 50) W3_exp_integrable
    (fun x hx => W3_tail_tangent x hx)
  have hR : (24:ℝ) ≤ W3 (7/2:ℝ) := by norm_num [W3, octicPolynomial]
  have he : Real.exp (-W3 (7/2:ℝ)) ≤ 1/(2:ℝ)^24 :=
    (Real.exp_le_exp.mpr (neg_le_neg hR)).trans exp_neg_twenty_four_le
  calc
    (∫ x in Ioi (7/2:ℝ), Real.exp (-W3 x)) ≤ Real.exp (-W3 (7/2:ℝ)) / 50 := ht
    _ ≤ (1/(2:ℝ)^24)/50 := div_le_div_of_nonneg_right he (by norm_num)
    _ = 1/(50*(2:ℝ)^24) := by ring

theorem partitionFunction_W3_split :
    partitionFunction W3 = 2 * (∫ x in 0..(7/2:ℝ), Real.exp (-W3 x)) +
      2 * (∫ x in Ioi (7/2:ℝ), Real.exp (-W3 x)) := by
  unfold partitionFunction
  rw [even_integral_eq_two_mul_Ioi W3_exp_integrable (fun x => by rw [W3_even])]
  have h := intervalIntegral.integral_interval_add_Ioi
    (a := (0:ℝ)) (b := (7/2:ℝ)) W3_exp_integrable.integrableOn W3_exp_integrable.integrableOn
  rw [←h]
  ring

theorem W4_eq_rationalPolynomial : W4 = rationalPolynomial W4IntegerCoeffs W4Denominator := by
  funext x
  norm_num [W4, octicPolynomial, rationalPolynomial, W4IntegerCoeffs, W4Denominator,
    eval, List.foldr]
  <;> ring

theorem W4_monotoneOn : MonotoneOn W4 (Ici 0) := by
  apply octicPolynomial_monotoneOn <;> norm_num

theorem W4_rational_monotoneOn :
    MonotoneOn (rationalPolynomial W4IntegerCoeffs W4Denominator) (Ici 0) := by
  rw [← W4_eq_rationalPolynomial]
  exact W4_monotoneOn

theorem W4_even (x : ℝ) : W4 (-x) = W4 x := by
  unfold W4 octicPolynomial
  ring

theorem W4_tail_tangent (x : ℝ) (hx : 4 ≤ x) :
    W4 4 + 40 * (x - 4) ≤ W4 x := by
  have hy : 0 ≤ x - 4 := sub_nonneg.mpr hx
  have he : W4 x - W4 4 - 40*(x - 4) =
      (133193/31250:ℝ)*(x - 4)^1 + (10271321/250000:ℝ)*(x - 4)^2 + (359053/15625:ℝ)*(x - 4)^3 + (398073/50000:ℝ)*(x - 4)^4 + (107587/62500:ℝ)*(x - 4)^5 + (113217/500000:ℝ)*(x - 4)^6 + (259/15625:ℝ)*(x - 4)^7 + (259/500000:ℝ)*(x - 4)^8 := by
    unfold W4 octicPolynomial
    ring
  have hp : 0 ≤ W4 x - W4 4 - 40*(x - 4) := by
    rw [he]
    positivity
  linarith

theorem W4_tail_integral_le :
    (∫ x in Ioi 4, Real.exp (-W4 x)) ≤ 1 / (40 * (2:ℝ)^24) := by
  have ht := exp_tail_integral_le (by norm_num : (0:ℝ) < 40) W4_exp_integrable
    (fun x hx => W4_tail_tangent x hx)
  have hR : (24:ℝ) ≤ W4 4 := by norm_num [W4, octicPolynomial]
  have he : Real.exp (-W4 4) ≤ 1/(2:ℝ)^24 :=
    (Real.exp_le_exp.mpr (neg_le_neg hR)).trans exp_neg_twenty_four_le
  calc
    (∫ x in Ioi 4, Real.exp (-W4 x)) ≤ Real.exp (-W4 4) / 40 := ht
    _ ≤ (1/(2:ℝ)^24)/40 := div_le_div_of_nonneg_right he (by norm_num)
    _ = 1/(40*(2:ℝ)^24) := by ring

theorem partitionFunction_W4_split :
    partitionFunction W4 = 2 * (∫ x in 0..4, Real.exp (-W4 x)) +
      2 * (∫ x in Ioi 4, Real.exp (-W4 x)) := by
  unfold partitionFunction
  rw [even_integral_eq_two_mul_Ioi W4_exp_integrable (fun x => by rw [W4_even])]
  have h := intervalIntegral.integral_interval_add_Ioi
    (a := (0:ℝ)) (b := 4) W4_exp_integrable.integrableOn W4_exp_integrable.integrableOn
  rw [←h]
  ring

theorem W5_eq_rationalPolynomial : W5 = rationalPolynomial W5IntegerCoeffs W5Denominator := by
  funext x
  norm_num [W5, octicPolynomial, rationalPolynomial, W5IntegerCoeffs, W5Denominator,
    eval, List.foldr]
  <;> ring

theorem W5_monotoneOn : MonotoneOn W5 (Ici 0) := by
  apply octicPolynomial_monotoneOn <;> norm_num

theorem W5_rational_monotoneOn :
    MonotoneOn (rationalPolynomial W5IntegerCoeffs W5Denominator) (Ici 0) := by
  rw [← W5_eq_rationalPolynomial]
  exact W5_monotoneOn

theorem W5_even (x : ℝ) : W5 (-x) = W5 x := by
  unfold W5 octicPolynomial
  ring

theorem W5_tail_tangent (x : ℝ) (hx : (9/2:ℝ) ≤ x) :
    W5 (9/2:ℝ) + 40 * (x - (9/2:ℝ)) ≤ W5 x := by
  have hy : 0 ≤ x - (9/2:ℝ) := sub_nonneg.mpr hx
  have he : W5 x - W5 (9/2:ℝ) - 40*(x - (9/2:ℝ)) =
      (1076202157/800000000:ℝ)*(x - (9/2:ℝ))^1 + (25137889711/800000000:ℝ)*(x - (9/2:ℝ))^2 + (2966449329/200000000:ℝ)*(x - (9/2:ℝ))^3 + (353351281/80000000:ℝ)*(x - (9/2:ℝ))^4 + (41512959/50000000:ℝ)*(x - (9/2:ℝ))^5 + (4789451/50000000:ℝ)*(x - (9/2:ℝ))^6 + (77427/12500000:ℝ)*(x - (9/2:ℝ))^7 + (8603/50000000:ℝ)*(x - (9/2:ℝ))^8 := by
    unfold W5 octicPolynomial
    ring
  have hp : 0 ≤ W5 x - W5 (9/2:ℝ) - 40*(x - (9/2:ℝ)) := by
    rw [he]
    positivity
  linarith

theorem W5_tail_integral_le :
    (∫ x in Ioi (9/2:ℝ), Real.exp (-W5 x)) ≤ 1 / (40 * (2:ℝ)^24) := by
  have ht := exp_tail_integral_le (by norm_num : (0:ℝ) < 40) W5_exp_integrable
    (fun x hx => W5_tail_tangent x hx)
  have hR : (24:ℝ) ≤ W5 (9/2:ℝ) := by norm_num [W5, octicPolynomial]
  have he : Real.exp (-W5 (9/2:ℝ)) ≤ 1/(2:ℝ)^24 :=
    (Real.exp_le_exp.mpr (neg_le_neg hR)).trans exp_neg_twenty_four_le
  calc
    (∫ x in Ioi (9/2:ℝ), Real.exp (-W5 x)) ≤ Real.exp (-W5 (9/2:ℝ)) / 40 := ht
    _ ≤ (1/(2:ℝ)^24)/40 := div_le_div_of_nonneg_right he (by norm_num)
    _ = 1/(40*(2:ℝ)^24) := by ring

theorem partitionFunction_W5_split :
    partitionFunction W5 = 2 * (∫ x in 0..(9/2:ℝ), Real.exp (-W5 x)) +
      2 * (∫ x in Ioi (9/2:ℝ), Real.exp (-W5 x)) := by
  unfold partitionFunction
  rw [even_integral_eq_two_mul_Ioi W5_exp_integrable (fun x => by rw [W5_even])]
  have h := intervalIntegral.integral_interval_add_Ioi
    (a := (0:ℝ)) (b := (9/2:ℝ)) W5_exp_integrable.integrableOn W5_exp_integrable.integrableOn
  rw [←h]
  ring

theorem W6_eq_rationalPolynomial : W6 = rationalPolynomial W6IntegerCoeffs W6Denominator := by
  funext x
  norm_num [W6, octicPolynomial, rationalPolynomial, W6IntegerCoeffs, W6Denominator,
    eval, List.foldr]
  <;> ring

theorem W6_monotoneOn : MonotoneOn W6 (Ici 0) := by
  apply octicPolynomial_monotoneOn <;> norm_num

theorem W6_rational_monotoneOn :
    MonotoneOn (rationalPolynomial W6IntegerCoeffs W6Denominator) (Ici 0) := by
  rw [← W6_eq_rationalPolynomial]
  exact W6_monotoneOn

theorem W6_even (x : ℝ) : W6 (-x) = W6 x := by
  unfold W6 octicPolynomial
  ring

theorem W6_tail_tangent (x : ℝ) (hx : 5 ≤ x) :
    W6 5 + 40 * (x - 5) ≤ W6 x := by
  have hy : 0 ≤ x - 5 := sub_nonneg.mpr hx
  have he : W6 x - W6 5 - 40*(x - 5) =
      (113221/40000:ℝ)*(x - 5)^1 + (11091721/400000:ℝ)*(x - 5)^2 + (226479/20000:ℝ)*(x - 5)^3 + (1181309/400000:ℝ)*(x - 5)^4 + (490401/1000000:ℝ)*(x - 5)^5 + (503387/10000000:ℝ)*(x - 5)^6 + (1821/625000:ℝ)*(x - 5)^7 + (1821/25000000:ℝ)*(x - 5)^8 := by
    unfold W6 octicPolynomial
    ring
  have hp : 0 ≤ W6 x - W6 5 - 40*(x - 5) := by
    rw [he]
    positivity
  linarith

theorem W6_tail_integral_le :
    (∫ x in Ioi 5, Real.exp (-W6 x)) ≤ 1 / (40 * (2:ℝ)^24) := by
  have ht := exp_tail_integral_le (by norm_num : (0:ℝ) < 40) W6_exp_integrable
    (fun x hx => W6_tail_tangent x hx)
  have hR : (24:ℝ) ≤ W6 5 := by norm_num [W6, octicPolynomial]
  have he : Real.exp (-W6 5) ≤ 1/(2:ℝ)^24 :=
    (Real.exp_le_exp.mpr (neg_le_neg hR)).trans exp_neg_twenty_four_le
  calc
    (∫ x in Ioi 5, Real.exp (-W6 x)) ≤ Real.exp (-W6 5) / 40 := ht
    _ ≤ (1/(2:ℝ)^24)/40 := div_le_div_of_nonneg_right he (by norm_num)
    _ = 1/(40*(2:ℝ)^24) := by ring

theorem partitionFunction_W6_split :
    partitionFunction W6 = 2 * (∫ x in 0..5, Real.exp (-W6 x)) +
      2 * (∫ x in Ioi 5, Real.exp (-W6 x)) := by
  unfold partitionFunction
  rw [even_integral_eq_two_mul_Ioi W6_exp_integrable (fun x => by rw [W6_even])]
  have h := intervalIntegral.integral_interval_add_Ioi
    (a := (0:ℝ)) (b := 5) W6_exp_integrable.integrableOn W6_exp_integrable.integrableOn
  rw [←h]
  ring

end
end ENT.Small
