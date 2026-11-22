module

public import ENT.Small.QuadratureOctic

/-! Tail estimates beyond 8 for the octic partition integrals in dimensions 3–6, as in Appendix C. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Small
noncomputable section

def octicFirst (c₁ c₂ c₃ c₄ x : ℝ) : ℝ :=
  2*c₁*x + 4*c₂*x^3 + 6*c₃*x^5 + 8*c₄*x^7

def octicSecond (c₁ c₂ c₃ c₄ x : ℝ) : ℝ :=
  2*c₁ + 12*c₂*x^2 + 30*c₃*x^4 + 56*c₄*x^6

theorem deriv_octicPolynomial (c₁ c₂ c₃ c₄ : ℝ) :
    deriv (octicPolynomial c₁ c₂ c₃ c₄) = octicFirst c₁ c₂ c₃ c₄ := by
  funext x
  exact (hasDerivAt_octicPolynomial c₁ c₂ c₃ c₄ x).deriv

theorem deriv_octicFirst (c₁ c₂ c₃ c₄ : ℝ) :
    deriv (octicFirst c₁ c₂ c₃ c₄) = octicSecond c₁ c₂ c₃ c₄ := by
  funext x
  have h := ((((hasDerivAt_id x).const_mul (2*c₁)).add
    (((hasDerivAt_id x).pow 3).const_mul (4*c₂))).add
    (((hasDerivAt_id x).pow 5).const_mul (6*c₃))).add
    (((hasDerivAt_id x).pow 7).const_mul (8*c₄))
  change HasDerivAt (octicFirst c₁ c₂ c₃ c₄) _ x at h
  convert h.deriv using 1 <;> norm_num [octicSecond] <;> ring

theorem W3_deriv_eight_pos : 0 < deriv W3 8 := by
  unfold W3
  rw [deriv_octicPolynomial]
  norm_num [octicFirst]

theorem W3_second_pos_on_tail (x : ℝ) (hx : 8 ≤ x) :
    0 < deriv (deriv W3) x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : deriv (deriv W3) x =
      (371609393/12500:ℝ) +
      (71747544/3125:ℝ)*(x-8)^1 +
      (9180543/1250:ℝ)*(x-8)^2 +
      (778504/625:ℝ)*(x-8)^3 +
      (295329/2500:ℝ)*(x-8)^4 +
      (18564/3125:ℝ)*(x-8)^5 +
      (1547/12500:ℝ)*(x-8)^6 := by
    unfold W3
    rw [deriv_octicPolynomial, deriv_octicFirst]
    unfold octicSecond
    ring
  rw [he]
  positivity

theorem W3_tail_eight_tangent (x : ℝ) (hx : 8 ≤ x) :
    W3 8 + deriv W3 8 * (x-8) ≤ W3 x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : W3 x - W3 8 - deriv W3 8 * (x-8) =
      (371609393/25000:ℝ)*(x-8)^2 +
      (11957924/3125:ℝ)*(x-8)^3 +
      (3060181/5000:ℝ)*(x-8)^4 +
      (194626/3125:ℝ)*(x-8)^5 +
      (98443/25000:ℝ)*(x-8)^6 +
      (442/3125:ℝ)*(x-8)^7 +
      (221/100000:ℝ)*(x-8)^8 := by
    unfold W3
    rw [deriv_octicPolynomial]
    unfold octicPolynomial octicFirst
    ring
  have hp : 0 ≤ W3 x - W3 8 - deriv W3 8 * (x-8) := by
    rw [he]
    positivity
  linarith

theorem W3_tail_eight_integral_le :
    (∫ x in Ioi (8:ℝ), Real.exp (-W3 x)) ≤
      Real.exp (-W3 8) / deriv W3 8 :=
  exp_tail_integral_le W3_deriv_eight_pos W3_exp_integrable
    (fun x hx => W3_tail_eight_tangent x hx)

theorem partitionFunction_W3_eight_error :
    0 ≤ partitionFunction W3 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W3 x)) ∧
    partitionFunction W3 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W3 x)) ≤
      2*Real.exp (-W3 8) / deriv W3 8 := by
  have hs : partitionFunction W3 =
      2*(∫ x in (0:ℝ)..8, Real.exp (-W3 x)) +
      2*(∫ x in Ioi (8:ℝ), Real.exp (-W3 x)) := by
    unfold partitionFunction
    rw [even_integral_eq_two_mul_Ioi W3_exp_integrable (fun x => by rw [W3_even])]
    have h := intervalIntegral.integral_interval_add_Ioi
      (a := (0:ℝ)) (b := (8:ℝ)) W3_exp_integrable.integrableOn W3_exp_integrable.integrableOn
    rw [←h]
    ring
  rw [hs]
  have hp : 0 ≤ ∫ x in Ioi (8:ℝ), Real.exp (-W3 x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have ht := W3_tail_eight_integral_le
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

theorem W4_deriv_eight_pos : 0 < deriv W4 8 := by
  unfold W4
  rw [deriv_octicPolynomial]
  norm_num [octicFirst]

theorem W4_second_pos_on_tail (x : ℝ) (hx : 8 ≤ x) :
    0 < deriv (deriv W4) x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : deriv (deriv W4) x =
      (867048569/125000:ℝ) +
      (83798076/15625:ℝ)*(x-8)^1 +
      (21471939/12500:ℝ)*(x-8)^2 +
      (911366/3125:ℝ)*(x-8)^3 +
      (1383939/50000:ℝ)*(x-8)^4 +
      (21756/15625:ℝ)*(x-8)^5 +
      (1813/62500:ℝ)*(x-8)^6 := by
    unfold W4
    rw [deriv_octicPolynomial, deriv_octicFirst]
    unfold octicSecond
    ring
  rw [he]
  positivity

theorem W4_tail_eight_tangent (x : ℝ) (hx : 8 ≤ x) :
    W4 8 + deriv W4 8 * (x-8) ≤ W4 x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : W4 x - W4 8 - deriv W4 8 * (x-8) =
      (867048569/250000:ℝ)*(x-8)^2 +
      (13966346/15625:ℝ)*(x-8)^3 +
      (7157313/50000:ℝ)*(x-8)^4 +
      (455683/31250:ℝ)*(x-8)^5 +
      (461313/500000:ℝ)*(x-8)^6 +
      (518/15625:ℝ)*(x-8)^7 +
      (259/500000:ℝ)*(x-8)^8 := by
    unfold W4
    rw [deriv_octicPolynomial]
    unfold octicPolynomial octicFirst
    ring
  have hp : 0 ≤ W4 x - W4 8 - deriv W4 8 * (x-8) := by
    rw [he]
    positivity
  linarith

theorem W4_tail_eight_integral_le :
    (∫ x in Ioi (8:ℝ), Real.exp (-W4 x)) ≤
      Real.exp (-W4 8) / deriv W4 8 :=
  exp_tail_integral_le W4_deriv_eight_pos W4_exp_integrable
    (fun x hx => W4_tail_eight_tangent x hx)

theorem partitionFunction_W4_eight_error :
    0 ≤ partitionFunction W4 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W4 x)) ∧
    partitionFunction W4 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W4 x)) ≤
      2*Real.exp (-W4 8) / deriv W4 8 := by
  have hs : partitionFunction W4 =
      2*(∫ x in (0:ℝ)..8, Real.exp (-W4 x)) +
      2*(∫ x in Ioi (8:ℝ), Real.exp (-W4 x)) := by
    unfold partitionFunction
    rw [even_integral_eq_two_mul_Ioi W4_exp_integrable (fun x => by rw [W4_even])]
    have h := intervalIntegral.integral_interval_add_Ioi
      (a := (0:ℝ)) (b := (8:ℝ)) W4_exp_integrable.integrableOn W4_exp_integrable.integrableOn
    rw [←h]
    ring
  rw [hs]
  have hp : 0 ≤ ∫ x in Ioi (8:ℝ), Real.exp (-W4 x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have ht := W4_tail_eight_integral_le
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

theorem W5_deriv_eight_pos : 0 < deriv W5 8 := by
  unfold W5
  rw [deriv_octicPolynomial]
  norm_num [octicFirst]

theorem W5_second_pos_on_tail (x : ℝ) (hx : 8 ≤ x) :
    0 < deriv (deriv W5) x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : deriv (deriv W5) x =
      (7253540037/3125000:ℝ) +
      (698690898/390625:ℝ)*(x-8)^1 +
      (357376149/625000:ℝ)*(x-8)^2 +
      (7575613/78125:ℝ)*(x-8)^3 +
      (22992189/2500000:ℝ)*(x-8)^4 +
      (180663/390625:ℝ)*(x-8)^5 +
      (60221/6250000:ℝ)*(x-8)^6 := by
    unfold W5
    rw [deriv_octicPolynomial, deriv_octicFirst]
    unfold octicSecond
    ring
  rw [he]
  positivity

theorem W5_tail_eight_tangent (x : ℝ) (hx : 8 ≤ x) :
    W5 8 + deriv W5 8 * (x-8) ≤ W5 x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : W5 x - W5 8 - deriv W5 8 * (x-8) =
      (7253540037/6250000:ℝ)*(x-8)^2 +
      (116448483/390625:ℝ)*(x-8)^3 +
      (119125383/2500000:ℝ)*(x-8)^4 +
      (7575613/1562500:ℝ)*(x-8)^5 +
      (7664063/25000000:ℝ)*(x-8)^6 +
      (8603/781250:ℝ)*(x-8)^7 +
      (8603/50000000:ℝ)*(x-8)^8 := by
    unfold W5
    rw [deriv_octicPolynomial]
    unfold octicPolynomial octicFirst
    ring
  have hp : 0 ≤ W5 x - W5 8 - deriv W5 8 * (x-8) := by
    rw [he]
    positivity
  linarith

theorem W5_tail_eight_integral_le :
    (∫ x in Ioi (8:ℝ), Real.exp (-W5 x)) ≤
      Real.exp (-W5 8) / deriv W5 8 :=
  exp_tail_integral_le W5_deriv_eight_pos W5_exp_integrable
    (fun x hx => W5_tail_eight_tangent x hx)

theorem partitionFunction_W5_eight_error :
    0 ≤ partitionFunction W5 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W5 x)) ∧
    partitionFunction W5 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W5 x)) ≤
      2*Real.exp (-W5 8) / deriv W5 8 := by
  have hs : partitionFunction W5 =
      2*(∫ x in (0:ℝ)..8, Real.exp (-W5 x)) +
      2*(∫ x in Ioi (8:ℝ), Real.exp (-W5 x)) := by
    unfold partitionFunction
    rw [even_integral_eq_two_mul_Ioi W5_exp_integrable (fun x => by rw [W5_even])]
    have h := intervalIntegral.integral_interval_add_Ioi
      (a := (0:ℝ)) (b := (8:ℝ)) W5_exp_integrable.integrableOn W5_exp_integrable.integrableOn
    rw [←h]
    ring
  rw [hs]
  have hp : 0 ≤ ∫ x in Ioi (8:ℝ), Real.exp (-W5 x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have ht := W5_tail_eight_integral_le
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

theorem W6_deriv_eight_pos : 0 < deriv W6 8 := by
  unfold W6
  rw [deriv_octicPolynomial]
  norm_num [octicFirst]

theorem W6_second_pos_on_tail (x : ℝ) (hx : 8 ≤ x) :
    0 < deriv (deriv W6) x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : deriv (deriv W6) x =
      (6238078361/6250000:ℝ) +
      (298437822/390625:ℝ)*(x-8)^1 +
      (152035251/625000:ℝ)*(x-8)^2 +
      (6429069/156250:ℝ)*(x-8)^3 +
      (19481997/5000000:ℝ)*(x-8)^4 +
      (76482/390625:ℝ)*(x-8)^5 +
      (12747/3125000:ℝ)*(x-8)^6 := by
    unfold W6
    rw [deriv_octicPolynomial, deriv_octicFirst]
    unfold octicSecond
    ring
  rw [he]
  positivity

theorem W6_tail_eight_tangent (x : ℝ) (hx : 8 ≤ x) :
    W6 8 + deriv W6 8 * (x-8) ≤ W6 x := by
  have hy : 0 ≤ x-8 := sub_nonneg.mpr hx
  have he : W6 x - W6 8 - deriv W6 8 * (x-8) =
      (6238078361/12500000:ℝ)*(x-8)^2 +
      (49739637/390625:ℝ)*(x-8)^3 +
      (50678417/2500000:ℝ)*(x-8)^4 +
      (6429069/3125000:ℝ)*(x-8)^5 +
      (6493999/50000000:ℝ)*(x-8)^6 +
      (1821/390625:ℝ)*(x-8)^7 +
      (1821/25000000:ℝ)*(x-8)^8 := by
    unfold W6
    rw [deriv_octicPolynomial]
    unfold octicPolynomial octicFirst
    ring
  have hp : 0 ≤ W6 x - W6 8 - deriv W6 8 * (x-8) := by
    rw [he]
    positivity
  linarith

theorem W6_tail_eight_integral_le :
    (∫ x in Ioi (8:ℝ), Real.exp (-W6 x)) ≤
      Real.exp (-W6 8) / deriv W6 8 :=
  exp_tail_integral_le W6_deriv_eight_pos W6_exp_integrable
    (fun x hx => W6_tail_eight_tangent x hx)

theorem partitionFunction_W6_eight_error :
    0 ≤ partitionFunction W6 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W6 x)) ∧
    partitionFunction W6 - 2*(∫ x in (0:ℝ)..8, Real.exp (-W6 x)) ≤
      2*Real.exp (-W6 8) / deriv W6 8 := by
  have hs : partitionFunction W6 =
      2*(∫ x in (0:ℝ)..8, Real.exp (-W6 x)) +
      2*(∫ x in Ioi (8:ℝ), Real.exp (-W6 x)) := by
    unfold partitionFunction
    rw [even_integral_eq_two_mul_Ioi W6_exp_integrable (fun x => by rw [W6_even])]
    have h := intervalIntegral.integral_interval_add_Ioi
      (a := (0:ℝ)) (b := (8:ℝ)) W6_exp_integrable.integrableOn W6_exp_integrable.integrableOn
    rw [←h]
    ring
  rw [hs]
  have hp : 0 ≤ ∫ x in Ioi (8:ℝ), Real.exp (-W6 x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have ht := W6_tail_eight_integral_le
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

end
end ENT.Small
