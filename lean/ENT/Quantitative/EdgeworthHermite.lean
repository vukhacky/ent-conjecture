module

public import ENT.Quantitative.EdgeworthGaussian
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots

/-! Exact Gaussian polynomial integrals used by the specialized uniform
Edgeworth expansion.  These are genuine integrals, with polynomial
integrability proved before evaluating them.  No density approximation is
asserted by this file. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators

namespace ENT.Quantitative
noncomputable section

theorem integral_even_pow_standardGaussianPDF (k : ℕ) :
    (∫ x : ℝ, x^(2*k) * gaussianPDFReal 0 1 x) = Pang.gaussianCap k := by
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (∫ x : ℝ, x^(2*k) * Pang.gaussianWeight x) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [standardGaussianPDF_eq]
      ring
    _ = _ := by simpa only [Pang.gaussianMoment, one_div] using Pang.gaussianMoment_eq_cap k

theorem integrable_evenPolynomial_gaussian (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval (x^2) * gaussianPDFReal 0 1 x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [eval_add, add_mul] using hp.fun_add hq
  | monomial k c =>
      simpa only [eval_monomial, ← pow_mul, mul_assoc] using
        (integrable_pow_standardGaussianPDF (2*k)).const_mul c

/-- Gaussian integration of even polynomials, as an actual linear map. -/
def gaussianEvenPolynomialIntegral : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : ℝ, p.eval (x^2) * gaussianPDFReal 0 1 x
  map_add' p q := by
    simp only [eval_add, add_mul]
    exact integral_add (integrable_evenPolynomial_gaussian p)
      (integrable_evenPolynomial_gaussian q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, mul_assoc, integral_const_mul,
      RingHom.id_apply]

theorem gaussianEvenPolynomialIntegral_monomial (k : ℕ) (c : ℝ) :
    gaussianEvenPolynomialIntegral (monomial k c) = c * Pang.gaussianCap k := by
  change (∫ x : ℝ, (monomial k c).eval (x^2) * gaussianPDFReal 0 1 x) = _
  simp only [eval_monomial, ← pow_mul, mul_assoc, integral_const_mul,
    integral_even_pow_standardGaussianPDF]

theorem gaussianEvenPolynomialIntegral_C_mul_X_pow (c : ℝ) (k : ℕ) :
    gaussianEvenPolynomialIntegral (C c * X^k) = c * Pang.gaussianCap k := by
  rw [C_mul_X_pow_eq_monomial, gaussianEvenPolynomialIntegral_monomial]

theorem gaussianEvenPolynomialIntegral_C (c : ℝ) :
    gaussianEvenPolynomialIntegral (C c) = c := by
  simpa only [pow_zero, mul_one, Pang.gaussianCap] using
    gaussianEvenPolynomialIntegral_C_mul_X_pow c 0

/-- `H₄(x)` expressed as a polynomial in `x²`. -/
def hermite4Even : ℝ[X] := X^2 - C 6 * X + C 3

/-- `H₆(x)` expressed as a polynomial in `x²`. -/
def hermite6Even : ℝ[X] := X^3 - C 15 * X^2 + C 45 * X - C 15

/-- `H₈(x)` expressed as a polynomial in `x²`. -/
def hermite8Even : ℝ[X] := X^4 - C 28 * X^3 + C 210 * X^2 - C 420 * X + C 105

def uniformEdgeworthA : ℝ[X] := C (-1/20) * hermite4Even
def uniformEdgeworthB : ℝ[X] := C (1/105) * hermite6Even + C (1/800) * hermite8Even

theorem hermite4Even_eval (x : ℝ) : hermite4Even.eval (x^2) = x^4 - 6*x^2 + 3 := by
  simp only [hermite4Even, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  ring

theorem hermite4Even_lower (x : ℝ) : -6 ≤ hermite4Even.eval (x^2) := by
  rw [hermite4Even_eval]
  nlinarith [sq_nonneg (x^2 - 3)]

private theorem gaussianIntegral_X_pow (k : ℕ) :
    gaussianEvenPolynomialIntegral (X^k) = Pang.gaussianCap k := by
  simpa only [map_one, one_mul] using gaussianEvenPolynomialIntegral_C_mul_X_pow 1 k

private theorem gaussianIntegral_X : gaussianEvenPolynomialIntegral X = 1 := by
  simpa [Pang.gaussianCap] using gaussianIntegral_X_pow 1

theorem gaussianIntegral_hermite4 : gaussianEvenPolynomialIntegral hermite4Even = 0 := by
  unfold hermite4Even
  rw [map_add, map_sub, gaussianIntegral_X_pow]
  rw [show C (6:ℝ) * X = C 6 * X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite4_sq :
    gaussianEvenPolynomialIntegral (hermite4Even^2) = 24 := by
  have he : hermite4Even^2 = X^4 - C 12 * X^3 + C 42 * X^2 - C 36 * X + C 9 := by
    unfold hermite4Even
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [he]
  simp only [map_add, map_sub, gaussianIntegral_X_pow,
    show C (36:ℝ) * X = C 36 * X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite4_cube :
    gaussianEvenPolynomialIntegral (hermite4Even^3) = 1728 := by
  have he : hermite4Even^3 = X^6 - C 18 * X^5 + C 117 * X^4 - C 324 * X^3 +
      C 351 * X^2 - C 162 * X + C 27 := by
    unfold hermite4Even
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [he]
  simp only [map_add, map_sub, gaussianIntegral_X_pow,
    show C (162:ℝ) * X = C 162 * X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite4_mul_hermite6 :
    gaussianEvenPolynomialIntegral (hermite4Even * hermite6Even) = 0 := by
  have he : hermite4Even * hermite6Even = X^5 - C 21 * X^4 + C 138 * X^3 -
      C 330 * X^2 + C 225 * X - C 45 := by
    unfold hermite4Even hermite6Even
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [he]
  simp only [map_add, map_sub, gaussianIntegral_X_pow,
    show C (225:ℝ) * X = C 225 * X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem gaussianIntegral_hermite4_mul_hermite8 :
    gaussianEvenPolynomialIntegral (hermite4Even * hermite8Even) = 0 := by
  have he : hermite4Even * hermite8Even = X^6 - C 34 * X^5 + C 381 * X^4 -
      C 1764 * X^3 + C 3255 * X^2 - C 1890 * X + C 315 := by
    unfold hermite4Even hermite8Even
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [he]
  simp only [map_add, map_sub, gaussianIntegral_X_pow,
    show C (1890:ℝ) * X = C 1890 * X^1 by simp,
    gaussianEvenPolynomialIntegral_C_mul_X_pow, gaussianEvenPolynomialIntegral_C]
  norm_num [Pang.gaussianCap]

theorem uniformEdgeworth_leading_entropy_coefficient :
    gaussianEvenPolynomialIntegral (C (1/2) * uniformEdgeworthA^2) = (3/100:ℝ) := by
  have he : C (1/2) * uniformEdgeworthA^2 = (1/800:ℝ) • hermite4Even^2 := by
    simp only [uniformEdgeworthA, smul_eq_C_mul]
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C]
    ring
  rw [he, map_smul, gaussianIntegral_hermite4_sq]
  norm_num

theorem uniformEdgeworth_third_entropy_coefficient :
    gaussianEvenPolynomialIntegral
      (uniformEdgeworthA * uniformEdgeworthB - C (1/6) * uniformEdgeworthA^3) = (9/250:ℝ) := by
  have he : uniformEdgeworthA * uniformEdgeworthB - C (1/6) * uniformEdgeworthA^3 =
      (-1/2100:ℝ) • (hermite4Even * hermite6Even) +
      (-1/16000:ℝ) • (hermite4Even * hermite8Even) +
      (1/48000:ℝ) • hermite4Even^3 := by
    simp only [uniformEdgeworthA, uniformEdgeworthB, smul_eq_C_mul]
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C]
    ring
  rw [he, map_add, map_add, map_smul, map_smul, map_smul,
    gaussianIntegral_hermite4_mul_hermite6, gaussianIntegral_hermite4_mul_hermite8,
    gaussianIntegral_hermite4_cube]
  norm_num

end
end ENT.Quantitative
