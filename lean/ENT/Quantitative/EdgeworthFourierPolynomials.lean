module

public import ENT.Quantitative.EdgeworthUniformFourier
public import ENT.Quantitative.EdgeworthFourierCalculus

/-! Exact Fourier inverses of the three Edgeworth polynomial profiles.
All integrals are Bochner integrals with polynomial Gaussian integrability. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory ProbabilityTheory Polynomial
open scoped Topology

namespace ENT.Quantitative
noncomputable section

theorem integrable_gaussianPolynomial_fourierKernel (p : ℝ[X]) (x : ℝ) :
    Integrable (fun u : ℝ => Pang.probabilityFourierKernel x u * ((p.eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ)) := by
  apply (integrable_evenPolynomial_gaussianWeight p).norm.mono'
  · unfold Pang.probabilityFourierKernel Pang.gaussianWeight
    fun_prop
  · filter_upwards [] with u
    rw [norm_mul, Pang.norm_probabilityFourierKernel, one_mul, Complex.norm_real]

def gaussianFourierPolynomial (x : ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := (Pang.probabilityFourierInverse (fun u => ((p.eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ)) x).re
  map_add' p q := by
    unfold Pang.probabilityFourierInverse
    have he : (fun u : ℝ => Pang.probabilityFourierKernel x u * (((p+q).eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ)) =
        fun u => Pang.probabilityFourierKernel x u * ((p.eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ) +
          Pang.probabilityFourierKernel x u * ((q.eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ) := by
      funext u
      simp only [eval_add, add_mul, Complex.ofReal_add, mul_add]
    rw [he, integral_add (integrable_gaussianPolynomial_fourierKernel p x)
      (integrable_gaussianPolynomial_fourierKernel q x), smul_add, Complex.add_re]
  map_smul' c p := by
    unfold Pang.probabilityFourierInverse
    have he : (fun u : ℝ => Pang.probabilityFourierKernel x u * (((c • p).eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ)) =
        fun u => c • (Pang.probabilityFourierKernel x u * ((p.eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ)) := by
      funext u
      simp only [eval_smul, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [he, integral_smul, smul_comm, Complex.smul_re, RingHom.id_apply]

theorem gaussianFourierPolynomial_C_mul_X_pow (x c : ℝ) (k : ℕ) :
    gaussianFourierPolynomial x (C c*X^k) = c*(-1:ℝ)^k*iteratedDeriv (2*k) (gaussianPDFReal 0 1) x := by
  have hp (u : ℝ) : (-1:ℂ)^k*(-Complex.I*(u:ℂ))^(2*k) = (u:ℂ)^(2*k) := by
    rw [pow_mul, ← mul_pow]
    have he : (-1:ℂ)*(-Complex.I*(u:ℂ))^2 = (u:ℂ)^2 := by
      rw [mul_pow]
      norm_num
    rw [he, ← pow_mul]
  have he : (fun u : ℝ => Pang.probabilityFourierKernel x u * (((C c*X^k).eval (u^2)*Pang.gaussianWeight u : ℝ) : ℂ)) =
      fun u => (c*(-1:ℝ)^k) • Pang.fourierDerivativeIntegrand (charFun (gaussianReal 0 1)) (2*k) x u := by
    funext u
    simp only [eval_mul, eval_C, eval_pow, eval_X, Pang.fourierDerivativeIntegrand,
      charFun_standardGaussian, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    rw [show ((u:ℂ)^2)^k = (u:ℂ)^(2*k) by rw [pow_mul], ← hp]
    ring
  change (Pang.probabilityFourierInverse _ x).re = _
  rw [Pang.probabilityFourierInverse, he, integral_smul, smul_comm, Complex.smul_re]
  change (c*(-1:ℝ)^k)*(Pang.fourierDerivativeIntegral (charFun (gaussianReal 0 1)) (2*k) x).re = _
  rw [iteratedDeriv_standardGaussianPDF_fourier]

theorem gaussianFourierPolynomial_C (x c : ℝ) : gaussianFourierPolynomial x (C c) = c*gaussianPDFReal 0 1 x := by
  simpa only [pow_zero, mul_one, Nat.mul_zero, iteratedDeriv_zero] using gaussianFourierPolynomial_C_mul_X_pow x c 0

def uniformFourierProfilePolynomial (n : ℕ) : ℝ[X] :=
  C 1+C (-1/(20*(n:ℝ)))*X^2+C (-1/(105*(n:ℝ)^2))*X^3+
    C (1/(800*(n:ℝ)^2)-3/(1400*(n:ℝ)^3))*X^4+
    C (1/(2100*(n:ℝ)^3))*X^5+C (-1/(48000*(n:ℝ)^3))*X^6

theorem uniformFourierProfile_eq_polynomial (n : ℕ) (u : ℝ) :
    uniformFourierProfile n u = (uniformFourierProfilePolynomial n).eval (u^2)*Pang.gaussianWeight u := by
  simp only [uniformFourierProfile, exponentialThirdProfile, uniformCumulantA, uniformCumulantB,
    uniformCumulantC, uniformFourierProfilePolynomial, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    div_eq_mul_inv, inv_mul_cancel₀, mul_inv_rev, inv_pow]
  ring

private theorem hermite_value_2 : hermite 2 = (X^2 + C (-1) : ℤ[X]) := by
  have h := hermite_succ 1
  rw [hermite_one] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_3 : hermite 3 = (X^3 + C (-3)*X^1 : ℤ[X]) := by
  have h := hermite_succ 2
  rw [hermite_value_2] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_4 : hermite 4 = (X^4 + C (-6)*X^2 + C (3) : ℤ[X]) := by
  have h := hermite_succ 3
  rw [hermite_value_3] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_5 : hermite 5 = (X^5 + C (-10)*X^3 + C (15)*X^1 : ℤ[X]) := by
  have h := hermite_succ 4
  rw [hermite_value_4] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_6 : hermite 6 = (X^6 + C (-15)*X^4 + C (45)*X^2 + C (-15) : ℤ[X]) := by
  have h := hermite_succ 5
  rw [hermite_value_5] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_7 : hermite 7 = (X^7 + C (-21)*X^5 + C (105)*X^3 + C (-105)*X^1 : ℤ[X]) := by
  have h := hermite_succ 6
  rw [hermite_value_6] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_8 : hermite 8 = (X^8 + C (-28)*X^6 + C (210)*X^4 + C (-420)*X^2 + C (105) : ℤ[X]) := by
  have h := hermite_succ 7
  rw [hermite_value_7] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_9 : hermite 9 = (X^9 + C (-36)*X^7 + C (378)*X^5 + C (-1260)*X^3 + C (945)*X^1 : ℤ[X]) := by
  have h := hermite_succ 8
  rw [hermite_value_8] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_10 : hermite 10 = (X^10 + C (-45)*X^8 + C (630)*X^6 + C (-3150)*X^4 + C (4725)*X^2 + C (-945) : ℤ[X]) := by
  have h := hermite_succ 9
  rw [hermite_value_9] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_11 : hermite 11 = (X^11 + C (-55)*X^9 + C (990)*X^7 + C (-6930)*X^5 + C (17325)*X^3 + C (-10395)*X^1 : ℤ[X]) := by
  have h := hermite_succ 10
  rw [hermite_value_10] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

private theorem hermite_value_12 : hermite 12 = (X^12 + C (-66)*X^10 + C (1485)*X^8 + C (-13860)*X^6 + C (51975)*X^4 + C (-62370)*X^2 + C (10395) : ℤ[X]) := by
  have h := hermite_succ 11
  rw [hermite_value_11] at h
  rw [h]
  norm_num [derivative_add, derivative_sub, derivative_mul, derivative_pow]
  ring

theorem gaussianFourierPolynomial_profile (n : ℕ) (x : ℝ) :
    gaussianFourierPolynomial x (uniformFourierProfilePolynomial n) = uniformEdgeworthApprox n x := by
  unfold uniformFourierProfilePolynomial
  rw [map_add, map_add, map_add, map_add, map_add]
  simp only [gaussianFourierPolynomial_C_mul_X_pow, gaussianFourierPolynomial_C]
  norm_num only [show 2*2=4 from rfl, show 2*3=6 from rfl, show 2*4=8 from rfl,
    show 2*5=10 from rfl, show 2*6=12 from rfl]
  rw [iteratedDeriv_standardGaussianPDF, iteratedDeriv_standardGaussianPDF,
    iteratedDeriv_standardGaussianPDF, iteratedDeriv_standardGaussianPDF,
    iteratedDeriv_standardGaussianPDF]
  rw [hermite_value_4, hermite_value_6, hermite_value_8, hermite_value_10, hermite_value_12]
  simp only [map_add, map_mul, map_pow, map_neg, aeval_X, aeval_C]
  norm_num [uniformEdgeworthApprox, uniformEdgeworthA, uniformEdgeworthB, uniformEdgeworthC,
    hermite4Even, hermite6Even, hermite8Even, hermite10Even, hermite12Even,
    div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem uniformFourierProfile_inverse (n : ℕ) (x : ℝ) :
    (Pang.probabilityFourierInverse (fun u => (uniformFourierProfile n u : ℂ)) x).re =
      uniformEdgeworthApprox n x := by
  simp_rw [uniformFourierProfile_eq_polynomial]
  exact gaussianFourierPolynomial_profile n x

end
end ENT.Quantitative
