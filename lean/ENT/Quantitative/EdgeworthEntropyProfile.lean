module

public import ENT.Quantitative.EdgeworthDensityExpansion
public import ENT.Entropy.LawInvariance

/-! The cubic entropy profile and its integral. The Gaussian Gibbs defect equals the finite entropy difference. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory ProbabilityTheory Polynomial
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def uniformEdgeworthRelativeProfile (n : ℕ) (x : ℝ) : ℝ :=
  uniformEdgeworthA.eval (x^2)/(n:ℝ)+uniformEdgeworthB.eval (x^2)/(n:ℝ)^2+
    uniformEdgeworthC.eval (x^2)/(n:ℝ)^3

def uniformEdgeworthEntropyProfile (n : ℕ) (x : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x * ((uniformEdgeworthRelativeProfile n x)^2/2-
    (uniformEdgeworthRelativeProfile n x)^3/6)

theorem uniformEdgeworthApprox_eq_relative (n : ℕ) (x : ℝ) :
    uniformEdgeworthApprox n x = gaussianPDFReal 0 1 x*(1+uniformEdgeworthRelativeProfile n x) := by
  unfold uniformEdgeworthApprox uniformEdgeworthRelativeProfile
  ring

private def relativeProfilePolynomial (r : ℝ) : ℝ[X] :=
  r • uniformEdgeworthA+r^2 • uniformEdgeworthB+r^3 • uniformEdgeworthC

private def entropyProfilePolynomial (r : ℝ) : ℝ[X] :=
  (1/2:ℝ) • (relativeProfilePolynomial r)^2-(1/6:ℝ) • (relativeProfilePolynomial r)^3

private theorem entropyProfilePolynomial_eval (n : ℕ) (x : ℝ) :
    (entropyProfilePolynomial (n:ℝ)⁻¹).eval (x^2)*gaussianPDFReal 0 1 x =
      uniformEdgeworthEntropyProfile n x := by
  simp only [entropyProfilePolynomial, relativeProfilePolynomial, uniformEdgeworthEntropyProfile,
    uniformEdgeworthRelativeProfile, eval_add, eval_sub, eval_smul, eval_pow, smul_eq_mul,
    div_eq_mul_inv, inv_pow]
  ring

theorem integrable_uniformEdgeworthEntropyProfile (n : ℕ) :
    Integrable (uniformEdgeworthEntropyProfile n) := by
  have h := integrable_evenPolynomial_gaussian (entropyProfilePolynomial (n:ℝ)⁻¹)
  simpa only [entropyProfilePolynomial_eval] using h

private def entropyProfileRemainderPolynomial (r : ℝ) : ℝ[X] :=
  (uniformEdgeworthA*uniformEdgeworthC+(1/2:ℝ) • uniformEdgeworthB^2-
      (1/2:ℝ) • (uniformEdgeworthA^2*uniformEdgeworthB)) +
  r • (uniformEdgeworthB*uniformEdgeworthC-(1/2:ℝ) • (uniformEdgeworthA^2*uniformEdgeworthC)-
      (1/2:ℝ) • (uniformEdgeworthA*uniformEdgeworthB^2)) +
  r^2 • ((1/2:ℝ) • uniformEdgeworthC^2-uniformEdgeworthA*uniformEdgeworthB*uniformEdgeworthC-
      (1/6:ℝ) • uniformEdgeworthB^3) -
  r^3 • ((1/2:ℝ) • (uniformEdgeworthA*uniformEdgeworthC^2+uniformEdgeworthB^2*uniformEdgeworthC)) -
  r^4 • ((1/2:ℝ) • (uniformEdgeworthB*uniformEdgeworthC^2)) -
  r^5 • ((1/6:ℝ) • uniformEdgeworthC^3)

private theorem entropyProfilePolynomial_expansion (r : ℝ) :
    entropyProfilePolynomial r =
      r^2 • (C (1/2)*uniformEdgeworthA^2)+
      r^3 • (uniformEdgeworthA*uniformEdgeworthB-C (1/6)*uniformEdgeworthA^3)+
      r^4 • entropyProfileRemainderPolynomial r := by
  apply Polynomial.funext
  intro x
  simp only [entropyProfilePolynomial, relativeProfilePolynomial, entropyProfileRemainderPolynomial,
    eval_add, eval_sub, eval_mul, eval_smul, eval_pow, eval_C, smul_eq_mul]
  ring

private def entropyProfileRemainder (r : ℝ) : ℝ :=
  gaussianEvenPolynomialIntegral (entropyProfileRemainderPolynomial r)

private theorem continuous_entropyProfileRemainder : Continuous entropyProfileRemainder := by
  unfold entropyProfileRemainder entropyProfileRemainderPolynomial
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  fun_prop

private theorem integral_uniformEdgeworthEntropyProfile (n : ℕ) :
    (∫ x, uniformEdgeworthEntropyProfile n x) =
      (3/100:ℝ)*(n:ℝ)⁻¹^2+(9/250:ℝ)*(n:ℝ)⁻¹^3+
      (n:ℝ)⁻¹^4*entropyProfileRemainder (n:ℝ)⁻¹ := by
  have he : (∫ x, uniformEdgeworthEntropyProfile n x) =
      gaussianEvenPolynomialIntegral (entropyProfilePolynomial (n:ℝ)⁻¹) := by
    change (∫ x, uniformEdgeworthEntropyProfile n x) =
      ∫ x, (entropyProfilePolynomial (n:ℝ)⁻¹).eval (x^2)*gaussianPDFReal 0 1 x
    simp only [entropyProfilePolynomial_eval]
  rw [he, entropyProfilePolynomial_expansion, map_add, map_add, map_smul, map_smul, map_smul,
    uniformEdgeworth_leading_entropy_coefficient, uniformEdgeworth_third_entropy_coefficient]
  simp only [smul_eq_mul, entropyProfileRemainder]
  ring

theorem uniformEdgeworthEntropyProfile_integral_expansion :
    Tendsto (fun n : ℕ => (n:ℝ)^3*((∫ x, uniformEdgeworthEntropyProfile n x)-
      (3/100:ℝ)/(n:ℝ)^2-(9/250:ℝ)/(n:ℝ)^3)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hr := continuous_entropyProfileRemainder.continuousAt.tendsto.comp hi
  have ht := hi.mul hr
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [integral_uniformEdgeworthEntropyProfile]
  dsimp only [Function.comp_def]
  field_simp
  ring

theorem standardizedDiagonal_gibbs_ae {n : ℕ} (hn : 2 ≤ n) :
    (fun x => gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)) =ᵐ[volume]
      (fun x => gibbsDefect ((standardizedProjectionDensity (diagonal n) (isUnit_diagonal (by omega))).density x)
        (standardGaussianFiniteEntropyDensity.density x)) := by
  have h := (standardizedDiagonalFiniteEntropyDensity n hn).density_ae_eq
    (standardizedProjectionDensity (diagonal n) (isUnit_diagonal (by omega)))
  filter_upwards [h] with x hx
  change gibbsDefect ((standardizedDiagonalFiniteEntropyDensity n hn).density x)
    (standardGaussianFiniteEntropyDensity.density x) = _
  rw [hx]

theorem integrable_standardizedDiagonal_gibbs {n : ℕ} (hn : 2 ≤ n) :
    Integrable (fun x => gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)) := by
  have h := (standardizedProjectionFiniteKL (diagonal n) (isUnit_diagonal (by omega))).integrable_gibbsDefect
  exact h.congr (standardizedDiagonal_gibbs_ae hn).symm

theorem integral_standardizedDiagonal_gibbs {n : ℕ} (hn : 2 ≤ n) :
    (∫ x, gibbsDefect (standardizedDiagonalDensity n x) (gaussianPDFReal 0 1 x)) =
      diagonalGaussianDefect n := by
  rw [integral_congr_ae (standardizedDiagonal_gibbs_ae hn),
    (standardizedProjectionFiniteKL (diagonal n) (isUnit_diagonal (by omega))).integral_gibbsDefect_eq,
    diagonalGaussianDefect_eq_kl (by omega)]

end
end ENT.Quantitative
