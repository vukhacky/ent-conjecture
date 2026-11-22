module

public import ENT.Quantitative.SharpnessCoefficients
public import ENT.Basic.ProjectionMoments
public import ENT.Entropy.Scaling
public import ENT.Entropy.Gibbs
public import ENT.Comparison.DensityExpectations
public import ENT.Pang.GaussianMoments
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! Gaussian relative entropy and integrability for standardized uniform projections. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ENT.Quantitative
noncomputable section

private theorem sqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity

theorem standardGaussianPDF_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Pang.gaussianWeight x := by
  simp [gaussianPDFReal, Pang.gaussianWeight, one_div]

theorem log_standardGaussianPDF (x : ℝ) :
    Real.log (gaussianPDFReal 0 1 x) =
      -Real.log (Real.sqrt (2 * Real.pi)) - x^2 / 2 := by
  rw [standardGaussianPDF_eq, Real.log_mul
    (inv_ne_zero sqrt_two_pi_pos.ne') (Pang.gaussianWeight_pos x).ne']
  rw [Real.log_inv, Pang.gaussianWeight, Real.log_exp]
  ring

theorem integrable_pow_standardGaussianPDF (k : ℕ) :
    Integrable (fun x : ℝ => x^k * gaussianPDFReal 0 1 x) := by
  have hi := (Pang.integrable_pow_mul_gaussianWeight k).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  funext x
  rw [standardGaussianPDF_eq]
  ring

theorem integrable_standardGaussianPDF_mul_log :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * Real.log (gaussianPDFReal 0 1 x)) := by
  have h₀ := (integrable_gaussianPDFReal 0 1).mul_const
    (-Real.log (Real.sqrt (2 * Real.pi)))
  have h₂ := (integrable_pow_standardGaussianPDF 2).div_const 2
  convert h₀.sub h₂ using 1
  funext x
  change gaussianPDFReal 0 1 x * Real.log (gaussianPDFReal 0 1 x) =
    gaussianPDFReal 0 1 x * (-Real.log (Real.sqrt (2 * Real.pi))) -
      (x^2 * gaussianPDFReal 0 1 x) / 2
  rw [log_standardGaussianPDF]
  ring

def standardGaussianFiniteEntropyDensity : FiniteEntropyDensity (gaussianReal 0 1) where
  density := gaussianPDFReal 0 1
  nonneg := gaussianPDFReal_nonneg 0 1
  measurable := measurable_gaussianPDFReal 0 1
  integrable := integrable_gaussianPDFReal 0 1
  mass_one := integral_gaussianPDFReal_eq_one 0 (by norm_num)
  law_eq := gaussianReal_of_var_ne_zero 0 (by norm_num)
  entropy_integrable := integrable_standardGaussianPDF_mul_log

theorem integral_sq_standardGaussianPDF :
    (∫ x : ℝ, x^2 * gaussianPDFReal 0 1 x) = 1 := by
  have h := Pang.gaussianMoment_one
  unfold Pang.gaussianMoment at h
  calc
    (∫ x : ℝ, x^2 * gaussianPDFReal 0 1 x) =
        (Real.sqrt (2 * Real.pi))⁻¹ * (∫ x : ℝ, x^2 * Pang.gaussianWeight x) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [standardGaussianPDF_eq]
      ring
    _ = 1 := by simpa only [Nat.mul_one, one_div] using h

theorem standardGaussian_entropy :
    standardGaussianFiniteEntropyDensity.entropy =
      Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2 := by
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x * Real.log (gaussianPDFReal 0 1 x)) =
      (fun x : ℝ => gaussianPDFReal 0 1 x *
        (-Real.log (Real.sqrt (2 * Real.pi))) - (x^2 * gaussianPDFReal 0 1 x) / 2) := by
    funext x
    rw [log_standardGaussianPDF]
    ring
  change -(∫ x : ℝ, gaussianPDFReal 0 1 x * Real.log (gaussianPDFReal 0 1 x)) = _
  rw [he, integral_sub ((integrable_gaussianPDFReal 0 1).mul_const _)
    ((integrable_pow_standardGaussianPDF 2).div_const 2), integral_mul_const,
    integral_div, integral_gaussianPDFReal_eq_one 0 (by norm_num),
    integral_sq_standardGaussianPDF]
  ring

def standardizedProjectionLaw {n : ℕ} (a : Fin n → ℝ) : Measure ℝ :=
  (projectionLaw a).map (fun x => Real.sqrt 3 * x)

def standardizedProjectionDensity {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    FiniteEntropyDensity (standardizedProjectionLaw a) :=
  (projectionFiniteEntropyDensity a ha).scale (Real.sqrt 3) (by positivity)

theorem integrable_standardizedProjection_pow {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (standardizedProjectionLaw a) :=
  integrable_map_mul_pow _ (integrable_projectionLaw_pow a k) _

theorem integral_standardizedProjection_sq {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x : ℝ, x^2 ∂standardizedProjectionLaw a) = 1 := by
  rw [standardizedProjectionLaw, integral_map_mul_pow,
    integral_projectionLaw_sq_of_isUnit a ha, Real.sq_sqrt (by norm_num)]
  norm_num

theorem integrable_log_standardGaussian_under_projection {n : ℕ}
    (a : Fin n → ℝ) :
    Integrable (fun x => Real.log (gaussianPDFReal 0 1 x)) (standardizedProjectionLaw a) := by
  letI : IsProbabilityMeasure (standardizedProjectionLaw a) := by
    unfold standardizedProjectionLaw
    infer_instance
  simp_rw [log_standardGaussianPDF]
  exact (integrable_const _).sub ((integrable_standardizedProjection_pow a 2).div_const 2)

def standardizedProjectionFiniteKL {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    FiniteKLData (standardizedProjectionDensity a ha) standardGaussianFiniteEntropyDensity where
  cross_integrable := by
    change Integrable (fun x => (standardizedProjectionDensity a ha).density x *
      Real.log (gaussianPDFReal 0 1 x))
    have h := ((standardizedProjectionDensity a ha).integrable_iff_density
      (fun x => Real.log (gaussianPDFReal 0 1 x))).mp
        (integrable_log_standardGaussian_under_projection a)
    simpa only [mul_comm] using h
  support_ae := Filter.Eventually.of_forall fun x hx =>
    False.elim ((gaussianPDFReal_pos 0 1 x (by norm_num)).ne' hx)

theorem integral_log_standardGaussian_under_projection {n : ℕ}
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, Real.log (gaussianPDFReal 0 1 x) ∂standardizedProjectionLaw a) =
      -Real.log (Real.sqrt (2 * Real.pi)) - 1 / 2 := by
  letI : IsProbabilityMeasure (standardizedProjectionLaw a) := by
    unfold standardizedProjectionLaw
    infer_instance
  simp_rw [log_standardGaussianPDF]
  rw [integral_sub (integrable_const _)
    ((integrable_standardizedProjection_pow a 2).div_const 2),
    integral_const, integral_div, integral_standardizedProjection_sq a ha]
  simp

theorem standardizedProjection_kl_eq_entropy_defect {n : ℕ}
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (standardizedProjectionFiniteKL a ha).klDivergence =
      Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2 -
        Real.log (Real.sqrt 3) - projectionEntropy a ha := by
  let p := standardizedProjectionDensity a ha
  have hc := integral_log_standardGaussian_under_projection a ha
  rw [p.integral_eq_density] at hc
  have hent : p.entropy = projectionEntropy a ha + Real.log (Real.sqrt 3) := by
    exact FiniteEntropyDensity.entropy_scale _ _ _
  unfold FiniteKLData.klDivergence
  rw [integral_sub p.entropy_integrable
    (standardizedProjectionFiniteKL a ha).cross_integrable]
  change (∫ x, p.density x * Real.log (p.density x)) -
    (∫ x, p.density x * Real.log (gaussianPDFReal 0 1 x)) = _
  have hc' : (∫ x, p.density x * Real.log (gaussianPDFReal 0 1 x)) =
      -Real.log (Real.sqrt (2 * Real.pi)) - 1 / 2 := by
    simpa only [mul_comm] using hc
  rw [hc']
  have hp : (∫ x, p.density x * Real.log (p.density x)) = -p.entropy := by
    simp only [FiniteEntropyDensity.entropy, neg_neg]
  rw [hp]
  rw [hent]
  ring

/-- The relative entropy of `sqrt(3) T_n` with respect to the standard
Gaussian, expressed through genuine finite differential entropies. -/
def diagonalGaussianDefect (n : ℕ) : ℝ :=
  Real.log (Real.sqrt (2 * Real.pi)) + 1 / 2 - Real.log (Real.sqrt 3) - diagonalEntropy n

theorem diagonalGaussianDefect_eq_kl {n : ℕ} (hn : 0 < n) :
    diagonalGaussianDefect n =
      (standardizedProjectionFiniteKL (diagonal n) (isUnit_diagonal hn)).klDivergence := by
  rw [standardizedProjection_kl_eq_entropy_defect, diagonalGaussianDefect,
    diagonalEntropy, dif_pos hn]

theorem diagonalGaussianDefect_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ diagonalGaussianDefect n := by
  rw [diagonalGaussianDefect_eq_kl hn]
  exact FiniteKLData.klDivergence_nonneg _

theorem diagonalGaussianDefect_difference (m n : ℕ) :
    diagonalGaussianDefect m - diagonalGaussianDefect n =
      diagonalEntropy n - diagonalEntropy m := by
  unfold diagonalGaussianDefect
  ring

end
end ENT.Quantitative
