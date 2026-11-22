module

public import ENT.Quantitative.EdgeworthCharacteristic
public import ENT.Pang.FourierDerivatives
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-! Generic differentiation of absolutely convergent characteristic
integrals, specialized to the genuine un-tilted uniform density and the
standard Gaussian. Every derivative under the integral has its own proved
weighted integrability condition. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace ENT.Quantitative
noncomputable section

theorem integrable_fourierDerivative_of_weight {φ : ℝ → ℂ} (hφ : Measurable φ)
    (k : ℕ) (hk : Integrable (fun u : ℝ => u^k • φ u)) (x : ℝ) :
    Integrable (Pang.fourierDerivativeIntegrand φ k x) := by
  apply hk.norm.mono'
  · exact (Pang.measurable_fourierDerivativeIntegrand hφ k x).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Pang.norm_fourierDerivativeIntegrand, norm_smul, Real.norm_eq_abs, abs_pow]

theorem hasDerivAt_fourierDerivative_of_weight {φ : ℝ → ℂ} (hφ : Measurable φ)
    (k : ℕ) (hk : Integrable (fun u : ℝ => u^k • φ u))
    (hk1 : Integrable (fun u : ℝ => u^(k+1) • φ u)) (x : ℝ) :
    HasDerivAt (Pang.fourierDerivativeIntegral φ k)
      (Pang.fourierDerivativeIntegral φ (k+1) x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => Pang.fourierDerivativeIntegrand φ k x u)
    (F' := fun x u => Pang.fourierDerivativeIntegrand φ (k+1) x u)
    (x₀ := x) (s := univ) (bound := fun u : ℝ => ‖u^(k+1) • φ u‖)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      (Pang.measurable_fourierDerivativeIntegrand hφ k y).aestronglyMeasurable)
    (integrable_fourierDerivative_of_weight hφ k hk x)
    ((Pang.measurable_fourierDerivativeIntegrand hφ (k+1) x).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u y _ => by
      rw [Pang.norm_fourierDerivativeIntegrand, norm_smul, Real.norm_eq_abs, abs_pow])
    hk1.norm
    (Filter.Eventually.of_forall fun u y _ => Pang.hasDerivAt_fourierDerivativeIntegrand φ k y u)
  exact h.2.const_smul ((2*Real.pi)⁻¹:ℝ)

theorem iteratedDeriv_real_fourierInverse {φ : ℝ → ℂ} (hφ : Measurable φ) (k : ℕ)
    (hk : ∀ j ≤ k, Integrable (fun u : ℝ => u^j • φ u)) :
    iteratedDeriv k (fun x => (Pang.probabilityFourierInverse φ x).re) =
      fun x => (Pang.fourierDerivativeIntegral φ k x).re := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, Pang.fourierDerivativeIntegral_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih (fun j hj => hk j (by omega))]
    funext x
    have hd := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x
      (hasDerivAt_fourierDerivative_of_weight hφ k (hk k (by omega))
        (hk (k+1) le_rfl) x)
    exact hd.deriv

theorem iteratedDeriv_standardizedDiagonalDensity {n k : ℕ} (hn : k+2 < n) :
    iteratedDeriv k (standardizedDiagonalDensity n) =
      fun x => (Pang.fourierDerivativeIntegral
        (charFun (standardizedProjectionLaw (diagonal n))) k x).re := by
  let : IsProbabilityMeasure (standardizedProjectionLaw (diagonal n)) := by
    unfold standardizedProjectionLaw
    infer_instance
  have h := iteratedDeriv_real_fourierInverse (φ := charFun (standardizedProjectionLaw (diagonal n)))
    (by fun_prop) k (fun j hj => integrable_pow_smul_charFun_standardizedDiagonal (by omega))
  have he : (fun x => (Pang.probabilityFourierInverse
      (charFun (standardizedProjectionLaw (diagonal n))) x).re) = standardizedDiagonalDensity n := by
    funext x
    rw [standardizedDiagonalDensity_fourier_inversion (by omega), Complex.ofReal_re]
  rwa [he] at h

theorem charFun_standardGaussian (u : ℝ) :
    charFun (gaussianReal 0 1) u = (Pang.gaussianWeight u : ℂ) := by
  rw [charFun_gaussianReal]
  unfold Pang.gaussianWeight
  simp only [Complex.ofReal_zero, Complex.ofReal_one, NNReal.coe_one, mul_zero, zero_mul,
    one_mul, zero_sub, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  congr 1
  ring

theorem integrable_pow_smul_charFun_standardGaussian (k : ℕ) :
    Integrable (fun u : ℝ => u^k • charFun (gaussianReal 0 1) u) := by
  have h : Integrable (fun u : ℝ => ((u^k*Pang.gaussianWeight u : ℝ) : ℂ)) :=
    (Pang.integrable_pow_mul_gaussianWeight k).ofReal
  simpa only [charFun_standardGaussian, Complex.real_smul, Complex.ofReal_mul] using h

theorem standardGaussianPDF_fourier_inversion (x : ℝ) :
    Pang.probabilityFourierInverse (charFun (gaussianReal 0 1)) x =
      (gaussianPDFReal 0 1 x : ℂ) := by
  exact Pang.probabilityFourierInverse_eq_density (gaussianReal 0 1)
    (by unfold gaussianPDFReal; fun_prop) (integrable_gaussianPDFReal 0 1)
    (gaussianPDFReal_nonneg 0 1) standardGaussianFiniteEntropyDensity.law_eq
    (by simpa only [pow_zero, one_smul] using integrable_pow_smul_charFun_standardGaussian 0) x

theorem iteratedDeriv_standardGaussianPDF_fourier (k : ℕ) :
    iteratedDeriv k (gaussianPDFReal 0 1) =
      fun x => (Pang.fourierDerivativeIntegral (charFun (gaussianReal 0 1)) k x).re := by
  have h := iteratedDeriv_real_fourierInverse (φ := charFun (gaussianReal 0 1))
    (by fun_prop) k (fun j _ => integrable_pow_smul_charFun_standardGaussian j)
  have he : (fun x => (Pang.probabilityFourierInverse (charFun (gaussianReal 0 1)) x).re) =
      gaussianPDFReal 0 1 := by
    funext x
    rw [standardGaussianPDF_fourier_inversion, Complex.ofReal_re]
  rwa [he] at h

theorem iteratedDeriv_standardGaussianPDF (k : ℕ) (x : ℝ) :
    iteratedDeriv k (gaussianPDFReal 0 1) x =
      (-1:ℝ)^k * Polynomial.aeval x (Polynomial.hermite k) * gaussianPDFReal 0 1 x := by
  have he : gaussianPDFReal 0 1 = fun y : ℝ =>
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(y^2/2)) := by
    funext y
    rw [standardGaussianPDF_eq]
    unfold Pang.gaussianWeight
    congr 2
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
  ring

end
end ENT.Quantitative
