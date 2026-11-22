module

public import ENT.Pang.FourierDensity
public import ENT.Pang.EnvelopeIntegrability
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
Fourier inversion for the actual continuous standardized density.  Integrability
of the characteristic function is proved from the independent-sum envelope.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform ENNReal RealInnerProductSpace

namespace ENT.Pang

noncomputable section

theorem norm_charFun_standardizedSumLaw_le_pangEnvelope {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) (u : ℝ) :
    ‖charFun (standardizedSumLaw n t) u‖ ≤ pangEnvelope n u := by
  apply (norm_charFun_standardizedSumLaw_le ht hn u).trans
  apply Real.rpow_le_rpow_of_exponent_le
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have h : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
    linarith
  · linarith

theorem integrable_pow_smul_charFun_standardizedSumLaw {t : ℝ} (ht : 0 < t)
    {n k : ℕ} (hn : k + 2 < n) :
    Integrable (fun u : ℝ => u ^ k • charFun (standardizedSumLaw n t) u) := by
  let := isProbabilityMeasure_standardizedSumLaw ht n
  apply (integrable_abs_pow_mul_pangEnvelope hn).mono'
  · fun_prop
  · exact Filter.Eventually.of_forall fun u => by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (norm_charFun_standardizedSumLaw_le_pangEnvelope ht (by omega) u) (by positivity)

theorem integrable_charFun_standardizedSumLaw {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 2 < n) : Integrable (charFun (standardizedSumLaw n t)) := by
  simpa only [pow_zero, one_smul] using
    (integrable_pow_smul_charFun_standardizedSumLaw ht (k := 0) hn)

def probabilityFourierKernel (x u : ℝ) : ℂ :=
  Complex.exp (((-u * x : ℝ) : ℂ) * Complex.I)

def probabilityFourierInverse (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ u, probabilityFourierKernel x u * φ u

theorem probabilityFourierInverse_eq_fourier (φ : ℝ → ℂ) (x : ℝ) :
    probabilityFourierInverse φ x =
      ((2 * Real.pi)⁻¹ : ℝ) • (𝓕 φ) (x / (2 * Real.pi)) := by
  rw [probabilityFourierInverse, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [smul_eq_mul, probabilityFourierKernel]
  congr 2
  congr 1
  field_simp

theorem fourierInv_charFun_scale (φ : ℝ → ℂ) (x : ℝ) :
    (𝓕⁻ (fun u => φ ((-2 * Real.pi) * u))) x = probabilityFourierInverse φ x := by
  rw [Real.fourierInv_eq']
  let g : ℝ → ℂ := fun u => probabilityFourierKernel x u * φ u
  calc
    _ = ∫ u, g ((-2 * Real.pi) * u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [g, probabilityFourierKernel]
      simp only [conj_trivial]
      congr 2
      push_cast
      ring
    _ = |(-2 * Real.pi)⁻¹| • ∫ u, g u := Measure.integral_comp_mul_left g _
    _ = _ := by
      simp only [abs_inv, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rfl

theorem fourier_density_eq_charFun (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (hlaw : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) (u : ℝ) :
    (𝓕 (fun x => (f x : ℂ))) u = charFun μ ((-2 * Real.pi) * u) := by
  rw [Real.fourier_real_eq_integral_exp_smul, charFun_apply_real, hlaw,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (h0 x)]
  simp only [smul_eq_mul, Complex.real_smul]
  rw [mul_comm (f x : ℂ)]
  congr 2
  push_cast
  ring

theorem probabilityFourierInverse_eq_density (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (h0 : ∀ x, 0 ≤ f x)
    (hlaw : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hφ : Integrable (charFun μ)) (x : ℝ) :
    probabilityFourierInverse (charFun μ) x = (f x : ℂ) := by
  have hFourier : 𝓕 (fun x => (f x : ℂ)) = fun u => charFun μ ((-2 * Real.pi) * u) :=
    funext (fourier_density_eq_charFun μ hf.measurable h0 hlaw)
  have hFourierInt : Integrable (𝓕 (fun x => (f x : ℂ))) := by
    rw [hFourier]
    exact hφ.comp_mul_left' (by positivity)
  have hinv := hfi.ofReal.fourierInv_fourier_eq hFourierInt (v := x)
    (Complex.continuous_ofReal.comp hf).continuousAt
  rw [hFourier, fourierInv_charFun_scale] at hinv
  exact hinv

theorem standardizedDensity_fourier_inversion {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 2 < n) (x : ℝ) :
    probabilityFourierInverse (charFun (standardizedSumLaw n t)) x =
      (standardizedDensity n t x : ℂ) :=
  probabilityFourierInverse_eq_density (standardizedSumLaw n t)
    (continuous_standardizedDensity n t) (integrable_standardizedDensity ht (by omega))
    (standardizedDensity_nonneg ht (by omega)) (standardizedDensity_law ht (by omega))
    (integrable_charFun_standardizedSumLaw ht hn) x

end
end ENT.Pang
