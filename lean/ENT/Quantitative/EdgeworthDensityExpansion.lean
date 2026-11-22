module

public import ENT.Quantitative.EdgeworthFourierPolynomials

/-! The actual three-profile Edgeworth expansion of the standardized
continuous uniform-sum density.  This theorem has no Edgeworth hypothesis:
it combines the proved characteristic-function remainder, its integrable
majorant, and exact Fourier inversion. -/

@[expose] public section
set_option autoImplicit false
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def thirdFourierCorrection (n : ℕ) (u : ℝ) : ℂ :=
  ((n:ℝ)^4*(uniformFourierFactor n u-uniformFourierProfile n u) : ℝ)

theorem thirdFourierCorrection_eq (n : ℕ) (u : ℝ) :
    thirdFourierCorrection n u = (n:ℝ)^4 •
      (charFun (standardizedProjectionLaw (diagonal n)) u-(uniformFourierProfile n u:ℂ)) := by
  simp only [thirdFourierCorrection, charFun_standardizedDiagonal, uniformFourierFactor,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.real_smul]

theorem thirdFourierCorrection_inverse_re {n : ℕ} (hn : 2 < n) (x : ℝ) :
    (Pang.probabilityFourierInverse (thirdFourierCorrection n) x).re =
      (n:ℝ)^4*(standardizedDiagonalDensity n x-uniformEdgeworthApprox n x) := by
  let : IsProbabilityMeasure (standardizedProjectionLaw (diagonal n)) := by
    unfold standardizedProjectionLaw
    infer_instance
  have hchar : Integrable (charFun (standardizedProjectionLaw (diagonal n))) := by
    simpa only [pow_zero, one_smul] using integrable_pow_smul_charFun_standardizedDiagonal (k := 0) hn
  have hni : Integrable (fun u => Pang.probabilityFourierKernel x u*
      charFun (standardizedProjectionLaw (diagonal n)) u) := by
    apply hchar.norm.mono'
    · unfold Pang.probabilityFourierKernel
      fun_prop
    · filter_upwards [] with u
      rw [norm_mul, Pang.norm_probabilityFourierKernel, one_mul]
  have hpi : Integrable (fun u => Pang.probabilityFourierKernel x u*(uniformFourierProfile n u:ℂ)) := by
    simp_rw [uniformFourierProfile_eq_polynomial]
    exact integrable_gaussianPolynomial_fourierKernel (uniformFourierProfilePolynomial n) x
  have he : (fun u => Pang.probabilityFourierKernel x u*thirdFourierCorrection n u) =
      fun u => (n:ℝ)^4 • (Pang.probabilityFourierKernel x u*
        charFun (standardizedProjectionLaw (diagonal n)) u-
        Pang.probabilityFourierKernel x u*(uniformFourierProfile n u:ℂ)) := by
    funext u
    rw [thirdFourierCorrection_eq]
    simp only [Complex.real_smul]
    ring
  have heq : Pang.probabilityFourierInverse (thirdFourierCorrection n) x = (n:ℝ)^4 •
      (Pang.probabilityFourierInverse (charFun (standardizedProjectionLaw (diagonal n))) x-
        Pang.probabilityFourierInverse (fun u => (uniformFourierProfile n u:ℂ)) x) := by
    unfold Pang.probabilityFourierInverse
    rw [he, integral_smul, integral_sub hni hpi]
    simp only [smul_sub, smul_smul]
    congr 1 <;> ring
  rw [heq, Complex.smul_re, Complex.sub_re, standardizedDiagonalDensity_fourier_inversion hn,
    Complex.ofReal_re, uniformFourierProfile_inverse, smul_eq_mul]

theorem standardizedDiagonalDensity_uniform_error {C δ : ℝ} (hC : 0 ≤ C) (hδ0 : 0 < δ)
    (hδ : SincLogNeighborhood δ)
    (hlog : ∀ x : ℝ, |x| < δ → |Real.log (Real.sinc x)-logSincEighth x| ≤ C*x^10)
    {n : ℕ} (hn : 16 ≤ n) (x : ℝ) :
    |(n:ℝ)^4*(standardizedDiagonalDensity n x-uniformEdgeworthApprox n x)| ≤
      (2*Real.pi)⁻¹*(∫ u, uniformFourierMajorant C δ 16 u) := by
  have hb := uniformFourierFactor_third_bound hC hδ0 hδ hlog (by norm_num : 0 < (16:ℕ)) hn
  have hi := integrable_uniformFourierMajorant (by norm_num : 10 < (16:ℕ)) C δ
  have hnorm : ‖∫ u, Pang.probabilityFourierKernel x u*thirdFourierCorrection n u‖ ≤
      ∫ u, uniformFourierMajorant C δ 16 u := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [] with u
    simpa only [norm_mul, Pang.norm_probabilityFourierKernel, one_mul,
      thirdFourierCorrection, Complex.norm_real, Real.norm_eq_abs, abs_mul] using hb u
  have htotal : ‖Pang.probabilityFourierInverse (thirdFourierCorrection n) x‖ ≤
      (2*Real.pi)⁻¹*(∫ u, uniformFourierMajorant C δ 16 u) := by
    unfold Pang.probabilityFourierInverse
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2*Real.pi)⁻¹)]
    exact mul_le_mul_of_nonneg_left hnorm (by positivity)
  rw [← thirdFourierCorrection_inverse_re (by omega)]
  exact (Complex.abs_re_le_norm _).trans htotal

/-- Uniform, absolute O(n⁻⁴) error for the true continuous density.  The
constant is existential and the theorem is independent of an entropy
expansion or a quantitative central limit theorem. -/
theorem uniformDensityEdgeworthBound_proved : UniformDensityEdgeworthBound := by
  obtain ⟨C, δ, hC, hδ0, hδ1, hδ, hlog⟩ := exists_logSincEighth_bound
  let B := (2*Real.pi)⁻¹*(∫ u, uniformFourierMajorant C δ 16 u)
  refine ⟨|B|+1, by positivity, 16, by norm_num, ?_⟩
  intro n hn x
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb := standardizedDiagonalDensity_uniform_error hC.le hδ0 hδ hlog hn x
  change |(n:ℝ)^4*(standardizedDiagonalDensity n x-uniformEdgeworthApprox n x)| ≤ B at hb
  rw [abs_mul, abs_of_pos (by positivity : 0 < (n:ℝ)^4)] at hb
  apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)^4)).mpr
  nlinarith [le_abs_self B]

end
end ENT.Quantitative
