module

public import ENT.Quantitative.EdgeworthFourierBounds
public import ENT.Quantitative.EdgeworthFourierCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! First-order local Edgeworth expansion for every derivative of the actual
standardized diagonal density. The interchange of the limit and the Fourier
integral is proved using the weighted majorant from EdgeworthFourierBounds. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace ENT.Quantitative
noncomputable section

def firstFourierCorrection (n : ℕ) (u : ℝ) : ℂ :=
  ((n:ℝ)*(uniformFourierFactor n u-Pang.gaussianWeight u) : ℝ)

def firstFourierLimit (u : ℝ) : ℂ := (-u^4/20*Pang.gaussianWeight u : ℝ)

theorem measurable_firstFourierCorrection (n : ℕ) : Measurable (firstFourierCorrection n) := by
  unfold firstFourierCorrection uniformFourierFactor uniformSumFrequency Pang.gaussianWeight
  exact Complex.continuous_ofReal.measurable.comp
    ((continuous_const.mul (((Real.continuous_sinc.comp (by fun_prop)).pow n).sub
      (by fun_prop))).measurable)

theorem firstFourierCorrection_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => firstFourierCorrection n u) atTop (𝓝 (firstFourierLimit u)) := by
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp (uniformFourierFactor_first_correction u)

theorem fourierDerivative_firstCorrection_tendsto (k : ℕ) (x : ℝ) :
    Tendsto (fun n : ℕ => Pang.fourierDerivativeIntegral (firstFourierCorrection n) k x)
      atTop (𝓝 (Pang.fourierDerivativeIntegral firstFourierLimit k x)) := by
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_sincLogNeighborhood
  let N := k+6
  have hN : 0 < N := by dsimp [N]; omega
  have hNk : k+4 < N := by dsimp [N]; omega
  have hi := tendsto_integral_filter_of_dominated_convergence
    (F := fun n u => Pang.fourierDerivativeIntegrand (firstFourierCorrection n) k x u)
    (f := Pang.fourierDerivativeIntegrand firstFourierLimit k x)
    (fun u : ℝ => |u|^k*firstFourierMajorant δ N u)
    (Filter.Eventually.of_forall fun n =>
      (Pang.measurable_fourierDerivativeIntegrand (measurable_firstFourierCorrection n) k x).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop N] with n hn
      filter_upwards [] with u
      rw [Pang.norm_fourierDerivativeIntegrand]
      have he : ‖firstFourierCorrection n u‖ =
          |(n:ℝ)*(uniformFourierFactor n u-Pang.gaussianWeight u)| := by
        simp only [firstFourierCorrection, Complex.norm_real, Real.norm_eq_abs]
      rw [he]
      exact mul_le_mul_of_nonneg_left (uniformFourierFactor_first_bound hδ0 hδ hN hn u) (by positivity))
    (integrable_firstFourierMajorant_weighted hNk δ)
    (Filter.Eventually.of_forall fun u => by
      exact (firstFourierCorrection_tendsto u).const_mul
        ((-Complex.I*(u:ℂ))^k*Pang.probabilityFourierKernel x u))
  exact hi.const_smul ((2*Real.pi)⁻¹:ℝ)

theorem firstFourierCorrection_eq (n : ℕ) (u : ℝ) :
    firstFourierCorrection n u = (n:ℝ) •
      (charFun (standardizedProjectionLaw (diagonal n)) u-charFun (gaussianReal 0 1) u) := by
  simp only [firstFourierCorrection, charFun_standardizedDiagonal, charFun_standardGaussian,
    uniformFourierFactor, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.real_smul]

theorem fourierDerivative_firstCorrection_eq {n k : ℕ} (hn : k+2 < n) (x : ℝ) :
    Pang.fourierDerivativeIntegral (firstFourierCorrection n) k x = (n:ℝ) •
      (Pang.fourierDerivativeIntegral (charFun (standardizedProjectionLaw (diagonal n))) k x -
        Pang.fourierDerivativeIntegral (charFun (gaussianReal 0 1)) k x) := by
  let : IsProbabilityMeasure (standardizedProjectionLaw (diagonal n)) := by
    unfold standardizedProjectionLaw
    infer_instance
  have hnint := integrable_fourierDerivative_of_weight
    (φ := charFun (standardizedProjectionLaw (diagonal n))) (by fun_prop) k
    (integrable_pow_smul_charFun_standardizedDiagonal hn) x
  have hgint := integrable_fourierDerivative_of_weight (φ := charFun (gaussianReal 0 1))
    (by fun_prop) k (integrable_pow_smul_charFun_standardGaussian k) x
  have he : Pang.fourierDerivativeIntegrand (firstFourierCorrection n) k x = fun u =>
      (n:ℝ) • (Pang.fourierDerivativeIntegrand
        (charFun (standardizedProjectionLaw (diagonal n))) k x u -
        Pang.fourierDerivativeIntegrand (charFun (gaussianReal 0 1)) k x u) := by
    funext u
    unfold Pang.fourierDerivativeIntegrand
    rw [firstFourierCorrection_eq]
    simp only [Pang.fourierDerivativeIntegrand, Complex.real_smul]
    ring
  simp only [Pang.fourierDerivativeIntegral]
  rw [he, integral_smul, integral_sub hnint hgint]
  simp only [smul_sub, smul_smul]
  congr 1 <;> ring

theorem fourierDerivative_firstLimit_eq (k : ℕ) (x : ℝ) :
    Pang.fourierDerivativeIntegral firstFourierLimit k x =
      (-1/20:ℝ) • Pang.fourierDerivativeIntegral (charFun (gaussianReal 0 1)) (k+4) x := by
  have he : Pang.fourierDerivativeIntegrand firstFourierLimit k x = fun u =>
      (-1/20:ℝ) • Pang.fourierDerivativeIntegrand (charFun (gaussianReal 0 1)) (k+4) x u := by
    funext u
    have hi : (-Complex.I*(u:ℂ))^4 = (u:ℂ)^4 := by
      rw [mul_pow]
      norm_num [show (4:ℕ) = 2*2 from rfl, pow_mul, Complex.I_sq]
    simp only [Pang.fourierDerivativeIntegrand, firstFourierLimit, charFun_standardGaussian,
      pow_add, hi, Complex.real_smul]
    push_cast
    ring
  simp only [Pang.fourierDerivativeIntegral]
  rw [he, integral_smul]
  simp only [smul_smul]
  congr 1
  ring

/-- First-order Edgeworth expansion of every density derivative at every
fixed real point. This is a density result, not an entropy expansion. -/
theorem standardizedDiagonalDensity_jet_first_correction (k : ℕ) (x : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*
      (iteratedDeriv k (standardizedDiagonalDensity n) x - iteratedDeriv k (gaussianPDFReal 0 1) x))
      atTop (𝓝 ((-1/20:ℝ)*iteratedDeriv (k+4) (gaussianPDFReal 0 1) x)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (fourierDerivative_firstCorrection_tendsto k x)
  rw [fourierDerivative_firstLimit_eq] at ht
  simp only [Complex.smul_re, smul_eq_mul] at ht
  rw [iteratedDeriv_standardGaussianPDF_fourier (k+4)]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k+3)] with n hn
  change (Pang.fourierDerivativeIntegral (firstFourierCorrection n) k x).re = _
  rw [fourierDerivative_firstCorrection_eq (by omega), Complex.smul_re, Complex.sub_re,
    smul_eq_mul, iteratedDeriv_standardizedDiagonalDensity (by omega),
    iteratedDeriv_standardGaussianPDF_fourier]

theorem standardizedDiagonalDensity_jet_tendsto (k : ℕ) (x : ℝ) :
    Tendsto (fun n : ℕ => iteratedDeriv k (standardizedDiagonalDensity n) x)
      atTop (𝓝 (iteratedDeriv k (gaussianPDFReal 0 1) x)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((standardizedDiagonalDensity_jet_first_correction k x).mul hi).add_const
    (iteratedDeriv k (gaussianPDFReal 0 1) x)
  simp only [mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  ring

theorem standardizedDiagonalDensity_zero_tendsto :
    Tendsto (fun n : ℕ => standardizedDiagonalDensity n 0)
      atTop (𝓝 (gaussianPDFReal 0 1 0)) := by
  simpa only [iteratedDeriv_zero] using standardizedDiagonalDensity_jet_tendsto 0 0

theorem standardizedDiagonalDensity_second_zero_tendsto :
    Tendsto (fun n : ℕ => iteratedDeriv 2 (standardizedDiagonalDensity n) 0)
      atTop (𝓝 (-gaussianPDFReal 0 1 0)) := by
  have he : iteratedDeriv 2 (gaussianPDFReal 0 1) 0 = -gaussianPDFReal 0 1 0 := by
    rw [iteratedDeriv_standardGaussianPDF]
    norm_num [Polynomial.hermite, Polynomial.derivative_mul, Polynomial.derivative_X]
  simpa only [he] using standardizedDiagonalDensity_jet_tendsto 2 0

end
end ENT.Quantitative
