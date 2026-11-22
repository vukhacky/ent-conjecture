module

public import ENT.Pang.FourierInversion
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.RealDeriv

/-!
Differentiation under the absolutely convergent characteristic integral.
The resulting derivatives belong to the actual standardized density identified
in FourierDensity, with no assumed derivative formula.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology ENNReal

namespace ENT.Pang

noncomputable section

theorem norm_probabilityFourierKernel (x u : ℝ) : ‖probabilityFourierKernel x u‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_probabilityFourierKernel (x u : ℝ) :
    HasDerivAt (fun x => probabilityFourierKernel x u)
      ((-Complex.I * (u : ℂ)) * probabilityFourierKernel x u) x := by
  have h := (((hasDerivAt_id x).const_mul (-u)).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1
  · rfl
  · simp only [probabilityFourierKernel, id_eq, mul_one, Complex.ofReal_neg]
    ring

def fourierDerivativeIntegrand (φ : ℝ → ℂ) (k : ℕ) (x u : ℝ) : ℂ :=
  (-Complex.I * (u : ℂ)) ^ k * probabilityFourierKernel x u * φ u

def fourierDerivativeIntegral (φ : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ u, fourierDerivativeIntegrand φ k x u

@[simp]
theorem fourierDerivativeIntegral_zero (φ : ℝ → ℂ) :
    fourierDerivativeIntegral φ 0 = probabilityFourierInverse φ := by
  funext x
  simp only [fourierDerivativeIntegral, fourierDerivativeIntegrand,
    pow_zero, one_mul, probabilityFourierInverse]

theorem norm_fourierDerivativeIntegrand (φ : ℝ → ℂ) (k : ℕ) (x u : ℝ) :
    ‖fourierDerivativeIntegrand φ k x u‖ = |u| ^ k * ‖φ u‖ := by
  simp only [fourierDerivativeIntegrand, norm_mul, norm_pow, norm_neg, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, norm_probabilityFourierKernel, one_mul, mul_one]

theorem measurable_fourierDerivativeIntegrand {φ : ℝ → ℂ} (hφ : Measurable φ)
    (k : ℕ) (x : ℝ) : Measurable (fourierDerivativeIntegrand φ k x) := by
  unfold fourierDerivativeIntegrand probabilityFourierKernel
  fun_prop

theorem integrable_fourierDerivativeIntegrand {t : ℝ} (ht : 0 < t)
    {n k : ℕ} (hn : k + 2 < n) (x : ℝ) :
    Integrable (fourierDerivativeIntegrand (charFun (standardizedSumLaw n t)) k x) := by
  let := isProbabilityMeasure_standardizedSumLaw ht n
  apply (integrable_abs_pow_mul_pangEnvelope hn).mono'
  · exact (measurable_fourierDerivativeIntegrand (by fun_prop) k x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => by
      rw [norm_fourierDerivativeIntegrand]
      exact mul_le_mul_of_nonneg_left
        (norm_charFun_standardizedSumLaw_le_pangEnvelope ht (by omega) u) (by positivity)

theorem continuous_fourierDerivativeIntegral {t : ℝ} (ht : 0 < t)
    {n k : ℕ} (hn : k + 2 < n) :
    Continuous (fourierDerivativeIntegral (charFun (standardizedSumLaw n t)) k) := by
  let := isProbabilityMeasure_standardizedSumLaw ht n
  change Continuous (fun x => ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ u, fourierDerivativeIntegrand (charFun (standardizedSumLaw n t)) k x u)
  apply Continuous.fun_smul continuous_const
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated
    (bound := fun u : ℝ => |u| ^ k * pangEnvelope n u)
  · exact Filter.Eventually.of_forall fun y =>
      (measurable_fourierDerivativeIntegrand (by fun_prop) k y).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun u => by
      rw [norm_fourierDerivativeIntegrand]
      exact mul_le_mul_of_nonneg_left
        (norm_charFun_standardizedSumLaw_le_pangEnvelope ht (by omega) u) (by positivity)
  · exact integrable_abs_pow_mul_pangEnvelope hn
  · exact Filter.Eventually.of_forall fun u => by
      unfold fourierDerivativeIntegrand probabilityFourierKernel
      fun_prop

theorem hasDerivAt_fourierDerivativeIntegrand (φ : ℝ → ℂ) (k : ℕ) (x u : ℝ) :
    HasDerivAt (fun x => fourierDerivativeIntegrand φ k x u)
      (fourierDerivativeIntegrand φ (k + 1) x u) x := by
  convert ((hasDerivAt_probabilityFourierKernel x u).const_mul
    ((-Complex.I * (u : ℂ)) ^ k)).mul_const (φ u) using 1
  · rfl
  · simp only [fourierDerivativeIntegrand, pow_succ]
    ring

theorem hasDerivAt_fourierDerivativeIntegral {t : ℝ} (ht : 0 < t)
    {n k : ℕ} (hn : k + 3 < n) (x : ℝ) :
    HasDerivAt (fourierDerivativeIntegral (charFun (standardizedSumLaw n t)) k)
      (fourierDerivativeIntegral (charFun (standardizedSumLaw n t)) (k + 1) x) x := by
  let := isProbabilityMeasure_standardizedSumLaw ht n
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => fourierDerivativeIntegrand (charFun (standardizedSumLaw n t)) k x u)
    (F' := fun x u => fourierDerivativeIntegrand (charFun (standardizedSumLaw n t)) (k + 1) x u)
    (x₀ := x) (s := univ) (bound := fun u : ℝ => |u| ^ (k + 1) * pangEnvelope n u)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun y =>
      (measurable_fourierDerivativeIntegrand (by fun_prop) k y).aestronglyMeasurable)
    (integrable_fourierDerivativeIntegrand ht (by omega) x)
    ((measurable_fourierDerivativeIntegrand (by fun_prop) (k + 1) x).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u y _ => by
      rw [norm_fourierDerivativeIntegrand]
      exact mul_le_mul_of_nonneg_left
        (norm_charFun_standardizedSumLaw_le_pangEnvelope ht (by omega) u) (by positivity))
    (integrable_abs_pow_mul_pangEnvelope (by omega))
    (Filter.Eventually.of_forall fun u y _ =>
      hasDerivAt_fourierDerivativeIntegrand _ k y u)
  exact h.2.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem iteratedDeriv_standardizedDensity {t : ℝ} (ht : 0 < t)
    {n k : ℕ} (hn : k + 2 < n) :
    iteratedDeriv k (standardizedDensity n t) =
      fun x => (fourierDerivativeIntegral (charFun (standardizedSumLaw n t)) k x).re := by
  induction k with
  | zero =>
      funext x
      rw [iteratedDeriv_zero, fourierDerivativeIntegral_zero,
        standardizedDensity_fourier_inversion ht (by omega), Complex.ofReal_re]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih (by omega)]
      funext x
      have h := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x
        (hasDerivAt_fourierDerivativeIntegral ht (by omega : k + 3 < n) x)
      exact h.deriv

theorem contDiff_standardizedDensity {t : ℝ} (ht : 0 < t)
    {n N : ℕ} (hn : N + 2 < n) : ContDiff ℝ N (standardizedDensity n t) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro k hk
    rw [iteratedDeriv_standardizedDensity ht (by omega)]
    exact Complex.continuous_re.comp (continuous_fourierDerivativeIntegral ht (by omega))
  · intro k hk
    rw [iteratedDeriv_standardizedDensity ht (by omega)]
    intro x
    exact ((Complex.reCLM.hasFDerivAt).comp_hasDerivAt x
      (hasDerivAt_fourierDerivativeIntegral ht (by omega : k + 3 < n) x)).differentiableAt

theorem contDiff_three_standardizedDensity {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) : ContDiff ℝ 3 (standardizedDensity n t) :=
  contDiff_standardizedDensity ht (N := 3) (by omega)

end
end ENT.Pang
