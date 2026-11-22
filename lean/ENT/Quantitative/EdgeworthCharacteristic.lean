module

public import ENT.Quantitative.EdgeworthGaussian
public import ENT.Pang.FourierInversion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The exact characteristic function and an integrable Fourier envelope
for the actual un-tilted standardized continuous uniform sum. This handles
`t = 0` directly; no limiting interpretation of the tilted law is used. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace ENT.Quantitative
noncomputable section

theorem integral_uniformUnit_eq_interval (f : ℝ → ℝ) :
    (∫ x, f x ∂uniformUnit) = (1/2:ℝ) * ∫ x in (-1:ℝ)..1, f x := by
  rw [uniformUnit, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  simp

theorem integral_uniformUnit_cos (u : ℝ) :
    (∫ x, Real.cos (u*x) ∂uniformUnit) = Real.sinc u := by
  by_cases hu : u = 0
  · simp [hu]
  rw [integral_uniformUnit_eq_interval]
  have hi := Pang.integral_exp_cos 0 u (-1) 1 (by positivity)
  simp only [zero_mul, Real.exp_zero, one_mul, zero_add, zero_pow (by decide : (2:ℕ) ≠ 0),
    mul_one, mul_neg_one, Real.cos_neg, Real.sin_neg, mul_neg, neg_zero, sub_neg_eq_add] at hi
  rw [hi, Real.sinc_of_ne_zero hu]
  field_simp
  ring

theorem integral_uniformUnit_sin (u : ℝ) :
    (∫ x, Real.sin (u*x) ∂uniformUnit) = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  rw [integral_uniformUnit_eq_interval]
  have hi := Pang.integral_exp_sin 0 u (-1) 1 (by positivity)
  simp only [zero_mul, Real.exp_zero, one_mul, zero_sub, zero_add,
    zero_pow (by decide : (2:ℕ) ≠ 0), mul_one, mul_neg_one, neg_zero, Real.cos_neg, Real.sin_neg,
    sub_self, zero_div] at hi
  rw [hi]
  ring

theorem charFun_uniformUnit (u : ℝ) : charFun uniformUnit u = (Real.sinc u : ℂ) := by
  apply Complex.ext
  · rw [Pang.charFun_re_real, integral_uniformUnit_cos]
    rfl
  · rw [Pang.charFun_im_real, integral_uniformUnit_sin]
    rfl

def uniformSumFrequency (n : ℕ) (u : ℝ) : ℝ :=
  Real.sqrt 3 * (Real.sqrt (n:ℝ))⁻¹ * u

theorem uniformSumFrequency_sq {n : ℕ} (hn : 0 < n) (u : ℝ) :
    uniformSumFrequency n u ^ 2 = 3*u^2/(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold uniformSumFrequency
  rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hnR.le, Real.sq_sqrt (by norm_num)]
  ring

theorem charFun_standardizedDiagonal (n : ℕ) (u : ℝ) :
    charFun (standardizedProjectionLaw (diagonal n)) u =
      (Real.sinc (uniformSumFrequency n u) : ℂ)^n := by
  have hp : (fun x : Fin n → ℝ => Real.sqrt 3 * projection (diagonal n) x) =
      (fun x : Fin n → ℝ => (Real.sqrt 3 * (Real.sqrt (n:ℝ))⁻¹) * ∑ i, x i) := by
    funext x
    simp only [projection, diagonal, ← Finset.mul_sum]
    ring
  rw [standardizedProjectionLaw, projectionLaw,
    Measure.map_map (by fun_prop) (measurable_projection _)]
  change charFun ((cubeLaw n).map (fun x => Real.sqrt 3 * projection (diagonal n) x)) u = _
  rw [hp, charFun_map_mul_comp (by fun_prop)]
  change charFun ((Measure.pi fun _ : Fin n => uniformUnit).map (fun x => ∑ i, x i))
    ((Real.sqrt 3 * (Real.sqrt (n:ℝ))⁻¹) * u) = _
  rw [charFun_map_sum_pi_eq_prod]
  simp only [Finset.prod_apply, charFun_uniformUnit, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, uniformSumFrequency]

theorem sinc_square_envelope (u : ℝ) :
    Real.sinc u ^ 2 ≤ 1 / (1 + u^2/3) := by
  by_cases hu : u = 0
  · simp [hu]
  have hs := Pang.sine_variance_envelope u (1/3) le_rfl
  rw [Real.sinc_of_ne_zero hu, div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero hu) (by positivity : 0 < 1+u^2/3)).mpr
  nlinarith only [hs]

theorem norm_charFun_standardizedDiagonal_sq_le {n : ℕ} (hn : 0 < n) (u : ℝ) :
    ‖charFun (standardizedProjectionLaw (diagonal n)) u‖^2 ≤
      (1/(1 + u^2/(n:ℝ)))^n := by
  have h := sinc_square_envelope (uniformSumFrequency n u)
  rw [uniformSumFrequency_sq hn] at h
  have he : 3*u^2/(n:ℝ)/3 = u^2/(n:ℝ) := by ring
  rw [he] at h
  have hp := pow_le_pow_left₀ (sq_nonneg (Real.sinc (uniformSumFrequency n u))) h n
  rw [charFun_standardizedDiagonal, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have he' : (|Real.sinc (uniformSumFrequency n u)|^n)^2 =
      (Real.sinc (uniformSumFrequency n u)^2)^n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, sq_abs]
  rwa [he']

theorem norm_charFun_standardizedDiagonal_le {n : ℕ} (hn : 0 < n) (u : ℝ) :
    ‖charFun (standardizedProjectionLaw (diagonal n)) u‖ ≤
      (1 + u^2/(n:ℝ)) ^ (-(n:ℝ)/2) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hb : 0 < 1 + u^2/(n:ℝ) := by positivity
  have hr : 0 ≤ (1 + u^2/(n:ℝ)) ^ (-(n:ℝ)/2) :=
    (Real.rpow_pos_of_pos hb _).le
  have heq : ((1 + u^2/(n:ℝ)) ^ (-(n:ℝ)/2))^2 =
      (1/(1 + u^2/(n:ℝ)))^n := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    rw [show -(n:ℝ)/2*2 = -(n:ℝ) by ring,
      Real.rpow_neg hb.le, Real.rpow_natCast]
    simp only [one_div, inv_pow]
  have h := norm_charFun_standardizedDiagonal_sq_le hn u
  rw [← heq] at h
  nlinarith [norm_nonneg (charFun (standardizedProjectionLaw (diagonal n)) u)]

theorem norm_charFun_standardizedDiagonal_le_pangEnvelope {n : ℕ} (hn : 0 < n) (u : ℝ) :
    ‖charFun (standardizedProjectionLaw (diagonal n)) u‖ ≤ Pang.pangEnvelope n u := by
  apply (norm_charFun_standardizedDiagonal_le hn u).trans
  apply Real.rpow_le_rpow_of_exponent_le
  · have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have hp : 0 ≤ u^2/(n:ℝ) := by positivity
    linarith
  · linarith

theorem integrable_pow_smul_charFun_standardizedDiagonal {n k : ℕ} (hn : k+2 < n) :
    Integrable (fun u : ℝ => u^k • charFun (standardizedProjectionLaw (diagonal n)) u) := by
  let : IsProbabilityMeasure (standardizedProjectionLaw (diagonal n)) := by
    unfold standardizedProjectionLaw
    infer_instance
  apply (Pang.integrable_abs_pow_mul_pangEnvelope hn).mono'
  · fun_prop
  · filter_upwards [] with u
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left
      (norm_charFun_standardizedDiagonal_le_pangEnvelope (by omega) u) (by positivity)

theorem integrable_charFun_standardizedDiagonal {n : ℕ} (hn : 2 < n) :
    Integrable (charFun (standardizedProjectionLaw (diagonal n))) := by
  simpa only [pow_zero, one_smul] using
    integrable_pow_smul_charFun_standardizedDiagonal (k := 0) hn

def standardizedDiagonalDensity (n : ℕ) : ℝ → ℝ :=
  scaledDensity (Real.sqrt 3) (Spline.diagonalSplineDensity n)

def standardizedDiagonalFiniteEntropyDensity (n : ℕ) (hn : 2 ≤ n) :
    FiniteEntropyDensity (standardizedProjectionLaw (diagonal n)) :=
  (Spline.diagonalFiniteEntropyDensity n hn).scale (Real.sqrt 3) (by positivity)

@[simp] theorem standardizedDiagonalFiniteEntropyDensity_density (n : ℕ) (hn : 2 ≤ n) :
    (standardizedDiagonalFiniteEntropyDensity n hn).density = standardizedDiagonalDensity n := rfl

theorem continuous_standardizedDiagonalDensity (n : ℕ) :
    Continuous (standardizedDiagonalDensity n) := by
  unfold standardizedDiagonalDensity scaledDensity
  exact continuous_const.mul ((Spline.continuous_diagonalSplineDensity n).comp (by fun_prop))

theorem standardizedDiagonalDensity_fourier_inversion {n : ℕ} (hn : 2 < n) (x : ℝ) :
    Pang.probabilityFourierInverse (charFun (standardizedProjectionLaw (diagonal n))) x =
      (standardizedDiagonalDensity n x : ℂ) :=
  Pang.probabilityFourierInverse_eq_density (standardizedProjectionLaw (diagonal n))
    (continuous_standardizedDiagonalDensity n)
    (standardizedDiagonalFiniteEntropyDensity n (by omega)).integrable
    (standardizedDiagonalFiniteEntropyDensity n (by omega)).nonneg
    (standardizedDiagonalFiniteEntropyDensity n (by omega)).law_eq
    (integrable_charFun_standardizedDiagonal hn) x

end
end ENT.Quantitative
