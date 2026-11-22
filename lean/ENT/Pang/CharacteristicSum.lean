module

public import ENT.Pang.Characteristic
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Independent-sum characteristic envelope

The sum law is the pushforward of the genuine finite product of standardized
tilted laws. Characteristic factorization uses mathlib's proved independence
theorem; it is not an additional assumption about the sum.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ENT.Pang

noncomputable section

def standardize (t x : ℝ) : ℝ := (x - tiltMean t) / Real.sqrt (tiltVariance t)

def standardizedLaw (t : ℝ) : Measure ℝ := (tiltLaw t).map (standardize t)

theorem continuous_standardize (t : ℝ) : Continuous (standardize t) := by
  unfold standardize
  fun_prop

theorem isProbabilityMeasure_standardizedLaw {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (standardizedLaw t) := by
  letI := isProbabilityMeasure_tiltLaw ht
  unfold standardizedLaw
  infer_instance

theorem integrable_cexp_mul_real (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (((u * x : ℝ) : ℂ) * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Filter.Eventually.of_forall (fun x => by
      rw [Complex.norm_exp_ofReal_mul_I])

theorem charFun_re_real (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ) :
    (charFun μ u).re = ∫ x, Real.cos (u * x) ∂μ := by
  rw [charFun_apply_real]
  simp only [← Complex.ofReal_mul]
  simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] using
    (integral_re (integrable_cexp_mul_real μ u)).symm

theorem charFun_im_real (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ) :
    (charFun μ u).im = ∫ x, Real.sin (u * x) ∂μ := by
  rw [charFun_apply_real]
  simp only [← Complex.ofReal_mul]
  simpa only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I_im] using
    (integral_im (integrable_cexp_mul_real μ u)).symm

theorem charFun_standardizedLaw_re {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (charFun (standardizedLaw t) u).re = standardCos t u := by
  letI := isProbabilityMeasure_standardizedLaw ht
  rw [charFun_re_real]
  unfold standardizedLaw
  rw [integral_map (continuous_standardize t).measurable.aemeasurable (by fun_prop)]
  rfl

theorem charFun_standardizedLaw_im {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (charFun (standardizedLaw t) u).im = standardSin t u := by
  letI := isProbabilityMeasure_standardizedLaw ht
  rw [charFun_im_real]
  unfold standardizedLaw
  rw [integral_map (continuous_standardize t).measurable.aemeasurable (by fun_prop)]
  rfl

theorem norm_charFun_standardizedLaw_sq {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ‖charFun (standardizedLaw t) u‖ ^ 2 = standardCos t u ^ 2 + standardSin t u ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    charFun_standardizedLaw_re ht, charFun_standardizedLaw_im ht]
  ring

theorem norm_charFun_standardizedLaw_sq_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ‖charFun (standardizedLaw t) u‖ ^ 2 ≤ 1 / (1 + u ^ 2) := by
  rw [norm_charFun_standardizedLaw_sq ht]
  exact standard_characteristic_envelope ht u

def standardizedSumLaw (n : ℕ) (t : ℝ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin n => standardizedLaw t)).map
    (fun x : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, x i)

theorem isProbabilityMeasure_standardizedSumLaw {t : ℝ} (ht : 0 < t) (n : ℕ) :
    IsProbabilityMeasure (standardizedSumLaw n t) := by
  letI := isProbabilityMeasure_standardizedLaw ht
  unfold standardizedSumLaw
  infer_instance

theorem charFun_standardizedSumLaw {t : ℝ} (ht : 0 < t) (n : ℕ) (u : ℝ) :
    charFun (standardizedSumLaw n t) u =
      charFun (standardizedLaw t) ((Real.sqrt (n : ℝ))⁻¹ * u) ^ n := by
  letI := isProbabilityMeasure_standardizedLaw ht
  unfold standardizedSumLaw
  rw [charFun_map_mul_comp (by fun_prop),
    charFun_map_sum_pi_eq_prod (fun _ : Fin n => standardizedLaw t)]
  simp only [Finset.prod_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Squared envelope, using only integer powers and exact arithmetic. -/
theorem norm_charFun_standardizedSumLaw_sq_le {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) (u : ℝ) :
    ‖charFun (standardizedSumLaw n t) u‖ ^ 2 ≤ (1 / (1 + u ^ 2 / (n : ℝ))) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : ((Real.sqrt (n : ℝ))⁻¹ * u) ^ 2 = u ^ 2 / (n : ℝ) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hnR.le]
    ring
  have h := norm_charFun_standardizedLaw_sq_le ht ((Real.sqrt (n : ℝ))⁻¹ * u)
  rw [hscale] at h
  have hp := pow_le_pow_left₀ (sq_nonneg ‖charFun (standardizedLaw t)
    ((Real.sqrt (n : ℝ))⁻¹ * u)‖) h n
  rw [charFun_standardizedSumLaw ht, norm_pow]
  convert hp using 1 <;> ring

/-- Pang's full independent-sum envelope `rₙ(u)`. -/
theorem norm_charFun_standardizedSumLaw_le {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) (u : ℝ) :
    ‖charFun (standardizedSumLaw n t) u‖ ≤
      (1 + u ^ 2 / (n : ℝ)) ^ (-(n : ℝ) / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 1 + u ^ 2 / (n : ℝ) := by positivity
  have hr : 0 ≤ (1 + u ^ 2 / (n : ℝ)) ^ (-(n : ℝ) / 2) :=
    (Real.rpow_pos_of_pos hb _).le
  have heq : ((1 + u ^ 2 / (n : ℝ)) ^ (-(n : ℝ) / 2)) ^ 2 =
      (1 / (1 + u ^ 2 / (n : ℝ))) ^ n := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    have he : -(n : ℝ) / 2 * 2 = -(n : ℝ) := by ring
    rw [he, Real.rpow_neg hb.le, Real.rpow_natCast]
    simp only [one_div, inv_pow]
  have h := norm_charFun_standardizedSumLaw_sq_le ht hn u
  rw [← heq] at h
  nlinarith [norm_nonneg (charFun (standardizedSumLaw n t) u)]

end
end ENT.Pang
