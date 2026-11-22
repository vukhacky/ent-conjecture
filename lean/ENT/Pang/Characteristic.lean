module

public import ENT.Pang.CharacteristicRaw

/-! Pang Lemma 4.2, with actual standardized cosine and sine expectations. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ENT.Pang

noncomputable section

def standardCos (t u : ℝ) : ℝ :=
  ∫ x, Real.cos (u * ((x - tiltMean t) / Real.sqrt (tiltVariance t))) ∂tiltLaw t

def standardSin (t u : ℝ) : ℝ :=
  ∫ x, Real.sin (u * ((x - tiltMean t) / Real.sqrt (tiltVariance t))) ∂tiltLaw t

theorem standardCos_eq {t : ℝ} (ht : 0 < t) (u : ℝ) :
    standardCos t u =
      tiltCos t (u / Real.sqrt (tiltVariance t)) *
          Real.cos ((u / Real.sqrt (tiltVariance t)) * tiltMean t) +
        tiltSin t (u / Real.sqrt (tiltVariance t)) *
          Real.sin ((u / Real.sqrt (tiltVariance t)) * tiltMean t) := by
  let s := u / Real.sqrt (tiltVariance t)
  have hc : Integrable (fun x : ℝ => Real.cos (s * x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by fun_prop)
  have hs : Integrable (fun x : ℝ => Real.sin (s * x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by fun_prop)
  have heq : (fun x : ℝ => Real.cos (u * ((x - tiltMean t) / Real.sqrt (tiltVariance t)))) =
      (fun x : ℝ => Real.cos (s * x) * Real.cos (s * tiltMean t) +
        Real.sin (s * x) * Real.sin (s * tiltMean t)) := by
    funext x
    rw [show u * ((x - tiltMean t) / Real.sqrt (tiltVariance t)) =
      s * x - s * tiltMean t by dsimp [s]; ring, Real.cos_sub]
  unfold standardCos
  rw [heq, integral_add (hc.mul_const _) (hs.mul_const _),
    integral_mul_const, integral_mul_const]
  rfl

theorem standardSin_eq {t : ℝ} (ht : 0 < t) (u : ℝ) :
    standardSin t u =
      tiltSin t (u / Real.sqrt (tiltVariance t)) *
          Real.cos ((u / Real.sqrt (tiltVariance t)) * tiltMean t) -
        tiltCos t (u / Real.sqrt (tiltVariance t)) *
          Real.sin ((u / Real.sqrt (tiltVariance t)) * tiltMean t) := by
  let s := u / Real.sqrt (tiltVariance t)
  have hc : Integrable (fun x : ℝ => Real.cos (s * x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by fun_prop)
  have hs : Integrable (fun x : ℝ => Real.sin (s * x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by fun_prop)
  have heq : (fun x : ℝ => Real.sin (u * ((x - tiltMean t) / Real.sqrt (tiltVariance t)))) =
      (fun x : ℝ => Real.sin (s * x) * Real.cos (s * tiltMean t) -
        Real.cos (s * x) * Real.sin (s * tiltMean t)) := by
    funext x
    rw [show u * ((x - tiltMean t) / Real.sqrt (tiltVariance t)) =
      s * x - s * tiltMean t by dsimp [s]; ring, Real.sin_sub]
  unfold standardSin
  rw [heq, integral_sub (hs.mul_const _) (hc.mul_const _),
    integral_mul_const, integral_mul_const]
  rfl

theorem standardTrig_sq_eq {t : ℝ} (ht : 0 < t) (u : ℝ) :
    standardCos t u ^ 2 + standardSin t u ^ 2 =
      tiltCos t (u / Real.sqrt (tiltVariance t)) ^ 2 +
        tiltSin t (u / Real.sqrt (tiltVariance t)) ^ 2 := by
  rw [standardCos_eq ht, standardSin_eq ht]
  ring_nf
  rw [Real.cos_sq']
  ring

theorem standardTrig_sq_pos {t : ℝ} (ht : 0 < t) (u : ℝ) :
    0 < standardCos t u ^ 2 + standardSin t u ^ 2 := by
  rw [standardTrig_sq_eq ht]
  exact tiltTrig_sq_pos ht _

/-- The complete single-summand envelope of Pang Lemma 4.2. -/
theorem standard_characteristic_envelope {t : ℝ} (ht : 0 < t) (u : ℝ) :
    standardCos t u ^ 2 + standardSin t u ^ 2 ≤ 1 / (1 + u ^ 2) := by
  have hv := tiltVariance_pos ht
  have hscale : (u / Real.sqrt (tiltVariance t)) ^ 2 * tiltVariance t = u ^ 2 := by
    rw [div_pow, Real.sq_sqrt hv.le]
    field_simp [hv.ne']
  rw [standardTrig_sq_eq ht]
  have h := tiltTrig_sq_le ht (u / Real.sqrt (tiltVariance t))
  rwa [hscale] at h

theorem standardCos_zero {t : ℝ} (ht : 0 < t) : standardCos t 0 = 1 := by
  letI := isProbabilityMeasure_tiltLaw ht
  simp [standardCos]

theorem standardSin_zero (t : ℝ) : standardSin t 0 = 0 := by
  simp [standardSin]

theorem standardCos_neg (t u : ℝ) : standardCos t (-u) = standardCos t u := by
  unfold standardCos
  apply integral_congr_ae
  filter_upwards [] with x
  rw [neg_mul, Real.cos_neg]

theorem standardSin_neg (t u : ℝ) : standardSin t (-u) = -standardSin t u := by
  unfold standardSin
  simp only [neg_mul, Real.sin_neg, integral_neg]

end
end ENT.Pang
