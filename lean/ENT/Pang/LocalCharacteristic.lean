module

public import ENT.Pang.SineSum
public import ENT.Pang.ComplexPolar
public import ENT.Pang.LogEnvelope

/-! Radius and angle estimates for the local characteristic function. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ENT.Pang

noncomputable section

def sumFrequency (n : ℕ) (u : ℝ) : ℝ := (Real.sqrt (n : ℝ))⁻¹ * u

def localRadius (n : ℕ) (t u : ℝ) : ℝ :=
  ‖charFun (standardizedLaw t) (sumFrequency n u)‖ ^ n

def localAngle (n : ℕ) (t u : ℝ) : ℝ :=
  (n : ℝ) * (charFun (standardizedLaw t) (sumFrequency n u)).arg

theorem sumFrequency_sq {n : ℕ} (hn : 0 < n) (u : ℝ) :
    sumFrequency n u ^ 2 = u ^ 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold sumFrequency
  rw [mul_pow, inv_pow, Real.sq_sqrt hnR.le]
  ring

theorem sumFrequency_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ sumFrequency n u := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hu

theorem scaled_frequency_cube {n : ℕ} (hn : 0 < n) (u : ℝ) :
    (n : ℝ) * sumFrequency n u ^ 3 = u ^ 3 / Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have hsq := Real.sq_sqrt hnR.le
  unfold sumFrequency
  field_simp [hs]
  nlinarith [congrArg (fun z : ℝ => z * u ^ 3) hsq]

theorem standardCos_lower {t : ℝ} (ht : 0 < t) (u : ℝ) :
    1 - u ^ 2 / 2 ≤ standardCos t u := by
  letI := isProbabilityMeasure_tiltLaw ht
  have hp : Integrable (fun x => u ^ 2 / 2 * standardize t x ^ 2) (tiltLaw t) :=
    (integrable_tilt_standard_power ht 2).const_mul _
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (tiltLaw t) := integrable_const _
  have hf : Integrable (fun x => 1 - u ^ 2 / 2 * standardize t x ^ 2) (tiltLaw t) :=
    hconst.sub hp
  have hc : Integrable (fun x => Real.cos (u * standardize t x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by unfold standardize; fun_prop)
  have hm := integral_mono hf hc (fun x => show
      1 - u ^ 2 / 2 * standardize t x ^ 2 ≤ Real.cos (u * standardize t x) by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := u * standardize t x)])
  rw [integral_sub hconst hp, integral_const_mul, integral_standardize_pow ht,
    tiltStandardMoment_two ht] at hm
  simpa [standardSin, standardCos, standardize] using hm

theorem standardCos_local_lower {t : ℝ} (ht : 0 < t) {v : ℝ} (hv : v ^ 2 ≤ 1 / 4) :
    (7 : ℝ) / 8 ≤ standardCos t v := by
  linarith [standardCos_lower ht v]

theorem standardSin_local_nonneg {t : ℝ} (ht : 0 < t) {v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ^ 2 ≤ 1 / 4) : 0 ≤ standardSin t v := by
  have h := standardSin_lower ht hv0
  have hf : 0 ≤ 1 - 11 * v ^ 2 / 10 := by linarith
  exact (mul_nonneg (by positivity) hf).trans h

theorem sumCos_eq_polar {t : ℝ} (ht : 0 < t) (n : ℕ) (u : ℝ) :
    sumCos n t u = localRadius n t u * Real.cos (localAngle n t u) := by
  rw [sumCos_eq_re ht, charFun_standardizedSumLaw ht]
  exact (complex_pow_polar _ n).1

theorem sumSin_eq_polar {t : ℝ} (ht : 0 < t) (n : ℕ) (u : ℝ) :
    sumSin n t u = localRadius n t u * Real.sin (localAngle n t u) := by
  rw [sumSin_eq_im ht, charFun_standardizedSumLaw ht]
  exact (complex_pow_polar _ n).2

theorem localRadius_nonneg (n : ℕ) (t u : ℝ) : 0 ≤ localRadius n t u :=
  pow_nonneg (norm_nonneg _) _

theorem localRadius_le_envelope {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    localRadius n t u ≤ pangEnvelope n u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := norm_charFun_standardizedLaw_pow_le ht (sumFrequency n u) n
  rw [sumFrequency_sq hn] at h
  apply h.trans
  apply Real.rpow_le_rpow_of_exponent_le
  · have hq : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
    linarith
  · linarith

theorem localRadius_lower {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    Real.exp (-u ^ 2 / 2 - u ^ 4 / (7 * (n : ℝ))) ≤ localRadius n t u := by
  have hb : 0 ≤ 1 - u ^ 2 / (2 * (n : ℝ)) := by
    have he : u ^ 2 / (2 * (n : ℝ)) = (u ^ 2 / (n : ℝ)) / 2 := by ring
    rw [he]
    linarith
  have hc := standardCos_lower ht (sumFrequency n u)
  rw [sumFrequency_sq hn, ← charFun_standardizedLaw_re ht] at hc
  have he : 1 - u ^ 2 / (n : ℝ) / 2 = 1 - u ^ 2 / (2 * (n : ℝ)) := by ring
  rw [he] at hc
  exact (gaussian_lower_power hn hu).trans
    (pow_le_pow_left₀ hb (hc.trans (Complex.re_le_norm _)) n)

theorem localAngle_nonneg {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) : 0 ≤ localAngle n t u := by
  have hv : sumFrequency n u ^ 2 ≤ 1 / 4 := by rwa [sumFrequency_sq hn]
  have hs := standardSin_local_nonneg ht (sumFrequency_nonneg hu0) hv
  rw [← charFun_standardizedLaw_im ht] at hs
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.arg_nonneg_iff.mpr hs)

theorem localAngle_upper {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    localAngle n t u ≤ 4 * |tiltStandardMoment t 3| * u ^ 3 /
      (21 * Real.sqrt (n : ℝ)) := by
  have hv0 := sumFrequency_nonneg (n := n) hu0
  have hv : sumFrequency n u ^ 2 ≤ 1 / 4 := by rwa [sumFrequency_sq hn]
  have hc := standardCos_local_lower ht hv
  have hs := standardSin_local_nonneg ht hv0 hv
  have hb := (le_abs_self (standardSin t (sumFrequency n u))).trans
    (abs_standardSin_le ht (sumFrequency n u))
  rw [abs_of_nonneg hv0] at hb
  rw [← charFun_standardizedLaw_re ht] at hc
  rw [← charFun_standardizedLaw_im ht] at hs hb
  have ha := complex_arg_le_im_div_re (by linarith :
      0 < (charFun (standardizedLaw t) (sumFrequency n u)).re) hs
  have hd := div_le_div₀ (show 0 ≤ |tiltStandardMoment t 3| * sumFrequency n u ^ 3 / 6 by
      positivity) hb (by norm_num : (0 : ℝ) < 7 / 8) hc
  have hm := mul_le_mul_of_nonneg_left (ha.trans hd) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : (n : ℝ) * ((|tiltStandardMoment t 3| * sumFrequency n u ^ 3 / 6) / (7 / 8)) =
      4 * |tiltStandardMoment t 3| * u ^ 3 / (21 * Real.sqrt (n : ℝ)) := by
    calc
      _ = 4 * |tiltStandardMoment t 3| / 21 * ((n : ℝ) * sumFrequency n u ^ 3) := by ring
      _ = _ := by rw [scaled_frequency_cube hn]; ring
  rw [he] at hm
  exact hm

theorem localAngle_lower {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    |tiltStandardMoment t 3| * u ^ 3 / (6 * Real.sqrt (n : ℝ)) *
      (1 - 11 * u ^ 2 / (10 * (n : ℝ))) ≤ localAngle n t u := by
  letI := isProbabilityMeasure_standardizedLaw ht
  have hv0 := sumFrequency_nonneg (n := n) hu0
  have hv : sumFrequency n u ^ 2 ≤ 1 / 4 := by rwa [sumFrequency_sq hn]
  have hs := standardSin_local_nonneg ht hv0 hv
  rw [← charFun_standardizedLaw_im ht] at hs
  have ha := complex_im_le_arg hs (norm_charFun_le_one (sumFrequency n u))
  have hl := standardSin_lower ht hv0
  rw [← charFun_standardizedLaw_im ht] at hl
  have hm := mul_le_mul_of_nonneg_left (hl.trans ha) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : (n : ℝ) * (|tiltStandardMoment t 3| * sumFrequency n u ^ 3 / 6 *
      (1 - 11 * sumFrequency n u ^ 2 / 10)) =
      |tiltStandardMoment t 3| * u ^ 3 / (6 * Real.sqrt (n : ℝ)) *
        (1 - 11 * u ^ 2 / (10 * (n : ℝ))) := by
    calc
      _ = |tiltStandardMoment t 3| / 6 * ((n : ℝ) * sumFrequency n u ^ 3) *
          (1 - 11 * sumFrequency n u ^ 2 / 10) := by ring
      _ = _ := by rw [scaled_frequency_cube hn, sumFrequency_sq hn]; ring
  rw [he] at hm
  exact hm

end
end ENT.Pang
