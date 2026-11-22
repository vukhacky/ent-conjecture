module

public import ENT.Pang.SineBounds

/-! Global sine and cosine envelopes for the genuine independent sum. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ENT.Pang

noncomputable section

def pangEnvelope (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u ^ 2 / (n : ℝ)) ^ (-((n : ℝ) - 1) / 2)

def sumCos (n : ℕ) (t u : ℝ) : ℝ :=
  ∫ x, Real.cos (u * x) ∂standardizedSumLaw n t

def sumSin (n : ℕ) (t u : ℝ) : ℝ :=
  ∫ x, Real.sin (u * x) ∂standardizedSumLaw n t

def normalizedSumSin (n : ℕ) (t u : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) / |tiltStandardMoment t 3| * sumSin n t u

theorem sumCos_eq_re {t : ℝ} (ht : 0 < t) (n : ℕ) (u : ℝ) :
    sumCos n t u = (charFun (standardizedSumLaw n t) u).re := by
  letI := isProbabilityMeasure_standardizedSumLaw ht n
  exact (charFun_re_real _ _).symm

theorem sumSin_eq_im {t : ℝ} (ht : 0 < t) (n : ℕ) (u : ℝ) :
    sumSin n t u = (charFun (standardizedSumLaw n t) u).im := by
  letI := isProbabilityMeasure_standardizedSumLaw ht n
  exact (charFun_im_real _ _).symm

theorem pangEnvelope_pos {n : ℕ} (hn : 0 < n) (u : ℝ) : 0 < pangEnvelope n u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.rpow_pos_of_pos (by positivity) _

theorem abs_im_pow_succ_le (z : ℂ) (n : ℕ) :
    |(z ^ (n + 1)).im| ≤ (n + 1 : ℝ) * |z.im| * ‖z‖ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      |(z ^ (n + 1 + 1)).im| =
          |(z ^ (n + 1)).re * z.im + (z ^ (n + 1)).im * z.re| := by
        rw [pow_succ, Complex.mul_im]
      _ ≤ |(z ^ (n + 1)).re| * |z.im| + |(z ^ (n + 1)).im| * |z.re| := by
        simpa only [abs_mul] using abs_add_le
          ((z ^ (n + 1)).re * z.im) ((z ^ (n + 1)).im * z.re)
      _ ≤ ‖z‖ ^ (n + 1) * |z.im| +
          ((n + 1 : ℝ) * |z.im| * ‖z‖ ^ n) * ‖z‖ := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          simpa only [norm_pow] using Complex.abs_re_le_norm (z ^ (n + 1))
        · exact mul_le_mul ih (Complex.abs_re_le_norm z) (abs_nonneg _) (by positivity)
      _ = ((n + 1 : ℕ) + 1 : ℝ) * |z.im| * ‖z‖ ^ (n + 1) := by
        push_cast
        rw [pow_succ]
        ring

theorem abs_im_pow_le (z : ℂ) (n : ℕ) :
    |(z ^ n).im| ≤ (n : ℝ) * |z.im| * ‖z‖ ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
      abs_im_pow_succ_le z n

theorem norm_charFun_standardizedLaw_pow_le {t : ℝ} (ht : 0 < t)
    (u : ℝ) (k : ℕ) :
    ‖charFun (standardizedLaw t) u‖ ^ k ≤ (1 + u ^ 2) ^ (-(k : ℝ) / 2) := by
  have hb : 0 < 1 + u ^ 2 := by positivity
  have hr : 0 ≤ (1 + u ^ 2) ^ (-(k : ℝ) / 2) := (Real.rpow_pos_of_pos hb _).le
  have heq : ((1 + u ^ 2) ^ (-(k : ℝ) / 2)) ^ 2 = (1 / (1 + u ^ 2)) ^ k := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    have he : -(k : ℝ) / 2 * 2 = -(k : ℝ) := by ring
    rw [he, Real.rpow_neg hb.le, Real.rpow_natCast]
    simp only [one_div, inv_pow]
  have h := pow_le_pow_left₀ (sq_nonneg ‖charFun (standardizedLaw t) u‖)
    (norm_charFun_standardizedLaw_sq_le ht u) k
  have hsq : (‖charFun (standardizedLaw t) u‖ ^ k) ^ 2 ≤
      ((1 + u ^ 2) ^ (-(k : ℝ) / 2)) ^ 2 := by
    rw [heq]
    convert h using 1 <;> ring
  nlinarith [pow_nonneg (norm_nonneg (charFun (standardizedLaw t) u)) k]

theorem abs_sumCos_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    |sumCos n t u| ≤ pangEnvelope n u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sumCos_eq_re ht]
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_charFun_standardizedSumLaw_le ht hn u).trans
  apply Real.rpow_le_rpow_of_exponent_le
  · have h : 0 ≤ u ^ 2 / (n : ℝ) := by positivity
    linarith
  · linarith

theorem abs_sumSin_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    |sumSin n t u| ≤ |tiltStandardMoment t 3| / Real.sqrt (n : ℝ) *
      |u| ^ 3 / 6 * pangEnvelope n u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hsq := Real.sq_sqrt hnR.le
  have hscale : ((Real.sqrt (n : ℝ))⁻¹ * u) ^ 2 = u ^ 2 / (n : ℝ) := by
    rw [mul_pow, inv_pow, hsq]
    ring
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have hmod := norm_charFun_standardizedLaw_pow_le ht
    ((Real.sqrt (n : ℝ))⁻¹ * u) (n - 1)
  rw [hscale, hcast] at hmod
  have hsin := abs_standardSin_le ht ((Real.sqrt (n : ℝ))⁻¹ * u)
  rw [← charFun_standardizedLaw_im ht] at hsin
  have hcoeff : (n : ℝ) * (|tiltStandardMoment t 3| *
      |(Real.sqrt (n : ℝ))⁻¹ * u| ^ 3 / 6) =
      |tiltStandardMoment t 3| / Real.sqrt (n : ℝ) * |u| ^ 3 / 6 := by
    rw [abs_mul, abs_inv, abs_of_pos hs]
    field_simp [hs.ne']
    nlinarith [congrArg (fun z : ℝ => z * |tiltStandardMoment t 3| * |u| ^ 3) hsq]
  rw [sumSin_eq_im ht, charFun_standardizedSumLaw ht]
  apply (abs_im_pow_le _ n).trans
  calc
    (n : ℝ) * |(charFun (standardizedLaw t) ((Real.sqrt (n : ℝ))⁻¹ * u)).im| *
        ‖charFun (standardizedLaw t) ((Real.sqrt (n : ℝ))⁻¹ * u)‖ ^ (n - 1) ≤
      (n : ℝ) * (|tiltStandardMoment t 3| * |(Real.sqrt (n : ℝ))⁻¹ * u| ^ 3 / 6) *
        pangEnvelope n u := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsin hnR.le) hmod
        (by positivity) (by positivity)
    _ = _ := by rw [hcoeff]

/-- Equation (45) of Pang, with the standard normalization retained. -/
theorem abs_normalizedSumSin_le {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) (u : ℝ) :
    |normalizedSumSin n t u| ≤ |u| ^ 3 / 6 * pangEnvelope n u := by
  have hk : tiltStandardMoment t 3 ≠ 0 := (pang_tilt_moment_bounds ht).2.1.2.ne
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hc : 0 ≤ Real.sqrt (n : ℝ) / |tiltStandardMoment t 3| := by positivity
  have h := mul_le_mul_of_nonneg_left (abs_sumSin_le ht hn u) hc
  unfold normalizedSumSin
  rw [abs_mul, abs_of_nonneg hc]
  convert h using 1
  field_simp [hs.ne', abs_ne_zero.mpr hk]

end
end ENT.Pang
