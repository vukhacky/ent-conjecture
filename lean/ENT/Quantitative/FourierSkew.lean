module

public import ENT.Pang.FourierAverage

/-! Retain the squared skewness in the local sine remainder. -/

@[expose] public section
set_option autoImplicit false
namespace ENT.Quantitative
open ENT.Pang
noncomputable section

def skewSquared (t : ℝ) : ℝ := |tiltStandardMoment t 3|^2

theorem skewSquared_nonneg (t : ℝ) : 0≤skewSquared t := sq_nonneg _

theorem skewSquared_le_four {t : ℝ} (ht : 0<t) : skewSquared t≤4 := by
  have h := abs_tiltStandardMoment_three_le_two ht
  unfold skewSquared
  nlinarith [abs_nonneg (tiltStandardMoment t 3)]

theorem localAngle_cube_div_six_le_skew {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    localAngle n t u ^ 3 / 6 ≤ |tiltStandardMoment t 3| * skewSquared t * u ^ 9 /
      (864 * (n : ℝ) * Real.sqrt (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs3 : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [pow_succ, Real.sq_sqrt hnR.le]
  have ha := pow_le_pow_left₀ (localAngle_nonneg ht hn hu0 hu)
    (localAngle_upper ht hn hu0 hu) 3
  have he : (4 * |tiltStandardMoment t 3| * u ^ 3 /
      (21 * Real.sqrt (n : ℝ))) ^ 3 =
      64 * |tiltStandardMoment t 3| ^ 3 * u ^ 9 /
        (9261 * (n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [div_pow]
    simp only [mul_pow]
    rw [hs3]
    ring
  rw [he] at ha
  have hm0 : 0 ≤ |tiltStandardMoment t 3| := abs_nonneg _
  have hc : 64 * |tiltStandardMoment t 3| ^ 3 / (9261 * 6) ≤
      |tiltStandardMoment t 3| * skewSquared t / 864 := by
    unfold skewSquared
    nlinarith [pow_nonneg hm0 3]
  have hp := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ u ^ 9 / ((n : ℝ) * Real.sqrt (n : ℝ)) by positivity)
  simp only [div_eq_mul_inv, mul_inv_rev] at ha hp ⊢
  nlinarith

theorem sumSin_local_lower_skew {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    |tiltStandardMoment t 3| / Real.sqrt (n : ℝ) *
      (u ^ 3 / 6 * Real.exp (-u ^ 2 / 2) *
        (1 - 11 * u ^ 2 / (10 * (n : ℝ)) - u ^ 4 / (7 * (n : ℝ))) -
        skewSquared t * u ^ 9 / (864 * (n : ℝ)) * pangEnvelope n u) ≤ sumSin n t u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 := localRadius_nonneg n t u
  have hθ0 := localAngle_nonneg ht hn hu0 hu
  have hr := localRadius_lower ht hn hu
  have hθ := localAngle_lower ht hn hu0 hu
  have ha0 : 0 ≤ 11 * u ^ 2 / (10 * (n : ℝ)) := by positivity
  have ha1 : 11 * u ^ 2 / (10 * (n : ℝ)) ≤ 1 := by
    have he : 11 * u ^ 2 / (10 * (n : ℝ)) = 11 / 10 * (u ^ 2 / (n : ℝ)) := by ring
    rw [he]
    linarith
  have hL0 : 0 ≤ |tiltStandardMoment t 3| * u ^ 3 / (6 * Real.sqrt (n : ℝ)) *
      (1 - 11 * u ^ 2 / (10 * (n : ℝ))) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr ha1)
  have hprod := mul_le_mul hr hθ hL0 hr0
  have hrem := exp_neg_mul_one_sub_lower ha0 ha1
    (show 0 ≤ u ^ 4 / (7 * (n : ℝ)) by positivity)
  have hrem' := mul_le_mul_of_nonneg_left hrem
    (show 0 ≤ |tiltStandardMoment t 3| * u ^ 3 / (6 * Real.sqrt (n : ℝ)) *
      Real.exp (-u ^ 2 / 2) by positivity)
  have hexp : Real.exp (-u ^ 2 / 2 - u ^ 4 / (7 * (n : ℝ))) =
      Real.exp (-u ^ 2 / 2) * Real.exp (-(u ^ 4 / (7 * (n : ℝ)))) := by
    rw [sub_eq_add_neg, Real.exp_add]
  rw [hexp] at hprod
  have herr := mul_le_mul (localRadius_le_envelope ht hn u)
    (localAngle_cube_div_six_le_skew ht hn hu0 hu) (by positivity)
    (pangEnvelope_pos hn u).le
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hθ0) hr0
  rw [sumSin_eq_polar ht]
  simp only [div_eq_mul_inv, mul_inv_rev] at hprod hrem' herr hsin ⊢
  nlinarith

theorem normalizedSumSin_local_lower_skew {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    u ^ 3 / 6 * Real.exp (-u ^ 2 / 2) *
      (1 - 11 * u ^ 2 / (10 * (n : ℝ)) - u ^ 4 / (7 * (n : ℝ))) -
      skewSquared t * u ^ 9 / (864 * (n : ℝ)) * pangEnvelope n u ≤ normalizedSumSin n t u := by
  have hk : tiltStandardMoment t 3 ≠ 0 := (pang_tilt_moment_bounds ht).2.1.2.ne
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := mul_le_mul_of_nonneg_left (sumSin_local_lower_skew ht hn hu0 hu)
    (show 0 ≤ Real.sqrt (n : ℝ) / |tiltStandardMoment t 3| by positivity)
  unfold normalizedSumSin
  convert h using 1
  field_simp [hs.ne', abs_ne_zero.mpr hk]

theorem mul_normalizedSumSin_local_lower_skew {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    (1 / 6 : ℝ) * (u ^ 4 * gaussianWeight u) -
      (11 / (60 * (n : ℝ))) * (u ^ 6 * gaussianWeight u) -
      (1 / (42 * (n : ℝ))) * (u ^ 8 * gaussianWeight u) -
      (skewSquared t / (864 * (n : ℝ))) * (u ^ 10 * pangEnvelope n u) ≤
        u * normalizedSumSin n t u := by
  have huv : |u| ^ 2 / (n : ℝ) ≤ 1 / 4 := by simpa only [sq_abs] using hu
  have h := mul_le_mul_of_nonneg_left
    (normalizedSumSin_local_lower_skew ht hn (abs_nonneg u) huv) (abs_nonneg u)
  have hsin : |u| * normalizedSumSin n t |u| = u * normalizedSumSin n t u := by
    by_cases hu0 : 0 ≤ u
    · rw [abs_of_nonneg hu0]
    · rw [abs_of_neg (lt_of_not_ge hu0), normalizedSumSin_neg]
      ring
  rw [hsin] at h
  have hg : Real.exp (-|u| ^ 2 / 2) = gaussianWeight u := by
    simp only [gaussianWeight, sq_abs]
  have hr : pangEnvelope n |u| = pangEnvelope n u := by
    simp only [pangEnvelope, sq_abs]
  rw [hg, hr] at h
  have h4 : |u| ^ 4 = u ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h6 : |u| ^ 6 = u ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h8 : |u| ^ 8 = u ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h10 : |u| ^ 10 = u ^ 10 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have he : |u| * (|u| ^ 3 / 6 * gaussianWeight u *
      (1 - 11 * |u| ^ 2 / (10 * (n : ℝ)) - |u| ^ 4 / (7 * (n : ℝ))) -
        skewSquared t * |u| ^ 9 / (864 * (n : ℝ)) * pangEnvelope n u) =
      (1 / 6 : ℝ) * (u ^ 4 * gaussianWeight u) -
      (11 / (60 * (n : ℝ))) * (u ^ 6 * gaussianWeight u) -
      (1 / (42 * (n : ℝ))) * (u ^ 8 * gaussianWeight u) -
      (skewSquared t / (864 * (n : ℝ))) * (u ^ 10 * pangEnvelope n u) := by
    calc
      _ = (1 / 6 : ℝ) * (|u| ^ 4 * gaussianWeight u) -
          (11 / (60 * (n : ℝ))) * (|u| ^ 6 * gaussianWeight u) -
          (1 / (42 * (n : ℝ))) * (|u| ^ 8 * gaussianWeight u) -
          (skewSquared t / (864 * (n : ℝ))) * (|u| ^ 10 * pangEnvelope n u) := by ring
      _ = _ := by rw [h4, h6, h8, h10]
  rwa [he] at h

end
end ENT.Quantitative
