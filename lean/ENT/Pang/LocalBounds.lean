module

public import ENT.Pang.LocalCharacteristic

/-! Pang Lemma 4.6: local lower bounds with the signed skewness factor retained. -/

@[expose] public section

set_option autoImplicit false

namespace ENT.Pang

noncomputable section

theorem abs_tiltStandardMoment_three_le_two {t : ℝ} (ht : 0 < t) :
    |tiltStandardMoment t 3| ≤ 2 := by
  have h := (pang_tilt_moment_bounds ht).2.1
  rw [abs_of_neg h.2]
  linarith [h.1]

theorem exp_sub_lower (a b : ℝ) : Real.exp a * (1 - b) ≤ Real.exp (a - b) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-b)) (Real.exp_pos a).le
  rw [← Real.exp_add] at h
  simpa only [sub_eq_add_neg, neg_add_eq_sub] using h

theorem exp_neg_mul_one_sub_lower {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) :
    1 - a - b ≤ Real.exp (-b) * (1 - a) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-b)) (sub_nonneg.mpr ha1)
  nlinarith [mul_nonneg ha0 hb]

theorem localAngle_square_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    localAngle n t u ^ 2 ≤ u ^ 6 / (6 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha := pow_le_pow_left₀ (localAngle_nonneg ht hn hu0 hu)
    (localAngle_upper ht hn hu0 hu) 2
  have he : (4 * |tiltStandardMoment t 3| * u ^ 3 /
      (21 * Real.sqrt (n : ℝ))) ^ 2 =
      16 * |tiltStandardMoment t 3| ^ 2 * u ^ 6 / (441 * (n : ℝ)) := by
    rw [div_pow]
    simp only [mul_pow]
    rw [Real.sq_sqrt hnR.le]
    ring
  rw [he] at ha
  have hm0 : 0 ≤ |tiltStandardMoment t 3| := abs_nonneg _
  have hm2 := abs_tiltStandardMoment_three_le_two ht
  have hc : 16 * |tiltStandardMoment t 3| ^ 2 / 441 ≤ 1 / 6 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ u ^ 6 / (n : ℝ) by positivity)
  simp only [div_eq_mul_inv, mul_inv_rev] at ha hp ⊢
  nlinarith

theorem localAngle_cube_div_six_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    localAngle n t u ^ 3 / 6 ≤ |tiltStandardMoment t 3| * u ^ 9 /
      (216 * (n : ℝ) * Real.sqrt (n : ℝ)) := by
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
  have hm2 := abs_tiltStandardMoment_three_le_two ht
  have hm_sq : |tiltStandardMoment t 3| ^ 2 ≤ 4 := by nlinarith
  have hm_cube := mul_le_mul_of_nonneg_right hm_sq hm0
  have hc : 64 * |tiltStandardMoment t 3| ^ 3 / (9261 * 6) ≤
      |tiltStandardMoment t 3| / 216 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ u ^ 9 / ((n : ℝ) * Real.sqrt (n : ℝ)) by positivity)
  simp only [div_eq_mul_inv, mul_inv_rev] at ha hp ⊢
  nlinarith

theorem sumCos_local_lower_of_nonneg {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    Real.exp (-u ^ 2 / 2) * (1 - u ^ 4 / (7 * (n : ℝ))) -
      u ^ 6 / (12 * (n : ℝ)) * pangEnvelope n u ≤ sumCos n t u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 := localRadius_nonneg n t u
  have hr := localRadius_le_envelope ht hn u
  have ha := localAngle_square_le ht hn hu0 hu
  have he := mul_le_mul hr ha (sq_nonneg _) (pangEnvelope_pos hn u).le
  have hc := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := localAngle n t u)) hr0
  have hl := (exp_sub_lower (-u ^ 2 / 2) (u ^ 4 / (7 * (n : ℝ)))).trans
    (localRadius_lower ht hn hu)
  rw [sumCos_eq_polar ht]
  simp only [div_eq_mul_inv, mul_inv_rev] at he hc hl ⊢
  nlinarith

theorem sumCos_neg_local (n : ℕ) (t u : ℝ) : sumCos n t (-u) = sumCos n t u := by
  unfold sumCos
  simp only [neg_mul, Real.cos_neg]

theorem sumCos_local_lower {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    Real.exp (-u ^ 2 / 2) * (1 - u ^ 4 / (7 * (n : ℝ))) -
      u ^ 6 / (12 * (n : ℝ)) * pangEnvelope n u ≤ sumCos n t u := by
  by_cases hu0 : 0 ≤ u
  · exact sumCos_local_lower_of_nonneg ht hn hu0 hu
  · have hu' : (-u) ^ 2 / (n : ℝ) ≤ 1 / 4 := by simpa only [neg_sq] using hu
    have h := sumCos_local_lower_of_nonneg ht hn (by linarith : 0 ≤ -u) hu'
    simpa only [pangEnvelope, neg_sq, show (-u) ^ 4 = u ^ 4 by ring,
      show (-u) ^ 6 = u ^ 6 by ring, sumCos_neg_local] using h

theorem sumSin_local_lower {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    |tiltStandardMoment t 3| / Real.sqrt (n : ℝ) *
      (u ^ 3 / 6 * Real.exp (-u ^ 2 / 2) *
        (1 - 11 * u ^ 2 / (10 * (n : ℝ)) - u ^ 4 / (7 * (n : ℝ))) -
        u ^ 9 / (216 * (n : ℝ)) * pangEnvelope n u) ≤ sumSin n t u := by
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
    (localAngle_cube_div_six_le ht hn hu0 hu) (by positivity)
    (pangEnvelope_pos hn u).le
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hθ0) hr0
  rw [sumSin_eq_polar ht]
  simp only [div_eq_mul_inv, mul_inv_rev] at hprod hrem' herr hsin ⊢
  nlinarith

theorem normalizedSumSin_local_lower {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    u ^ 3 / 6 * Real.exp (-u ^ 2 / 2) *
      (1 - 11 * u ^ 2 / (10 * (n : ℝ)) - u ^ 4 / (7 * (n : ℝ))) -
      u ^ 9 / (216 * (n : ℝ)) * pangEnvelope n u ≤ normalizedSumSin n t u := by
  have hk : tiltStandardMoment t 3 ≠ 0 := (pang_tilt_moment_bounds ht).2.1.2.ne
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := mul_le_mul_of_nonneg_left (sumSin_local_lower ht hn hu0 hu)
    (show 0 ≤ Real.sqrt (n : ℝ) / |tiltStandardMoment t 3| by positivity)
  unfold normalizedSumSin
  convert h using 1
  field_simp [hs.ne', abs_ne_zero.mpr hk]

theorem local_frequency_condition {n : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : |u| ≤ Real.sqrt (n : ℝ) / 2) : u ^ 2 / (n : ℝ) ≤ 1 / 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
  rw [sq_abs, div_pow, Real.sq_sqrt hnR.le] at h
  apply (div_le_iff₀ hnR).mpr
  nlinarith

/-- The cosine part of Pang Lemma 4.6, in the paper's interval form. -/
theorem pang_local_cosine_bound {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n)
    {u : ℝ} (hu : |u| ≤ Real.sqrt (n : ℝ) / 2) :
    Real.exp (-u ^ 2 / 2) * (1 - u ^ 4 / (7 * (n : ℝ))) -
      u ^ 6 / (12 * (n : ℝ)) * pangEnvelope n u ≤ sumCos n t u :=
  sumCos_local_lower ht (by omega) (local_frequency_condition (by omega) hu)

/-- The sine part of Pang Lemma 4.6, in the paper's interval form. -/
theorem pang_local_sine_bound {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ Real.sqrt (n : ℝ) / 2) :
    u ^ 3 / 6 * Real.exp (-u ^ 2 / 2) *
      (1 - 11 * u ^ 2 / (10 * (n : ℝ)) - u ^ 4 / (7 * (n : ℝ))) -
      u ^ 9 / (216 * (n : ℝ)) * pangEnvelope n u ≤ normalizedSumSin n t u :=
  normalizedSumSin_local_lower ht (by omega) hu0
    (local_frequency_condition (by omega) (by rwa [abs_of_nonneg hu0]))

end
end ENT.Pang
