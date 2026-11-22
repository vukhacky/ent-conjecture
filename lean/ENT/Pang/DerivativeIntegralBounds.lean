module

public import ENT.Pang.FourierAverage

/-! The three Fourier-integral estimates underlying Pang Proposition 4.7. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def cosineLowerModel (n : ℕ) (u : ℝ) : ℝ :=
  gaussianWeight u - (1 / (7 * (n : ℝ))) * (u ^ 4 * gaussianWeight u) -
    (1 / (12 * (n : ℝ))) * (u ^ 6 * pangEnvelope n u) -
    (pangTail n).indicator (fun v => gaussianWeight v + pangEnvelope n v) u

theorem cosineLowerModel_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    cosineLowerModel n u ≤ sumCos n t u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := (gaussianWeight_pos u).le
  have hr := (pangEnvelope_pos hn u).le
  unfold cosineLowerModel
  by_cases hu : u ∈ pangTail n
  · rw [indicator_of_mem hu]
    have h := (abs_le.mp (abs_sumCos_le ht hn u)).1
    have h4 : 0 ≤ (1 / (7 * (n : ℝ))) * (u ^ 4 * gaussianWeight u) := by positivity
    have h6 : 0 ≤ (1 / (12 * (n : ℝ))) * (u ^ 6 * pangEnvelope n u) := by positivity
    linarith
  · rw [indicator_of_notMem hu]
    have hv : |u| ≤ Real.sqrt (n : ℝ) / 2 := le_of_not_gt hu
    have h := sumCos_local_lower ht hn (local_frequency_condition hn hv)
    unfold gaussianWeight
    convert h using 1 <;> ring

theorem integrable_cosineLowerModel {n : ℕ} (hn : 8 < n) :
    Integrable (cosineLowerModel n) := by
  have hg : Integrable gaussianWeight := by
    simpa using integrable_pow_mul_gaussianWeight 0
  have hg4 := (integrable_pow_mul_gaussianWeight 4).const_mul (1 / (7 * (n : ℝ)))
  have hr6 := (integrable_pow_mul_pangEnvelope (k := 6) hn).const_mul (1 / (12 * (n : ℝ)))
  have hc : Integrable (fun u : ℝ => gaussianWeight u + pangEnvelope n u) := by
    simpa using integrable_pow_mul_combinedWeight (n := n) (k := 0) (by omega)
  exact ((hg.sub hg4).sub hr6).sub (hc.indicator (measurableSet_pangTail n))

theorem fourierAverage_cosineLowerModel {n : ℕ} (hn : 8 < n) :
    fourierAverage (cosineLowerModel n) =
      1 - 3 / (7 * (n : ℝ)) - envelopeMoment n 3 / (12 * (n : ℝ)) -
        normalizedTailMoment n 0 := by
  have hg : Integrable gaussianWeight := by
    simpa using integrable_pow_mul_gaussianWeight 0
  have hg4 := (integrable_pow_mul_gaussianWeight 4).const_mul (1 / (7 * (n : ℝ)))
  have hr6 := (integrable_pow_mul_pangEnvelope (k := 6) hn).const_mul (1 / (12 * (n : ℝ)))
  have hc : Integrable (fun u : ℝ => gaussianWeight u + pangEnvelope n u) := by
    simpa using integrable_pow_mul_combinedWeight (n := n) (k := 0) (by omega)
  have ht := hc.indicator (measurableSet_pangTail n)
  have htail : fourierAverage ((pangTail n).indicator
      (fun u => gaussianWeight u + pangEnvelope n u)) = normalizedTailMoment n 0 := by
    simpa only [mul_zero, pow_zero, one_mul] using fourierAverage_tail n 0
  have ha := fourierAverage_sub ((hg.sub hg4).sub hr6) ht
  have hb := fourierAverage_sub (hg.sub hg4) hr6
  have hd := fourierAverage_sub hg hg4
  simp only [Pi.sub_def] at ha hb hd
  unfold cosineLowerModel
  rw [ha, hb, hd,
    fourierAverage_const_mul, fourierAverage_const_mul, fourierAverage_gaussian,
    htail]
  change 1 - (1 / (7 * (n : ℝ))) * gaussianMoment 2 -
    (1 / (12 * (n : ℝ))) * envelopeMoment n 3 - normalizedTailMoment n 0 = _
  rw [gaussianMoment_two]
  ring

theorem fourierAverage_sumCos_gt {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n) :
    (19 : ℝ) / 20 < fourierAverage (sumCos n t) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi : Integrable (sumCos n t) := by
    simpa using integrable_pow_mul_sumCos ht (k := 0) (by omega : 0 + 2 < n)
  have h := fourierAverage_mono (integrable_cosineLowerModel (by omega)) hi
    (cosineLowerModel_le ht (by omega))
  rw [fourierAverage_cosineLowerModel (by omega)] at h
  have h6 := div_lt_div_of_pos_right (envelopeMoment_order6_lt hn)
    (show 0 < 12 * (n : ℝ) by positivity)
  have htail := normalizedTailMoment_zero_lt hn
  have hbound : (3 : ℝ) / (7 * (n : ℝ)) + 24 / (12 * (n : ℝ)) + 1 / (n : ℝ) < 1 / 20 := by
    have he : (3 : ℝ) / (7 * (n : ℝ)) + 24 / (12 * (n : ℝ)) + 1 / (n : ℝ) =
        (24 : ℝ) / (7 * (n : ℝ)) := by ring
    rw [he]
    apply (div_lt_iff₀ (show 0 < 7 * (n : ℝ) by positivity)).mpr
    linarith
  linarith

theorem fourierAverage_secondCos_lt {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n) :
    fourierAverage (fun u => u ^ 2 * sumCos n t u) < 21 / 20 := by
  have h := fourierAverage_mono (integrable_pow_mul_sumCos ht (k := 2) (by omega))
    (integrable_pow_mul_pangEnvelope (n := n) (k := 2) (by omega))
    (fun u => mul_le_mul_of_nonneg_left
      ((abs_le.mp (abs_sumCos_le ht (by omega : 0 < n) u)).2) (sq_nonneg u))
  exact h.trans_lt (envelopeMoment_order2_lt hn)

def firstSineLowerModel (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 6 : ℝ) * (u ^ 4 * gaussianWeight u) -
    (11 / (60 * (n : ℝ))) * (u ^ 6 * gaussianWeight u) -
    (1 / (42 * (n : ℝ))) * (u ^ 8 * gaussianWeight u) -
    (1 / (216 * (n : ℝ))) * (u ^ 10 * pangEnvelope n u) -
    (1 / 6 : ℝ) * (pangTail n).indicator
      (fun v => v ^ 4 * (gaussianWeight v + pangEnvelope n v)) u

theorem firstSineLowerModel_le {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) (u : ℝ) :
    firstSineLowerModel n u ≤ u * normalizedSumSin n t u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := (gaussianWeight_pos u).le
  have hr := (pangEnvelope_pos hn u).le
  unfold firstSineLowerModel
  by_cases hu : u ∈ pangTail n
  · rw [indicator_of_mem hu]
    have h := (abs_le.mp (abs_mul_normalizedSumSin_le ht hn u)).1
    have h6 : 0 ≤ (11 / (60 * (n : ℝ))) * (u ^ 6 * gaussianWeight u) := by positivity
    have h8 : 0 ≤ (1 / (42 * (n : ℝ))) * (u ^ 8 * gaussianWeight u) := by positivity
    have h10 : 0 ≤ (1 / (216 * (n : ℝ))) * (u ^ 10 * pangEnvelope n u) := by positivity
    nlinarith
  · rw [indicator_of_notMem hu, mul_zero, sub_zero]
    exact mul_normalizedSumSin_local_lower ht hn
      (local_frequency_condition hn (le_of_not_gt hu))

theorem integrable_firstSineLowerModel {n : ℕ} (hn : 12 < n) :
    Integrable (firstSineLowerModel n) := by
  exact ((((integrable_pow_mul_gaussianWeight 4).const_mul _).sub
    ((integrable_pow_mul_gaussianWeight 6).const_mul _)).sub
    ((integrable_pow_mul_gaussianWeight 8).const_mul _)).sub
    ((integrable_pow_mul_pangEnvelope (k := 10) hn).const_mul _) |>.sub
    (((integrable_pow_mul_combinedWeight (k := 4) (by omega)).indicator
      (measurableSet_pangTail n)).const_mul _)

theorem fourierAverage_firstSineLowerModel {n : ℕ} (hn : 12 < n) :
    fourierAverage (firstSineLowerModel n) =
      1 / 2 - 11 / (4 * (n : ℝ)) - 5 / (2 * (n : ℝ)) -
        envelopeMoment n 5 / (216 * (n : ℝ)) - normalizedTailMoment n 2 / 6 := by
  have h4 := (integrable_pow_mul_gaussianWeight 4).const_mul (1 / 6 : ℝ)
  have h6 := (integrable_pow_mul_gaussianWeight 6).const_mul (11 / (60 * (n : ℝ)))
  have h8 := (integrable_pow_mul_gaussianWeight 8).const_mul (1 / (42 * (n : ℝ)))
  have h10 := (integrable_pow_mul_pangEnvelope (k := 10) hn).const_mul (1 / (216 * (n : ℝ)))
  have ht := ((integrable_pow_mul_combinedWeight (n := n) (k := 4) (by omega)).indicator
      (measurableSet_pangTail n)).const_mul (1 / 6 : ℝ)
  have ha := fourierAverage_sub (((h4.sub h6).sub h8).sub h10) ht
  have hb := fourierAverage_sub ((h4.sub h6).sub h8) h10
  have hc := fourierAverage_sub (h4.sub h6) h8
  have hd := fourierAverage_sub h4 h6
  simp only [Pi.sub_def] at ha hb hc hd
  unfold firstSineLowerModel
  rw [ha, hb, hc, hd]
  simp only [fourierAverage_const_mul]
  rw [show (fun u : ℝ => u ^ 4 * (gaussianWeight u + pangEnvelope n u)) =
    (fun u => u ^ (2 * 2) * (gaussianWeight u + pangEnvelope n u)) by rfl,
    fourierAverage_tail]
  change (1 / 6 : ℝ) * gaussianMoment 2 - (11 / (60 * (n : ℝ))) * gaussianMoment 3 -
    (1 / (42 * (n : ℝ))) * gaussianMoment 4 -
    (1 / (216 * (n : ℝ))) * envelopeMoment n 5 - (1 / 6 : ℝ) * normalizedTailMoment n 2 = _
  rw [gaussianMoment_two, gaussianMoment_three, gaussianMoment_four]
  ring

theorem fourierAverage_firstSine_pos {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n) :
    0 < fourierAverage (fun u => u * normalizedSumSin n t u) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi : Integrable (fun u => u * normalizedSumSin n t u) := by
    simpa using integrable_pow_mul_normalizedSumSin ht (k := 1) (by omega : 1 + 2 < n)
  have h := fourierAverage_mono (integrable_firstSineLowerModel (by omega)) hi
    (firstSineLowerModel_le ht (by omega))
  rw [fourierAverage_firstSineLowerModel (by omega)] at h
  have h10 := div_lt_div_of_pos_right (envelopeMoment_order10_lt hn)
    (show 0 < 216 * (n : ℝ) by positivity)
  have htail := div_lt_div_of_pos_right (normalizedTailMoment_order4_lt hn)
    (by norm_num : (0 : ℝ) < 6)
  have hbound : (11 : ℝ) / (4 * (n : ℝ)) + 5 / (2 * (n : ℝ)) +
      1500 / (216 * (n : ℝ)) + (3 / (n : ℝ)) / 6 < 1 / 2 := by
    have he : (11 : ℝ) / (4 * (n : ℝ)) + 5 / (2 * (n : ℝ)) +
      1500 / (216 * (n : ℝ)) + (3 / (n : ℝ)) / 6 = 457 / (36 * (n : ℝ)) := by ring
    rw [he]
    apply (div_lt_iff₀ (show 0 < 36 * (n : ℝ) by positivity)).mpr
    linarith
  linarith

theorem fourierAverage_firstSine_lt {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 150 ≤ n) :
    fourierAverage (fun u => u * normalizedSumSin n t u) < 1 := by
  have hi : Integrable (fun u => u * normalizedSumSin n t u) := by
    simpa using integrable_pow_mul_normalizedSumSin ht (k := 1) (by omega : 1 + 2 < n)
  have hg := (integrable_pow_mul_pangEnvelope (n := n) (k := 4) (by omega)).const_mul (1 / 6 : ℝ)
  have h := fourierAverage_mono hi hg (fun u =>
    (abs_le.mp (abs_mul_normalizedSumSin_le ht (by omega : 0 < n) u)).2)
  rw [fourierAverage_const_mul] at h
  change fourierAverage (fun u => u * normalizedSumSin n t u) ≤ (1 / 6 : ℝ) * envelopeMoment n 2 at h
  linarith [envelopeMoment_order4_lt hn]

end
end ENT.Pang
