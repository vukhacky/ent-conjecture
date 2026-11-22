module

public import ENT.Pang.TailBounds
public import ENT.Pang.FourierAtZero
public import ENT.Pang.LocalBounds

/-! Normalized Fourier integrals and parity identities used by the quantitative bounds. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def fourierAverage (f : ℝ → ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ u, f u

theorem fourierScale_pos : 0 < 1 / Real.sqrt (2 * Real.pi) := by positivity

theorem fourierAverage_mono {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (h : ∀ u, f u ≤ g u) : fourierAverage f ≤ fourierAverage g :=
  mul_le_mul_of_nonneg_left (integral_mono hf hg h) fourierScale_pos.le

theorem fourierAverage_nonneg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) :
    0 ≤ fourierAverage f :=
  mul_nonneg fourierScale_pos.le (integral_nonneg hf)

theorem fourierAverage_add {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    fourierAverage (fun u => f u + g u) = fourierAverage f + fourierAverage g := by
  simp only [fourierAverage, integral_add hf hg]
  ring

theorem fourierAverage_sub {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    fourierAverage (fun u => f u - g u) = fourierAverage f - fourierAverage g := by
  simp only [fourierAverage, integral_sub hf hg]
  ring

theorem fourierAverage_const_mul (c : ℝ) (f : ℝ → ℝ) :
    fourierAverage (fun u => c * f u) = c * fourierAverage f := by
  simp only [fourierAverage, integral_const_mul]
  ring

theorem fourierAverage_neg (f : ℝ → ℝ) :
    fourierAverage (fun u => -f u) = -fourierAverage f := by
  simp only [fourierAverage, integral_neg]
  ring

theorem fourierAverage_gaussian_moment (k : ℕ) :
    fourierAverage (fun u => u ^ (2 * k) * gaussianWeight u) = gaussianMoment k := rfl

theorem fourierAverage_envelope_moment (n k : ℕ) :
    fourierAverage (fun u => u ^ (2 * k) * pangEnvelope n u) = envelopeMoment n k := rfl

theorem fourierAverage_gaussian : fourierAverage gaussianWeight = 1 := by
  simpa only [gaussianMoment, mul_zero, pow_zero, one_mul, fourierAverage] using gaussianMoment_zero

theorem fourierAverage_tail (n k : ℕ) :
    fourierAverage ((pangTail n).indicator
      (fun u => u ^ (2 * k) * (gaussianWeight u + pangEnvelope n u))) =
        normalizedTailMoment n k := by
  rw [fourierAverage, integral_indicator (measurableSet_pangTail n)]
  rfl

theorem gaussianWeight_neg (u : ℝ) : gaussianWeight (-u) = gaussianWeight u := by
  simp only [gaussianWeight, neg_sq]

theorem pangEnvelope_neg (n : ℕ) (u : ℝ) : pangEnvelope n (-u) = pangEnvelope n u := by
  simp only [pangEnvelope, neg_sq]

theorem normalizedSumSin_neg (n : ℕ) (t u : ℝ) :
    normalizedSumSin n t (-u) = -normalizedSumSin n t u := by
  simp only [normalizedSumSin, sumSin_neg, mul_neg]

theorem integrable_pow_mul_normalizedSumSin {t : ℝ} (ht : 0 < t) {n k : ℕ}
    (hn : k + 2 < n) : Integrable (fun u : ℝ => u ^ k * normalizedSumSin n t u) := by
  have h := (integrable_pow_mul_sumSin ht hn).const_mul
    (Real.sqrt (n : ℝ) / |tiltStandardMoment t 3|)
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => by simp only [normalizedSumSin]; ring)

theorem abs_mul_normalizedSumSin_le {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) (u : ℝ) :
    |u * normalizedSumSin n t u| ≤ (1 / 6 : ℝ) * (u ^ 4 * pangEnvelope n u) := by
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_left (abs_normalizedSumSin_le ht hn u) (abs_nonneg u)
  have he : |u| * (|u| ^ 3 / 6 * pangEnvelope n u) =
      (1 / 6 : ℝ) * (u ^ 4 * pangEnvelope n u) := by
    have hp : |u| ^ 4 = u ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    calc
      _ = (1 / 6 : ℝ) * (|u| ^ 4 * pangEnvelope n u) := by ring
      _ = _ := by rw [hp]
  exact h.trans_eq he

theorem mul_normalizedSumSin_local_lower {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : u ^ 2 / (n : ℝ) ≤ 1 / 4) :
    (1 / 6 : ℝ) * (u ^ 4 * gaussianWeight u) -
      (11 / (60 * (n : ℝ))) * (u ^ 6 * gaussianWeight u) -
      (1 / (42 * (n : ℝ))) * (u ^ 8 * gaussianWeight u) -
      (1 / (216 * (n : ℝ))) * (u ^ 10 * pangEnvelope n u) ≤
        u * normalizedSumSin n t u := by
  have huv : |u| ^ 2 / (n : ℝ) ≤ 1 / 4 := by simpa only [sq_abs] using hu
  have h := mul_le_mul_of_nonneg_left
    (normalizedSumSin_local_lower ht hn (abs_nonneg u) huv) (abs_nonneg u)
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
        |u| ^ 9 / (216 * (n : ℝ)) * pangEnvelope n u) =
      (1 / 6 : ℝ) * (u ^ 4 * gaussianWeight u) -
      (11 / (60 * (n : ℝ))) * (u ^ 6 * gaussianWeight u) -
      (1 / (42 * (n : ℝ))) * (u ^ 8 * gaussianWeight u) -
      (1 / (216 * (n : ℝ))) * (u ^ 10 * pangEnvelope n u) := by
    calc
      _ = (1 / 6 : ℝ) * (|u| ^ 4 * gaussianWeight u) -
          (11 / (60 * (n : ℝ))) * (|u| ^ 6 * gaussianWeight u) -
          (1 / (42 * (n : ℝ))) * (|u| ^ 8 * gaussianWeight u) -
          (1 / (216 * (n : ℝ))) * (|u| ^ 10 * pangEnvelope n u) := by ring
      _ = _ := by rw [h4, h6, h8, h10]
  rwa [he] at h

end
end ENT.Pang
