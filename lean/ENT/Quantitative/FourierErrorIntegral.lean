module

public import ENT.Quantitative.FourierSmallInterval
public import ENT.Quantitative.FourierCaps

/-! The signed error integral of Pang Lemma B.2(iii), with constant 80. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Quantitative
open ENT.Pang

noncomputable section

def gaussianErrorWeight (u : ℝ) : ℝ :=
  (1 / 42 : ℝ) * (u ^ 10 * gaussianWeight u) +
  (23 / 210 : ℝ) * (u ^ 8 * gaussianWeight u) -
  (341 / 600 : ℝ) * (u ^ 6 * gaussianWeight u)

def envelopeErrorWeight (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 216 : ℝ) * (u ^ 12 * pangEnvelope n u) -
  (31 / 2160 : ℝ) * (u ^ 10 * pangEnvelope n u)

def pangErrorWeight (n : ℕ) (u : ℝ) : ℝ :=
  (u ^ 2 - 31 / 10) * (((11 / 60 : ℝ) * u ^ 6 + (1 / 42 : ℝ) * u ^ 8) *
    gaussianWeight u + (1 / 216 : ℝ) * u ^ 10 * pangEnvelope n u)

theorem pangErrorWeight_split (n : ℕ) (u : ℝ) :
    pangErrorWeight n u = gaussianErrorWeight u + envelopeErrorWeight n u := by
  unfold pangErrorWeight gaussianErrorWeight envelopeErrorWeight
  ring

theorem pangErrorWeight_eq_neg_quantSmallErrorWeight (n : ℕ) (u : ℝ) :
    pangErrorWeight n u = -quantSmallErrorWeight n u := by
  unfold pangErrorWeight quantSmallErrorWeight
  ring

theorem integrable_gaussianErrorWeight : Integrable gaussianErrorWeight :=
  (((integrable_pow_mul_gaussianWeight 10).const_mul _).add
    ((integrable_pow_mul_gaussianWeight 8).const_mul _)).sub
    ((integrable_pow_mul_gaussianWeight 6).const_mul _)

theorem integrable_envelopeErrorWeight {n : ℕ} (hn : 14 < n) :
    Integrable (envelopeErrorWeight n) :=
  ((integrable_pow_mul_pangEnvelope (k := 12) hn).const_mul _).sub
    ((integrable_pow_mul_pangEnvelope (k := 10) (by omega)).const_mul _)

theorem integrable_pangErrorWeight {n : ℕ} (hn : 14 < n) :
    Integrable (pangErrorWeight n) := by
  have h := integrable_gaussianErrorWeight.add (integrable_envelopeErrorWeight hn)
  apply h.congr
  exact Filter.Eventually.of_forall (fun u => (pangErrorWeight_split n u).symm)

theorem fourierAverage_gaussianErrorWeight :
    fourierAverage gaussianErrorWeight = 1019 / 40 := by
  have h10 := (integrable_pow_mul_gaussianWeight 10).const_mul (1 / 42 : ℝ)
  have h8 := (integrable_pow_mul_gaussianWeight 8).const_mul (23 / 210 : ℝ)
  have h6 := (integrable_pow_mul_gaussianWeight 6).const_mul (341 / 600 : ℝ)
  have ha := fourierAverage_sub (h10.add h8) h6
  have hb := fourierAverage_add h10 h8
  simp only [Pi.add_def, Pi.sub_def] at ha hb
  unfold gaussianErrorWeight
  rw [ha, hb]
  simp only [fourierAverage_const_mul]
  change (1 / 42 : ℝ) * gaussianMoment 5 + (23 / 210 : ℝ) * gaussianMoment 4 -
    (341 / 600 : ℝ) * gaussianMoment 3 = _
  rw [gaussianMoment_five, gaussianMoment_four, gaussianMoment_three]
  norm_num

theorem fourierAverage_envelopeErrorWeight {n : ℕ} (hn : 14 < n) :
    fourierAverage (envelopeErrorWeight n) =
      (envelopeMoment n 6 - (31 / 10 : ℝ) * envelopeMoment n 5) / 216 := by
  have h12 := (integrable_pow_mul_pangEnvelope (k := 12) hn).const_mul (1 / 216 : ℝ)
  have h10 := (integrable_pow_mul_pangEnvelope (n := n) (k := 10) (by omega)).const_mul (31 / 2160 : ℝ)
  unfold envelopeErrorWeight
  rw [fourierAverage_sub h12 h10]
  simp only [fourierAverage_const_mul]
  change (1 / 216 : ℝ) * envelopeMoment n 6 - (31 / 2160 : ℝ) * envelopeMoment n 5 = _
  ring

theorem envelope_error_moment_le {n : ℕ} (hn : 256 ≤ n) :
    (envelopeMoment n 6 - (31 / 10 : ℝ) * envelopeMoment n 5) / 216 ≤ 44047/1000 := by
  have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : (n : ℝ) - 14 ≠ 0 := by linarith
  have hrec : envelopeMoment n 6 =
      11 * (n : ℝ) / ((n : ℝ) - 14) * envelopeMoment n 5 := by
    have hrec0 := envelopeMoment_succ (n := n) (k := 5) (by omega)
    norm_num at hrec0
    convert hrec0 using 1 <;> ring
  have hrel : ((n : ℝ) - 14) * envelopeMoment n 6 =
      11 * (n : ℝ) * envelopeMoment n 5 := by
    rw [hrec]
    field_simp [hd]
  have he : (envelopeMoment n 6 - (31 / 10 : ℝ) * envelopeMoment n 5) / 216 =
      ((79 * (n : ℝ) + 434) / (23760 * (n : ℝ))) * envelopeMoment n 6 := by
    field_simp [hn0.ne']
    nlinarith [hrel]
  rw [he]
  have hcoeff : (79 * (n : ℝ) + 434) / (23760 * (n : ℝ)) ≤
      (79*256+434 : ℝ)/(23760*256) := by
    apply (div_le_iff₀ (show 0 < 23760*(n:ℝ) by positivity)).mpr
    nlinarith
  have hm : envelopeMoment n 6 ≤ 12969 := by
    apply (envelopeMoment_le_at256 hn 6 (by norm_num)).trans
    norm_num [momentMajorant]
  calc
    _ ≤ (79*256+434 : ℝ)/(23760*256) * envelopeMoment n 6 :=
      mul_le_mul_of_nonneg_right hcoeff (envelopeMoment_nonneg (by omega) 6)
    _ ≤ (79*256+434 : ℝ)/(23760*256) * 12969 :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ 44047/1000 := by norm_num

def positiveErrorWeight (n : ℕ) : ℝ → ℝ := quantSmallᶜ.indicator (pangErrorWeight n)

theorem positiveErrorWeight_eq (n : ℕ) (u : ℝ) :
    positiveErrorWeight n u = pangErrorWeight n u +
      quantSmall.indicator (quantSmallErrorWeight n) u := by
  unfold positiveErrorWeight
  by_cases hu : u ∈ quantSmall
  · rw [indicator_of_notMem (show u ∉ quantSmallᶜ from fun h => h hu), indicator_of_mem hu,
      pangErrorWeight_eq_neg_quantSmallErrorWeight]
    ring
  · rw [indicator_of_mem (show u ∈ quantSmallᶜ from hu), indicator_of_notMem hu, add_zero]

theorem positiveErrorWeight_nonneg {n : ℕ} (hn : 0 < n) (u : ℝ) :
    0 ≤ positiveErrorWeight n u := by
  unfold positiveErrorWeight
  by_cases hu : u ∈ quantSmall
  · rw [indicator_of_notMem (show u ∉ quantSmallᶜ from fun h => h hu)]
  · rw [indicator_of_mem (show u ∈ quantSmallᶜ from hu)]
    unfold pangErrorWeight
    have hg := (gaussianWeight_pos u).le
    have hr := (pangEnvelope_pos hn u).le
    exact mul_nonneg (sub_nonneg.mpr (sq_gt_of_not_mem_quantSmall hu).le) (by positivity)

theorem integrable_positiveErrorWeight {n : ℕ} (hn : 14 < n) :
    Integrable (positiveErrorWeight n) :=
  (integrable_pangErrorWeight hn).indicator measurableSet_quantSmall.compl

/-- The normalized whole-line version of Pang Lemma B.2(iii), equivalent by evenness. -/
theorem quant_error_integral_lt {n : ℕ} (hn : 256 ≤ n) :
    fourierAverage (positiveErrorWeight n) < 70623/1000 := by
  have hi := integrable_pangErrorWeight (by omega : 14 < n)
  have hsmall : Integrable (quantSmall.indicator (quantSmallErrorWeight n)) := by
    have h := (hi.neg).indicator measurableSet_quantSmall
    apply h.congr
    exact Filter.Eventually.of_forall (fun u => by
      by_cases hu : u ∈ quantSmall
      · simp only [indicator_of_mem hu, Pi.neg_apply, pangErrorWeight_eq_neg_quantSmallErrorWeight, neg_neg]
      · simp only [indicator_of_notMem hu])
  have he : positiveErrorWeight n = (fun u => pangErrorWeight n u +
      quantSmall.indicator (quantSmallErrorWeight n) u) := funext (positiveErrorWeight_eq n)
  have hsplit : pangErrorWeight n =
      (fun u => gaussianErrorWeight u + envelopeErrorWeight n u) :=
    funext (pangErrorWeight_split n)
  rw [he, fourierAverage_add hi hsmall, hsplit,
    fourierAverage_add integrable_gaussianErrorWeight (integrable_envelopeErrorWeight (by omega)),
    fourierAverage_gaussianErrorWeight, fourierAverage_envelopeErrorWeight (by omega)]
  linarith [envelope_error_moment_le hn, small_error_integral_bound (by omega : 150 ≤ n)]

end
end ENT.Quantitative
