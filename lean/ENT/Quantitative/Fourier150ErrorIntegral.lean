module

public import ENT.Quantitative.Fourier150SmallInterval
public import ENT.Quantitative.FourierHigherCaps
public import ENT.Quantitative.FourierSkew

/-! Signed-integral errors with squared skewness retained at threshold 150. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace ENT.Quantitative.Threshold150
open ENT.Pang
noncomputable section

def gaussianErrorWeight (u : ℝ) : ℝ :=
  (1/42:ℝ)*(u^10*gaussianWeight u)+(3/28:ℝ)*(u^8*gaussianWeight u)-
    (44/75:ℝ)*(u^6*gaussianWeight u)

def envelopeErrorWeight (n : ℕ) (t u : ℝ) : ℝ :=
  (skewSquared t/864)*(u^12*pangEnvelope n u-(16/5:ℝ)*(u^10*pangEnvelope n u))

def pangErrorWeight (n : ℕ) (t u : ℝ) : ℝ :=
  (u^2-16/5)*(((11/60:ℝ)*u^6+(1/42:ℝ)*u^8)*gaussianWeight u+
    (skewSquared t/864)*u^10*pangEnvelope n u)

def smallSkewErrorWeight (n : ℕ) (t u : ℝ) : ℝ :=
  (16/5-u^2)*(((11/60:ℝ)*u^6+(1/42:ℝ)*u^8)*gaussianWeight u+
    (skewSquared t/864)*u^10*pangEnvelope n u)

theorem pangErrorWeight_split (n : ℕ) (t u : ℝ) :
    pangErrorWeight n t u=gaussianErrorWeight u+envelopeErrorWeight n t u := by
  unfold pangErrorWeight gaussianErrorWeight envelopeErrorWeight
  ring

theorem pangErrorWeight_eq_neg_small (n : ℕ) (t u : ℝ) :
    pangErrorWeight n t u = -smallSkewErrorWeight n t u := by
  unfold pangErrorWeight smallSkewErrorWeight
  ring

theorem smallSkewErrorWeight_le {n : ℕ} (hn : 0<n) {t : ℝ} (ht : 0<t)
    {u : ℝ} (hu : u∈quantSmall) :
    smallSkewErrorWeight n t u≤quantSmallErrorWeight n u := by
  unfold smallSkewErrorWeight quantSmallErrorWeight
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (sq_le_of_mem_quantSmall hu))
  have hq : skewSquared t/864≤1/216 := by linarith [skewSquared_le_four ht]
  have hr := (pangEnvelope_pos hn u).le
  have h := mul_le_mul_of_nonneg_right hq
    (show 0≤u^10*pangEnvelope n u by positivity)
  nlinarith

theorem integrable_gaussianErrorWeight : Integrable gaussianErrorWeight :=
  (((integrable_pow_mul_gaussianWeight 10).const_mul _).add
    ((integrable_pow_mul_gaussianWeight 8).const_mul _)).sub
    ((integrable_pow_mul_gaussianWeight 6).const_mul _)

theorem integrable_envelopeErrorWeight {n : ℕ} (hn : 14<n) (t : ℝ) :
    Integrable (envelopeErrorWeight n t) :=
  ((integrable_pow_mul_pangEnvelope (k:=12) hn).sub
    ((integrable_pow_mul_pangEnvelope (k:=10) (by omega)).const_mul _)).const_mul _

theorem integrable_pangErrorWeight {n : ℕ} (hn : 14<n) (t : ℝ) :
    Integrable (pangErrorWeight n t) := by
  apply (integrable_gaussianErrorWeight.add (integrable_envelopeErrorWeight hn t)).congr
  exact Filter.Eventually.of_forall fun u=>(pangErrorWeight_split n t u).symm

theorem fourierAverage_gaussianErrorWeight : fourierAverage gaussianErrorWeight=499/20 := by
  have h10 := (integrable_pow_mul_gaussianWeight 10).const_mul (1/42:ℝ)
  have h8 := (integrable_pow_mul_gaussianWeight 8).const_mul (3/28:ℝ)
  have h6 := (integrable_pow_mul_gaussianWeight 6).const_mul (44/75:ℝ)
  have ha := fourierAverage_sub (h10.add h8) h6
  have hb := fourierAverage_add h10 h8
  simp only [Pi.add_def] at ha hb
  unfold gaussianErrorWeight
  rw [ha,hb]
  simp only [fourierAverage_const_mul]
  change (1/42:ℝ)*gaussianMoment 5+(3/28:ℝ)*gaussianMoment 4-(44/75:ℝ)*gaussianMoment 3=_
  rw [gaussianMoment_five,gaussianMoment_four,gaussianMoment_three]
  norm_num

theorem fourierAverage_envelopeErrorWeight {n : ℕ} (hn : 14<n) (t : ℝ) :
    fourierAverage (envelopeErrorWeight n t)=
      (skewSquared t/864)*(envelopeMoment n 6-(16/5:ℝ)*envelopeMoment n 5) := by
  unfold envelopeErrorWeight
  rw [fourierAverage_const_mul,
    fourierAverage_sub (integrable_pow_mul_pangEnvelope (k:=12) hn)
      ((integrable_pow_mul_pangEnvelope (k:=10) (by omega)).const_mul _),
    fourierAverage_const_mul]
  rfl

theorem envelope_error_moment_le {n : ℕ} (hn : 150≤n) :
    envelopeMoment n 6-(16/5:ℝ)*envelopeMoment n 5≤11232 := by
  have hnR : (150:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hd : (n:ℝ)-14≠0 := by linarith
  have hrec : envelopeMoment n 6=11*(n:ℝ)/((n:ℝ)-14)*envelopeMoment n 5 := by
    have h := envelopeMoment_succ (n:=n) (k:=5) (by omega)
    norm_num at h
    convert h using 1 <;> ring
  have hrel : ((n:ℝ)-14)*envelopeMoment n 6=11*(n:ℝ)*envelopeMoment n 5 := by
    rw [hrec]
    field_simp [hd]
  have he : envelopeMoment n 6-(16/5:ℝ)*envelopeMoment n 5 =
      ((39*(n:ℝ)+224)/(55*(n:ℝ)))*envelopeMoment n 6 := by
    field_simp [hn0.ne']
    nlinarith [hrel]
  rw [he]
  have hcoeff : (39*(n:ℝ)+224)/(55*(n:ℝ))≤(39*150+224:ℝ)/(55*150) := by
    apply (div_le_iff₀ (show 0<55*(n:ℝ) by positivity)).mpr
    nlinarith
  have hm : envelopeMoment n 6≤15249 := by
    apply (envelopeMoment_le_at150 hn 6 (by norm_num)).trans
    norm_num [momentMajorant]
  calc
    _≤(39*150+224:ℝ)/(55*150)*envelopeMoment n 6 :=
      mul_le_mul_of_nonneg_right hcoeff (envelopeMoment_nonneg (by omega) 6)
    _≤(39*150+224:ℝ)/(55*150)*15249 :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _≤11232 := by norm_num

def positiveErrorWeight (n : ℕ) (t : ℝ) : ℝ→ℝ := quantSmallᶜ.indicator (pangErrorWeight n t)

theorem positiveErrorWeight_eq (n : ℕ) (t u : ℝ) :
    positiveErrorWeight n t u=pangErrorWeight n t u+quantSmall.indicator (smallSkewErrorWeight n t) u := by
  unfold positiveErrorWeight
  by_cases hu : u∈quantSmall
  · rw [indicator_of_notMem (show u∉quantSmallᶜ from fun h=>h hu),indicator_of_mem hu,
      pangErrorWeight_eq_neg_small]
    ring
  · rw [indicator_of_mem (show u∈quantSmallᶜ from hu),indicator_of_notMem hu,add_zero]

theorem positiveErrorWeight_nonneg {n : ℕ} (hn : 0<n) (t u : ℝ) :
    0≤positiveErrorWeight n t u := by
  unfold positiveErrorWeight
  by_cases hu : u∈quantSmall
  · rw [indicator_of_notMem (show u∉quantSmallᶜ from fun h=>h hu)]
  · rw [indicator_of_mem (show u∈quantSmallᶜ from hu)]
    unfold pangErrorWeight
    have hg := (gaussianWeight_pos u).le
    have hr := (pangEnvelope_pos hn u).le
    have hq := skewSquared_nonneg t
    exact mul_nonneg (sub_nonneg.mpr (sq_gt_of_not_mem_quantSmall hu).le) (by positivity)

theorem integrable_positiveErrorWeight {n : ℕ} (hn : 14<n) (t : ℝ) :
    Integrable (positiveErrorWeight n t) :=
  (integrable_pangErrorWeight hn t).indicator measurableSet_quantSmall.compl

theorem small_skew_error_integral_bound {n : ℕ} (hn : 150≤n) {t : ℝ} (ht : 0<t) :
    fourierAverage (quantSmall.indicator (smallSkewErrorWeight n t))<5/4 := by
  have hc : Continuous (smallSkewErrorWeight n t) := by
    unfold smallSkewErrorWeight gaussianWeight
    have hr := continuous_pangEnvelope (by omega : 0<n)
    fun_prop
  have hj : Continuous (quantSmallErrorWeight n) := by
    unfold quantSmallErrorWeight gaussianWeight
    have hr := continuous_pangEnvelope (by omega : 0<n)
    fun_prop
  apply (fourierAverage_mono (integrable_indicator_quantSmall_of_continuous hc)
    (integrable_indicator_quantSmall_of_continuous hj) ?_).trans_lt (small_error_integral_bound hn)
  intro u
  by_cases hu : u∈quantSmall
  · rw [indicator_of_mem hu,indicator_of_mem hu]
    exact smallSkewErrorWeight_le (by omega) ht hu
  · rw [indicator_of_notMem hu,indicator_of_notMem hu]

theorem quant_error_integral_lt {n : ℕ} (hn : 150≤n) {t : ℝ} (ht : 0<t) :
    fourierAverage (positiveErrorWeight n t)<131/5+13*skewSquared t := by
  have hi := integrable_pangErrorWeight (by omega : 14<n) t
  have hsmall : Integrable (quantSmall.indicator (smallSkewErrorWeight n t)) := by
    apply ((hi.neg).indicator measurableSet_quantSmall).congr
    exact Filter.Eventually.of_forall (fun u=>by
      by_cases hu : u∈quantSmall
      · simp only [indicator_of_mem hu,Pi.neg_apply,pangErrorWeight_eq_neg_small,neg_neg]
      · simp only [indicator_of_notMem hu])
  have he : positiveErrorWeight n t=(fun u=>pangErrorWeight n t u+
      quantSmall.indicator (smallSkewErrorWeight n t) u) := funext (positiveErrorWeight_eq n t)
  have hs : pangErrorWeight n t=(fun u=>gaussianErrorWeight u+envelopeErrorWeight n t u) :=
    funext (pangErrorWeight_split n t)
  rw [he,fourierAverage_add hi hsmall,hs,
    fourierAverage_add integrable_gaussianErrorWeight (integrable_envelopeErrorWeight (by omega) t),
    fourierAverage_gaussianErrorWeight,fourierAverage_envelopeErrorWeight (by omega)]
  have henv := mul_le_mul_of_nonneg_left (envelope_error_moment_le hn)
    (div_nonneg (skewSquared_nonneg t) (by norm_num : (0:ℝ)≤864))
  have hc := small_skew_error_integral_bound hn ht
  linarith

end
end ENT.Quantitative.Threshold150
