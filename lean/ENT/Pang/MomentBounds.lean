module

public import ENT.Pang.TiltLaw
public import ENT.Pang.VarianceBounds
public import ENT.Pang.SkewBound
public import ENT.Pang.FifthGap
public import ENT.Pang.FifthSign

/-! Pang’s variance, skewness and fifth-to-third moment ratio bounds for the standardized tilted uniform law. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace ENT.Pang

noncomputable section

theorem integrable_tiltLaw_of_continuous {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f (tiltLaw t) := by
  unfold tiltLaw
  rw [integrable_withDensity_iff (measurable_tiltDensity t).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (tiltDensity_nonneg ht _)]
  have heq : (fun x => f x * tiltDensity t x) =
      (Icc (-1 : ℝ) 1).indicator (fun x => f x * tiltWeight t x) := by
    funext x
    unfold tiltDensity
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  rw [heq]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply ContinuousOn.integrableOn_Icc
  apply Continuous.continuousOn
  apply hf.mul
  unfold tiltWeight
  fun_prop

/-- The standardized central moment; its probability integral is proved below. -/
def tiltStandardMoment (t : ℝ) (k : ℕ) : ℝ :=
  tiltCentralMoment t k / Real.sqrt (tiltVariance t) ^ k

theorem integrable_tilt_standard_power {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun x : ℝ => ((x - tiltMean t) / Real.sqrt (tiltVariance t)) ^ k)
      (tiltLaw t) := by
  apply integrable_tiltLaw_of_continuous ht
  fun_prop

theorem tiltStandardMoment_eq_integral {t : ℝ} (ht : 0 < t) (k : ℕ) :
    tiltStandardMoment t k =
      ∫ x, ((x - tiltMean t) / Real.sqrt (tiltVariance t)) ^ k ∂tiltLaw t := by
  rw [integral_tiltLaw ht]
  simp_rw [div_pow]
  have heq : (fun x : ℝ => (x - tiltMean t) ^ k / Real.sqrt (tiltVariance t) ^ k *
      tiltWeight t x) =
      (fun x : ℝ => ((x - tiltMean t) ^ k * tiltWeight t x) /
        Real.sqrt (tiltVariance t) ^ k) := by
    funext x
    ring
  rw [heq, intervalIntegral.integral_div]
  rfl

theorem tiltCentralMoment_zero {t : ℝ} (ht : 0 < t) : tiltCentralMoment t 0 = 1 := by
  simpa only [tiltCentralMoment, pow_zero, one_mul] using integral_tiltWeight ht

theorem tiltCentralMoment_one {t : ℝ} (ht : 0 < t) : tiltCentralMoment t 1 = 0 := by
  have h := tiltCentralMoment_eq_sum t 1
  simpa [Finset.sum_range_succ, Nat.choose, tiltMoment_zero ht, tiltMoment_one ht] using h

theorem tiltStandardMoment_zero {t : ℝ} (ht : 0 < t) : tiltStandardMoment t 0 = 1 := by
  simp only [tiltStandardMoment, tiltCentralMoment_zero ht, pow_zero, div_one]

theorem tiltStandardMoment_one {t : ℝ} (ht : 0 < t) : tiltStandardMoment t 1 = 0 := by
  simp only [tiltStandardMoment, tiltCentralMoment_one ht, zero_div]

theorem tiltStandardMoment_two {t : ℝ} (ht : 0 < t) : tiltStandardMoment t 2 = 1 := by
  rw [tiltStandardMoment, tiltCentralMoment_two ht, Real.sq_sqrt (tiltVariance_pos ht).le,
    div_self (tiltVariance_pos ht).ne']

theorem tiltStandardMoment_three {t : ℝ} (ht : 0 < t) :
    tiltStandardMoment t 3 = tiltSkewness t := by
  rw [tiltStandardMoment, tiltCentralMoment_three ht]
  rfl

theorem tiltStandardMoment_fifth_ratio_eq {t : ℝ} (ht : 0 < t) :
    tiltStandardMoment t 5 / tiltStandardMoment t 3 =
      tiltCentralMoment t 5 / (tiltVariance t * tiltThirdCumulant t) := by
  have hv : 0 < tiltVariance t := tiltVariance_pos ht
  have hs : Real.sqrt (tiltVariance t) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  have hk : tiltThirdCumulant t ≠ 0 := (tiltThirdCumulant_neg ht).ne
  have hs5 : Real.sqrt (tiltVariance t) ^ 5 =
      tiltVariance t * Real.sqrt (tiltVariance t) ^ 3 := by
    calc
      Real.sqrt (tiltVariance t) ^ 5 =
          Real.sqrt (tiltVariance t) ^ 2 * Real.sqrt (tiltVariance t) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hv.le]
  unfold tiltStandardMoment
  rw [tiltCentralMoment_three ht, hs5]
  field_simp [hv.ne', hs, hk]

theorem tiltStandardMoment_fifth_ratio_pos {t : ℝ} (ht : 0 < t) :
    0 < tiltStandardMoment t 5 / tiltStandardMoment t 3 := by
  rw [tiltStandardMoment_fifth_ratio_eq ht]
  exact div_pos_of_neg_of_neg (tiltCentralMoment_five_neg ht)
    (mul_neg_of_pos_of_neg (tiltVariance_pos ht) (tiltThirdCumulant_neg ht))

theorem tiltStandardMoment_fifth_ratio_lt {t : ℝ} (ht : 0 < t) :
    tiltStandardMoment t 5 / tiltStandardMoment t 3 < 22 := by
  rw [tiltStandardMoment_fifth_ratio_eq ht, tiltCentralMoment_five ht]
  have heq : (tiltFifthCumulant t + 10 * tiltVariance t * tiltThirdCumulant t) /
      (tiltVariance t * tiltThirdCumulant t) =
      10 + tiltFifthCumulant t / (tiltVariance t * tiltThirdCumulant t) := by
    field_simp [(tiltVariance_pos ht).ne', (tiltThirdCumulant_neg ht).ne]
    <;> ring
  rw [heq]
  exact explicit_fifth_ratio_lt_twentyTwo ht

/-- A strict version of the three numerical bounds in Pang's Lemma 4.1,
for every positive tilt. Each standardized moment has the integral meaning
given by `tiltStandardMoment_eq_integral`, with integrability proved above. -/
theorem pang_tilt_moment_bounds {t : ℝ} (ht : 0 < t) :
    tiltVariance t ∈ Ioo (0 : ℝ) (1 / 3) ∧
      tiltStandardMoment t 3 ∈ Ioo (-2 : ℝ) 0 ∧
      tiltStandardMoment t 5 / tiltStandardMoment t 3 ∈ Ioo (0 : ℝ) 22 := by
  refine ⟨tiltVariance_mem_Ioo ht, ?_, ?_⟩
  · rw [tiltStandardMoment_three ht]
    exact tiltSkewness_mem_Ioo ht
  · exact ⟨tiltStandardMoment_fifth_ratio_pos ht, tiltStandardMoment_fifth_ratio_lt ht⟩

end
end ENT.Pang
