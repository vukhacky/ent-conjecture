module

public import ENT.Pang.Moments
public import ENT.Entropy.Finite
public import ENT.Entropy.LawInvariance
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A genuine probability law for the positive tilt

The global density includes its support indicator. Normalization is proved
from the interval integral; finite entropy follows from the shared bounded-
support construction. Moments of the resulting measure are connected to the
explicit cumulant formulas.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace ENT.Pang

noncomputable section

def tiltDensity (t : ℝ) : ℝ → ℝ :=
  (Icc (-1 : ℝ) 1).indicator (tiltWeight t)

def tiltLaw (t : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (tiltDensity t x))

theorem measurable_tiltDensity (t : ℝ) : Measurable (tiltDensity t) := by
  have hc : Continuous (tiltWeight t) := by
    unfold tiltWeight
    fun_prop
  exact hc.measurable.indicator measurableSet_Icc

theorem tiltDensity_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ tiltDensity t x := by
  unfold tiltDensity
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx]
    exact (tiltWeight_pos ht x).le
  · rw [indicator_of_notMem hx]

theorem tiltDensity_support (t x : ℝ) (hx : x ∉ Icc (-1 : ℝ) 1) :
    tiltDensity t x = 0 := by
  exact indicator_of_notMem hx _

theorem tiltDensity_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    tiltDensity t x ≤ tiltWeight t 1 := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · unfold tiltDensity
    rw [indicator_of_mem hx]
    unfold tiltWeight
    apply mul_le_mul_of_nonneg_left
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 ht.le)
    · exact (div_pos ht (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr ht))).le
  · rw [tiltDensity_support t x hx]
    exact (tiltWeight_pos ht 1).le

theorem integral_tiltDensity {t : ℝ} (ht : 0 < t) :
    (∫ x, tiltDensity t x) = 1 := by
  unfold tiltDensity
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  exact integral_tiltWeight ht

def tiltFiniteEntropyDensity {t : ℝ} (ht : 0 < t) : FiniteEntropyDensity (tiltLaw t) :=
  finiteEntropyDensityOfBoundedSupport (tiltLaw t) (tiltDensity t) (tiltWeight t 1) 1
    (measurable_tiltDensity t) (tiltDensity_nonneg ht) (tiltDensity_le ht)
    (tiltDensity_support t) (integral_tiltDensity ht) rfl

theorem isProbabilityMeasure_tiltLaw {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (tiltLaw t) :=
  (tiltFiniteEntropyDensity ht).isProbabilityMeasure

theorem integral_mul_tiltDensity (t : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x * tiltDensity t x) =
      ∫ x in (-1 : ℝ)..1, f x * tiltWeight t x := by
  have heq : (fun x => f x * tiltDensity t x) =
      (Icc (-1 : ℝ) 1).indicator (fun x => f x * tiltWeight t x) := by
    funext x
    unfold tiltDensity
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

theorem integral_tiltLaw {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) :
    (∫ x, f x ∂tiltLaw t) = ∫ x in (-1 : ℝ)..1, f x * tiltWeight t x := by
  unfold tiltLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_tiltDensity t).ennreal_ofReal (Filter.Eventually.of_forall
      (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (tiltDensity_nonneg ht _), smul_eq_mul]
  have heq : (fun x => tiltDensity t x * f x) =
      (fun x => f x * tiltDensity t x) := by
    funext x
    exact mul_comm _ _
  rw [heq, integral_mul_tiltDensity]

theorem tiltLaw_mean {t : ℝ} (ht : 0 < t) :
    (∫ x, x ∂tiltLaw t) = tiltMean t := by
  rw [integral_tiltLaw ht]
  simpa only [tiltMoment, pow_one] using tiltMoment_one ht

theorem tiltLaw_centered_second {t : ℝ} (ht : 0 < t) :
    (∫ x, (x - tiltMean t) ^ 2 ∂tiltLaw t) = tiltVariance t := by
  rw [integral_tiltLaw ht]
  exact tiltCentralMoment_two ht

theorem tiltLaw_centered_third {t : ℝ} (ht : 0 < t) :
    (∫ x, (x - tiltMean t) ^ 3 ∂tiltLaw t) = tiltThirdCumulant t := by
  rw [integral_tiltLaw ht]
  exact tiltCentralMoment_three ht

end
end ENT.Pang
