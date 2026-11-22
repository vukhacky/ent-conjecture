module

public import ENT.Pang.TiltIntegrals

/-!
# First three moments of the exponential tilt

This module connects the explicit calculus formulas to actual integrals on
`[-1,1]`. The normalization and recurrence are proved in `TiltIntegrals`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace ENT.Pang

noncomputable section

theorem tiltMoment_odd_boundary {t : ℝ} (ht : 0 < t) :
    t / (2 * Real.sinh t) * (Real.exp t + Real.exp (-t)) =
      t * tiltMean t + 1 := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have he : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by
    rw [Real.cosh_eq]
    ring
  rw [he]
  unfold tiltMean
  field_simp [ht.ne', hs]
  <;> ring

theorem tiltMoment_even_boundary {t : ℝ} (ht : 0 < t) :
    t / (2 * Real.sinh t) * (Real.exp t - Real.exp (-t)) = t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  have he : Real.exp t - Real.exp (-t) = 2 * Real.sinh t := by
    rw [Real.sinh_eq]
    ring
  rw [he]
  field_simp [hs]

theorem tiltMoment_one {t : ℝ} (ht : 0 < t) :
    tiltMoment t 1 = tiltMean t := by
  have h := tiltMoment_succ t 0
  norm_num only [Nat.zero_add, Nat.cast_zero, zero_add, pow_one, neg_mul, one_mul,
    sub_neg_eq_add] at h
  rw [tiltMoment_zero ht, tiltMoment_odd_boundary ht] at h
  nlinarith

theorem tiltMoment_two {t : ℝ} (ht : 0 < t) :
    tiltMoment t 2 = 1 - 2 * tiltMean t / t := by
  have h := tiltMoment_succ t 1
  norm_num only [Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two, neg_one_sq,
    one_mul] at h
  rw [tiltMoment_one ht, tiltMoment_even_boundary ht] at h
  apply (mul_left_cancel₀ ht.ne')
  calc
    t * tiltMoment t 2 = t - 2 * tiltMean t := by linarith
    _ = t * (1 - 2 * tiltMean t / t) := by field_simp

theorem tiltMoment_three {t : ℝ} (ht : 0 < t) :
    tiltMoment t 3 = tiltMean t + 1 / t - 3 * tiltMoment t 2 / t := by
  have h := tiltMoment_succ t 2
  norm_num at h
  rw [tiltMoment_odd_boundary ht] at h
  apply (mul_left_cancel₀ ht.ne')
  calc
    t * tiltMoment t 3 = t * tiltMean t + 1 - 3 * tiltMoment t 2 := by linarith
    _ = t * (tiltMean t + 1 / t - 3 * tiltMoment t 2 / t) := by
      field_simp
      <;> ring

theorem tiltMoment_two_sub_mean_sq {t : ℝ} (ht : 0 < t) :
    tiltMoment t 2 - tiltMean t ^ 2 = tiltVariance t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  rw [tiltMoment_two ht]
  unfold tiltMean tiltVariance
  field_simp [ht.ne', hs]
  nlinarith [congrArg (fun x : ℝ => t ^ 2 * x) (Real.cosh_sq_sub_sinh_sq t)]

theorem tiltMoment_three_centered {t : ℝ} (ht : 0 < t) :
    tiltMoment t 3 - 3 * tiltMean t * tiltMoment t 2 + 2 * tiltMean t ^ 3 =
      tiltThirdCumulant t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  rw [tiltMoment_three ht, tiltMoment_two ht]
  unfold tiltMean tiltThirdCumulant
  field_simp [ht.ne', hs]
  have hc3 : Real.cosh t ^ 3 = Real.cosh t * (Real.sinh t ^ 2 + 1) := by
    rw [pow_succ, Real.cosh_sq]
    ring
  ring_nf
  simp only [hc3]
  ring

/-- Centered interval moment, with centering by the proved mean. -/
def tiltCentralMoment (t : ℝ) (k : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (x - tiltMean t) ^ k * tiltWeight t x

theorem intervalIntegrable_tiltCentralMoment (t : ℝ) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => (x - tiltMean t) ^ k * tiltWeight t x)
      volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  unfold tiltWeight
  fun_prop

theorem tiltCentralMoment_two {t : ℝ} (ht : 0 < t) :
    tiltCentralMoment t 2 = tiltVariance t := by
  have hi0 : IntervalIntegrable (tiltWeight t) volume (-1) 1 := by
    simpa only [pow_zero, one_mul] using intervalIntegrable_tiltMoment t 0
  have hi1 : IntervalIntegrable (fun x : ℝ => x * tiltWeight t x) volume (-1) 1 := by
    simpa only [pow_one] using intervalIntegrable_tiltMoment t 1
  have hi2 := intervalIntegrable_tiltMoment t 2
  have hm1 : (∫ x in (-1 : ℝ)..1, x * tiltWeight t x) = tiltMean t := by
    simpa only [tiltMoment, pow_one] using tiltMoment_one ht
  have heq : (fun x : ℝ => (x - tiltMean t) ^ 2 * tiltWeight t x) =
      (fun x : ℝ => (x ^ 2 * tiltWeight t x -
        (2 * tiltMean t) * (x * tiltWeight t x)) +
        tiltMean t ^ 2 * tiltWeight t x) := by
    funext x
    ring
  unfold tiltCentralMoment
  rw [heq, intervalIntegral.integral_add (hi2.sub (hi1.const_mul _))
      (hi0.const_mul _), intervalIntegral.integral_sub hi2 (hi1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hm1, integral_tiltWeight ht]
  change tiltMoment t 2 - 2 * tiltMean t * tiltMean t + tiltMean t ^ 2 * 1 =
    tiltVariance t
  nlinarith [tiltMoment_two_sub_mean_sq ht]

theorem tiltCentralMoment_three {t : ℝ} (ht : 0 < t) :
    tiltCentralMoment t 3 = tiltThirdCumulant t := by
  have hi0 : IntervalIntegrable (tiltWeight t) volume (-1) 1 := by
    simpa only [pow_zero, one_mul] using intervalIntegrable_tiltMoment t 0
  have hi1 : IntervalIntegrable (fun x : ℝ => x * tiltWeight t x) volume (-1) 1 := by
    simpa only [pow_one] using intervalIntegrable_tiltMoment t 1
  have hi2 := intervalIntegrable_tiltMoment t 2
  have hi3 := intervalIntegrable_tiltMoment t 3
  have hm1 : (∫ x in (-1 : ℝ)..1, x * tiltWeight t x) = tiltMean t := by
    simpa only [tiltMoment, pow_one] using tiltMoment_one ht
  have heq : (fun x : ℝ => (x - tiltMean t) ^ 3 * tiltWeight t x) =
      (fun x : ℝ => ((x ^ 3 * tiltWeight t x -
        (3 * tiltMean t) * (x ^ 2 * tiltWeight t x)) +
        (3 * tiltMean t ^ 2) * (x * tiltWeight t x)) -
        tiltMean t ^ 3 * tiltWeight t x) := by
    funext x
    ring
  unfold tiltCentralMoment
  rw [heq, intervalIntegral.integral_sub
      ((hi3.sub (hi2.const_mul _)).add (hi1.const_mul _)) (hi0.const_mul _),
    intervalIntegral.integral_add (hi3.sub (hi2.const_mul _)) (hi1.const_mul _),
    intervalIntegral.integral_sub hi3 (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hm1, integral_tiltWeight ht]
  change (tiltMoment t 3 - 3 * tiltMean t * tiltMoment t 2 +
    3 * tiltMean t ^ 2 * tiltMean t) - tiltMean t ^ 3 * 1 = tiltThirdCumulant t
  nlinarith [tiltMoment_three_centered ht]

end
end ENT.Pang
