module

public import ENT.Pang.Moments
public import ENT.Pang.MomentAlgebra
public import Mathlib.Data.Nat.Choose.Sum

/-! The binomial centered-moment identity and the actual fifth tilt moment. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval BigOperators

namespace ENT.Pang

noncomputable section

theorem tiltMoment_four {t : ℝ} (ht : 0 < t) :
    tiltMoment t 4 = 1 - 4 * tiltMoment t 3 / t := by
  have h := tiltMoment_succ t 3
  norm_num at h
  rw [tiltMoment_even_boundary ht] at h
  apply (mul_left_cancel₀ ht.ne')
  calc
    t * tiltMoment t 4 = t - 4 * tiltMoment t 3 := by linarith
    _ = t * (1 - 4 * tiltMoment t 3 / t) := by field_simp

theorem tiltMoment_five {t : ℝ} (ht : 0 < t) :
    tiltMoment t 5 = tiltMean t + 1 / t - 5 * tiltMoment t 4 / t := by
  have h := tiltMoment_succ t 4
  norm_num at h
  rw [tiltMoment_odd_boundary ht] at h
  apply (mul_left_cancel₀ ht.ne')
  calc
    t * tiltMoment t 5 = t * tiltMean t + 1 - 5 * tiltMoment t 4 := by linarith
    _ = t * (tiltMean t + 1 / t - 5 * tiltMoment t 4 / t) := by
      field_simp

theorem tiltMoment_five_centered {t : ℝ} (ht : 0 < t) :
    tiltMoment t 5 - 5 * tiltMean t * tiltMoment t 4 +
      10 * tiltMean t ^ 2 * tiltMoment t 3 - 10 * tiltMean t ^ 3 * tiltMoment t 2 +
      4 * tiltMean t ^ 5 =
      tiltFifthCumulant t + 10 * tiltVariance t * tiltThirdCumulant t := by
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  rw [tiltMoment_five ht, tiltMoment_four ht, tiltMoment_three ht, tiltMoment_two ht]
  unfold tiltMean tiltVariance tiltThirdCumulant tiltFifthCumulant
  field_simp [ht.ne', hs]
  have hc3 : Real.cosh t ^ 3 = Real.cosh t * (Real.sinh t ^ 2 + 1) := by
    rw [pow_succ, Real.cosh_sq]
    ring
  have hc4 : Real.cosh t ^ 4 = (Real.sinh t ^ 2 + 1) ^ 2 := by
    calc
      Real.cosh t ^ 4 = (Real.cosh t ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.cosh_sq]
  have hc5 : Real.cosh t ^ 5 = Real.cosh t * (Real.sinh t ^ 2 + 1) ^ 2 := by
    calc
      Real.cosh t ^ 5 = Real.cosh t * Real.cosh t ^ 4 := by ring
      _ = _ := by rw [hc4]
  ring_nf
  simp only [Real.cosh_sq, hc3, hc5]
  ring

theorem tiltCentralMoment_eq_sum (t : ℝ) (k : ℕ) :
    tiltCentralMoment t k =
      ∑ j ∈ Finset.range (k + 1),
        ((-tiltMean t) ^ (k - j) * (k.choose j : ℝ)) * tiltMoment t j := by
  have heq : (fun x : ℝ => (x - tiltMean t) ^ k * tiltWeight t x) =
      (fun x : ℝ => ∑ j ∈ Finset.range (k + 1),
        ((-tiltMean t) ^ (k - j) * (k.choose j : ℝ)) *
          (x ^ j * tiltWeight t x)) := by
    funext x
    rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold tiltCentralMoment
  rw [heq, intervalIntegral.integral_finsetSum
    (fun j _ => (intervalIntegrable_tiltMoment t j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem tiltCentralMoment_five {t : ℝ} (ht : 0 < t) :
    tiltCentralMoment t 5 =
      tiltFifthCumulant t + 10 * tiltVariance t * tiltThirdCumulant t := by
  have h := tiltCentralMoment_eq_sum t 5
  norm_num [Finset.sum_range_succ, Nat.choose, tiltMoment_zero ht, tiltMoment_one ht] at h
  nlinarith [tiltMoment_five_centered ht]

end
end ENT.Pang
