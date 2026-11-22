module

public import ENT.Pang.Tilt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral formulas for the tilted uniform distribution

The weight is normalized on `[-1,1]`. These are actual integral identities,
proved by the fundamental theorem of calculus. They provide the normalization
and a moment recurrence for the positive exponential tilt without assuming a
probabilistic moment-generating-function differentiation theorem.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval

namespace ENT.Pang

noncomputable section

/-- The unnormalized exponential moment over the uniform support. -/
def exponentialMoment (t : ℝ) (k : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, x ^ k * Real.exp (t * x)

/-- The positive-tilt weight on its support; use an indicator for a global PDF. -/
def tiltWeight (t x : ℝ) : ℝ :=
  t / (2 * Real.sinh t) * Real.exp (t * x)

/-- A raw moment of the normalized weight on `[-1,1]`. -/
def tiltMoment (t : ℝ) (k : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, x ^ k * tiltWeight t x

theorem tiltWeight_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < tiltWeight t x := by
  unfold tiltWeight
  exact mul_pos (div_pos ht (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr ht)))
    (Real.exp_pos _)

theorem intervalIntegrable_exponentialMoment (t : ℝ) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ k * Real.exp (t * x)) volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem intervalIntegrable_tiltMoment (t : ℝ) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ k * tiltWeight t x) volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  unfold tiltWeight
  fun_prop

theorem tiltMoment_eq_mul (t : ℝ) (k : ℕ) :
    tiltMoment t k = t / (2 * Real.sinh t) * exponentialMoment t k := by
  unfold tiltMoment tiltWeight exponentialMoment
  have heq : (fun x : ℝ => x ^ k * (t / (2 * Real.sinh t) * Real.exp (t * x))) =
      (fun x : ℝ => t / (2 * Real.sinh t) * (x ^ k * Real.exp (t * x))) := by
    funext x
    ring
  rw [heq, intervalIntegral.integral_const_mul]

theorem integral_exp_mul {t : ℝ} (ht : t ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.exp (t * x)) =
      (Real.exp (t * b) - Real.exp (t * a)) / t := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (t * y) / t) (Real.exp (t * x)) x := by
    intro x
    have h := (((hasDerivAt_id x).const_mul t).exp).div_const t
    apply h.congr_deriv
    change (Real.exp (t * x) * (t * 1)) / t = Real.exp (t * x)
    field_simp [ht]
  have hi : IntervalIntegrable (fun x : ℝ => Real.exp (t * x)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi
  simpa only [sub_div] using h

theorem exponentialMoment_zero {t : ℝ} (ht : t ≠ 0) :
    exponentialMoment t 0 = 2 * Real.sinh t / t := by
  unfold exponentialMoment
  simp only [pow_zero, one_mul]
  rw [integral_exp_mul ht]
  simp only [mul_one, mul_neg_one]
  rw [Real.sinh_eq]
  ring

/-- Integration by parts in a form requiring no division by the tilt. -/
theorem exponentialMoment_succ (t : ℝ) (k : ℕ) :
    t * exponentialMoment t (k + 1) + (k + 1 : ℝ) * exponentialMoment t k =
      Real.exp t - (-1 : ℝ) ^ (k + 1) * Real.exp (-t) := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y ^ (k + 1) * Real.exp (t * y))
        ((k + 1 : ℝ) * (x ^ k * Real.exp (t * x)) +
          t * (x ^ (k + 1) * Real.exp (t * x))) x := by
    intro x
    have h := ((hasDerivAt_id x).pow (k + 1)).mul
      (((hasDerivAt_id x).const_mul t).exp)
    apply h.congr_deriv
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.pow_apply, id_eq]
    ring
  have h1 := (intervalIntegrable_exponentialMoment t k).const_mul (k + 1 : ℝ)
  have h2 := (intervalIntegrable_exponentialMoment t (k + 1)).const_mul t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simpa [exponentialMoment, add_comm] using h

theorem tiltMoment_zero {t : ℝ} (ht : 0 < t) : tiltMoment t 0 = 1 := by
  rw [tiltMoment_eq_mul, exponentialMoment_zero ht.ne']
  have hs : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
  field_simp [ht.ne', hs]

theorem integral_tiltWeight {t : ℝ} (ht : 0 < t) :
    (∫ x in (-1 : ℝ)..1, tiltWeight t x) = 1 := by
  simpa [tiltMoment] using tiltMoment_zero ht

theorem tiltMoment_succ (t : ℝ) (k : ℕ) :
    t * tiltMoment t (k + 1) + (k + 1 : ℝ) * tiltMoment t k =
      t / (2 * Real.sinh t) *
        (Real.exp t - (-1 : ℝ) ^ (k + 1) * Real.exp (-t)) := by
  rw [tiltMoment_eq_mul, tiltMoment_eq_mul]
  have h := congrArg (fun x : ℝ => t / (2 * Real.sinh t) * x)
    (exponentialMoment_succ t k)
  nlinarith only [h]

end
end ENT.Pang
