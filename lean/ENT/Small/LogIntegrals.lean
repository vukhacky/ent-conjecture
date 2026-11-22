module

public import ENT.Base.TwoEntropy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Elementary logarithmic integrals used by the dimension-three local proof. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Small

noncomputable section

def halfLogRatio (x : ℝ) : ℝ := (Real.log (1 + x) - Real.log (1 - x)) / 2

theorem halfLogRatio_eq_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    halfLogRatio x = Real.artanh x := by
  rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩,
    Real.log_div (by linarith [hx.1] : 1 + x ≠ 0) (by linarith [hx.2] : 1 - x ≠ 0)]
  unfold halfLogRatio
  ring

theorem hasDerivAt_halfLogRatio {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt halfLogRatio (1 / (1 - x ^ 2)) x := by
  have hp : 1 + x ≠ 0 := by linarith [hx.1]
  have hm : 1 - x ≠ 0 := by linarith [hx.2]
  have hq : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have h := ((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hp).sub
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hm)).div_const 2
  convert h using 1
  · rfl
  · simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    field_simp
    ring

def capLogPrimitive (x : ℝ) : ℝ :=
  (x - x ^ 3 / 3) * Real.log (1 - x ^ 2) + 2 * x ^ 3 / 9 -
    4 * x / 3 + (4 / 3) * halfLogRatio x

theorem hasDerivAt_capLogPrimitive {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt capLogPrimitive ((1 - x ^ 2) * Real.log (1 - x ^ 2)) x := by
  have hq : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hA := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).div_const 3)
  have hL := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).log hq
  have h := ((((hA.mul hL).add ((((hasDerivAt_id x).pow 3).const_mul 2).div_const 9)).sub
    (((hasDerivAt_id x).const_mul 4).div_const 3)).add
      ((hasDerivAt_halfLogRatio hx).const_mul (4 / 3 : ℝ)))
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

theorem integral_one_sub_sq_mul_log {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ x in 0..c, (1 - x ^ 2) * Real.log (1 - x ^ 2)) =
      (c - c ^ 3 / 3) * Real.log (1 - c ^ 2) + 2 * c ^ 3 / 9 -
        4 * c / 3 + (4 / 3) * Real.artanh c := by
  have hcont : ContinuousOn capLogPrimitive (Icc 0 c) := by
    intro x hx
    exact (hasDerivAt_capLogPrimitive ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) * Real.log (1 - x ^ 2)) volume 0 c :=
    (Real.continuous_mul_log.comp (continuous_const.sub (continuous_id.pow 2))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc0 hcont
    (fun x hx => hasDerivAt_capLogPrimitive ⟨by linarith [hx.1], by linarith [hx.2]⟩) hi]
  have hzero : capLogPrimitive 0 = 0 := by simp [capLogPrimitive, halfLogRatio]
  rw [hzero, sub_zero]
  unfold capLogPrimitive
  rw [halfLogRatio_eq_artanh ⟨by linarith, hc1⟩]

def logCapPrimitive (x : ℝ) : ℝ :=
  x * Real.log (1 - x ^ 2) - 2 * x + 2 * halfLogRatio x

theorem hasDerivAt_logCapPrimitive {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt logCapPrimitive (Real.log (1 - x ^ 2)) x := by
  have hq : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hL := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).log hq
  have h := (((hasDerivAt_id x).mul hL).sub ((hasDerivAt_id x).const_mul 2)).add
    ((hasDerivAt_halfLogRatio hx).const_mul 2)
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

theorem integral_log_one_sub_sq {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ x in 0..c, Real.log (1 - x ^ 2)) =
      c * Real.log (1 - c ^ 2) - 2 * c + 2 * Real.artanh c := by
  have hcont : ContinuousOn logCapPrimitive (Icc 0 c) := by
    intro x hx
    exact (hasDerivAt_logCapPrimitive ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun x : ℝ => Real.log (1 - x ^ 2)) volume 0 c := by
    apply ContinuousOn.intervalIntegrable
    apply (continuous_const.sub (continuous_id.pow 2)).continuousOn.log
    intro x hx
    rw [uIcc_of_le hc0] at hx
    change 1 - x ^ 2 ≠ 0
    nlinarith [hx.1, hx.2]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc0 hcont
    (fun x hx => hasDerivAt_logCapPrimitive ⟨by linarith [hx.1], by linarith [hx.2]⟩) hi]
  have hzero : logCapPrimitive 0 = 0 := by simp [logCapPrimitive, halfLogRatio]
  rw [hzero, sub_zero]
  unfold logCapPrimitive
  rw [halfLogRatio_eq_artanh ⟨by linarith, hc1⟩]

theorem integral_sq_mul_log_from_zero {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in 0..c, x ^ 2 * Real.log x) = c ^ 3 / 3 * Real.log c - c ^ 3 / 9 := by
  let P : ℝ → ℝ := fun x => x ^ 2 * (x * Real.log x) / 3 - x ^ 3 / 9
  have hcont : Continuous P := by dsimp [P]; fun_prop
  have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt P (x ^ 2 * Real.log x) x := by
    intro x hx
    have h := ((((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_mul_log hx.1.ne')).div_const 3).sub
      (((hasDerivAt_id x).pow 3).div_const 9)
    convert h using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have hi : IntervalIntegrable (fun x : ℝ => x ^ 2 * Real.log x) volume 0 c := by
    have hfun : (fun x : ℝ => x ^ 2 * Real.log x) = (fun x => x * (x * Real.log x)) := by funext x; ring
    rw [hfun]
    exact (continuous_id.mul Real.continuous_mul_log).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc hcont.continuousOn hderiv hi]
  simp only [P, zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 2 ≠ 0),
    zero_mul, mul_zero, zero_div, sub_zero]
  ring

theorem integral_scaled_square_mul_log {k c : ℝ} (hk : 0 < k) (hc : 0 ≤ c) :
    (∫ x in 0..c, (k * x ^ 2) * Real.log (k * x ^ 2)) =
      k * c ^ 3 / 3 * Real.log (k * c ^ 2) - 2 * k * c ^ 3 / 9 := by
  have heq : (fun x : ℝ => (k * x ^ 2) * Real.log (k * x ^ 2)) =
      (fun x => (k * Real.log k) * x ^ 2 + (2 * k) * (x ^ 2 * Real.log x)) := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_mul hk.ne' (pow_ne_zero _ hx), Real.log_pow]
      norm_num
      ring
  have hi : IntervalIntegrable (fun x : ℝ => x ^ 2 * Real.log x) volume 0 c := by
    have hfun : (fun x : ℝ => x ^ 2 * Real.log x) = (fun x => x * (x * Real.log x)) := by funext x; ring
    rw [hfun]
    exact (continuous_id.mul Real.continuous_mul_log).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 c :=
    (continuous_id.pow 2).intervalIntegrable 0 c
  rw [heq, intervalIntegral.integral_add (hi2.const_mul _) (hi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_sq_mul_log_from_zero hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · rw [Real.log_mul hk.ne' (pow_ne_zero _ hc0), Real.log_pow]
    norm_num
    ring

theorem integral_quadratic_cap_mul_log {k c : ℝ} (hk : 0 < k) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ x in 0..c, (k * (1 - x ^ 2)) * Real.log (k * (1 - x ^ 2))) =
      k * ((c - c ^ 3 / 3) * Real.log (k * (1 - c ^ 2)) +
        2 * c ^ 3 / 9 - 4 * c / 3 + (4 / 3) * Real.artanh c) := by
  have hq : 1 - c ^ 2 ≠ 0 := by nlinarith
  have heq : (∫ x in 0..c, (k * (1 - x ^ 2)) * Real.log (k * (1 - x ^ 2))) =
      ∫ x in 0..c, (k * Real.log k) * (1 - x ^ 2) +
        k * ((1 - x ^ 2) * Real.log (1 - x ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hc0] at hx
    dsimp only
    rw [Real.log_mul hk.ne' (by nlinarith [hx.1, hx.2] : 1 - x ^ 2 ≠ 0)]
    ring
  have hi : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2) volume 0 c :=
    (continuous_const.sub (continuous_id.pow 2)).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) * Real.log (1 - x ^ 2)) volume 0 c :=
    (Real.continuous_mul_log.comp (continuous_const.sub (continuous_id.pow 2))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 c :=
    (continuous_id.pow 2).intervalIntegrable 0 c
  rw [heq, intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_sub_sq_mul_log hc0 hc1,
    intervalIntegral.integral_sub intervalIntegrable_const hi2,
    intervalIntegral.integral_const, integral_pow,
    Real.log_mul hk.ne' hq]
  norm_num
  ring

theorem integral_neg_log_quadratic_cap {k c : ℝ} (hk : 0 < k)
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ x in 0..c, -Real.log (k * (1 - x ^ 2))) =
      -c * Real.log (k * (1 - c ^ 2)) + 2 * c - 2 * Real.artanh c := by
  have hq : 1 - c ^ 2 ≠ 0 := by nlinarith
  have heq : (∫ x in 0..c, -Real.log (k * (1 - x ^ 2))) =
      ∫ x in 0..c, -Real.log k - Real.log (1 - x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hc0] at hx
    dsimp only
    rw [Real.log_mul hk.ne' (by nlinarith [hx.1, hx.2] : 1 - x ^ 2 ≠ 0)]
    ring
  have hi : IntervalIntegrable (fun x : ℝ => Real.log (1 - x ^ 2)) volume 0 c := by
    apply ContinuousOn.intervalIntegrable
    apply (continuous_const.sub (continuous_id.pow 2)).continuousOn.log
    intro x hx
    rw [uIcc_of_le hc0] at hx
    change 1 - x ^ 2 ≠ 0
    nlinarith [hx.1, hx.2]
  rw [heq, intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const, integral_log_one_sub_sq hc0 hc1,
    Real.log_mul hk.ne' hq]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem integral_neg_log_scaled_square {k c : ℝ} (hk : 0 < k) (hc : 0 < c) :
    (∫ x in 0..c, -Real.log (k * x ^ 2)) = -c * Real.log (k * c ^ 2) + 2 * c := by
  have heq : (∫ x in 0..c, -Real.log (k * x ^ 2)) =
      ∫ x in 0..c, -Real.log k - 2 * Real.log x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc.le
    intro x hx
    dsimp only
    rw [Real.log_mul hk.ne' (pow_ne_zero _ hx.1.ne'), Real.log_pow]
    norm_num
    ring
  rw [heq, intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_log'.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_log_from_zero,
    Real.log_mul hk.ne' (pow_ne_zero _ hc.ne'), Real.log_pow]
  norm_num
  ring

theorem integral_mul_neg_log_scaled_square {k c : ℝ} (hk : 0 < k) (hc : 0 ≤ c) :
    (∫ x in 0..c, x * (-Real.log (k * x ^ 2))) =
      -(c ^ 2 / 2) * Real.log (k * c ^ 2) + c ^ 2 / 2 := by
  have heq : (fun x : ℝ => x * (-Real.log (k * x ^ 2))) =
      (fun x => (-Real.log k) * x - 2 * (x * Real.log x)) := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_mul hk.ne' (pow_ne_zero _ hx), Real.log_pow]
      norm_num
      ring
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 c := continuous_id.intervalIntegrable _ _
  have hj : IntervalIntegrable (fun x : ℝ => x * Real.log x) volume 0 c :=
    Real.continuous_mul_log.intervalIntegrable _ _
  rw [heq, intervalIntegral.integral_sub (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, integral_mul_log_from_zero hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · rw [Real.log_mul hk.ne' (pow_ne_zero _ hc0), Real.log_pow]
    norm_num
    ring

end
end ENT.Small
