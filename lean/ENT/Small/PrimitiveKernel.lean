module

public import ENT.Small.BoxPrimitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Kernel representations with integrable endpoint singularities. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

attribute [local instance 1001] NormedField.toNormedSpace

namespace ENT.Small

noncomputable section

theorem boxPrimitive_two_eq_kernel {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {x : ℝ} (hx : 0 ≤ x)
    (hc : ContinuousOn f (Ioo 0 x)) :
    boxPrimitive f 2 x = ∫ t in 0..x, (x - t) * f t := by
  have hderiv : ∀ y ∈ Ioo (min 0 x) (max 0 x),
      HasDerivAt (boxPrimitive f 1) (f y) y := by
    intro y hy
    rw [min_eq_left hx, max_eq_right hx] at hy
    exact intervalIntegral.integral_hasDerivAt_right (hf 0 y)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc y hy)
      ((hc y hy).continuousAt (isOpen_Ioo.mem_nhds hy))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => x - t) (v := boxPrimitive f 1)
    (u' := fun _ => (-1 : ℝ)) (v' := f)
    (a := 0) (b := x)
    (by fun_prop) (continuous_boxPrimitive_succ hf 0).continuousOn
    (fun y _ => by
      convert (hasDerivAt_const y x).sub (hasDerivAt_id y) using 1
      · rfl
      · norm_num)
    hderiv intervalIntegrable_const (hf 0 x)
  have hz : boxPrimitive f 1 0 = 0 := by simp
  simp only [sub_self, zero_mul, hz, mul_zero, sub_zero, zero_sub,
    intervalIntegral.integral_const_mul, neg_one_mul, neg_neg] at h
  rw [intervalIntegral.integral_neg, neg_neg] at h
  change (∫ t in 0..x, boxPrimitive f 1 t) = _
  exact h.symm

theorem boxPrimitive_three_eq_kernel {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {x : ℝ} (hx : 0 ≤ x)
    (hc : ContinuousOn f (Ioo 0 x)) :
    boxPrimitive f 3 x = (1 / 2) * ∫ t in 0..x, (x - t) ^ 2 * f t := by
  have hderiv : ∀ y ∈ Ioo (min 0 x) (max 0 x),
      HasDerivAt (boxPrimitive f 1) (f y) y := by
    intro y hy
    rw [min_eq_left hx, max_eq_right hx] at hy
    exact intervalIntegral.integral_hasDerivAt_right (hf 0 y)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc y hy)
      ((hc y hy).continuousAt (isOpen_Ioo.mem_nhds hy))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => (x - t) ^ 2) (v := boxPrimitive f 1)
    (u' := fun t => -2 * (x - t)) (v' := f)
    (a := 0) (b := x)
    (by fun_prop) (continuous_boxPrimitive_succ hf 0).continuousOn
    (fun y _ => by
      convert ((hasDerivAt_const y x).sub (hasDerivAt_id y)).pow 2 using 1
      · rfl
      · simp only [Pi.sub_apply, id_eq]
        ring)
    hderiv ((show Continuous (fun t : ℝ => -2 * (x - t)) by fun_prop).intervalIntegrable _ _) (hf 0 x)
  have hk := boxPrimitive_two_eq_kernel
    (fun a b => (continuous_boxPrimitive_succ hf 0).intervalIntegrable a b) hx
    (continuous_boxPrimitive_succ hf 0).continuousOn
  change boxPrimitive f 3 x = ∫ t in 0..x, (x - t) * boxPrimitive f 1 t at hk
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, boxPrimitive_succ_zero,
    mul_zero, sub_zero, zero_sub] at h
  have heq : (fun t : ℝ => (-2 * (x - t)) * boxPrimitive f 1 t) =
      (fun t => -2 * ((x - t) * boxPrimitive f 1 t)) := by funext t; ring
  rw [heq, intervalIntegral.integral_const_mul, ← hk] at h
  linarith

theorem boxPrimitive_two_difference {f : ℝ → ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hc : ContinuousOn f (Ioo 0 R)) :
    boxPrimitive f 2 R - boxPrimitive f 2 r =
      (R - r) * (∫ t in 0..r, f t) + ∫ t in r..R, (R - t) * f t := by
  have hi (a b c : ℝ) : IntervalIntegrable (fun t : ℝ => (c - t) * f t) volume a b :=
    (hf a b).continuousOn_mul (by fun_prop)
  have hcr : ContinuousOn f (Ioo 0 r) := hc.mono (fun y hy => ⟨hy.1, lt_of_lt_of_le hy.2 hrR⟩)
  rw [boxPrimitive_two_eq_kernel hf (le_trans hr hrR) hc, boxPrimitive_two_eq_kernel hf hr hcr,
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 r R) (hi r R R)]
  have hsub : (∫ t in 0..r, (R - t) * f t) - (∫ t in 0..r, (r - t) * f t) =
      (R - r) * ∫ t in 0..r, f t := by
    rw [← intervalIntegral.integral_sub (hi 0 r R) (hi 0 r r), ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  linarith

end
end ENT.Small
