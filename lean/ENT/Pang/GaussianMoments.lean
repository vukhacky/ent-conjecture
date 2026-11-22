module

public import ENT.Pang.EnvelopeBounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Gaussian reference moments by integration by parts. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory

namespace ENT.Pang

noncomputable section

def gaussianWeight (u : ℝ) : ℝ := Real.exp (-u ^ 2 / 2)

def gaussianMoment (k : ℕ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ u : ℝ, u ^ (2 * k) * gaussianWeight u

theorem gaussianWeight_pos (u : ℝ) : 0 < gaussianWeight u := Real.exp_pos _

theorem continuous_gaussianWeight : Continuous gaussianWeight := by
  unfold gaussianWeight
  fun_prop

theorem integrable_pow_mul_gaussianWeight (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k * gaussianWeight u) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
    (s := (k : ℝ)) (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
  convert h using 1
  funext u
  rw [Real.rpow_natCast]
  unfold gaussianWeight
  congr 2
  ring

theorem gaussianMoment_zero : gaussianMoment 0 = 1 := by
  have h : (∫ u : ℝ, gaussianWeight u) = Real.sqrt (2 * Real.pi) := by
    have he : (fun u : ℝ => gaussianWeight u) = (fun u : ℝ => Real.exp (-(1 / 2) * u ^ 2)) := by
      funext u
      unfold gaussianWeight
      congr 1
      ring
    rw [he, integral_gaussian]
    congr 1
    ring
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  simp only [gaussianMoment, mul_zero, pow_zero, one_mul, h]
  field_simp

theorem hasDerivAt_gaussian_moment_primitive (k : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (2 * k + 1) * gaussianWeight x)
      (((2 * k + 1 : ℕ) : ℝ) * (u ^ (2 * k) * gaussianWeight u) -
        u ^ (2 * (k + 1)) * gaussianWeight u) u := by
  have h := ((hasDerivAt_id u).pow (2 * k + 1)).mul
    (((((hasDerivAt_id u).pow 2).neg).div_const 2).exp)
  apply h.congr_deriv
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.reduceSub, Nat.add_sub_cancel, pow_one,
    Nat.cast_ofNat, mul_one]
  unfold gaussianWeight
  rw [show 2 * (k + 1) = 2 * k + 2 by omega]
  simp only [pow_add, pow_one]
  ring

theorem gaussianMoment_succ (k : ℕ) :
    gaussianMoment (k + 1) = ((2 * k + 1 : ℕ) : ℝ) * gaussianMoment k := by
  have h0 := integrable_pow_mul_gaussianWeight (2 * k)
  have h1 := integrable_pow_mul_gaussianWeight (2 * (k + 1))
  have hi : Integrable (fun u : ℝ => ((2 * k + 1 : ℕ) : ℝ) *
      (u ^ (2 * k) * gaussianWeight u) - u ^ (2 * (k + 1)) * gaussianWeight u) :=
    (h0.const_mul _).sub h1
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
    (hasDerivAt_gaussian_moment_primitive k) hi (integrable_pow_mul_gaussianWeight (2 * k + 1))
  rw [integral_sub (h0.const_mul _) h1, integral_const_mul] at h
  have he : (∫ u : ℝ, u ^ (2 * (k + 1)) * gaussianWeight u) =
      ((2 * k + 1 : ℕ) : ℝ) * ∫ u : ℝ, u ^ (2 * k) * gaussianWeight u := by linarith
  unfold gaussianMoment
  rw [he]
  ring

def gaussianCap : ℕ → ℝ
  | 0 => 1
  | k + 1 => ((2 * k + 1 : ℕ) : ℝ) * gaussianCap k

theorem gaussianMoment_eq_cap (k : ℕ) : gaussianMoment k = gaussianCap k := by
  induction k with
  | zero => exact gaussianMoment_zero
  | succ k ih => rw [gaussianMoment_succ, ih, gaussianCap]

theorem gaussianMoment_one : gaussianMoment 1 = 1 := by
  rw [gaussianMoment_eq_cap]
  norm_num [gaussianCap]

theorem gaussianMoment_two : gaussianMoment 2 = 3 := by
  rw [gaussianMoment_eq_cap]
  norm_num [gaussianCap]

theorem gaussianMoment_three : gaussianMoment 3 = 15 := by
  rw [gaussianMoment_eq_cap]
  norm_num [gaussianCap]

theorem gaussianMoment_four : gaussianMoment 4 = 105 := by
  rw [gaussianMoment_eq_cap]
  norm_num [gaussianCap]

theorem gaussianMoment_five : gaussianMoment 5 = 945 := by
  rw [gaussianMoment_eq_cap]
  norm_num [gaussianCap]

theorem gaussianMoment_six : gaussianMoment 6 = 10395 := by
  rw [gaussianMoment_eq_cap]
  norm_num [gaussianCap]

end
end ENT.Pang
