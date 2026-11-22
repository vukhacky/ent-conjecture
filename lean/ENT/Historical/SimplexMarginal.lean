module

public import ENT.Historical.CappedMarginal
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The uncapped simplex coordinate marginal and its first two moments. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Historical
noncomputable section

def simplexMarginalDensity (n : ℕ) (s x : ℝ) : ℝ :=
  (Icc (0 : ℝ) s).indicator
    (fun x => ((n : ℝ) - 1) / s ^ (n - 1) * (s - x) ^ (n - 2)) x

theorem simplexMarginalDensity_nonneg (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s)
    (x : ℝ) : 0 ≤ simplexMarginalDensity n s x := by
  unfold simplexMarginalDensity
  by_cases hx : x ∈ Icc (0 : ℝ) s
  · rw [indicator_of_mem hx]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (div_nonneg (by linarith) (pow_nonneg hs.le _))
      (pow_nonneg (sub_nonneg.mpr hx.2) _)
  · rw [indicator_of_notMem hx]

theorem simplexMarginalDensity_pos (n : ℕ) (hn : 2 ≤ n) {s x : ℝ}
    (hs : 0 < s) (hx : x ∈ Ioo (0 : ℝ) s) : 0 < simplexMarginalDensity n s x := by
  rw [simplexMarginalDensity, indicator_of_mem (Ioo_subset_Icc_self hx)]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact mul_pos (div_pos (by linarith) (pow_pos hs _)) (pow_pos (sub_pos.mpr hx.2) _)

theorem simplexMarginalDensity_eq_zero {n : ℕ} {s x : ℝ} (hx : x ∉ Icc (0 : ℝ) s) :
    simplexMarginalDensity n s x = 0 := by
  exact indicator_of_notMem hx _

theorem simplexMarginalDensity_integrable (n : ℕ) (s : ℝ) :
    Integrable (simplexMarginalDensity n s) volume := by
  have hc : Continuous (fun x : ℝ => ((n : ℝ) - 1) / s ^ (n - 1) * (s - x) ^ (n - 2)) := by
    fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem simplexMarginalDensity_test_integrable (n : ℕ) (s : ℝ) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 s)) :
    Integrable (fun x => φ x * simplexMarginalDensity n s x) volume := by
  have hc : Continuous (fun x : ℝ => ((n : ℝ) - 1) / s ^ (n - 1) * (s - x) ^ (n - 2)) := by
    fun_prop
  have hi := (hφ.mul hc.continuousOn).integrableOn_compact (μ := volume) isCompact_Icc
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext x
  by_cases hx : x ∈ Icc (0 : ℝ) s <;> simp [simplexMarginalDensity, hx]

theorem integral_pow_shift (k : ℕ) (s : ℝ) :
    (∫ x in (0 : ℝ)..s, (s - x) ^ k) = s ^ (k + 1) / (k + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ k) s]
  simp [integral_pow]

theorem integral_mul_pow_shift (k : ℕ) (s : ℝ) :
    (∫ x in (0 : ℝ)..s, x * (s - x) ^ k) =
      s ^ (k + 2) / (((k : ℝ) + 1) * (k + 2)) := by
  have hfun : (fun x : ℝ => x * (s - x) ^ k) =
      (fun x => s * (s - x) ^ k - (s - x) ^ (k + 1)) := by
    funext x
    rw [pow_succ]
    ring
  rw [hfun, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun x : ℝ => s * (s - x) ^ k)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => (s - x) ^ (k + 1))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_pow_shift, integral_pow_shift]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show k + 1 + 1 = k + 2 by omega, show k + 2 = k + 1 + 1 by omega, pow_succ]
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem integral_sq_mul_pow_shift (k : ℕ) (s : ℝ) :
    (∫ x in (0 : ℝ)..s, x ^ 2 * (s - x) ^ k) =
      2 * s ^ (k + 3) / (((k : ℝ) + 1) * (k + 2) * (k + 3)) := by
  have hfun : (fun x : ℝ => x ^ 2 * (s - x) ^ k) =
      (fun x => s ^ 2 * (s - x) ^ k -
        2 * s * (s - x) ^ (k + 1) + (s - x) ^ (k + 2)) := by
    funext x
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  rw [hfun, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ => s ^ 2 * (s - x) ^ k -
      2 * s * (s - x) ^ (k + 1))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => (s - x) ^ (k + 2))).intervalIntegrable _ _),
    intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun x : ℝ => s ^ 2 * (s - x) ^ k)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => 2 * s * (s - x) ^ (k + 1))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow_shift,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 3 ≠ 0 := by positivity
  have hk2 : k + 1 + 1 = k + 2 := by omega
  have hk3 : k + 2 + 1 = k + 3 := by omega
  rw [hk2, hk3]
  simp only [show (k : ℝ) + 1 + 1 = k + 2 by ring,
    show (k : ℝ) + 2 + 1 = k + 3 by ring]
  rw [show k + 2 = k + 1 + 1 by omega, show k + 3 = k + 1 + 1 + 1 by omega]
  simp only [pow_succ]
  field_simp
  ring

theorem simplexMarginalDensity_integral_test (n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (φ : ℝ → ℝ) :
    (∫ x, φ x * simplexMarginalDensity n s x) =
      ((n : ℝ) - 1) / s ^ (n - 1) * ∫ x in (0 : ℝ)..s, φ x * (s - x) ^ (n - 2) := by
  have hfun : (fun x => φ x * simplexMarginalDensity n s x) =
      (Icc (0 : ℝ) s).indicator
        (fun x => ((n : ℝ) - 1) / s ^ (n - 1) * (φ x * (s - x) ^ (n - 2))) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) s
    · simp only [simplexMarginalDensity, indicator_of_mem hx]
      ring
    · simp [simplexMarginalDensity, hx]
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hs, intervalIntegral.integral_const_mul]

theorem simplexMarginalDensity_mass (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    (∫ x, simplexMarginalDensity n s x) = 1 := by
  have h := simplexMarginalDensity_integral_test n hs.le (fun _ => 1)
  simp only [one_mul, integral_pow_shift] at h
  rw [h]
  have hk : n - 2 + 1 = n - 1 := by omega
  have hkR : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  simp only [hk, hkR]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ) - 1 ≠ 0 := by linarith
  have hsp : s ^ (n - 1) ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp

theorem simplexMarginalDensity_mean (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    (∫ x, x * simplexMarginalDensity n s x) = s / n := by
  rw [simplexMarginalDensity_integral_test n hs.le, integral_mul_pow_shift]
  have hk : n - 2 + 2 = n := by omega
  have hnk : n = n - 1 + 1 := by omega
  have hkR1 : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  have hkR2 : ((n - 2 : ℕ) : ℝ) + 2 = (n : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  have hpow : s ^ n = s ^ (n - 1) * s := by
    conv_lhs => rw [hnk]
    rw [pow_succ]
  rw [hk, hkR1, hkR2, hpow]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsp : s ^ (n - 1) ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp

theorem simplexMarginalDensity_second_moment (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    (∫ x, x ^ 2 * simplexMarginalDensity n s x) = 2 * s ^ 2 / ((n : ℝ) * (n + 1)) := by
  rw [simplexMarginalDensity_integral_test n hs.le, integral_sq_mul_pow_shift]
  have hk : n - 2 + 3 = n - 1 + 2 := by omega
  have hkR1 : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  have hkR2 : ((n - 2 : ℕ) : ℝ) + 2 = (n : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  have hkR3 : ((n - 2 : ℕ) : ℝ) + 3 = (n : ℝ) + 1 := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  rw [hk, hkR1, hkR2, hkR3, pow_add]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hsp : s ^ (n - 1) ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp

end
end ENT.Historical
