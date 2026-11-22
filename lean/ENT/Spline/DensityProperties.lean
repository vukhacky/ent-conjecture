module

public import ENT.Spline.Recurrence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Nonnegativity, compact support and a uniform bound for the spline formula.
These are proved from the exact window recurrence, without a density-law axiom. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Spline

noncomputable section

theorem continuous_unitSumSplineDensity (n : ℕ) : Continuous (unitSumSplineDensity n) :=
  continuous_const.mul (continuous_unnormalizedSpline n)

theorem unitSumSplineDensity_two_formula (t : ℝ) :
    unitSumSplineDensity 2 t = max 0 t - 2 * max 0 (t - 1) + max 0 (t - 2) := by
  norm_num [unitSumSplineDensity, unnormalizedSpline, positivePower,
    Finset.sum_range_succ, Nat.choose] <;> ring

theorem unitSumSplineDensity_two_overlap (t : ℝ) :
    unitSumSplineDensity 2 t = max 0 (min 1 t - max 0 (t - 1)) := by
  rw [unitSumSplineDensity_two_formula]
  by_cases h0 : t ≤ 0
  · simp [max_eq_left h0, max_eq_left (show t - 1 ≤ 0 by linarith),
      max_eq_left (show t - 2 ≤ 0 by linarith), min_eq_right (show t ≤ 1 by linarith)]
  have hp : 0 ≤ t := by linarith
  by_cases h1 : t ≤ 1
  · simp [max_eq_right hp, max_eq_left (show t - 1 ≤ 0 by linarith),
      max_eq_left (show t - 2 ≤ 0 by linarith), min_eq_right h1]
  have hp1 : 0 ≤ t - 1 := by linarith
  by_cases h2 : t ≤ 2
  · simp [max_eq_right hp, max_eq_right hp1,
      max_eq_left (show t - 2 ≤ 0 by linarith), min_eq_left (show 1 ≤ t by linarith),
      max_eq_right (show 0 ≤ 1 - (t - 1) by linarith)] <;> ring
  · simp [max_eq_right hp, max_eq_right hp1,
      max_eq_right (show 0 ≤ t - 2 by linarith), min_eq_left (show 1 ≤ t by linarith),
      max_eq_left (show 1 - (t - 1) ≤ 0 by linarith)] <;> ring

theorem unitSumSplineDensity_nonneg (n : ℕ) (hn : 2 ≤ n) :
    ∀ t : ℝ, 0 ≤ unitSumSplineDensity n t := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro t
      rw [unitSumSplineDensity_two_overlap]
      exact le_max_left _ _
  | succ n hn ih =>
      intro t
      rw [← unitSumSplineDensity_window n hn t]
      exact intervalIntegral.integral_nonneg_of_forall (by linarith) ih

theorem unitSumSplineDensity_le_one (n : ℕ) (hn : 2 ≤ n) :
    ∀ t : ℝ, unitSumSplineDensity n t ≤ 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro t
      rw [unitSumSplineDensity_two_overlap]
      apply max_le (by norm_num)
      linarith [min_le_left (1 : ℝ) t, le_max_left (0 : ℝ) (t - 1)]
  | succ n hn ih =>
      intro t
      rw [← unitSumSplineDensity_window n hn t]
      have h := intervalIntegral.integral_mono (μ := volume)
        (f := unitSumSplineDensity n) (g := fun _ : ℝ => (1 : ℝ)) (a := t - 1) (b := t)
        (by linarith) ((continuous_unitSumSplineDensity n).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) ih
      simpa using h

theorem unitSumSplineDensity_eq_zero_of_not_mem (n : ℕ) (hn : 2 ≤ n) :
    ∀ t : ℝ, t ∉ Icc 0 (n : ℝ) → unitSumSplineDensity n t = 0 := by
  induction n, hn using Nat.le_induction with
  | base =>
      intro t ht
      have ht' : t < 0 ∨ (2 : ℝ) < t := by
        simpa only [Nat.cast_ofNat, mem_Icc, not_and_or, not_le] using ht
      rw [unitSumSplineDensity_two_overlap]
      apply max_eq_left
      rcases ht' with ht' | ht'
      · linarith [min_le_right (1 : ℝ) t, le_max_left (0 : ℝ) (t - 1)]
      · linarith [min_le_left (1 : ℝ) t, le_max_right (0 : ℝ) (t - 1)]
  | succ n hn ih =>
      intro t ht
      have ht' : t < 0 ∨ (n : ℝ) + 1 < t := by
        simpa only [Nat.cast_add, Nat.cast_one, mem_Icc, not_and_or, not_le] using ht
      rw [← unitSumSplineDensity_window n hn t]
      calc
        _ = ∫ y in (t - 1)..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          rw [uIcc_of_le (by linarith : t - 1 ≤ t)] at hy
          apply ih y
          intro hyn
          rcases ht' with ht' | ht'
          · linarith [hy.2, hyn.1]
          · linarith [hy.1, hyn.2]
        _ = 0 := by simp

theorem hasCompactSupport_unitSumSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    HasCompactSupport (unitSumSplineDensity n) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 (n : ℝ)) isCompact_Icc
  intro t ht
  by_contra hnot
  exact ht (unitSumSplineDensity_eq_zero_of_not_mem n hn t hnot)

theorem integrable_unitSumSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    Integrable (unitSumSplineDensity n) volume :=
  (continuous_unitSumSplineDensity n).integrable_of_hasCompactSupport
    (hasCompactSupport_unitSumSplineDensity n hn)

end
end ENT.Spline
