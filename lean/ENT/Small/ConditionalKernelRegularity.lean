module

public import ENT.Small.ConditionalKernelFormula
public import ENT.Spline.Symmetry

/-! Smoothness, support and symmetry of the actual weighted convolution kernel. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ContDiff

namespace ENT.Small
noncomputable section
open Spline

theorem contDiff_coordinateSquareKernel (r n : ℕ) (hn : 3 ≤ n) (hr : r < n - 1) :
    ContDiff ℝ r (coordinateSquareKernel n) := by
  have heq : coordinateSquareKernel n = coordinateSquareKernelFormula n :=
    funext (coordinateSquareKernel_eq_formula n hn)
  rw [heq]
  unfold coordinateSquareKernelFormula quadraticPowerPrimitive
  apply contDiff_const.mul
  apply ContDiff.sum
  intro j _
  have h1 := contDiff_positivePower r (n - 2 + 1) (by omega)
  have h2 := contDiff_positivePower r (n - 2 + 2) (by omega)
  have h3 := contDiff_positivePower r (n - 2 + 3) (by omega)
  fun_prop

theorem continuous_coordinateSquareKernel (n : ℕ) (hn : 3 ≤ n) :
    Continuous (coordinateSquareKernel n) :=
  (contDiff_coordinateSquareKernel 0 n hn (by omega)).continuous

theorem contDiff_varianceKernel (r n : ℕ) (hn : 3 ≤ n) (hr : r < n - 1) :
    ContDiff ℝ r (varianceKernel n) := by
  unfold varianceKernel
  exact ((contDiff_const.mul (contDiff_coordinateSquareKernel r n hn hr)).sub
    ((((contDiff_const.sub (contDiff_const.mul contDiff_id)).pow 2).div_const (n : ℝ)).mul
      (contDiff_unitSumSplineDensity r n hr))).div_const ((n : ℝ) - 1)

theorem coordinateSquareKernel_reflection (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    coordinateSquareKernel n ((n : ℝ) - t) = coordinateSquareKernel n t := by
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold coordinateSquareKernel
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (1 - 2 * (1 - x)) ^ 2 * unitSumSplineDensity (n - 1) (t - (1 - x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [show (n : ℝ) - t - x = ((n - 1 : ℕ) : ℝ) - (t - (1 - x)) by rw [hn1]; ring,
        unitSumSplineDensity_reflection (n - 1) (by omega)]
      congr 1
      ring
    _ = _ := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun x => (1 - 2 * x) ^ 2 * unitSumSplineDensity (n - 1) (t - x))
        (a := (0 : ℝ)) (b := (1 : ℝ)) 1
      simpa only [sub_self, sub_zero] using h

theorem varianceKernel_reflection (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    varianceKernel n ((n : ℝ) - t) = varianceKernel n t := by
  simp only [varianceKernel, coordinateSquareKernel_reflection n hn,
    unitSumSplineDensity_reflection n (by omega)]
  ring

theorem coordinateSquareKernel_eq_zero_of_not_mem (n : ℕ) (hn : 3 ≤ n)
    (t : ℝ) (ht : t ∉ Icc (0 : ℝ) n) : coordinateSquareKernel n t = 0 := by
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have ht' : t < 0 ∨ (n : ℝ) < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
  unfold coordinateSquareKernel
  calc
    _ = ∫ x in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [unitSumSplineDensity_eq_zero_of_not_mem (n - 1) (by omega) (t - x) (by
        intro hmem
        rw [mem_Icc, hn1] at hmem
        rcases ht' with ht' | ht' <;> linarith [hx.1, hx.2, hmem.1, hmem.2])]
      ring
    _ = 0 := by simp

theorem varianceKernel_eq_zero_of_not_mem (n : ℕ) (hn : 3 ≤ n)
    (t : ℝ) (ht : t ∉ Icc (0 : ℝ) n) : varianceKernel n t = 0 := by
  rw [varianceKernel, coordinateSquareKernel_eq_zero_of_not_mem n hn t ht,
    unitSumSplineDensity_eq_zero_of_not_mem n (by omega) t ht]
  ring

theorem hasCompactSupport_varianceKernel (n : ℕ) (hn : 3 ≤ n) :
    HasCompactSupport (varianceKernel n) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 (n : ℝ)) isCompact_Icc
  intro t ht
  by_contra hnot
  exact ht (varianceKernel_eq_zero_of_not_mem n hn t hnot)

theorem integrable_varianceKernel (n : ℕ) (hn : 3 ≤ n) :
    Integrable (varianceKernel n) volume :=
  (contDiff_varianceKernel 0 n hn (by omega)).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_varianceKernel n hn)

theorem coordinateSquareKernel_le_density (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    coordinateSquareKernel n t ≤ unitSumSplineDensity n t := by
  have hfn : Continuous (fun x : ℝ => unitSumSplineDensity (n - 1) (t - x)) :=
    (continuous_unitSumSplineDensity (n - 1)).comp (continuous_const.sub continuous_id)
  have hw : Continuous (fun x : ℝ => (1 - 2 * x) ^ 2 * unitSumSplineDensity (n - 1) (t - x)) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).pow 2).mul hfn
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, unitSumSplineDensity (n - 1) (t - x) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hw.intervalIntegrable 0 1) (hfn.intervalIntegrable 0 1)
      intro x hx
      have hweight : (1 - 2 * x) ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight
        (unitSumSplineDensity_nonneg (n - 1) (by omega) (t - x))
    _ = _ := by
      rw [intervalIntegral.integral_comp_sub_left]
      simpa only [sub_zero, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        unitSumSplineDensity_window (n - 1) (by omega) t

end
end ENT.Small
