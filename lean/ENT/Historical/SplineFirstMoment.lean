module

public import ENT.Historical.SplineEuler
public import Mathlib.Analysis.Calculus.MeanValue

/-! Pointwise first moment of the genuine capped coordinate slice.
The proof uses the Euler recurrence and the fundamental theorem of calculus,
so the conditional mean does not rely on selecting a density representative. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace ENT.Spline
noncomputable section

theorem continuous_window_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y in (t-1)..t, f y) (f x - f (x-1)) x := by
  have hF (t : ℝ) : HasDerivAt (fun s : ℝ => ∫ y in (0:ℝ)..s, f y) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have h := (hF x).sub ((hF (x-1)).comp x ((hasDerivAt_id x).sub_const 1))
  convert h using 1
  · funext t
    change (∫ y in (t-1)..t, f y) =
      (∫ y in (0:ℝ)..t, f y) - (∫ y in (0:ℝ)..(t-1), f y)
    have hi : (∫ y in (0:ℝ)..(t-1), f y) + (∫ y in (t-1)..t, f y) =
        ∫ y in (0:ℝ)..t, f y := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0:ℝ) (t-1)) (hf.intervalIntegrable (t-1) t)
    linarith
  · simp

theorem unitSumSplineDensity_hasDerivAt_window (n : ℕ) (hn : 3 ≤ n) (x : ℝ) :
    HasDerivAt (unitSumSplineDensity n)
      (unitSumSplineDensity (n-1) x - unitSumSplineDensity (n-1) (x-1)) x := by
  have h := continuous_window_hasDerivAt (unitSumSplineDensity (n-1))
    (continuous_unitSumSplineDensity (n-1)) x
  convert h using 1
  funext t
  rw [unitSumSplineDensity_window (n-1) (by omega), Nat.sub_add_cancel (by omega : 1 ≤ n)]

def coordinateFirstSlice (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, x * unitSumSplineDensity (n-1) (s-x)

theorem coordinateFirstSlice_window (n : ℕ) (hn : 3 ≤ n) (s : ℝ) :
    coordinateFirstSlice n s = s*unitSumSplineDensity n s -
      ∫ y in (s-1)..s, y*unitSumSplineDensity (n-1) y := by
  unfold coordinateFirstSlice
  calc
    _ = ∫ x in (0:ℝ)..1, (fun y => (s-y)*unitSumSplineDensity (n-1) y) (s-x) := by
      congr 1
      funext x
      ring
    _ = ∫ y in (s-1)..s, (s-y)*unitSumSplineDensity (n-1) y := by
      simpa only [sub_zero] using intervalIntegral.integral_comp_sub_left
        (fun y : ℝ => (s-y)*unitSumSplineDensity (n-1) y) (a := (0:ℝ)) (b := 1) s
    _ = _ := by
      have he : (fun y => (s-y)*unitSumSplineDensity (n-1) y) =
          (fun y => s*unitSumSplineDensity (n-1) y - y*unitSumSplineDensity (n-1) y) := by
        funext y
        ring
      have hf : IntervalIntegrable (fun y : ℝ => s*unitSumSplineDensity (n-1) y) volume (s-1) s :=
        (continuous_const.mul (continuous_unitSumSplineDensity (n-1))).intervalIntegrable _ _
      have hg : IntervalIntegrable (fun y : ℝ => y*unitSumSplineDensity (n-1) y) volume (s-1) s :=
        (continuous_id.mul (continuous_unitSumSplineDensity (n-1))).intervalIntegrable _ _
      rw [he, intervalIntegral.integral_sub hf hg,
        intervalIntegral.integral_const_mul,
        unitSumSplineDensity_window (n-1) (by omega),
        Nat.sub_add_cancel (by omega : 1 ≤ n)]

theorem coordinateFirstSlice_eq (n : ℕ) (hn : 3 ≤ n) (s : ℝ) :
    coordinateFirstSlice n s = (s/(n:ℝ))*unitSumSplineDensity n s := by
  let E : ℝ → ℝ := fun t => t*unitSumSplineDensity n t -
    (∫ y in (t-1)..t, y*unitSumSplineDensity (n-1) y) -
    (t/(n:ℝ))*unitSumSplineDensity n t
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hd (t : ℝ) : HasDerivAt E 0 t := by
    have hf := unitSumSplineDensity_hasDerivAt_window n hn t
    have hM := continuous_window_hasDerivAt (fun y => y*unitSumSplineDensity (n-1) y)
      (continuous_id.mul (continuous_unitSumSplineDensity (n-1))) t
    have h := (((hasDerivAt_id t).mul hf).sub hM).sub
      (((hasDerivAt_id t).div_const (n:ℝ)).mul hf)
    have he := unitSumSplineDensity_euler n hn t
    rw [hf.deriv] at he
    convert h using 1
    · rfl
    · simp only [id_eq, one_mul]
      field_simp
      nlinarith [he]
  have hconst := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s 0
  have hi : (∫ y in (-1:ℝ)..0, y*unitSumSplineDensity (n-1) y) = 0 := by
    calc
      _ = ∫ y in (-1:ℝ)..0, (0:ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro y hy
        change y*unitSumSplineDensity (n-1) y = 0
        rw [unitSumSplineDensity_eq_zero_of_not_mem (n-1) (by omega) y
          (by intro hmem; linarith [hmem.1, hy.2]), mul_zero]
      _ = 0 := by simp
  have hE0 : E 0 = 0 := by simp [E, hi]
  rw [hE0] at hconst
  rw [coordinateFirstSlice_window n hn]
  change _ - _ - _ = 0 at hconst
  linarith

end
end ENT.Spline
