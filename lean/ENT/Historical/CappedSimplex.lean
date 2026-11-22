module

public import ENT.Historical.SimplexMarginal
public import ENT.Historical.CappedConvexOrder
public import ENT.Historical.SplineRatioTwo
public import ENT.Historical.SplineFirstMoment

/-! Convex domination of the actual capped-simplex coordinate marginal by the
uncapped simplex coordinate marginal. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Historical
noncomputable section
open Spline

theorem cappedMarginalDensity_eq_indicator_min (n : ℕ) (hn : 3 ≤ n) (s x : ℝ) :
    cappedMarginalDensity n s x = (Icc (0 : ℝ) (min 1 s)).indicator
      (fun x => unitSumSplineDensity (n - 1) (s - x) / unitSumSplineDensity n s) x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · by_cases hxs : x ≤ s
    · have hx' : x ∈ Icc (0 : ℝ) (min 1 s) := ⟨hx.1, le_min hx.2 hxs⟩
      simp [cappedMarginalDensity, coordinateSlice, hx, hx']
    · have hzero : unitSumSplineDensity (n - 1) (s - x) = 0 :=
        unitSumSplineDensity_eq_zero_of_not_mem _ (by omega) _ (by
          intro h
          exact hxs (by linarith [h.1]))
      simp [cappedMarginalDensity, coordinateSlice, hx, hxs, hzero]
  · have hx' : x ∉ Icc (0 : ℝ) (min 1 s) :=
      fun h => hx ⟨h.1, h.2.trans (min_le_left _ _)⟩
    simp [cappedMarginalDensity, coordinateSlice, hx, hx']

theorem cappedMarginalDensity_eq_zero (n : ℕ) (hn : 3 ≤ n) (s x : ℝ)
    (hx : x ∉ Icc (0 : ℝ) (min 1 s)) : cappedMarginalDensity n s x = 0 := by
  rw [cappedMarginalDensity_eq_indicator_min n hn s x, indicator_of_notMem hx]

theorem cappedMarginalDensity_test_integrable (n : ℕ) (hn : 3 ≤ n) (s : ℝ)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 s)) :
    Integrable (fun x => φ x * cappedMarginalDensity n s x) volume := by
  have hφ' : ContinuousOn φ (Icc 0 (min 1 s)) :=
    hφ.mono (fun x hx => ⟨hx.1, hx.2.trans (min_le_right _ _)⟩)
  have hc : Continuous (fun x : ℝ => unitSumSplineDensity (n - 1) (s - x) /
      unitSumSplineDensity n s) :=
    ((continuous_unitSumSplineDensity _).comp
      (continuous_const.sub continuous_id)).div_const _
  have hi := (hφ'.mul hc.continuousOn).integrableOn_compact (μ := volume) isCompact_Icc
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext x
  rw [cappedMarginalDensity_eq_indicator_min n hn]
  by_cases hx : x ∈ Icc (0 : ℝ) (min 1 s) <;> simp [hx]

theorem cappedMarginalDensity_integral_test (n : ℕ) (s : ℝ) (φ : ℝ → ℝ) :
    (∫ x, φ x * cappedMarginalDensity n s x) =
      (∫ x in (0 : ℝ)..1, φ x * unitSumSplineDensity (n - 1) (s - x)) /
        unitSumSplineDensity n s := by
  have hfun : (fun x => φ x * cappedMarginalDensity n s x) =
      (Icc (0 : ℝ) 1).indicator
        (fun x => (φ x * unitSumSplineDensity (n - 1) (s - x)) /
          unitSumSplineDensity n s) := by
    ext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
      simp [cappedMarginalDensity, coordinateSlice, hx, mul_div_assoc]
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_div]

theorem cappedMarginalDensity_mean (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) :
    (∫ x, x * cappedMarginalDensity n s x) = s / n := by
  rw [cappedMarginalDensity_integral_test]
  change coordinateFirstSlice n s / unitSumSplineDensity n s = _
  rw [coordinateFirstSlice_eq n hn s]
  exact mul_div_cancel_right₀ _ (unitSumSplineDensity_pos n (by omega) s hs.1 hs.2).ne'

theorem capped_to_simplex_ratio (n : ℕ) (hn : 3 ≤ n) {s x : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) (hx : x ∈ Ioo (0 : ℝ) (min 1 s)) :
    cappedMarginalDensity n s x / simplexMarginalDensity n s x =
      (s ^ (n - 1) / (((n : ℝ) - 1) * unitSumSplineDensity n s)) *
        (unitSumSplineDensity (n - 1) (s - x) / (s - x) ^ (n - 2)) := by
  have hx1 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, (hx.2.trans_le (min_le_left _ _)).le⟩
  have hxs : x ∈ Icc (0 : ℝ) s := ⟨hx.1.le, (hx.2.trans_le (min_le_right _ _)).le⟩
  simp only [cappedMarginalDensity, coordinateSlice, simplexMarginalDensity,
    indicator_of_mem hx1, indicator_of_mem hxs]
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hf0 := (unitSumSplineDensity_pos n (by omega) s hs.1 hs.2).ne'
  have hsp : s ^ (n - 1) ≠ 0 := pow_ne_zero _ hs.1.ne'
  have hxp : (s - x) ^ (n - 2) ≠ 0 := pow_ne_zero _
    (sub_pos.mpr (hx.2.trans_le (min_le_right _ _))).ne'
  field_simp

theorem capped_to_simplex_ratio_monotone (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) :
    MonotoneOn (fun x => cappedMarginalDensity n s x / simplexMarginalDensity n s x)
      (Ioo (0 : ℝ) (min 1 s)) := by
  intro x hx y hy hxy
  change cappedMarginalDensity n s x / simplexMarginalDensity n s x ≤
    cappedMarginalDensity n s y / simplexMarginalDensity n s y
  rw [capped_to_simplex_ratio n (by omega) hs hx, capped_to_simplex_ratio n (by omega) hs hy]
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (pow_nonneg hs.1.le _)
      (mul_nonneg (by linarith) (unitSumSplineDensity_nonneg n (by omega) s)))
  have h := spline_div_power_antitone_ge_two (n := n - 1) (by omega)
    (x := s - y) (y := s - x)
    (by linarith [hy.2.trans_le (min_le_right (1 : ℝ) s)]) (by linarith)
  simpa only [show n - 1 - 1 = n - 2 by omega] using h

theorem cappedMarginal_convexOrder (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Icc 0 s) φ) (hφcont : ContinuousOn φ (Icc 0 s)) :
    (∫ x, φ x * cappedMarginalDensity n s x) ≤
      ∫ x, φ x * simplexMarginalDensity n s x := by
  apply convex_integral_le_of_capped_monotone_ratio
    (lt_min (by norm_num) hs.1) (min_le_right (1 : ℝ) s)
    (cappedMarginalDensity_nonneg n (by omega) s)
    (simplexMarginalDensity_nonneg n (by omega) hs.1)
    (cappedMarginalDensity_eq_zero n (by omega) s)
    (fun _ hx => simplexMarginalDensity_eq_zero hx)
    (fun x hx => simplexMarginalDensity_pos n (by omega) hs.1
      ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩)
    (capped_to_simplex_ratio_monotone n hn hs)
    (cappedMarginalDensity_integrable n s) (simplexMarginalDensity_integrable n s)
    (cappedMarginalDensity_test_integrable n (by omega) s continuous_id.continuousOn)
    (simplexMarginalDensity_test_integrable n s continuous_id.continuousOn)
    (cappedMarginalDensity_test_integrable n (by omega) s hφcont)
    (simplexMarginalDensity_test_integrable n s hφcont)
  · rw [cappedMarginalDensity_mass n (by omega) hs,
      simplexMarginalDensity_mass n (by omega) hs.1]
  · rw [cappedMarginalDensity_mean n (by omega) hs,
      simplexMarginalDensity_mean n (by omega) hs.1]
  · exact hφ

theorem cappedMarginal_second_moment_le (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) :
    (∫ x, x ^ 2 * cappedMarginalDensity n s x) ≤ 2 * s ^ 2 / ((n : ℝ) * (n + 1)) := by
  rw [← simplexMarginalDensity_second_moment n (by omega) hs.1]
  apply cappedMarginal_convexOrder n hn hs
  · exact (convexOn_pow (n := 2)).subset (by intro x hx; exact hx.1) (convex_Icc _ _)
  · fun_prop

end
end ENT.Historical
