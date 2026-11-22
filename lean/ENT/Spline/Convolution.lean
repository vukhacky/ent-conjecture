module

public import ENT.Spline.DensityProperties
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! The exact ENNReal convolution bridge needed by the probability-law induction. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ENT.Spline

noncomputable section

theorem unitInterval_lconvolution (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    lconvolution ((Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
      (fun y => ENNReal.ofReal (unitSumSplineDensity n y)) volume t =
      ENNReal.ofReal (unitSumSplineDensity (n + 1) t) := by
  have hfun :
      (fun y : ℝ => (Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) y *
        ENNReal.ofReal (unitSumSplineDensity n (-y + t))) =
      (Icc (0 : ℝ) 1).indicator
        (fun y => ENNReal.ofReal (unitSumSplineDensity n (t - y))) := by
    funext y
    by_cases hy : y ∈ Icc (0 : ℝ) 1 <;>
      simp [hy, sub_eq_add_neg, add_comm]
  rw [lconvolution_def, hfun, lintegral_indicator measurableSet_Icc]
  have hcont : Continuous (fun y : ℝ => unitSumSplineDensity n (t - y)) :=
    (continuous_unitSumSplineDensity n).comp (continuous_const.sub continuous_id)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (Filter.Eventually.of_forall (fun y => unitSumSplineDensity_nonneg n hn (t - y)))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left]
  simpa using unitSumSplineDensity_window n hn t

theorem unitInterval_conv_splineDensity (n : ℕ) (hn : 2 ≤ n) :
    Measure.conv ((volume : Measure ℝ).restrict (Icc 0 1))
      (volume.withDensity (fun y => ENNReal.ofReal (unitSumSplineDensity n y))) =
      volume.withDensity (fun y => ENNReal.ofReal (unitSumSplineDensity (n + 1) y)) := by
  have hunit : (volume : Measure ℝ).restrict (Icc 0 1) =
      volume.withDensity ((Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ≥0∞))) := by
    rw [withDensity_indicator measurableSet_Icc, withDensity_const, one_smul]
  rw [hunit, conv_withDensity_eq_lconvolution
    (measurable_const.indicator measurableSet_Icc)
    (continuous_unitSumSplineDensity n).measurable.ennreal_ofReal]
  congr 1
  funext t
  exact unitInterval_lconvolution n hn t

end
end ENT.Spline
