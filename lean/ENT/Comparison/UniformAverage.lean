module

public import ENT.Comparison.DensityExpectations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Averaging a potential against one continuous uniform variable. The operator
is an actual probability integral; its finite-difference derivative follows
from FTC, with all changes of variables justified. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped Interval

namespace ENT.Comparison
noncomputable section

def uniformAverage (b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u, g (x + b * u) ∂uniformUnit

def uniformDifference (b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (g (x + b) - g (x - b)) / (2 * b)

@[simp] theorem uniformAverage_zero (g : ℝ → ℝ) (x : ℝ) :
    uniformAverage 0 g x = g x := by simp [uniformAverage]

theorem uniformAverage_norm_le {g : ℝ → ℝ} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (b x : ℝ) : ‖uniformAverage b g x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const
    (μ := uniformUnit) (Filter.Eventually.of_forall (fun u => hC (x + b * u)))
  simpa only [uniformAverage, measureReal_def, uniformUnit_univ, ENNReal.toReal_one, mul_one] using h

theorem continuous_uniformAverage {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (b : ℝ) : Continuous (uniformAverage b g) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (hg.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun u => hC (x + b * u))
  · exact integrable_const C
  · apply Filter.Eventually.of_forall
    intro u
    exact hg.comp (by fun_prop)

theorem uniformAverage_even {g : ℝ → ℝ} (hg : Continuous g)
    (heven : ∀ x, g (-x) = g x) (b x : ℝ) :
    uniformAverage b g (-x) = uniformAverage b g x := by
  have hmap := integral_map (μ := uniformUnit) measurable_neg.aemeasurable
    (f := fun u => g (-x + b * u)) (hg.comp (by fun_prop)).aestronglyMeasurable
  rw [uniformUnit_map_neg] at hmap
  unfold uniformAverage
  rw [hmap]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  change g (-x + b * -u) = g (x + b * u)
  rw [show -x + b * -u = -(x + b * u) by ring, heven]

theorem uniformAverage_eq_interval {b : ℝ} (hb : 0 < b) {g : ℝ → ℝ}
    (hg : Continuous g) (x : ℝ) :
    uniformAverage b g x = (∫ y in x - b..x + b, g y) / (2 * b) := by
  have hmap := integral_map (μ := uniformUnit) (measurable_const_mul b).aemeasurable
    (f := fun y => g (x + y)) (hg.comp (by fun_prop)).aestronglyMeasurable
  rw [uniformUnit_map_mul_pos hb, integral_smul_measure] at hmap
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * b)⁻¹), smul_eq_mul] at hmap
  unfold uniformAverage
  rw [← hmap, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -b ≤ b),
    intervalIntegral.integral_comp_add_left]
  rw [show x + -b = x - b by ring]
  ring

theorem hasDerivAt_uniformAverage {b : ℝ} (hb : 0 < b) {g : ℝ → ℝ}
    (hg : Continuous g) (x : ℝ) :
    HasDerivAt (uniformAverage b g) (uniformDifference b g x) x := by
  have heq : uniformAverage b g = fun y =>
      ((∫ t in 0..y + b, g t) - ∫ t in 0..y - b, g t) / (2 * b) := by
    funext y
    rw [uniformAverage_eq_interval hb hg,
      intervalIntegral.integral_interval_sub_left
        (hg.intervalIntegrable 0 (y + b)) (hg.intervalIntegrable 0 (y - b))]
  rw [heq]
  have hp := (hg.integral_hasStrictDerivAt 0 (x + b)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const b)
  have hm := (hg.integral_hasStrictDerivAt 0 (x - b)).hasDerivAt.comp x
    ((hasDerivAt_id x).sub_const b)
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, mul_one, uniformDifference] using
    (hp.sub hm).div_const (2 * b)

theorem continuous_uniformDifference {g : ℝ → ℝ} (hg : Continuous g) (b : ℝ) :
    Continuous (uniformDifference b g) := by
  unfold uniformDifference
  exact ((hg.comp (continuous_id.add_const b)).sub
    (hg.comp (continuous_id.sub continuous_const))).div_const _

theorem hasDerivAt_uniformDifference {g g' : ℝ → ℝ} {b x : ℝ}
    (hp : HasDerivAt g (g' (x + b)) (x + b))
    (hm : HasDerivAt g (g' (x - b)) (x - b)) :
    HasDerivAt (uniformDifference b g) (uniformDifference b g' x) x := by
  change HasDerivAt (fun y : ℝ => (g (y + b) - g (y - b)) / (2 * b))
    ((g' (x + b) - g' (x - b)) / (2 * b)) x
  have hp' := hp.comp x ((hasDerivAt_id x).add_const b)
  have hm' := hm.comp x ((hasDerivAt_id x).sub_const b)
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, mul_one, uniformDifference] using
    (hp'.sub hm').div_const (2 * b)

end
end ENT.Comparison
