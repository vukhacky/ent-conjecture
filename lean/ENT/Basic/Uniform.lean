module

public import ENT.Statement
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! The canonical uniform and product laws and the density of the unit interval. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ENT

noncomputable section

@[simp]
theorem uniformUnit_univ : uniformUnit Set.univ = 1 := by
  norm_num [uniformUnit, smul_apply, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

instance uniformUnit_isProbabilityMeasure : IsProbabilityMeasure uniformUnit :=
  ⟨uniformUnit_univ⟩

instance cubeLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (cubeLaw n) := by
  unfold cubeLaw
  infer_instance

theorem continuous_projection {n : ℕ} (a : Fin n → ℝ) : Continuous (projection a) := by
  unfold projection
  fun_prop

theorem measurable_projection {n : ℕ} (a : Fin n → ℝ) : Measurable (projection a) :=
  (continuous_projection a).measurable

instance projectionLaw_isProbabilityMeasure {n : ℕ} (a : Fin n → ℝ) :
    IsProbabilityMeasure (projectionLaw a) := by
  unfold projectionLaw
  infer_instance

theorem uniformUnit_map_neg :
    uniformUnit.map (fun x : ℝ => -x) = uniformUnit := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Icc (-1) 1 = Set.Icc (-1) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume := by
    refine ⟨measurable_neg, ?_⟩
    simpa using (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  have hpres := hneg.restrict_preimage
    (s := Set.Icc (-1) 1) measurableSet_Icc
  rw [hpre] at hpres
  unfold uniformUnit
  rw [Measure.map_smul _ measurable_neg.aemeasurable, hpres.map_eq]

theorem cubeLaw_map_coordinate (n : ℕ) (i : Fin n) :
    (cubeLaw n).map (fun x : Fin n → ℝ => x i) = uniformUnit := by
  exact (measurePreserving_eval (fun _ : Fin n => uniformUnit) i).map_eq

def uniformDensity : ℝ → ℝ :=
  (Set.Icc (-1) 1).indicator (fun _ : ℝ => (1 / 2 : ℝ))

theorem uniformDensity_nonneg (x : ℝ) : 0 ≤ uniformDensity x := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [uniformDensity, hx]

theorem measurable_uniformDensity : Measurable uniformDensity := by
  exact measurable_const.indicator measurableSet_Icc

theorem integrable_uniformDensity : Integrable uniformDensity volume := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp [Real.volume_Icc])

@[simp]
theorem integral_uniformDensity : (∫ x, uniformDensity x) = 1 := by
  rw [uniformDensity, integral_indicator_const _ measurableSet_Icc]
  norm_num [measureReal_def, Real.volume_Icc]

theorem uniformDensity_law :
    uniformUnit = volume.withDensity (fun x => ENNReal.ofReal (uniformDensity x)) := by
  have h : (fun x => ENNReal.ofReal (uniformDensity x)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [uniformDensity, hx]
  rw [h, withDensity_indicator measurableSet_Icc, withDensity_const]
  rfl

theorem uniformDensity_mul_log :
    (fun x => uniformDensity x * Real.log (uniformDensity x)) =
      (Set.Icc (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [uniformDensity, hx]

theorem integrable_uniformDensity_mul_log :
    Integrable (fun x => uniformDensity x * Real.log (uniformDensity x)) volume := by
  rw [uniformDensity_mul_log]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp [Real.volume_Icc])

def uniformFiniteEntropyDensity : FiniteEntropyDensity uniformUnit where
  density := uniformDensity
  nonneg := uniformDensity_nonneg
  measurable := measurable_uniformDensity
  integrable := integrable_uniformDensity
  mass_one := integral_uniformDensity
  law_eq := uniformDensity_law
  entropy_integrable := integrable_uniformDensity_mul_log

@[simp]
theorem uniformFiniteEntropyDensity_entropy :
    uniformFiniteEntropyDensity.entropy = Real.log 2 := by
  change -(∫ x, uniformDensity x * Real.log (uniformDensity x)) = Real.log 2
  rw [uniformDensity_mul_log, integral_indicator_const _ measurableSet_Icc]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  norm_num [measureReal_def, Real.volume_Icc, hlog]
  ring

end
end ENT
