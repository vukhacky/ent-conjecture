module

public import ENT.Basic.Uniform
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The genuine density and entropy of a positive multiple of a unit uniform variable. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

theorem uniformUnit_map_mul_pos {c : ℝ} (hc : 0 < c) :
    uniformUnit.map (fun x => c * x) =
      ENNReal.ofReal ((2 * c)⁻¹) • volume.restrict (Set.Icc (-c) c) := by
  have hpre : (fun x : ℝ => c * x) ⁻¹' Set.Icc (-c) c = Set.Icc (-1) 1 := by
    rw [Set.preimage_const_mul_Icc₀ _ _ hc]
    simp [hc.ne']
  have hmap : ((volume : Measure ℝ).restrict (Set.Icc (-1) 1)).map
      (fun x => c * x) = ENNReal.ofReal c⁻¹ • volume.restrict (Set.Icc (-c) c) := by
    calc
      _ = ((volume : Measure ℝ).map (fun x => c * x)).restrict (Set.Icc (-c) c) := by
        rw [Measure.restrict_map (measurable_const_mul c) measurableSet_Icc, hpre]
      _ = _ := by
        rw [Real.map_volume_mul_left hc.ne', Measure.restrict_smul,
          abs_of_pos (inv_pos.mpr hc)]
  unfold uniformUnit
  rw [Measure.map_smul _ (measurable_const_mul c).aemeasurable, hmap, smul_smul]
  have hhalf : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 : ℝ)⁻¹) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  rw [hhalf, ← ENNReal.ofReal_mul (by positivity)]
  simp only [mul_inv]

def scaledUniformDensity (c : ℝ) : ℝ → ℝ :=
  (Set.Icc (-c) c).indicator (fun _ : ℝ => (2 * c)⁻¹)

theorem scaledUniformDensity_nonneg {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 ≤ scaledUniformDensity c x := by
  by_cases hx : x ∈ Set.Icc (-c) c
  · simp only [scaledUniformDensity, Set.indicator_of_mem hx]
    positivity
  · simp [scaledUniformDensity, hx]

theorem scaledUniformDensity_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    scaledUniformDensity c x ≤ (2 * c)⁻¹ := by
  by_cases hx : x ∈ Set.Icc (-c) c
  · simp only [scaledUniformDensity, Set.indicator_of_mem hx, le_refl]
  · simp only [scaledUniformDensity, Set.indicator_of_notMem hx]
    positivity

theorem scaledUniformDensity_eq_zero_of_not_mem (c x : ℝ)
    (hx : x ∉ Set.Icc (-c) c) : scaledUniformDensity c x = 0 := by
  simp only [scaledUniformDensity, Set.indicator_of_notMem hx]

theorem measurable_scaledUniformDensity (c : ℝ) : Measurable (scaledUniformDensity c) :=
  measurable_const.indicator measurableSet_Icc

theorem integrable_scaledUniformDensity (c : ℝ) :
    Integrable (scaledUniformDensity c) volume := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp [Real.volume_Icc])

theorem integral_scaledUniformDensity {c : ℝ} (hc : 0 < c) :
    (∫ x, scaledUniformDensity c x) = 1 := by
  rw [scaledUniformDensity, integral_indicator_const _ measurableSet_Icc]
  simp only [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ c - -c), smul_eq_mul]
  rw [show c - -c = 2 * c by ring, mul_inv_cancel₀ (by positivity)]

theorem scaledUniformDensity_law {c : ℝ} (hc : 0 < c) :
    uniformUnit.map (fun x => c * x) =
      volume.withDensity (fun x => ENNReal.ofReal (scaledUniformDensity c x)) := by
  have h : (fun x => ENNReal.ofReal (scaledUniformDensity c x)) =
      (Set.Icc (-c) c).indicator (fun _ : ℝ => ENNReal.ofReal ((2 * c)⁻¹)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-c) c <;> simp [scaledUniformDensity, hx]
  rw [h, withDensity_indicator measurableSet_Icc, withDensity_const]
  exact uniformUnit_map_mul_pos hc

theorem scaledUniformDensity_mul_log (c : ℝ) :
    (fun x => scaledUniformDensity c x * Real.log (scaledUniformDensity c x)) =
      (Set.Icc (-c) c).indicator
        (fun _ : ℝ => (2 * c)⁻¹ * Real.log ((2 * c)⁻¹)) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-c) c <;> simp [scaledUniformDensity, hx]

theorem integrable_scaledUniformDensity_mul_log (c : ℝ) :
    Integrable (fun x => scaledUniformDensity c x * Real.log (scaledUniformDensity c x))
      volume := by
  rw [scaledUniformDensity_mul_log]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (by simp [Real.volume_Icc])

def scaledUniformFiniteEntropyDensity (c : ℝ) (hc : 0 < c) :
    FiniteEntropyDensity (uniformUnit.map (fun x => c * x)) where
  density := scaledUniformDensity c
  nonneg := scaledUniformDensity_nonneg hc
  measurable := measurable_scaledUniformDensity c
  integrable := integrable_scaledUniformDensity c
  mass_one := integral_scaledUniformDensity hc
  law_eq := scaledUniformDensity_law hc
  entropy_integrable := integrable_scaledUniformDensity_mul_log c

@[simp]
theorem scaledUniformFiniteEntropyDensity_entropy (c : ℝ) (hc : 0 < c) :
    (scaledUniformFiniteEntropyDensity c hc).entropy = Real.log (2 * c) := by
  change -(∫ x, scaledUniformDensity c x * Real.log (scaledUniformDensity c x)) = _
  rw [scaledUniformDensity_mul_log, integral_indicator_const _ measurableSet_Icc]
  simp only [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ c - -c), smul_eq_mul]
  rw [show c - -c = 2 * c by ring, ← mul_assoc, mul_inv_cancel₀ (by positivity),
    one_mul, Real.log_inv, neg_neg]

end
end ENT
