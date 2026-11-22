module

public import ENT.Basic.Uniform
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! The continuous uniform law on [0,1] and its twofold convolution density. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ENT

noncomputable section

def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

@[simp]
theorem uniform01_univ : uniform01 Set.univ = 1 := by
  norm_num [uniform01, Real.volume_Icc]

instance uniform01_isProbabilityMeasure : IsProbabilityMeasure uniform01 :=
  ⟨uniform01_univ⟩

def toUnit (x : ℝ) : ℝ := (1 - x) / 2

theorem measurable_toUnit : Measurable toUnit := by
  unfold toUnit
  fun_prop

theorem volume_map_toUnit : (volume : Measure ℝ).map toUnit = (2 : ℝ≥0∞) • volume := by
  have hfun : toUnit = (fun y : ℝ => (1 / 2 : ℝ) + y) ∘
      (fun x : ℝ => (-1 / 2 : ℝ) * x) := by
    funext x
    simp only [toUnit, Function.comp_apply]
    ring
  rw [hfun, ← Measure.map_map (measurable_const_add (1 / 2 : ℝ))
      (measurable_const_mul (-1 / 2 : ℝ)),
    Real.map_volume_mul_left (by norm_num : (-1 / 2 : ℝ) ≠ 0),
    Measure.map_smul _ (measurable_const_add (1 / 2 : ℝ)).aemeasurable,
    map_add_left_eq_self]
  norm_num

theorem uniformUnit_map_to_unit : uniformUnit.map toUnit = uniform01 := by
  have hpre : toUnit ⁻¹' Set.Icc 0 1 = Set.Icc (-1) 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, toUnit]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  have hmap : ((volume : Measure ℝ).restrict (Set.Icc (-1) 1)).map toUnit =
      (2 : ℝ≥0∞) • volume.restrict (Set.Icc 0 1) := by
    rw [← hpre, ← Measure.restrict_map measurable_toUnit measurableSet_Icc,
      volume_map_toUnit, Measure.restrict_smul]
  unfold uniformUnit uniform01
  rw [Measure.map_smul _ measurable_toUnit.aemeasurable, hmap, smul_smul,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp), one_smul]

theorem uniform01_eq_withDensity :
    uniform01 = volume.withDensity ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))) := by
  symm
  exact withDensity_indicator_one measurableSet_Icc

def unitTriangleDensity (t : ℝ) : ℝ := max 0 (min 1 t - max 0 (t - 1))

theorem unitInterval_lconvolution (t : ℝ) :
    lconvolution ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)))
      ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))) volume t =
      ENNReal.ofReal (unitTriangleDensity t) := by
  have hfun : (fun y => (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) y *
      (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (-y + t)) =
      (Set.Icc (max 0 (t - 1)) (min 1 t)).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) := by
    funext y
    have hmem : y ∈ Set.Icc (max 0 (t - 1)) (min 1 t) ↔
        y ∈ Set.Icc (0 : ℝ) 1 ∧ -y + t ∈ Set.Icc (0 : ℝ) 1 := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
        exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
        exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩
    by_cases hya : y ∈ Set.Icc (0 : ℝ) 1 <;>
      by_cases hyb : -y + t ∈ Set.Icc (0 : ℝ) 1 <;>
      simp [Set.indicator, hmem, hya, hyb]
  rw [lconvolution_def, hfun, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
  simp [unitTriangleDensity]

theorem uniform01_conv_uniform01 :
    Measure.conv uniform01 uniform01 =
      volume.withDensity (fun t => ENNReal.ofReal (unitTriangleDensity t)) := by
  rw [uniform01_eq_withDensity,
    conv_withDensity_eq_lconvolution (measurable_const.indicator measurableSet_Icc)
      (measurable_const.indicator measurableSet_Icc)]
  congr 1
  funext t
  exact unitInterval_lconvolution t

end
end ENT
