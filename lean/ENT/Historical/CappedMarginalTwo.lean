module

public import ENT.Historical.CappedMarginal
public import ENT.Historical.SplineRatioTwo

/-! The two-uniform slice is an interval. Its residual sum consists of a single uniform variable. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Historical
noncomputable section
open Spline

def twoSliceInterval (s : ℝ) : Set ℝ := Icc (max 0 (s-1)) (min 1 s)

def twoCoordinateSlice (s x : ℝ) : ℝ :=
  (twoSliceInterval s).indicator (fun _ => 1) x

theorem mem_twoSliceInterval (s x : ℝ) :
    x ∈ twoSliceInterval s ↔ x ∈ Icc (0:ℝ) 1 ∧ s-x ∈ Icc (0:ℝ) 1 := by
  simp only [twoSliceInterval, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h0, hs1⟩, h1, hs⟩
    exact ⟨⟨h0,h1⟩,⟨by linarith,by linarith⟩⟩
  · rintro ⟨⟨h0,h1⟩,hlo,hhi⟩
    exact ⟨⟨h0,by linarith⟩,h1,by linarith⟩

theorem measurable_twoCoordinateSlice :
    Measurable (fun z : ℝ × ℝ => twoCoordinateSlice z.2 z.1) := by
  have hset : MeasurableSet {z : ℝ × ℝ | max 0 (z.2-1) ≤ z.1 ∧ z.1 ≤ min 1 z.2} :=
    (measurableSet_le
      (show Measurable (fun z : ℝ × ℝ => max 0 (z.2-1)) by fun_prop) measurable_fst).inter
      (measurableSet_le measurable_fst
        (show Measurable (fun z : ℝ × ℝ => min 1 z.2) by fun_prop))
  convert (measurable_const : Measurable (fun _ : ℝ × ℝ => (1:ℝ))).indicator hset using 1
  rfl

theorem twoCoordinateSlice_nonneg (s x : ℝ) : 0 ≤ twoCoordinateSlice s x := by
  by_cases hx : x ∈ twoSliceInterval s <;> simp [twoCoordinateSlice,hx]

theorem twoCoordinateSlice_integrable (s : ℝ) : Integrable (twoCoordinateSlice s) volume :=
  continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem coordinateSumLaw_two_density :
    coordinateSumLaw (0 : Fin 2) = (volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (twoCoordinateSlice z.2 z.1)) := by
  rw [coordinateSumLaw_succ, sumLaw01_one]
  have huniform : uniform01 = volume.withDensity
      ((Icc (0:ℝ) 1).indicator (fun _ : ℝ => (1:ℝ≥0∞))) := by
    rw [withDensity_indicator measurableSet_Icc, withDensity_const, one_smul]
    rfl
  rw [huniform, prod_withDensity (measurable_const.indicator measurableSet_Icc)
    (measurable_const.indicator measurableSet_Icc)]
  let T : ℝ × ℝ → ℝ × ℝ := fun z => (z.1,z.1+z.2)
  let w : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (twoCoordinateSlice z.2 z.1)
  have hw : Measurable w := measurable_twoCoordinateSlice.ennreal_ofReal
  have hweight : (fun z : ℝ × ℝ =>
      (Icc (0:ℝ) 1).indicator (fun _ : ℝ => (1:ℝ≥0∞)) z.1 *
      (Icc (0:ℝ) 1).indicator (fun _ : ℝ => (1:ℝ≥0∞)) z.2) = w ∘ T := by
    funext z
    have hm : z.1 ∈ twoSliceInterval (z.1+z.2) ↔
        z.1 ∈ Icc (0:ℝ) 1 ∧ z.2 ∈ Icc (0:ℝ) 1 := by
      simpa only [add_sub_cancel_left] using mem_twoSliceInterval (z.1+z.2) z.1
    by_cases h1 : z.1 ∈ Icc (0:ℝ) 1 <;>
      by_cases h2 : z.2 ∈ Icc (0:ℝ) 1 <;>
      simp [w,T,twoCoordinateSlice,hm,h1,h2]
  rw [hweight, Small.map_withDensity_comp _ (by fun_prop) hw]
  rw [(measurePreserving_prod_add (volume:Measure ℝ) volume).map_eq]

theorem twoSlice_endpoints {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    max 0 (s-1) ≤ min 1 s ∧ max 0 (s-1) + min 1 s = s := by
  by_cases hs1 : s ≤ 1
  · rw [max_eq_left (by linarith : s-1 ≤ 0), min_eq_right hs1]
    exact ⟨hs0, by ring⟩
  · rw [max_eq_right (by linarith : 0 ≤ s-1), min_eq_left (by linarith : 1 ≤ s)]
    exact ⟨by linarith, by ring⟩

theorem twoCoordinateSlice_mass {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (∫ x, twoCoordinateSlice s x) = unitSumSplineDensity 2 s := by
  have hab := (twoSlice_endpoints hs0 hs2).1
  unfold twoCoordinateSlice twoSliceInterval
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
  rw [unitSumSplineDensity_two_overlap, max_eq_right (sub_nonneg.mpr hab)]
  simp

theorem twoCoordinateSlice_centered_second {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (∫ x, (2*x-s)^2 * twoCoordinateSlice s x) =
      (unitSumSplineDensity 2 s)^3/3 := by
  obtain ⟨hab,hsum⟩ := twoSlice_endpoints hs0 hs2
  have he : (fun x => (2*x-s)^2 * twoCoordinateSlice s x) =
      (twoSliceInterval s).indicator (fun x => (2*x-s)^2) := by
    funext x
    by_cases hx : x ∈ twoSliceInterval s <;> simp [twoCoordinateSlice,hx]
  rw [he, twoSliceInterval, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => (2*y-s)^3/6) ((2*x-s)^2) x := by
    convert (((((hasDerivAt_id x).const_mul 2).sub_const s).pow 3).div_const 6) using 1 <;>
      first | rfl | (norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((show Continuous (fun x : ℝ => (2*x-s)^2) by fun_prop).intervalIntegrable _ _),
    unitSumSplineDensity_two_overlap, max_eq_right (sub_nonneg.mpr hab)]
  generalize max 0 (s-1) = a at hsum ⊢
  generalize min 1 s = b at hsum ⊢
  rw [←hsum]
  ring

end
end ENT.Historical
