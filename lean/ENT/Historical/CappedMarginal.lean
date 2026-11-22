module

public import ENT.Small.ConditionalKernelLaw
public import ENT.Spline.PositiveInterior
public import Mathlib.MeasureTheory.Group.Prod

/-! The joint law of a coordinate and the coordinate sum on the unit cube, and its normalized conditional coordinate density. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Historical
noncomputable section
open Spline

def coordinateSumLaw {n : ℕ} (i : Fin n) : Measure (ℝ × ℝ) :=
  (unitCube01 n).map (fun x => (x i, sumProjection01 n x))

def coordinateSlice (n : ℕ) (s x : ℝ) : ℝ :=
  (Icc (0 : ℝ) 1).indicator (fun x => unitSumSplineDensity (n - 1) (s - x)) x

def cappedMarginalDensity (n : ℕ) (s x : ℝ) : ℝ :=
  coordinateSlice n s x / unitSumSplineDensity n s

theorem measurable_coordinateSlice (n : ℕ) :
    Measurable (fun z : ℝ × ℝ => coordinateSlice n z.2 z.1) := by
  unfold coordinateSlice
  have h : Measurable (fun z : ℝ × ℝ => unitSumSplineDensity (n - 1) (z.2 - z.1)) :=
    (continuous_unitSumSplineDensity _).measurable.comp (measurable_snd.sub measurable_fst)
  have hi := h.indicator ((measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) 1)).preimage measurable_fst)
  convert hi using 1
  ext z
  by_cases hz : z.1 ∈ Icc (0 : ℝ) 1 <;> simp [hz]

theorem coordinateSlice_nonneg (n : ℕ) (hn : 3 ≤ n) (s x : ℝ) :
    0 ≤ coordinateSlice n s x := by
  unfold coordinateSlice
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    exact unitSumSplineDensity_nonneg _ (by omega) _
  · rw [indicator_of_notMem hx]

theorem coordinateSlice_integrable (n : ℕ) (s : ℝ) :
    Integrable (coordinateSlice n s) volume := by
  exact ((continuous_unitSumSplineDensity _).comp
    (continuous_const.sub continuous_id)).integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem coordinateSlice_mass (n : ℕ) (hn : 3 ≤ n) (s : ℝ) :
    (∫ x, coordinateSlice n s x) = unitSumSplineDensity n s := by
  simp only [coordinateSlice]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left]
  simpa only [sub_zero, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
    unitSumSplineDensity_window (n - 1) (by omega) s

theorem cappedMarginalDensity_nonneg (n : ℕ) (hn : 3 ≤ n) (s x : ℝ) :
    0 ≤ cappedMarginalDensity n s x :=
  div_nonneg (coordinateSlice_nonneg n hn s x)
    (unitSumSplineDensity_nonneg n (by omega) s)

theorem cappedMarginalDensity_integrable (n : ℕ) (s : ℝ) :
    Integrable (cappedMarginalDensity n s) volume :=
  (coordinateSlice_integrable n s).div_const _

theorem cappedMarginalDensity_mass (n : ℕ) (hn : 3 ≤ n) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) n) : (∫ x, cappedMarginalDensity n s x) = 1 := by
  simp only [cappedMarginalDensity]
  rw [integral_div, coordinateSlice_mass n hn]
  exact div_self (unitSumSplineDensity_pos n (by omega) s hs.1 hs.2).ne'

theorem coordinateSumLaw_succ (n : ℕ) :
    coordinateSumLaw (0 : Fin (n + 1)) =
      (uniform01.prod (sumLaw01 n)).map (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f : ℝ × (Fin n → ℝ) → ℝ × ℝ := fun z => (z.1, z.1 + sumProjection01 n z.2)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (unitCube01 (n + 1)).map e = uniform01.prod (unitCube01 n) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => uniform01) 0).map_eq
  have hfun : (fun x : Fin (n + 1) → ℝ => (x 0, sumProjection01 (n + 1) x)) = f ∘ e := by
    funext x
    simp [sumProjection01, f, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.tail]
  calc
    _ = (uniform01.prod (unitCube01 n)).map f := by
      rw [coordinateSumLaw, hfun, ← Measure.map_map hf e.measurable, he]
    _ = _ := by
      unfold sumLaw01
      have hprod := Measure.map_prod_map uniform01 (unitCube01 n)
        (f := (id : ℝ → ℝ)) (g := sumProjection01 n)
        measurable_id (measurable_sumProjection01 n)
      rw [Measure.map_id] at hprod
      rw [hprod, Measure.map_map (f := Prod.map (id : ℝ → ℝ) (sumProjection01 n))
        (g := fun z : ℝ × ℝ => (z.1, z.1 + z.2)) (by fun_prop) (by fun_prop)]
      rfl

theorem coordinateSumLaw_density (n : ℕ) (hn : 2 ≤ n) :
    coordinateSumLaw (0 : Fin (n + 1)) =
      (volume.prod volume).withDensity
        (fun z : ℝ × ℝ => ENNReal.ofReal (coordinateSlice (n + 1) z.2 z.1)) := by
  rw [coordinateSumLaw_succ, sumLaw01_eq_splineDensity n hn]
  have huniform : uniform01 = volume.withDensity
      ((Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ≥0∞))) := by
    rw [withDensity_indicator measurableSet_Icc, withDensity_const, one_smul]
    rfl
  rw [huniform, prod_withDensity (measurable_const.indicator measurableSet_Icc)
    (continuous_unitSumSplineDensity n).measurable.ennreal_ofReal]
  let T : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, z.1 + z.2)
  let w : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (coordinateSlice (n + 1) z.2 z.1)
  have hw : Measurable w := (measurable_coordinateSlice (n + 1)).ennreal_ofReal
  have hweight : (fun z : ℝ × ℝ =>
      (Icc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) z.1 *
        ENNReal.ofReal (unitSumSplineDensity n z.2)) = w ∘ T := by
    funext z
    by_cases hz : z.1 ∈ Icc (0 : ℝ) 1
    · simp [w, T, coordinateSlice, hz]
    · simp [w, T, coordinateSlice, hz]
  rw [hweight, Small.map_withDensity_comp _ (by fun_prop) hw]
  rw [(measurePreserving_prod_add (volume : Measure ℝ) volume).map_eq]

end
end ENT.Historical
