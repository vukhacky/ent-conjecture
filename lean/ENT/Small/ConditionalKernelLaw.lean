module

public import ENT.Small.ConditionalKernel
public import ENT.Small.ConditionalKernelFormula
public import ENT.Spline.DensityLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Probability-law identification of the coordinate-square spline kernel. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Small
noncomputable section
open Spline
universe u v

theorem map_withDensity_comp {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    {f : α → β} {w : β → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ hf]
  change (∫⁻ a, (φ ∘ f) a ∂μ.withDensity (w ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hw.comp hf) (hφ.comp hf),
    lintegral_withDensity_eq_lintegral_mul (μ.map f) hw hφ,
    lintegral_map (hw.mul hφ) hf]
  rfl

def coordinateWeight01 (x : ℝ) : ℝ := (1 - 2 * x) ^ 2

theorem coordinateWeight01_nonneg (x : ℝ) : 0 ≤ coordinateWeight01 x := sq_nonneg _

theorem continuous_coordinateWeight01 : Continuous coordinateWeight01 := by
  unfold coordinateWeight01
  fun_prop

def weightedUniform01 : Measure ℝ :=
  uniform01.withDensity (fun x => ENNReal.ofReal (coordinateWeight01 x))

instance weightedUniform01_sigmaFinite : SigmaFinite weightedUniform01 := by
  unfold weightedUniform01
  infer_instance

def weightedSumLaw01 {n : ℕ} (i : Fin n) : Measure ℝ :=
  ((unitCube01 n).withDensity (fun x => ENNReal.ofReal (coordinateWeight01 (x i)))).map
    (sumProjection01 n)

theorem weightedUniform01_eq_withDensity : weightedUniform01 =
    volume.withDensity ((Icc (0 : ℝ) 1).indicator
      (fun x => ENNReal.ofReal (coordinateWeight01 x))) := by
  unfold weightedUniform01 uniform01
  rw [← withDensity_indicator measurableSet_Icc]

theorem weightedSumLaw01_succ (n : ℕ) :
    weightedSumLaw01 (0 : Fin (n + 1)) = Measure.conv weightedUniform01 (sumLaw01 n) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let f : ℝ × (Fin n → ℝ) → ℝ := fun z => z.1 + sumProjection01 n z.2
  let w : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (coordinateWeight01 z.1)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hw : Measurable w := by dsimp [w]; exact
    (continuous_coordinateWeight01.measurable.comp measurable_fst).ennreal_ofReal
  have he : (unitCube01 (n + 1)).map e = uniform01.prod (unitCube01 n) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => uniform01) 0).map_eq
  have hsum : sumProjection01 (n + 1) = f ∘ e := by
    funext x
    simp [sumProjection01, f, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.tail]
  have hweight : (fun x : Fin (n + 1) → ℝ => ENNReal.ofReal (coordinateWeight01 (x 0))) =
      w ∘ e := by
    funext x
    simp [w, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
  have hew : ((unitCube01 (n + 1)).withDensity (w ∘ e)).map e =
      weightedUniform01.prod (unitCube01 n) := by
    rw [map_withDensity_comp _ e.measurable hw, he]
    exact (prod_withDensity_left continuous_coordinateWeight01.measurable.ennreal_ofReal).symm
  calc
    _ = (weightedUniform01.prod (unitCube01 n)).map f := by
      rw [weightedSumLaw01, hweight, hsum, ← Measure.map_map hf e.measurable, hew]
    _ = _ := by
      unfold Measure.conv sumLaw01
      have hprod := Measure.map_prod_map weightedUniform01 (unitCube01 n)
        (f := (id : ℝ → ℝ)) (g := sumProjection01 n)
        measurable_id (measurable_sumProjection01 n)
      rw [Measure.map_id] at hprod
      rw [hprod, Measure.map_map (f := Prod.map (id : ℝ → ℝ) (sumProjection01 n))
        (g := fun z : ℝ × ℝ => z.1 + z.2) (by fun_prop) (by fun_prop)]
      rfl

theorem coordinateSquareKernel_nonneg (n : ℕ) (hn : 3 ≤ n) (t : ℝ) :
    0 ≤ coordinateSquareKernel n t := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  exact mul_nonneg (sq_nonneg _) (unitSumSplineDensity_nonneg (n - 1) (by omega) _)

theorem measurable_coordinateSquareKernel (n : ℕ) (hn : 3 ≤ n) :
    Measurable (coordinateSquareKernel n) := by
  have heq : coordinateSquareKernel n = coordinateSquareKernelFormula n :=
    funext (coordinateSquareKernel_eq_formula n hn)
  rw [heq]
  unfold coordinateSquareKernelFormula quadraticPowerPrimitive positivePower
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  fun_prop

theorem weightedSumLaw01_density (n : ℕ) (hn : 2 ≤ n) :
    weightedSumLaw01 (0 : Fin (n + 1)) =
      volume.withDensity (fun t => ENNReal.ofReal (coordinateSquareKernel (n + 1) t)) := by
  rw [weightedSumLaw01_succ, weightedUniform01_eq_withDensity, sumLaw01_eq_splineDensity n hn,
    conv_withDensity_eq_lconvolution
      (continuous_coordinateWeight01.measurable.ennreal_ofReal.indicator measurableSet_Icc)
      (continuous_unitSumSplineDensity n).measurable.ennreal_ofReal]
  congr 1
  funext t
  have hfun : (fun x : ℝ => (Icc (0 : ℝ) 1).indicator
      (fun x => ENNReal.ofReal (coordinateWeight01 x)) x *
        ENNReal.ofReal (unitSumSplineDensity n (-x + t))) =
      (Icc (0 : ℝ) 1).indicator
        (fun x => ENNReal.ofReal (coordinateWeight01 x * unitSumSplineDensity n (t - x))) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp only [indicator_of_mem hx]
      rw [← ENNReal.ofReal_mul (coordinateWeight01_nonneg x)]
      rw [show -x + t = t - x by ring]
    · simp only [indicator_of_notMem hx, zero_mul]
  rw [lconvolution_def, hfun, lintegral_indicator measurableSet_Icc]
  have hc : Continuous (fun x : ℝ => coordinateWeight01 x * unitSumSplineDensity n (t - x)) :=
    continuous_coordinateWeight01.mul
      ((continuous_unitSumSplineDensity n).comp (continuous_const.sub continuous_id))
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
    (Filter.Eventually.of_forall fun x => mul_nonneg (coordinateWeight01_nonneg x)
      (unitSumSplineDensity_nonneg n hn _))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [coordinateSquareKernel, Nat.add_sub_cancel, coordinateWeight01]

theorem cubeLaw_square_weight_map_toUnitCube {n : ℕ} (i : Fin n) :
    ((cubeLaw n).withDensity (fun x => ENNReal.ofReal (x i ^ 2))).map (toUnitCube n) =
      (unitCube01 n).withDensity (fun x => ENNReal.ofReal (coordinateWeight01 (x i))) := by
  have hweight : (fun x : Fin n → ℝ => ENNReal.ofReal (x i ^ 2)) =
      (fun x : Fin n → ℝ => ENNReal.ofReal (coordinateWeight01 (x i))) ∘ toUnitCube n := by
    funext x
    simp only [Function.comp_apply, coordinateWeight01, toUnitCube, toUnit]
    congr 1
    ring
  have hw : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (coordinateWeight01 (x i))) := by
    unfold coordinateWeight01
    fun_prop
  rw [hweight, map_withDensity_comp _ (measurable_toUnitCube n) hw, cubeLaw_map_toUnitCube]

def sumToDiagonal (n : ℕ) (t : ℝ) : ℝ := ((n : ℝ) - 2 * t) / Real.sqrt n

theorem measurable_sumToDiagonal (n : ℕ) : Measurable (sumToDiagonal n) := by
  unfold sumToDiagonal
  fun_prop

theorem projection_diagonal_eq_sumToDiagonal (n : ℕ) :
    projection (diagonal n) = sumToDiagonal n ∘ (sumProjection01 n ∘ toUnitCube n) := by
  funext x
  simp only [projection, diagonal, Function.comp_apply, sumProjection01, toUnitCube, toUnit,
    ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sumToDiagonal]
  ring

theorem weighted_diagonal_projection_law (n : ℕ) (hn : 2 ≤ n) :
    (((cubeLaw (n + 1)).withDensity (fun x => ENNReal.ofReal (x 0 ^ 2))).map
      (projection (diagonal (n + 1)))) =
      (volume.withDensity (fun t => ENNReal.ofReal (coordinateSquareKernel (n + 1) t))).map
        (sumToDiagonal (n + 1)) := by
  rw [projection_diagonal_eq_sumToDiagonal,
    ← Measure.map_map (measurable_sumToDiagonal _)
      ((measurable_sumProjection01 _).comp (measurable_toUnitCube _)),
    ← Measure.map_map (measurable_sumProjection01 _) (measurable_toUnitCube _),
    cubeLaw_square_weight_map_toUnitCube]
  change (weightedSumLaw01 (0 : Fin (n + 1))).map _ = _
  rw [weightedSumLaw01_density n hn]

theorem diagonalTestMoment_eq_kernel (n : ℕ) (hn : 2 ≤ n) (f : ℝ → ℝ) (hf : Measurable f) :
    diagonalTestMoment f (0 : Fin (n + 1)) 0 =
      ∫ t, coordinateSquareKernel (n + 1) t * f (sumToDiagonal (n + 1) t) := by
  have h := congrArg (fun μ : Measure ℝ => ∫ t, f t ∂μ) (weighted_diagonal_projection_law n hn)
  rw [integral_map (measurable_projection _).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_sumToDiagonal _).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul ((measurable_pi_apply 0).pow_const 2).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (measurable_coordinateSquareKernel _ (by omega)).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (coordinateSquareKernel_nonneg (n + 1) (by omega) _), smul_eq_mul] at h
  simpa only [diagonalTestMoment, pow_two] using h

end
end ENT.Small
