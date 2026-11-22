module

public import ENT.Historical.CappedSimplex
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-! A Markov disintegration of the actual sum/coordinate law on the continuous
cube. Outside the support of the sum the kernel is assigned the probability
measure δ₀; all entropy/convex-order assertions use the interior density. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ENT.Historical
noncomputable section
open Spline

theorem measurable_cappedMarginalDensity (n : ℕ) :
    Measurable (Function.uncurry (cappedMarginalDensity n)) := by
  have hc : Measurable (fun z : ℝ × ℝ => coordinateSlice n z.1 z.2) :=
    by
      convert (measurable_coordinateSlice n).comp
        (measurable_swap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ)) using 1
      ext z
      rfl
  change Measurable (fun z : ℝ × ℝ => coordinateSlice n z.1 z.2 / unitSumSplineDensity n z.1)
  exact hc.div ((continuous_unitSumSplineDensity n).measurable.comp measurable_fst)

def cappedRawKernel (n : ℕ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity
    (fun s x => ENNReal.ofReal (cappedMarginalDensity n s x))

instance cappedRawKernel_sfinite (n : ℕ) : IsSFiniteKernel (cappedRawKernel n) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem cappedRawKernel_apply (n : ℕ) (s : ℝ) :
    cappedRawKernel n s = volume.withDensity (fun x => ENNReal.ofReal (cappedMarginalDensity n s x)) := by
  exact Kernel.withDensity_apply _ (measurable_cappedMarginalDensity n).ennreal_ofReal s

def cappedMarginalKernel (n : ℕ) : Kernel ℝ ℝ :=
  Kernel.piecewise (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) n))
    (cappedRawKernel n) (Kernel.const ℝ (Measure.dirac 0))

theorem cappedMarginalKernel_apply_interior (n : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) n) :
    cappedMarginalKernel n s = volume.withDensity
      (fun x => ENNReal.ofReal (cappedMarginalDensity n s x)) := by
  rw [cappedMarginalKernel, Kernel.piecewise_apply, if_pos hs, cappedRawKernel_apply]

theorem cappedMarginalKernel_markov (n : ℕ) (hn : 3 ≤ n) :
    IsMarkovKernel (cappedMarginalKernel n) := by
  constructor
  intro s
  by_cases hs : s ∈ Ioo (0 : ℝ) n
  · rw [cappedMarginalKernel_apply_interior n hs]
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal (cappedMarginalDensity_integrable n s)
        (Filter.Eventually.of_forall (cappedMarginalDensity_nonneg n hn s)),
      cappedMarginalDensity_mass n hn hs]
    simp
  · rw [cappedMarginalKernel, Kernel.piecewise_apply, if_neg hs, Kernel.const_apply]
    infer_instance

theorem sumLaw01_ae_interior (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ s ∂sumLaw01 n, s ∈ Ioo (0 : ℝ) n := by
  rw [sumLaw01_eq_splineDensity n hn,
    ae_withDensity_iff (continuous_unitSumSplineDensity n).measurable.ennreal_ofReal]
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (n : ℝ)] with s hs0 hsn hs
  have hscc : s ∈ Icc (0 : ℝ) n := by
    by_contra h
    rw [unitSumSplineDensity_eq_zero_of_not_mem n hn s h, ENNReal.ofReal_zero] at hs
    exact hs rfl
  exact ⟨lt_of_le_of_ne hscc.1 hs0.symm, lt_of_le_of_ne hscc.2 hsn⟩

theorem coordinateSlice_factorization_ae (n : ℕ) (hn : 3 ≤ n) (s : ℝ) :
    (fun x => coordinateSlice n s x) =ᵐ[volume]
      (fun x => unitSumSplineDensity n s * cappedMarginalDensity n s x) := by
  by_cases hs : unitSumSplineDensity n s = 0
  · have hzero := (integral_eq_zero_iff_of_nonneg
        (coordinateSlice_nonneg n hn s) (coordinateSlice_integrable n s)).mp
      (by rw [coordinateSlice_mass n hn s, hs])
    filter_upwards [hzero] with x hx
    simpa only [Pi.zero_apply, hs, zero_mul] using hx
  · exact Filter.Eventually.of_forall fun x => by
      simp [cappedMarginalDensity, mul_div_cancel₀ _ hs]

theorem coordinateSlice_factorization_prod_ae (n : ℕ) (hn : 3 ≤ n) :
    (fun z : ℝ × ℝ => coordinateSlice n z.1 z.2) =ᵐ[volume.prod volume]
      (fun z => unitSumSplineDensity n z.1 * cappedMarginalDensity n z.1 z.2) := by
  have hc : Measurable (fun z : ℝ × ℝ => coordinateSlice n z.1 z.2) := by
    convert (measurable_coordinateSlice n).comp
      (measurable_swap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ)) using 1
    ext z
    rfl
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    hc
    (((continuous_unitSumSplineDensity n).measurable.comp measurable_fst).mul
      (measurable_cappedMarginalDensity n)))).mpr
  exact Filter.Eventually.of_forall (coordinateSlice_factorization_ae n hn)

theorem sumCoordinateLaw_density (n : ℕ) (hn : 2 ≤ n) :
    (unitCube01 (n + 1)).map (fun x => (sumProjection01 (n + 1) x, x 0)) =
      (volume.prod volume).withDensity
        (fun z : ℝ × ℝ => ENNReal.ofReal (coordinateSlice (n + 1) z.1 z.2)) := by
  have hfun : (fun x : Fin (n + 1) → ℝ => (sumProjection01 (n + 1) x, x 0)) =
      Prod.swap ∘ (fun x => (x 0, sumProjection01 (n + 1) x)) := rfl
  rw [hfun, ← Measure.map_map measurable_swap (by fun_prop)]
  change (coordinateSumLaw (0 : Fin (n + 1))).map Prod.swap = _
  rw [coordinateSumLaw_density n hn]
  let w := fun z : ℝ × ℝ => ENNReal.ofReal (coordinateSlice (n + 1) z.1 z.2)
  have hw : Measurable w := by
    convert ((measurable_coordinateSlice (n + 1)).comp
      (measurable_swap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ))).ennreal_ofReal using 1
    ext z
    rfl
  change ((volume.prod volume).withDensity (w ∘ Prod.swap)).map Prod.swap = _
  rw [Small.map_withDensity_comp _ measurable_swap hw,
    Measure.prod_swap]

theorem cappedRawKernel_disintegration (n : ℕ) (hn : 2 ≤ n) :
    (unitCube01 (n + 1)).map (fun x => (sumProjection01 (n + 1) x, x 0)) =
      sumLaw01 (n + 1) ⊗ₘ cappedRawKernel (n + 1) := by
  rw [sumCoordinateLaw_density n hn, sumLaw01_eq_splineDensity (n + 1) (by omega)]
  letI : IsSFiniteKernel ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
      (fun s x => ENNReal.ofReal (cappedMarginalDensity (n + 1) s x))) :=
    cappedRawKernel_sfinite (n + 1)
  unfold cappedRawKernel
  rw [Measure.withDensity_compProd_withDensity
      (continuous_unitSumSplineDensity (n + 1)).measurable.ennreal_ofReal
      (measurable_cappedMarginalDensity (n + 1)).ennreal_ofReal,
    Measure.compProd_const]
  apply withDensity_congr_ae
  filter_upwards [coordinateSlice_factorization_prod_ae (n + 1) (by omega)] with z hz
  rw [hz, ENNReal.ofReal_mul (unitSumSplineDensity_nonneg (n + 1) (by omega) z.1)]

theorem cappedMarginalKernel_disintegration (n : ℕ) (hn : 2 ≤ n) :
    (unitCube01 (n + 1)).map (fun x => (sumProjection01 (n + 1) x, x 0)) =
      sumLaw01 (n + 1) ⊗ₘ cappedMarginalKernel (n + 1) := by
  letI := cappedMarginalKernel_markov (n + 1) (by omega)
  rw [cappedRawKernel_disintegration n hn]
  apply Measure.compProd_congr
  filter_upwards [sumLaw01_ae_interior (n + 1) (by omega)] with s hs
  rw [cappedMarginalKernel, Kernel.piecewise_apply, if_pos hs]

end
end ENT.Historical
