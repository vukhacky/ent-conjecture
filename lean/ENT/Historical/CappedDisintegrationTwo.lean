module

public import ENT.Historical.CappedDisintegration
public import ENT.Historical.CappedSimplexTwo

/-! Markov disintegration for the actual two-uniform slice. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ENT.Historical
noncomputable section
open Spline

theorem measurable_twoCoordinateSlice_uncurry :
    Measurable (Function.uncurry twoCoordinateSlice) := by
  convert measurable_twoCoordinateSlice.comp
    (measurable_swap : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ)) using 1
  ext z
  rfl

theorem measurable_twoCappedMarginalDensity :
    Measurable (Function.uncurry twoCappedMarginalDensity) := by
  exact measurable_twoCoordinateSlice_uncurry.div
    ((continuous_unitSumSplineDensity 2).measurable.comp measurable_fst)

def twoCappedRawKernel : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity
    (fun s x => ENNReal.ofReal (twoCappedMarginalDensity s x))

instance twoCappedRawKernel_sfinite : IsSFiniteKernel twoCappedRawKernel :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem twoCappedRawKernel_apply (s : ℝ) :
    twoCappedRawKernel s = volume.withDensity (fun x => ENNReal.ofReal (twoCappedMarginalDensity s x)) := by
  exact Kernel.withDensity_apply _ measurable_twoCappedMarginalDensity.ennreal_ofReal s

def twoCappedMarginalKernel : Kernel ℝ ℝ :=
  Kernel.piecewise (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 2))
    twoCappedRawKernel (Kernel.const ℝ (Measure.dirac 0))

theorem twoCappedMarginalKernel_apply_interior {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    twoCappedMarginalKernel s = volume.withDensity
      (fun x => ENNReal.ofReal (twoCappedMarginalDensity s x)) := by
  rw [twoCappedMarginalKernel, Kernel.piecewise_apply, if_pos hs, twoCappedRawKernel_apply]

instance twoCappedMarginalKernel_markov : IsMarkovKernel twoCappedMarginalKernel := by
  constructor
  intro s
  by_cases hs : s ∈ Ioo (0 : ℝ) 2
  · rw [twoCappedMarginalKernel_apply_interior hs]
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal (twoCappedMarginalDensity_integrable s)
        (Filter.Eventually.of_forall (twoCappedMarginalDensity_nonneg s)),
      twoCappedMarginalDensity_mass hs]
    simp
  · rw [twoCappedMarginalKernel, Kernel.piecewise_apply, if_neg hs, Kernel.const_apply]
    infer_instance

theorem twoCoordinateSlice_zero_outside_support {s x : ℝ} (hs : s ∉ Icc (0 : ℝ) 2) :
    twoCoordinateSlice s x = 0 := by
  apply indicator_of_notMem
  intro hx
  obtain ⟨h1, h2⟩ := (mem_twoSliceInterval s x).mp hx
  exact hs ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

theorem twoCoordinateSlice_mass_all (s : ℝ) :
    (∫ x, twoCoordinateSlice s x) = unitSumSplineDensity 2 s := by
  by_cases hs : s ∈ Icc (0 : ℝ) 2
  · exact twoCoordinateSlice_mass hs.1 hs.2
  · rw [unitSumSplineDensity_eq_zero_of_not_mem 2 (by omega) s (by simpa only [Nat.cast_ofNat] using hs)]
    have hzero : twoCoordinateSlice s = fun _ => 0 :=
      funext (fun _ => twoCoordinateSlice_zero_outside_support hs)
    rw [hzero, integral_zero]

theorem twoCoordinateSlice_factorization_ae (s : ℝ) :
    (fun x => twoCoordinateSlice s x) =ᵐ[volume]
      (fun x => unitSumSplineDensity 2 s * twoCappedMarginalDensity s x) := by
  by_cases hs : unitSumSplineDensity 2 s = 0
  · have hzero := (integral_eq_zero_iff_of_nonneg
        (twoCoordinateSlice_nonneg s) (twoCoordinateSlice_integrable s)).mp
      (by rw [twoCoordinateSlice_mass_all s, hs])
    filter_upwards [hzero] with x hx
    simpa only [Pi.zero_apply, hs, zero_mul] using hx
  · exact Filter.Eventually.of_forall fun x => by
      simp [twoCappedMarginalDensity, mul_div_cancel₀ _ hs]

theorem twoCoordinateSlice_factorization_prod_ae :
    (fun z : ℝ × ℝ => twoCoordinateSlice z.1 z.2) =ᵐ[volume.prod volume]
      (fun z => unitSumSplineDensity 2 z.1 * twoCappedMarginalDensity z.1 z.2) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    measurable_twoCoordinateSlice_uncurry
    (((continuous_unitSumSplineDensity 2).measurable.comp measurable_fst).mul
      measurable_twoCappedMarginalDensity))).mpr
  exact Filter.Eventually.of_forall twoCoordinateSlice_factorization_ae

theorem sumCoordinateLaw_two_density :
    (unitCube01 2).map (fun x => (sumProjection01 2 x, x 0)) =
      (volume.prod volume).withDensity
        (fun z : ℝ × ℝ => ENNReal.ofReal (twoCoordinateSlice z.1 z.2)) := by
  have hfun : (fun x : Fin 2 → ℝ => (sumProjection01 2 x, x 0)) =
      Prod.swap ∘ (fun x => (x 0, sumProjection01 2 x)) := rfl
  rw [hfun, ← Measure.map_map measurable_swap (by fun_prop)]
  change (coordinateSumLaw (0 : Fin 2)).map Prod.swap = _
  rw [coordinateSumLaw_two_density]
  let w := fun z : ℝ × ℝ => ENNReal.ofReal (twoCoordinateSlice z.1 z.2)
  have hw : Measurable w := measurable_twoCoordinateSlice_uncurry.ennreal_ofReal
  change ((volume.prod volume).withDensity (w ∘ Prod.swap)).map Prod.swap = _
  rw [Small.map_withDensity_comp _ measurable_swap hw, Measure.prod_swap]

theorem twoCappedRawKernel_disintegration :
    (unitCube01 2).map (fun x => (sumProjection01 2 x, x 0)) = sumLaw01 2 ⊗ₘ twoCappedRawKernel := by
  rw [sumCoordinateLaw_two_density, sumLaw01_eq_splineDensity 2 (by omega)]
  letI : IsSFiniteKernel ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
      (fun s x => ENNReal.ofReal (twoCappedMarginalDensity s x))) := twoCappedRawKernel_sfinite
  unfold twoCappedRawKernel
  rw [Measure.withDensity_compProd_withDensity
      (continuous_unitSumSplineDensity 2).measurable.ennreal_ofReal
      measurable_twoCappedMarginalDensity.ennreal_ofReal,
    Measure.compProd_const]
  apply withDensity_congr_ae
  filter_upwards [twoCoordinateSlice_factorization_prod_ae] with z hz
  rw [hz, ENNReal.ofReal_mul (unitSumSplineDensity_nonneg 2 (by omega) z.1)]

theorem twoCappedMarginalKernel_disintegration :
    (unitCube01 2).map (fun x => (sumProjection01 2 x, x 0)) = sumLaw01 2 ⊗ₘ twoCappedMarginalKernel := by
  rw [twoCappedRawKernel_disintegration]
  apply Measure.compProd_congr
  filter_upwards [sumLaw01_ae_interior 2 (by omega)] with s hs
  rw [twoCappedMarginalKernel, Kernel.piecewise_apply, if_pos (by norm_num at hs; exact hs)]

end
end ENT.Historical
