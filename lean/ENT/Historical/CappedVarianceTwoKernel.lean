module

public import ENT.Historical.CappedMarginalTwo

/-! Exact second-moment density of the genuine two-dimensional cube slice. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Historical
noncomputable section
open Spline

theorem twoCoordinateSlice_eq_zero_of_not_mem {s : ℝ} (hs : s ∉ Icc (0:ℝ) 2)
    (x : ℝ) : twoCoordinateSlice s x = 0 := by
  apply indicator_of_notMem
  intro hx
  obtain ⟨hx, hy⟩ := (mem_twoSliceInterval s x).mp hx
  apply hs
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem twoCoordinateSlice_centered_second_integrable (s : ℝ) :
    Integrable (fun x => (2*x-s)^2 * twoCoordinateSlice s x) volume := by
  have he : (fun x => (2*x-s)^2 * twoCoordinateSlice s x) =
      (twoSliceInterval s).indicator (fun x => (2*x-s)^2) := by
    funext x
    by_cases hx : x ∈ twoSliceInterval s <;> simp [twoCoordinateSlice,hx]
  rw [he]
  exact (show Continuous (fun x : ℝ => (2*x-s)^2) by fun_prop).integrableOn_Icc.integrable_indicator
    measurableSet_Icc

theorem twoCoordinateSlice_centered_second_all (s : ℝ) :
    (∫ x, (2*x-s)^2 * twoCoordinateSlice s x) =
      (unitSumSplineDensity 2 s)^3/3 := by
  by_cases hs : s ∈ Icc (0:ℝ) 2
  · exact twoCoordinateSlice_centered_second hs.1 hs.2
  · simp only [twoCoordinateSlice_eq_zero_of_not_mem hs, mul_zero, integral_zero,
      unitSumSplineDensity_eq_zero_of_not_mem 2 (by omega) s (by simpa using hs),
      zero_pow (by decide : 3 ≠ 0), zero_div]

theorem map_snd_withDensity_prod (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ((volume.prod volume).withDensity F).map Prod.snd =
      volume.withDensity (fun y => ∫⁻ x, F (x,y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ measurable_snd]
  change (∫⁻ z, (φ ∘ Prod.snd) z ∂(volume.prod volume).withDensity F) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hF (hφ.comp measurable_snd),
    lintegral_prod_symm' _ (hF.mul (hφ.comp measurable_snd)),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hφ]
  apply lintegral_congr
  intro y
  exact lintegral_mul_const (φ y) (hF.comp (measurable_id.prodMk measurable_const))

def twoDifferenceWeightedSumLaw : Measure ℝ :=
  ((unitCube01 2).withDensity (fun x => ENNReal.ofReal ((x 0-x 1)^2))).map
    (sumProjection01 2)

theorem twoDifferenceWeightedSumLaw_density :
    twoDifferenceWeightedSumLaw = volume.withDensity
      (fun s => ENNReal.ofReal ((unitSumSplineDensity 2 s)^3/3)) := by
  let Z : (Fin 2 → ℝ) → ℝ × ℝ := fun x => (x 0,sumProjection01 2 x)
  let W : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((2*z.1-z.2)^2)
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have hW : Measurable W := by dsimp [W]; fun_prop
  have he : (fun x : Fin 2 → ℝ => ENNReal.ofReal ((x 0-x 1)^2)) = W ∘ Z := by
    funext x
    dsimp [W,Z,sumProjection01]
    congr 1
    simp only [Fin.sum_univ_two]
    ring
  have hsum : sumProjection01 2 = Prod.snd ∘ Z := rfl
  rw [twoDifferenceWeightedSumLaw, he, hsum,
    ← Measure.map_map measurable_snd hZ, Small.map_withDensity_comp _ hZ hW]
  change ((coordinateSumLaw (0:Fin 2)).withDensity W).map Prod.snd = _
  rw [coordinateSumLaw_two_density, ← withDensity_mul _ measurable_twoCoordinateSlice.ennreal_ofReal hW,
    map_snd_withDensity_prod _ (measurable_twoCoordinateSlice.ennreal_ofReal.mul hW)]
  congr 1
  funext s
  have he' : (fun x => ENNReal.ofReal (twoCoordinateSlice s x) * W (x,s)) =
      (fun x => ENNReal.ofReal ((2*x-s)^2 * twoCoordinateSlice s x)) := by
    funext x
    dsimp [W]
    rw [← ENNReal.ofReal_mul (twoCoordinateSlice_nonneg s x), mul_comm]
  change (∫⁻ x, ENNReal.ofReal (twoCoordinateSlice s x) * W (x,s)) = _
  rw [he', ← ofReal_integral_eq_lintegral_ofReal
    (twoCoordinateSlice_centered_second_integrable s)
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (twoCoordinateSlice_nonneg s x)),
    twoCoordinateSlice_centered_second_all]

end
end ENT.Historical
