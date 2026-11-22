module

public import ENT.Historical.CappedSimplex
public import ENT.Historical.CappedMarginalTwo

/-! Convex order for the two-dimensional capped slice.  Its residual is a
single continuous uniform, so the slice is described by its actual interval. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set

namespace ENT.Historical
noncomputable section
open Spline

def twoCappedMarginalDensity (s x : ℝ) : ℝ :=
  twoCoordinateSlice s x / unitSumSplineDensity 2 s

theorem twoCappedMarginalDensity_nonneg (s x : ℝ) : 0 ≤ twoCappedMarginalDensity s x :=
  div_nonneg (twoCoordinateSlice_nonneg s x) (unitSumSplineDensity_nonneg 2 (by omega) s)

theorem twoCappedMarginalDensity_integrable (s : ℝ) :
    Integrable (twoCappedMarginalDensity s) volume := (twoCoordinateSlice_integrable s).div_const _

theorem twoCappedMarginalDensity_test_integrable (s : ℝ) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc 0 s)) :
    Integrable (fun x => φ x * twoCappedMarginalDensity s x) volume := by
  have hφ' : ContinuousOn φ (twoSliceInterval s) := hφ.mono (fun x hx =>
    ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩)
  have hi : IntegrableOn (fun x => φ x / unitSumSplineDensity 2 s) (twoSliceInterval s) volume :=
    (hφ'.div_const _).integrableOn_compact isCompact_Icc
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext x
  by_cases hx : x ∈ twoSliceInterval s <;> simp [twoCappedMarginalDensity, twoCoordinateSlice, hx, div_eq_mul_inv]

theorem twoCappedMarginalDensity_mass {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    (∫ x, twoCappedMarginalDensity s x) = 1 := by
  simp only [twoCappedMarginalDensity]
  rw [integral_div, twoCoordinateSlice_mass hs.1.le hs.2.le]
  exact div_self (unitSumSplineDensity_pos 2 (by omega) s hs.1 (by norm_num; exact hs.2)).ne'

theorem twoCappedMarginalDensity_mean {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    (∫ x, x * twoCappedMarginalDensity s x) = s / 2 := by
  have hab := (twoSlice_endpoints hs.1.le hs.2.le).1
  have hsum := (twoSlice_endpoints hs.1.le hs.2.le).2
  have hfun : (fun x => x * twoCappedMarginalDensity s x) =
      (twoSliceInterval s).indicator (fun x => x / unitSumSplineDensity 2 s) := by
    ext x
    by_cases hx : x ∈ twoSliceInterval s <;> simp [twoCappedMarginalDensity, twoCoordinateSlice, hx, div_eq_mul_inv]
  rw [hfun, twoSliceInterval, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_div, integral_id,
    unitSumSplineDensity_two_overlap, max_eq_right (sub_nonneg.mpr hab)]
  have hd : min 1 s - max 0 (s - 1) ≠ 0 := by
    have hp := unitSumSplineDensity_pos 2 (by omega) s hs.1 (by norm_num; exact hs.2)
    rw [unitSumSplineDensity_two_overlap, max_eq_right (sub_nonneg.mpr hab)] at hp
    exact hp.ne'
  generalize max 0 (s - 1) = a at hsum hd ⊢
  generalize min 1 s = b at hsum hd ⊢
  rw [← hsum]
  field_simp
  ring

theorem twoCappedMarginalDensity_eq_zero (s x : ℝ) (hx : x ∉ Icc (0 : ℝ) (min 1 s)) :
    twoCappedMarginalDensity s x = 0 := by
  have hnot : x ∉ twoSliceInterval s := fun h =>
    hx ⟨(le_max_left _ _).trans h.1, h.2⟩
  simp [twoCappedMarginalDensity, twoCoordinateSlice, hnot]

theorem twoCapped_to_simplex_ratio_monotone {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    MonotoneOn (fun x => twoCappedMarginalDensity s x / simplexMarginalDensity 2 s x)
      (Ioo (0 : ℝ) (min 1 s)) := by
  intro x hx y hy hxy
  change twoCappedMarginalDensity s x / simplexMarginalDensity 2 s x ≤
    twoCappedMarginalDensity s y / simplexMarginalDensity 2 s y
  have hxs : x ∈ Icc (0 : ℝ) s := ⟨hx.1.le, (hx.2.trans_le (min_le_right _ _)).le⟩
  have hys : y ∈ Icc (0 : ℝ) s := ⟨hy.1.le, (hy.2.trans_le (min_le_right _ _)).le⟩
  by_cases hxI : x ∈ twoSliceInterval s
  · have hyI : y ∈ twoSliceInterval s := ⟨hxI.1.trans hxy, hy.2.le⟩
    simp [twoCappedMarginalDensity, twoCoordinateSlice, simplexMarginalDensity, hxI, hyI, hxs, hys]
  · simp only [twoCappedMarginalDensity, twoCoordinateSlice, indicator_of_notMem hxI, zero_div]
    exact div_nonneg (twoCappedMarginalDensity_nonneg s y)
      (simplexMarginalDensity_nonneg 2 (by omega) hs.1 y)

theorem twoCappedMarginal_convexOrder {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Icc 0 s) φ) (hφcont : ContinuousOn φ (Icc 0 s)) :
    (∫ x, φ x * twoCappedMarginalDensity s x) ≤
      ∫ x, φ x * simplexMarginalDensity 2 s x := by
  apply convex_integral_le_of_capped_monotone_ratio
    (lt_min (by norm_num) hs.1) (min_le_right (1 : ℝ) s)
    (twoCappedMarginalDensity_nonneg s)
    (simplexMarginalDensity_nonneg 2 (by omega) hs.1)
    (twoCappedMarginalDensity_eq_zero s)
    (fun _ hx => simplexMarginalDensity_eq_zero hx)
    (fun x hx => simplexMarginalDensity_pos 2 (by omega) hs.1
      ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩)
    (twoCapped_to_simplex_ratio_monotone hs)
    (twoCappedMarginalDensity_integrable s) (simplexMarginalDensity_integrable 2 s)
    (twoCappedMarginalDensity_test_integrable s continuous_id.continuousOn)
    (simplexMarginalDensity_test_integrable 2 s continuous_id.continuousOn)
    (twoCappedMarginalDensity_test_integrable s hφcont)
    (simplexMarginalDensity_test_integrable 2 s hφcont)
  · rw [twoCappedMarginalDensity_mass hs, simplexMarginalDensity_mass 2 (by omega) hs.1]
  · rw [twoCappedMarginalDensity_mean hs, simplexMarginalDensity_mean 2 (by omega) hs.1]
    norm_num
  · exact hφ

end
end ENT.Historical
