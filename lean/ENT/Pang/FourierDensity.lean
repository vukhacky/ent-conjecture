module

public import ENT.Pang.FourierTiltLaw
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! An explicit continuous density of the actual standardized tilted sum law. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ENT.Pang

noncomputable section

def centerStandardize (n : ℕ) (t x : ℝ) : ℝ :=
  (x - Real.sqrt (n : ℝ) * tiltMean t) / Real.sqrt (tiltVariance t)

theorem measurable_centerStandardize (n : ℕ) (t : ℝ) :
    Measurable (centerStandardize n t) := by unfold centerStandardize; fun_prop

theorem standardizedSumLaw_eq_map_tiltedDiagonal {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) :
    standardizedSumLaw n t = (tiltedDiagonalLaw n t).map (centerStandardize n t) := by
  let := isProbabilityMeasure_tiltLaw ht
  let g : (Fin n → ℝ) → Fin n → ℝ := fun x i => standardize t (x i)
  have hg : Measurable g := by
    exact Measurable.of_eval fun i => (continuous_standardize t).measurable.comp (measurable_pi_apply i)
  have hprod : Measure.pi (fun _ : Fin n => standardizedLaw t) =
      (Measure.pi (fun _ : Fin n => tiltLaw t)).map g := by
    rw [show g = fun x i => standardize t (x i) from rfl,
      Measure.pi_map_pi (fun _ => (continuous_standardize t).measurable.aemeasurable)]
    rfl
  rw [standardizedSumLaw, hprod, Measure.map_map (by fun_prop) hg,
    tiltedDiagonalLaw, iidSumLaw,
    Measure.map_map (by fun_prop) (measurable_sumProjection01 n),
    Measure.map_map (measurable_centerStandardize n t) (by fun_prop)]
  congr 1
  funext x
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)
  have hv : Real.sqrt (tiltVariance t) ≠ 0 := Real.sqrt_ne_zero'.mpr (tiltVariance_pos ht)
  simp only [Function.comp_apply, g, standardize, centerStandardize, sumProjection01,
    ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  nlinarith [congrArg (fun z : ℝ => z * tiltMean t) (Real.sq_sqrt (Nat.cast_nonneg n))]

def tiltedDiagonalDensity (n : ℕ) (t x : ℝ) : ℝ :=
  Spline.diagonalSplineDensity n x *
    ((tiltNormalizer t) ^ n * Real.exp (t * Real.sqrt (n : ℝ) * x))

theorem continuous_tiltedDiagonalDensity (n : ℕ) (t : ℝ) :
    Continuous (tiltedDiagonalDensity n t) := by
  unfold tiltedDiagonalDensity
  exact (Spline.continuous_diagonalSplineDensity n).mul (by fun_prop)

theorem tiltedDiagonalDensity_nonneg {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n)
    (x : ℝ) : 0 ≤ tiltedDiagonalDensity n t x := by
  unfold tiltedDiagonalDensity
  exact mul_nonneg (Spline.diagonalSplineDensity_nonneg n hn x)
    (mul_nonneg (pow_nonneg (tiltNormalizer_pos ht).le n) (Real.exp_pos _).le)

theorem tiltedDiagonalDensity_support {n : ℕ} (hn : 2 ≤ n) (t x : ℝ)
    (hx : x ∉ Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))) :
    tiltedDiagonalDensity n t x = 0 := by
  unfold tiltedDiagonalDensity
  rw [Spline.diagonalSplineDensity_eq_zero_of_not_mem n hn x hx, zero_mul]

theorem hasCompactSupport_tiltedDiagonalDensity {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    HasCompactSupport (tiltedDiagonalDensity n t) := by
  exact (Spline.hasCompactSupport_diagonalSplineDensity n hn).mul_right

theorem integrable_tiltedDiagonalDensity {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    Integrable (tiltedDiagonalDensity n t) volume :=
  (continuous_tiltedDiagonalDensity n t).integrable_of_hasCompactSupport
    (hasCompactSupport_tiltedDiagonalDensity hn t)

theorem tiltedDiagonalDensity_law {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n) :
    tiltedDiagonalLaw n t =
      volume.withDensity (fun x => ENNReal.ofReal (tiltedDiagonalDensity n t x)) := by
  rw [tiltedDiagonalLaw_eq ht (by omega), Spline.diagonalSplineDensity_law n hn,
    ← withDensity_mul _ (Spline.continuous_diagonalSplineDensity n).measurable.ennreal_ofReal
      (measurable_exponentialWeight _ _)]
  congr 1
  funext x
  simp only [Pi.mul_apply, tiltedDiagonalDensity, exponentialWeight]
  exact (ENNReal.ofReal_mul (Spline.diagonalSplineDensity_nonneg n hn x)).symm

def standardizedDensity (n : ℕ) (t x : ℝ) : ℝ :=
  Real.sqrt (tiltVariance t) * tiltedDiagonalDensity n t
    (Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t)

theorem continuous_standardizedDensity (n : ℕ) (t : ℝ) : Continuous (standardizedDensity n t) := by
  unfold standardizedDensity
  exact continuous_const.mul ((continuous_tiltedDiagonalDensity n t).comp (by fun_prop))

theorem standardizedDensity_nonneg {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ standardizedDensity n t x :=
  mul_nonneg (Real.sqrt_nonneg _) (tiltedDiagonalDensity_nonneg ht hn _)

def standardizedDensityRadius (n : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (n : ℝ) + |Real.sqrt (n : ℝ) * tiltMean t|) / Real.sqrt (tiltVariance t)

theorem standardizedDensity_support {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n)
    (x : ℝ) (hx : x ∉ Icc (-standardizedDensityRadius n t) (standardizedDensityRadius n t)) :
    standardizedDensity n t x = 0 := by
  have hs : 0 < Real.sqrt (tiltVariance t) := Real.sqrt_pos.mpr (tiltVariance_pos ht)
  have hR : Real.sqrt (tiltVariance t) * standardizedDensityRadius n t =
      Real.sqrt (n : ℝ) + |Real.sqrt (n : ℝ) * tiltMean t| := by
    unfold standardizedDensityRadius
    field_simp
  have hout : Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t ∉
      Icc (-Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
    intro hz
    apply hx
    constructor
    · apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith [hz.1, le_abs_self (Real.sqrt (n : ℝ) * tiltMean t)]
    · apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith [hz.2, neg_abs_le (Real.sqrt (n : ℝ) * tiltMean t)]
  unfold standardizedDensity
  rw [tiltedDiagonalDensity_support hn _ _ hout, mul_zero]

theorem hasCompactSupport_standardizedDensity {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 2 ≤ n) : HasCompactSupport (standardizedDensity n t) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-standardizedDensityRadius n t) (standardizedDensityRadius n t)) isCompact_Icc
  intro x hx
  by_contra hnot
  exact hx (standardizedDensity_support ht hn x hnot)

theorem integrable_standardizedDensity {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n) :
    Integrable (standardizedDensity n t) volume :=
  (continuous_standardizedDensity n t).integrable_of_hasCompactSupport
    (hasCompactSupport_standardizedDensity ht hn)

def standardSumEquiv (n : ℕ) (t : ℝ) (ht : 0 < t) : ℝ ≃ᵐ ℝ where
  toFun x := Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t
  invFun := centerStandardize n t
  left_inv x := by
    have hs : Real.sqrt (tiltVariance t) ≠ 0 := Real.sqrt_ne_zero'.mpr (tiltVariance_pos ht)
    unfold centerStandardize
    field_simp
    <;> ring
  right_inv x := by
    have hs : Real.sqrt (tiltVariance t) ≠ 0 := Real.sqrt_ne_zero'.mpr (tiltVariance_pos ht)
    unfold centerStandardize
    field_simp
    <;> ring
  measurable_toFun := by
    change Measurable (fun x : ℝ => Real.sqrt (tiltVariance t) * x + Real.sqrt (n : ℝ) * tiltMean t)
    fun_prop
  measurable_invFun := measurable_centerStandardize n t

theorem standardSumEquiv_hasDerivAt (n : ℕ) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (standardSumEquiv n t ht) (Real.sqrt (tiltVariance t)) x := by
  convert ((hasDerivAt_id x).const_mul (Real.sqrt (tiltVariance t))).add_const
    (Real.sqrt (n : ℝ) * tiltMean t) using 1
  · rfl
  · ring

theorem standardizedDensity_law {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n) :
    standardizedSumLaw n t =
      volume.withDensity (fun x => ENNReal.ofReal (standardizedDensity n t x)) := by
  rw [standardizedSumLaw_eq_map_tiltedDiagonal ht (by omega), tiltedDiagonalDensity_law ht hn]
  let e := standardSumEquiv n t ht
  change (volume.withDensity (fun x => ENNReal.ofReal (tiltedDiagonalDensity n t x))).map e.symm = _
  apply Measure.ext
  intro s hs
  rw [e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs
    (fun x => standardSumEquiv_hasDerivAt n t ht x)
    (Filter.Eventually.of_forall (tiltedDiagonalDensity_nonneg ht hn))
    (integrable_tiltedDiagonalDensity hn t)]
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_standardizedDensity ht hn).integrableOn
      (Filter.Eventually.of_forall (standardizedDensity_nonneg ht hn))]
  congr 1
  apply setIntegral_congr_fun hs
  intro x hx
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

theorem integral_standardizedDensity {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 2 ≤ n) :
    (∫ x, standardizedDensity n t x) = 1 := by
  let := isProbabilityMeasure_standardizedSumLaw ht n
  exact integral_eq_one_of_density_law (integrable_standardizedDensity ht hn)
    (standardizedDensity_nonneg ht hn) (standardizedDensity_law ht hn)

end
end ENT.Pang
