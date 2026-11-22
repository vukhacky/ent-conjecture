module

public import ENT.Pang.CharacteristicSum
public import ENT.Pang.OddComparison

/-! The standardized tilted density and its single crossing, using an affine change of variables in Lebesgue integrals. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

def standardDensity (t y : ℝ) : ℝ :=
  Real.sqrt (tiltVariance t) *
    tiltDensity t (Real.sqrt (tiltVariance t) * y + tiltMean t)

def standardCrossing (t : ℝ) : ℝ :=
  (1 - tiltMean t) / Real.sqrt (tiltVariance t)

theorem standardDensity_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) :
    0 ≤ standardDensity t y := by
  exact mul_nonneg (Real.sqrt_nonneg _) (tiltDensity_nonneg ht _)

theorem standardCrossing_pos {t : ℝ} (ht : 0 < t) : 0 < standardCrossing t := by
  exact div_pos (sub_pos.mpr (tiltMean_lt_one ht)) (Real.sqrt_pos.mpr (tiltVariance_pos ht))

theorem integrable_mul_tiltDensity_of_continuous (t : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable (fun x => f x * tiltDensity t x) := by
  have heq : (fun x => f x * tiltDensity t x) =
      (Icc (-1 : ℝ) 1).indicator (fun x => f x * tiltWeight t x) := by
    funext x
    unfold tiltDensity
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  rw [heq]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply ContinuousOn.integrableOn_Icc
  apply Continuous.continuousOn
  apply hf.mul
  unfold tiltWeight
  fun_prop

theorem standardDensity_integrand_affine {t : ℝ} (ht : 0 < t)
    (h : ℝ → ℝ) (y : ℝ) :
    h y * standardDensity t y =
      Real.sqrt (tiltVariance t) *
        (h (standardize t (Real.sqrt (tiltVariance t) * y + tiltMean t)) *
          tiltDensity t (Real.sqrt (tiltVariance t) * y + tiltMean t)) := by
  have hs : Real.sqrt (tiltVariance t) ≠ 0 := (Real.sqrt_pos.mpr (tiltVariance_pos ht)).ne'
  have heq : standardize t (Real.sqrt (tiltVariance t) * y + tiltMean t) = y := by
    unfold standardize
    field_simp
    ring
  rw [heq]
  unfold standardDensity
  ring

theorem integrable_mul_standardDensity_of_continuous {t : ℝ} (ht : 0 < t)
    {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun y => h y * standardDensity t y) := by
  have hg := integrable_mul_tiltDensity_of_continuous t
    (hh.comp (continuous_standardize t))
  have hs : Real.sqrt (tiltVariance t) ≠ 0 := (Real.sqrt_pos.mpr (tiltVariance_pos ht)).ne'
  have ha := ((hg.comp_add_right (tiltMean t)).comp_mul_left' hs).const_mul
    (Real.sqrt (tiltVariance t))
  apply ha.congr
  exact Filter.Eventually.of_forall (fun y => (standardDensity_integrand_affine ht h y).symm)

/-- Exact affine density transformation, valid even before assuming the
integrability of the displayed test function. -/
theorem integral_mul_standardDensity {t : ℝ} (ht : 0 < t) (h : ℝ → ℝ) :
    (∫ y, h y * standardDensity t y) = ∫ x, h (standardize t x) ∂tiltLaw t := by
  let s := Real.sqrt (tiltVariance t)
  let g := fun x : ℝ => h (standardize t x) * tiltDensity t x
  have hs : 0 < s := Real.sqrt_pos.mpr (tiltVariance_pos ht)
  have heq : (fun y => h y * standardDensity t y) =
      (fun y => s * g (s * y + tiltMean t)) := by
    funext y
    exact standardDensity_integrand_affine ht h y
  have hc : (∫ y, g (s * y + tiltMean t)) = s⁻¹ * ∫ x, g x := by
    calc
      (∫ y, g (s * y + tiltMean t)) =
          |s⁻¹| • ∫ z, g (z + tiltMean t) :=
        Measure.integral_comp_mul_left (fun z => g (z + tiltMean t)) s
      _ = s⁻¹ * ∫ x, g x := by
        rw [integral_add_right_eq_self, abs_of_pos (inv_pos.mpr hs), smul_eq_mul]
  rw [heq, integral_const_mul, hc]
  rw [integral_tiltLaw ht, ← integral_mul_tiltDensity]
  change s * (s⁻¹ * ∫ x, g x) = ∫ x, g x
  field_simp

theorem integral_standardDensity {t : ℝ} (ht : 0 < t) :
    (∫ y, standardDensity t y) = 1 := by
  have h := integral_mul_standardDensity ht (fun _ => 1)
  letI := isProbabilityMeasure_tiltLaw ht
  simpa using h

theorem standardDensity_moment {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∫ y, y ^ k * standardDensity t y) = tiltStandardMoment t k := by
  rw [integral_mul_standardDensity ht, tiltStandardMoment_eq_integral ht]
  rfl

theorem standardDensity_mean {t : ℝ} (ht : 0 < t) :
    (∫ y, y * standardDensity t y) = 0 := by
  simpa only [pow_one, tiltStandardMoment_one ht] using standardDensity_moment ht 1

theorem tiltWeight_strictMono {t : ℝ} (ht : 0 < t) : StrictMono (tiltWeight t) := by
  intro x y hxy
  unfold tiltWeight
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxy ht))
    (div_pos ht (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr ht)))

theorem standardDensity_crossing_left {t : ℝ} (ht : 0 < t) {y : ℝ}
    (hy : 0 < y) (hyb : y < standardCrossing t) :
    0 < standardDensity t y - standardDensity t (-y) := by
  have hs : 0 < Real.sqrt (tiltVariance t) := Real.sqrt_pos.mpr (tiltVariance_pos ht)
  have hm := tiltMean_pos ht
  have hm1 := tiltMean_lt_one ht
  have hsy : 0 < Real.sqrt (tiltVariance t) * y := mul_pos hs hy
  have hupper : Real.sqrt (tiltVariance t) * y < 1 - tiltMean t := by
    have h := (lt_div_iff₀ hs).mp hyb
    nlinarith
  have hmem : Real.sqrt (tiltVariance t) * y + tiltMean t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  have hnmem : Real.sqrt (tiltVariance t) * (-y) + tiltMean t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith
  unfold standardDensity tiltDensity
  rw [indicator_of_mem hmem, indicator_of_mem hnmem]
  exact sub_pos.mpr (mul_lt_mul_of_pos_left
    (tiltWeight_strictMono ht (by nlinarith)) hs)

theorem standardDensity_crossing_right {t : ℝ} (ht : 0 < t) {y : ℝ}
    (hby : standardCrossing t < y) :
    standardDensity t y - standardDensity t (-y) ≤ 0 := by
  have hs : 0 < Real.sqrt (tiltVariance t) := Real.sqrt_pos.mpr (tiltVariance_pos ht)
  have hupper : 1 < Real.sqrt (tiltVariance t) * y + tiltMean t := by
    have h := (div_lt_iff₀ hs).mp hby
    nlinarith
  have hnmem : Real.sqrt (tiltVariance t) * y + tiltMean t ∉ Icc (-1 : ℝ) 1 := by
    intro h
    exact (not_le_of_gt hupper) h.2
  have hz : standardDensity t y = 0 := by
    unfold standardDensity
    rw [tiltDensity_support _ _ hnmem, mul_zero]
  rw [hz]
  exact sub_nonpos.mpr (standardDensity_nonneg ht _)

theorem standard_odd_convex_nonpos {t : ℝ} (ht : 0 < t) {h : ℝ → ℝ}
    (hh : Continuous h) (hodd : ∀ x, h (-x) = -h x)
    (hconv : ConvexOn ℝ (Ici 0) h) :
    (∫ x, h (standardize t x) ∂tiltLaw t) ≤ 0 := by
  rw [← integral_mul_standardDensity ht]
  apply integral_odd_convex_nonpos (standardCrossing_pos ht) hodd hconv
  · exact fun x hx hxb => (standardDensity_crossing_left ht hx hxb).le
  · exact fun x hbx => standardDensity_crossing_right ht hbx
  · exact integrable_mul_standardDensity_of_continuous ht hh
  · exact integrable_mul_standardDensity_of_continuous ht continuous_id
  · exact standardDensity_mean ht

end
end ENT.Pang
