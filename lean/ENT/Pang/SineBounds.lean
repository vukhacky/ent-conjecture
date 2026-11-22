module

public import ENT.Pang.StandardDensity
public import ENT.Pang.SineConvex

/-! Pang's single-summand signed sine bounds, with actual expectations. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT.Pang

noncomputable section

theorem integral_standardize_pow {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∫ x, standardize t x ^ k ∂tiltLaw t) = tiltStandardMoment t k :=
  (tiltStandardMoment_eq_integral ht k).symm

theorem integral_cubicSinPlus {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (∫ x, cubicSinPlus (u * standardize t x) ∂tiltLaw t) =
      u ^ 3 / 6 * tiltStandardMoment t 3 + standardSin t u := by
  have hp : Integrable (fun x => u ^ 3 / 6 * standardize t x ^ 3) (tiltLaw t) :=
    (integrable_tilt_standard_power ht 3).const_mul _
  have hs : Integrable (fun x => Real.sin (u * standardize t x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by unfold standardize; fun_prop)
  have heq : (fun x => cubicSinPlus (u * standardize t x)) =
      (fun x => u ^ 3 / 6 * standardize t x ^ 3 + Real.sin (u * standardize t x)) := by
    funext x
    unfold cubicSinPlus
    ring
  rw [heq, integral_add hp hs, integral_const_mul, integral_standardize_pow ht]
  rfl

theorem integral_cubicSinMinus {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (∫ x, cubicSinMinus (u * standardize t x) ∂tiltLaw t) =
      u ^ 3 / 6 * tiltStandardMoment t 3 - standardSin t u := by
  have hp : Integrable (fun x => u ^ 3 / 6 * standardize t x ^ 3) (tiltLaw t) :=
    (integrable_tilt_standard_power ht 3).const_mul _
  have hs : Integrable (fun x => Real.sin (u * standardize t x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by unfold standardize; fun_prop)
  have heq : (fun x => cubicSinMinus (u * standardize t x)) =
      (fun x => u ^ 3 / 6 * standardize t x ^ 3 - Real.sin (u * standardize t x)) := by
    funext x
    unfold cubicSinMinus
    ring
  rw [heq, integral_sub hp hs, integral_const_mul, integral_standardize_pow ht]
  rfl

theorem integral_fifthSinTest {t : ℝ} (ht : 0 < t) (u : ℝ) :
    (∫ x, fifthSinTest (u * standardize t x) ∂tiltLaw t) =
      u ^ 5 / 120 * tiltStandardMoment t 5 -
        u ^ 3 / 6 * tiltStandardMoment t 3 - standardSin t u := by
  have hp3 : Integrable (fun x => u ^ 3 / 6 * standardize t x ^ 3) (tiltLaw t) :=
    (integrable_tilt_standard_power ht 3).const_mul _
  have hp5 : Integrable (fun x => u ^ 5 / 120 * standardize t x ^ 5) (tiltLaw t) :=
    (integrable_tilt_standard_power ht 5).const_mul _
  have hs : Integrable (fun x => Real.sin (u * standardize t x)) (tiltLaw t) :=
    integrable_tiltLaw_of_continuous ht (by unfold standardize; fun_prop)
  have hp53 : Integrable (fun x => u ^ 5 / 120 * standardize t x ^ 5 -
      u ^ 3 / 6 * standardize t x ^ 3) (tiltLaw t) := hp5.sub hp3
  have heq : (fun x => fifthSinTest (u * standardize t x)) =
      (fun x => u ^ 5 / 120 * standardize t x ^ 5 -
        u ^ 3 / 6 * standardize t x ^ 3 - Real.sin (u * standardize t x)) := by
    funext x
    unfold fifthSinTest
    ring
  rw [heq, integral_sub hp53 hs, integral_sub hp5 hp3,
    integral_const_mul, integral_const_mul, integral_standardize_pow ht,
    integral_standardize_pow ht]
  rfl

theorem abs_standardSin_le_of_nonneg {t : ℝ} (ht : 0 < t)
    {u : ℝ} (hu : 0 ≤ u) :
    |standardSin t u| ≤ -tiltStandardMoment t 3 * u ^ 3 / 6 := by
  have hp := standard_odd_convex_nonpos ht
    (h := fun x => cubicSinPlus (u * x))
    (by unfold cubicSinPlus; fun_prop)
    (fun x => by rw [mul_neg, cubicSinPlus_odd])
    (convexOn_Ici_comp_mul_nonneg convexOn_cubicSinPlus hu)
  have hm := standard_odd_convex_nonpos ht
    (h := fun x => cubicSinMinus (u * x))
    (by unfold cubicSinMinus; fun_prop)
    (fun x => by rw [mul_neg, cubicSinMinus_odd])
    (convexOn_Ici_comp_mul_nonneg convexOn_cubicSinMinus hu)
  rw [integral_cubicSinPlus ht] at hp
  rw [integral_cubicSinMinus ht] at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The cubic global signed envelope from Pang Lemma 4.3. -/
theorem abs_standardSin_le {t : ℝ} (ht : 0 < t) (u : ℝ) :
    |standardSin t u| ≤ |tiltStandardMoment t 3| * |u| ^ 3 / 6 := by
  have hk : tiltStandardMoment t 3 < 0 := (pang_tilt_moment_bounds ht).2.1.2
  rw [abs_of_neg hk]
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
    exact abs_standardSin_le_of_nonneg ht hu
  · have h := abs_standardSin_le_of_nonneg ht (u := -u) (by linarith)
    rw [standardSin_neg, abs_neg] at h
    rwa [abs_of_neg (lt_of_not_ge hu)]

/-- The fifth-order signed lower estimate before applying the ratio bound. -/
theorem standardSin_lower_moments {t : ℝ} (ht : 0 < t)
    {u : ℝ} (hu : 0 ≤ u) :
    -tiltStandardMoment t 3 * u ^ 3 / 6 +
        tiltStandardMoment t 5 * u ^ 5 / 120 ≤ standardSin t u := by
  have h := standard_odd_convex_nonpos ht
    (h := fun x => fifthSinTest (u * x))
    (by unfold fifthSinTest; fun_prop)
    (fun x => by rw [mul_neg, fifthSinTest_odd])
    (convexOn_Ici_comp_mul_nonneg convexOn_fifthSinTest hu)
  rw [integral_fifthSinTest ht] at h
  linarith

/-- Pang Lemma 4.5. -/
theorem standardSin_lower {t : ℝ} (ht : 0 < t) {u : ℝ} (hu : 0 ≤ u) :
    |tiltStandardMoment t 3| * u ^ 3 / 6 * (1 - 11 * u ^ 2 / 10) ≤
      standardSin t u := by
  have hk : tiltStandardMoment t 3 < 0 := (pang_tilt_moment_bounds ht).2.1.2
  have hr : 22 * tiltStandardMoment t 3 < tiltStandardMoment t 5 :=
    (div_lt_iff_of_neg hk).mp (tiltStandardMoment_fifth_ratio_lt ht)
  have hm := mul_le_mul_of_nonneg_right hr.le (show 0 ≤ u ^ 5 / 120 by positivity)
  have hl := standardSin_lower_moments ht hu
  rw [abs_of_neg hk]
  nlinarith

end
end ENT.Pang
