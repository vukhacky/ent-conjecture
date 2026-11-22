module

public import ENT.Basic.ProjectionMoments
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Exact moments through degree eight for the variance-one uniform
projection used in the manuscript's small-dimensional argument. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace ENT.Small
noncomputable section

theorem integral_projectionLaw_pow_six {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 6 ∂projectionLaw a) =
      (5 / 9 : ℝ) * (∑ i, (a i) ^ 2) ^ 3 -
      (2 / 3 : ℝ) * (∑ i, (a i) ^ 2) * (∑ i, (a i) ^ 4) +
      (16 / 63 : ℝ) * ∑ i, (a i) ^ 6 := by
  induction n with
  | zero =>
    rw [projectionLaw, integral_map (measurable_projection a).aemeasurable (by fun_prop)]
    simp [projection]
  | succ n ih =>
    have h2 : (∑ i, (a i) ^ 2) = (a 0) ^ 2 +
        ∑ i, (removeCoefficient a 0 i) ^ 2 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 2) 0
    have h4 : (∑ i, (a i) ^ 4) = (a 0) ^ 4 +
        ∑ i, (removeCoefficient a 0 i) ^ 4 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 4) 0
    have h6 : (∑ i, (a i) ^ 6) = (a 0) ^ 6 +
        ∑ i, (removeCoefficient a 0 i) ^ 6 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 6) 0
    rw [h2, h4, h6, integral_projectionLaw_pow_succ]
    norm_num [Finset.sum_range_succ, Nat.choose, integral_projectionLaw_sq,
      integral_projectionLaw_pow_four, ih]
    ring

theorem integral_projectionLaw_pow_eight {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 8 ∂projectionLaw a) =
      (35 / 27 : ℝ) * (∑ i, (a i) ^ 2) ^ 4 -
      (28 / 9 : ℝ) * (∑ i, (a i) ^ 2) ^ 2 * (∑ i, (a i) ^ 4) +
      (64 / 27 : ℝ) * (∑ i, (a i) ^ 2) * (∑ i, (a i) ^ 6) +
      (28 / 45 : ℝ) * (∑ i, (a i) ^ 4) ^ 2 -
      (16 / 15 : ℝ) * ∑ i, (a i) ^ 8 := by
  induction n with
  | zero =>
    rw [projectionLaw, integral_map (measurable_projection a).aemeasurable (by fun_prop)]
    simp [projection]
  | succ n ih =>
    have h2 : (∑ i, (a i) ^ 2) = (a 0) ^ 2 +
        ∑ i, (removeCoefficient a 0 i) ^ 2 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 2) 0
    have h4 : (∑ i, (a i) ^ 4) = (a 0) ^ 4 +
        ∑ i, (removeCoefficient a 0 i) ^ 4 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 4) 0
    have h6 : (∑ i, (a i) ^ 6) = (a 0) ^ 6 +
        ∑ i, (removeCoefficient a 0 i) ^ 6 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 6) 0
    have h8 : (∑ i, (a i) ^ 8) = (a 0) ^ 8 +
        ∑ i, (removeCoefficient a 0 i) ^ 8 :=
      Fin.sum_univ_succAbove (fun i => (a i) ^ 8) 0
    rw [h2, h4, h6, h8, integral_projectionLaw_pow_succ]
    norm_num [Finset.sum_range_succ, Nat.choose, integral_projectionLaw_sq,
      integral_projectionLaw_pow_four, integral_projectionLaw_pow_six, ih]
    ring

def varianceOneProjectionLaw {n : ℕ} (a : Fin n → ℝ) : Measure ℝ :=
  (projectionLaw a).map (fun x => Real.sqrt 3 * x)

theorem integrable_varianceOne_pow {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    Integrable (fun x => x ^ k) (varianceOneProjectionLaw a) :=
  integrable_map_mul_pow _ (integrable_projectionLaw_pow a k) _

theorem varianceOne_moment_two {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x ^ 2 ∂varianceOneProjectionLaw a) = 1 := by
  rw [varianceOneProjectionLaw, integral_map_mul_pow,
    integral_projectionLaw_sq_of_isUnit a ha, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem varianceOne_moment_four {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x ^ 4 ∂varianceOneProjectionLaw a) =
      3 - (6 / 5 : ℝ) * ∑ i, (a i) ^ 4 := by
  rw [varianceOneProjectionLaw, integral_map_mul_pow,
    integral_projectionLaw_pow_four_of_isUnit a ha]
  have hs : Real.sqrt 3 ^ 4 = (9 : ℝ) := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hs]
  ring

theorem varianceOne_moment_six {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x ^ 6 ∂varianceOneProjectionLaw a) =
      15 - 18 * (∑ i, (a i) ^ 4) + (48 / 7 : ℝ) * ∑ i, (a i) ^ 6 := by
  rw [varianceOneProjectionLaw, integral_map_mul_pow, integral_projectionLaw_pow_six, ha]
  have hs : Real.sqrt 3 ^ 6 = (27 : ℝ) := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hs]
  ring

theorem varianceOne_moment_eight {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x ^ 8 ∂varianceOneProjectionLaw a) =
      105 - 252 * (∑ i, (a i) ^ 4) + 192 * (∑ i, (a i) ^ 6) +
      (252 / 5 : ℝ) * (∑ i, (a i) ^ 4) ^ 2 - (432 / 5 : ℝ) * ∑ i, (a i) ^ 8 := by
  rw [varianceOneProjectionLaw, integral_map_mul_pow, integral_projectionLaw_pow_eight, ha]
  have hs : Real.sqrt 3 ^ 8 = (81 : ℝ) := by
    rw [show (8 : ℕ) = 2 * 4 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hs]
  ring

def octicPolynomial (c₁ c₂ c₃ c₄ x : ℝ) : ℝ :=
  c₁ * x ^ 2 + c₂ * x ^ 4 + c₃ * x ^ 6 + c₄ * x ^ 8

def powerSum {n : ℕ} (w : Fin n → ℝ) (k : ℕ) : ℝ := ∑ i, (w i) ^ k

def octicWeightExpression {n : ℕ} (c₁ c₂ c₃ c₄ : ℝ) (w : Fin n → ℝ) : ℝ :=
  c₁ + 3 * c₂ + 15 * c₃ + 105 * c₄ -
    ((6 / 5 : ℝ) * c₂ + 18 * c₃ + 252 * c₄) * powerSum w 2 +
    ((48 / 7 : ℝ) * c₃ + 192 * c₄) * powerSum w 3 +
    ((252 / 5 : ℝ) * c₄) * (powerSum w 2) ^ 2 -
    ((432 / 5 : ℝ) * c₄) * powerSum w 4

theorem octicPolynomial_integrable {n : ℕ} (a : Fin n → ℝ) (c₁ c₂ c₃ c₄ : ℝ) :
    Integrable (octicPolynomial c₁ c₂ c₃ c₄) (varianceOneProjectionLaw a) :=
  (((integrable_varianceOne_pow a 2).const_mul c₁).add
    ((integrable_varianceOne_pow a 4).const_mul c₂)).add
    ((integrable_varianceOne_pow a 6).const_mul c₃) |>.add
    ((integrable_varianceOne_pow a 8).const_mul c₄)

theorem octicPolynomial_expectation {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a)
    (c₁ c₂ c₃ c₄ : ℝ) :
    (∫ x, octicPolynomial c₁ c₂ c₃ c₄ x ∂varianceOneProjectionLaw a) =
      octicWeightExpression c₁ c₂ c₃ c₄ (fun i => (a i) ^ 2) := by
  unfold octicPolynomial
  have h2 := (integrable_varianceOne_pow a 2).const_mul c₁
  have h4 := (integrable_varianceOne_pow a 4).const_mul c₂
  have h6 := (integrable_varianceOne_pow a 6).const_mul c₃
  have h8 := (integrable_varianceOne_pow a 8).const_mul c₄
  rw [integral_add ((h2.fun_add h4).fun_add h6) h8,
    integral_add (h2.fun_add h4) h6, integral_add h2 h4]
  simp only [integral_const_mul, varianceOne_moment_two a ha,
    varianceOne_moment_four a ha, varianceOne_moment_six a ha,
    varianceOne_moment_eight a ha, octicWeightExpression, powerSum, ← pow_mul]
  norm_num
  ring

end
end ENT.Small
