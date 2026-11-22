module

public import ENT.Basic.ProjectionSupport
public import ENT.Basic.ProjectionConvolution
public import ENT.Basic.Symmetry
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Exact finite moments of arbitrary uniform projections. -/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ENT

noncomputable section

theorem integrable_pow_of_ae_mem_Icc (μ : Measure ℝ) [IsFiniteMeasure μ]
    {R : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (-R) R) (k : ℕ) :
    Integrable (fun x => x ^ k) μ := by
  apply Integrable.of_bound (by fun_prop) (R ^ k)
  filter_upwards [hμ] with x hx
  simpa only [Real.norm_eq_abs, abs_pow] using
    (pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) k)

theorem integrable_projectionLaw_pow {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    Integrable (fun x => x ^ k) (projectionLaw a) :=
  integrable_pow_of_ae_mem_Icc (projectionLaw a) (projectionLaw_ae_mem a) k

theorem integrable_uniformUnit_pow (k : ℕ) : Integrable (fun x => x ^ k) uniformUnit :=
  integrable_pow_of_ae_mem_Icc uniformUnit uniformUnit_ae_mem k

theorem integral_uniformUnit_pow (k : ℕ) :
    (∫ x, x ^ k ∂uniformUnit) = (1 - (-1 : ℝ) ^ (k + 1)) / (2 * (k + 1)) := by
  rw [uniformUnit, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_pow]
  simp only [one_pow, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv]
  ring

theorem integral_map_mul_pow (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    (∫ x, x ^ k ∂μ.map (fun x => c * x)) = c ^ k * ∫ x, x ^ k ∂μ := by
  rw [integral_map (measurable_const_mul c).aemeasurable (by fun_prop)]
  simp only [mul_pow, integral_const_mul]

theorem integrable_map_mul_pow (μ : Measure ℝ) {k : ℕ}
    (hk : Integrable (fun x => x ^ k) μ) (c : ℝ) :
    Integrable (fun x => x ^ k) (μ.map (fun x => c * x)) := by
  apply (integrable_map_measure (by fun_prop) (measurable_const_mul c).aemeasurable).mpr
  change Integrable (fun x => (c * x) ^ k) μ
  simpa only [mul_pow] using hk.const_mul (c ^ k)

theorem integral_conv_pow (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (k : ℕ)
    (hμ : ∀ j ≤ k, Integrable (fun x => x ^ j) μ)
    (hν : ∀ j ≤ k, Integrable (fun x => x ^ j) ν) :
    (∫ x, x ^ k ∂Measure.conv μ ν) =
      ∑ j ∈ Finset.range (k + 1),
        (∫ x, x ^ j ∂μ) * (∫ y, y ^ (k - j) ∂ν) * (k.choose j : ℝ) := by
  unfold Measure.conv
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ z : ℝ × ℝ, (z.1 + z.2) ^ k ∂μ.prod ν) = _
  simp_rw [add_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const]
    congr 1
    exact integral_prod_mul (fun x : ℝ => x ^ j) (fun y : ℝ => y ^ (k - j))
  · intro j hj
    exact ((hμ j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).mul_prod
      (hν (k - j) (Nat.sub_le k j))).mul_const (k.choose j : ℝ)

theorem projectionLaw_map_neg {n : ℕ} (a : Fin n → ℝ) :
    (projectionLaw a).map (fun x => -x) = projectionLaw a := by
  have hneg : projectionLaw (fun i => -a i) = projectionLaw a := by
    rw [← projectionLaw_abs (fun i => -a i), ← projectionLaw_abs a]
    simp only [abs_neg]
  calc
    _ = projectionLaw (fun i => -a i) := by
      rw [projectionLaw, Measure.map_map (by fun_prop) (measurable_projection a)]
      congr 1
      funext x
      simp only [Function.comp_apply, projection, neg_mul, Finset.sum_neg_distrib]
    _ = _ := hneg

theorem integral_projectionLaw_pow_odd {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    (∫ x, x ^ (2 * k + 1) ∂projectionLaw a) = 0 := by
  have hneg : (∫ x, x ^ (2 * k + 1) ∂projectionLaw a) =
      -(∫ x, x ^ (2 * k + 1) ∂projectionLaw a) := by
    calc
      _ = ∫ x, x ^ (2 * k + 1) ∂(projectionLaw a).map (fun x => -x) := by
        rw [projectionLaw_map_neg]
      _ = _ := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
        simp only [hodd.neg_pow, integral_neg]
  linarith

@[simp]
theorem integral_projectionLaw_pow_zero {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 0 ∂projectionLaw a) = 1 := by simp

@[simp]
theorem integral_projectionLaw_pow_one {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 1 ∂projectionLaw a) = 0 := by
  simpa only [Nat.mul_zero, Nat.zero_add] using integral_projectionLaw_pow_odd a 0

@[simp]
theorem integral_projectionLaw_pow_three {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 3 ∂projectionLaw a) = 0 := by
  simpa only [Nat.mul_one] using integral_projectionLaw_pow_odd a 1

theorem integral_projectionLaw_pow_succ {n : ℕ} (a : Fin (n + 1) → ℝ) (k : ℕ) :
    (∫ x, x ^ k ∂projectionLaw a) =
      ∑ j ∈ Finset.range (k + 1),
        ((a 0) ^ j * ((1 - (-1 : ℝ) ^ (j + 1)) / (2 * (j + 1)))) *
          (∫ y, y ^ (k - j) ∂projectionLaw (removeCoefficient a 0)) * (k.choose j : ℝ) := by
  rw [projectionLaw_eq_conv_remove a 0,
    integral_conv_pow _ _ k
      (fun j _ => integrable_map_mul_pow uniformUnit (integrable_uniformUnit_pow j) (a 0))
      (fun j _ => integrable_projectionLaw_pow (removeCoefficient a 0) j)]
  simp_rw [integral_map_mul_pow, integral_uniformUnit_pow]

theorem integral_projectionLaw_sq {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 2 ∂projectionLaw a) = (∑ i, (a i) ^ 2) / 3 := by
  induction n with
  | zero =>
      rw [projectionLaw, integral_map (measurable_projection a).aemeasurable (by fun_prop)]
      simp [projection]
  | succ n ih =>
      have hsum : (∑ i, (a i) ^ 2) = (a 0) ^ 2 +
          ∑ i, (removeCoefficient a 0 i) ^ 2 :=
        Fin.sum_univ_succAbove (fun i => (a i) ^ 2) 0
      rw [hsum, integral_projectionLaw_pow_succ]
      norm_num [Finset.sum_range_succ, Nat.choose, ih]
      ring

theorem integral_projectionLaw_pow_four {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, x ^ 4 ∂projectionLaw a) =
      (∑ i, (a i) ^ 2) ^ 2 / 3 - (2 / 15 : ℝ) * ∑ i, (a i) ^ 4 := by
  induction n with
  | zero =>
      rw [projectionLaw, integral_map (measurable_projection a).aemeasurable (by fun_prop)]
      simp [projection]
  | succ n ih =>
      have hsum2 : (∑ i, (a i) ^ 2) = (a 0) ^ 2 +
          ∑ i, (removeCoefficient a 0 i) ^ 2 :=
        Fin.sum_univ_succAbove (fun i => (a i) ^ 2) 0
      have hsum4 : (∑ i, (a i) ^ 4) = (a 0) ^ 4 +
          ∑ i, (removeCoefficient a 0 i) ^ 4 :=
        Fin.sum_univ_succAbove (fun i => (a i) ^ 4) 0
      rw [hsum2, hsum4, integral_projectionLaw_pow_succ]
      norm_num [Finset.sum_range_succ, Nat.choose, integral_projectionLaw_sq, ih]
      ring

theorem integral_projectionLaw_sq_of_isUnit {n : ℕ} (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x ^ 2 ∂projectionLaw a) = (1 / 3 : ℝ) := by
  rw [integral_projectionLaw_sq, ha]

theorem integral_projectionLaw_pow_four_of_isUnit {n : ℕ} (a : Fin n → ℝ)
    (ha : IsUnit a) :
    (∫ x, x ^ 4 ∂projectionLaw a) = (1 / 3 : ℝ) - (2 / 15 : ℝ) * ∑ i, (a i) ^ 4 := by
  rw [integral_projectionLaw_pow_four, ha, one_pow]

theorem diagonal_fourth_moment_gap {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, x ^ 4 ∂projectionLaw (diagonal n)) -
        (∫ x, x ^ 4 ∂projectionLaw a) = (2 / 15 : ℝ) * deficit a := by
  rw [integral_projectionLaw_pow_four_of_isUnit a ha,
    integral_projectionLaw_pow_four_of_isUnit (diagonal n) (isUnit_diagonal hn),
    deficit_eq_sum_pow_four_sub_inv hn ha]
  have hdiag := deficit_eq_sum_pow_four_sub_inv hn (isUnit_diagonal hn)
  have hdiag0 : deficit (diagonal n) = 0 :=
    (deficit_eq_zero_iff (diagonal n)).mpr (isDiagonal_diagonal n)
  linarith

theorem projectionLaw_eq_diagonal_iff_isDiagonal {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    projectionLaw a = projectionLaw (diagonal n) ↔ IsDiagonal a := by
  refine ⟨fun h => ?_, projectionLaw_eq_diagonal_of_isDiagonal a⟩
  have h4 := congrArg (fun μ : Measure ℝ => ∫ x, x ^ 4 ∂μ) h
  rw [integral_projectionLaw_pow_four_of_isUnit a ha,
    integral_projectionLaw_pow_four_of_isUnit (diagonal n) (isUnit_diagonal hn)] at h4
  have hd := deficit_eq_sum_pow_four_sub_inv hn ha
  have hdiag := deficit_eq_sum_pow_four_sub_inv hn (isUnit_diagonal hn)
  have hdiag0 : deficit (diagonal n) = 0 :=
    (deficit_eq_zero_iff (diagonal n)).mpr (isDiagonal_diagonal n)
  apply (deficit_eq_zero_iff a).mp
  linarith

end
end ENT
