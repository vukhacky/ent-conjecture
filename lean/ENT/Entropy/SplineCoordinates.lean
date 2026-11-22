module

public import ENT.Spline.DensityLaw
public import ENT.Entropy.Finite
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Tactic.FieldSimp

/-! Entropy of the genuine diagonal law in unit-sum spline coordinates. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set

namespace ENT

noncomputable section

def unitSumFiniteEntropyDensity (n : ℕ) (hn : 2 ≤ n) : FiniteEntropyDensity (sumLaw01 n) :=
  finiteEntropyDensityOfBoundedSupportLaw (sumLaw01 n) (Spline.unitSumSplineDensity n)
    1 (n : ℝ) (Spline.continuous_unitSumSplineDensity n).measurable
    (Spline.unitSumSplineDensity_nonneg n hn) (Spline.unitSumSplineDensity_le_one n hn)
    (fun x hx => Spline.unitSumSplineDensity_eq_zero_of_not_mem n hn x (by
      intro hmem
      apply hx
      exact ⟨le_trans (neg_nonpos.mpr (Nat.cast_nonneg n)) hmem.1, hmem.2⟩))
    (Spline.sumLaw01_eq_splineDensity n hn)

@[simp] theorem unitSumFiniteEntropyDensity_density (n : ℕ) (hn : 2 ≤ n) :
    (unitSumFiniteEntropyDensity n hn).density = Spline.unitSumSplineDensity n := rfl

theorem integral_affine_reflection {k : ℝ} (hk : 0 < k) (d : ℝ) (f : ℝ → ℝ) :
    (∫ x, f (d - k * x)) = k⁻¹ * ∫ x, f x := by
  have heq : (fun x : ℝ => f (d - k * x)) = (fun x => (fun y => f (d + y)) ((-k) * x)) := by
    funext x
    congr 1
    ring
  rw [heq, Measure.integral_comp_mul_left (fun y => f (d + y)) (-k), integral_add_left_eq_self f d]
  simp only [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hk), smul_eq_mul]

theorem integral_affine_density_mul_log {μ : Measure ℝ} (p : FiniteEntropyDensity μ)
    {k : ℝ} (hk : 0 < k) (d : ℝ) :
    (∫ x, (k * p.density (d - k * x)) * Real.log (k * p.density (d - k * x))) =
      (∫ x, p.density x * Real.log (p.density x)) + Real.log k := by
  have heq : (fun x : ℝ => (k * p.density (d - k * x)) * Real.log (k * p.density (d - k * x))) =
      (fun x => k * ((fun y => p.density y * Real.log (p.density y) +
        Real.log k * p.density y) (d - k * x))) := by
    funext x
    by_cases hx : p.density (d - k * x) = 0
    · simp [hx]
    · rw [Real.log_mul hk.ne' hx]
      ring
  rw [heq, integral_const_mul, integral_affine_reflection hk d
    (fun y => p.density y * Real.log (p.density y) + Real.log k * p.density y),
    ← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul,
    integral_add p.entropy_integrable (p.integrable.const_mul (Real.log k)),
    integral_const_mul, p.mass_one, mul_one]

theorem diagonal_entropy_eq_unitSum_entropy (n : ℕ) (hn : 2 ≤ n) :
    (Spline.diagonalFiniteEntropyDensity n hn).entropy =
      (unitSumFiniteEntropyDensity n hn).entropy + Real.log (2 / Real.sqrt (n : ℝ)) := by
  have hk : 0 < Real.sqrt (n : ℝ) / 2 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hq : Spline.diagonalSplineDensity n = fun x => (Real.sqrt (n : ℝ) / 2) *
      (unitSumFiniteEntropyDensity n hn).density ((n : ℝ) / 2 - (Real.sqrt (n : ℝ) / 2) * x) := by
    funext x
    simp only [Spline.diagonalSplineDensity, unitSumFiniteEntropyDensity_density]
    congr 2
    ring
  change -(∫ x, Spline.diagonalSplineDensity n x * Real.log (Spline.diagonalSplineDensity n x)) = _
  rw [hq, integral_affine_density_mul_log _ hk]
  have hlog : -Real.log (Real.sqrt (n : ℝ) / 2) = Real.log (2 / Real.sqrt (n : ℝ)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  unfold FiniteEntropyDensity.entropy
  linarith

/-- The canonical unit-sum spline used by all rational cell integrations. -/
theorem diagonal_entropy_eq_unitSum_integral (n : ℕ) (hn : 2 ≤ n) :
    (Spline.diagonalFiniteEntropyDensity n hn).entropy =
      -(∫ t in 0..(n : ℝ), Spline.unitSumSplineDensity n t *
        Real.log (Spline.unitSumSplineDensity n t)) + Real.log (2 / Real.sqrt (n : ℝ)) := by
  rw [diagonal_entropy_eq_unitSum_entropy n hn]
  congr 1
  unfold FiniteEntropyDensity.entropy
  rw [unitSumFiniteEntropyDensity_density]
  congr 1
  calc
    _ = ∫ t in Icc (0 : ℝ) (n : ℝ), Spline.unitSumSplineDensity n t *
        Real.log (Spline.unitSumSplineDensity n t) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      rw [Spline.unitSumSplineDensity_eq_zero_of_not_mem n hn t ht, zero_mul]
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (Nat.cast_nonneg n)]

end
end ENT
