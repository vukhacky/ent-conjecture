module

public import ENT.Basic.Uniform01Sums
public import ENT.Entropy.Finite
public import ENT.Spline.Convolution
public import ENT.Spline.AffineDensity

/-! Identification of the spline with the actual diagonal projection law.
The normalization and entropy-integrability fields are supplied by proved
probability, support, and boundedness statements. -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ENT.Spline

noncomputable section

theorem sumLaw01_eq_splineDensity (n : ℕ) (hn : 2 ≤ n) :
    sumLaw01 n = volume.withDensity (fun t => ENNReal.ofReal (unitSumSplineDensity n t)) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [sumLaw01_two, uniform01_conv_uniform01]
      congr 1
      funext t
      rw [unitSumSplineDensity_two_overlap]
      rfl
  | succ n hn ih =>
      rw [sumLaw01_succ, ih]
      exact unitInterval_conv_splineDensity n hn

theorem diagonalSplineDensity_law (n : ℕ) (hn : 2 ≤ n) :
    projectionLaw (diagonal n) =
      volume.withDensity (fun x => ENNReal.ofReal (diagonalSplineDensity n x)) := by
  rw [projectionLaw_diagonal_eq_map_sumLaw01, sumLaw01_eq_splineDensity n hn]
  exact map_unitSumSplineDensity_standardization n hn

def diagonalFiniteEntropyDensity (n : ℕ) (hn : 2 ≤ n) :
    FiniteEntropyDensity (projectionLaw (diagonal n)) :=
  finiteEntropyDensityOfBoundedSupportLaw (projectionLaw (diagonal n))
    (diagonalSplineDensity n) (Real.sqrt (n : ℝ) / 2) (Real.sqrt (n : ℝ))
    (continuous_diagonalSplineDensity n).measurable
    (diagonalSplineDensity_nonneg n hn) (diagonalSplineDensity_le n hn)
    (diagonalSplineDensity_eq_zero_of_not_mem n hn) (diagonalSplineDensity_law n hn)

@[simp]
theorem diagonalFiniteEntropyDensity_density (n : ℕ) (hn : 2 ≤ n) :
    (diagonalFiniteEntropyDensity n hn).density = diagonalSplineDensity n := rfl

theorem integral_diagonalSplineDensity (n : ℕ) (hn : 2 ≤ n) :
    (∫ x, diagonalSplineDensity n x) = 1 :=
  (diagonalFiniteEntropyDensity n hn).mass_one

theorem integrable_diagonalSplineDensity_mul_log (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun x => diagonalSplineDensity n x * Real.log (diagonalSplineDensity n x)) volume :=
  (diagonalFiniteEntropyDensity n hn).entropy_integrable

end
end ENT.Spline
