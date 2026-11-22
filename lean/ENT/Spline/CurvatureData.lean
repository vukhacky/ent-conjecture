module

public import ENT.Spline.CertificateBridge
public import ENT.Spline.SupportInterior
public import ENT.Comparison.CurvatureExpectation

/-! From exact cell inequalities to the global potential expectation
comparison for the genuine diagonal density in every admissible dimension. -/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set
open ENT.Comparison

namespace ENT.Spline

noncomputable section

theorem diagonalSpline_curvaturePotential (n : ℕ) (hn : 5 ≤ n)
    (hcert : CellwiseCurvature n) :
    CurvaturePotential (Real.sqrt n) (diagonalSplinePotential n) := by
  apply curvaturePotential_of_density (diagonalFiniteEntropyDensity n (by omega)) (Real.sqrt n)
  · exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < n))
  · exact diagonalSplineDensity_even n (by omega)
  · exact diagonalSplineDensity_pos n (by omega)
  · intro x _
    exact (contDiff_diagonalSplineDensity 3 n (by omega)).contDiffAt
  · intro x hx
    exact le_trans (mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n)) hx.1)
      (diagonalSpline_curvature_of_cellwise n hn hcert x hx.1 hx.2)

theorem diagonalSplinePotential_integrable (n : ℕ) (hn : 2 ≤ n) :
    Integrable (diagonalSplinePotential n) (projectionLaw (diagonal n)) :=
  potential_integrable_of_density (diagonalFiniteEntropyDensity n hn)

theorem diagonalSplinePotential_expectation_le (n : ℕ) (hn : 5 ≤ n)
    (hcert : CellwiseCurvature n) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential n x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential n x ∂projectionLaw (diagonal n) :=
  (diagonalSpline_curvaturePotential n hn hcert).expectation_le (by omega)
    (ae_mem_diagonalSplineSupport n (by omega)) (diagonalSplinePotential_integrable n (by omega)) a ha

end
end ENT.Spline
