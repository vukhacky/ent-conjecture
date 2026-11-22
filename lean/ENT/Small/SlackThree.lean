module

public import ENT.Small.QuadratureW3
public import ENT.Small.ThreeEntropy
public import ENT.Small.Exterior

/-! The actual three-dimensional approximation defect, with every scalar bound proved. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory

namespace ENT.Small
noncomputable section
open ENT.Comparison

 theorem W3_diagonal_expectation :
    (∫ x, W3 x ∂varianceOneProjectionLaw (diagonal 3)) = (4555337/10500000:ℝ) := by
  unfold W3
  rw [octicPolynomial_expectation _ (isUnit_diagonal (by decide))]
  have hdiag : (fun i : Fin 3 => (diagonal 3 i)^2) = flatWeights 3 :=
    funext (diagonal_sq 3)
  rw [hdiag]
  norm_num [octicWeightExpression, powerSum, flatWeights, Fin.sum_univ_three]

 theorem log_partitionFunction_W3_upper :
    Real.log (partitionFunction W3) ≤ (24467/25000:ℝ) := by
  have h := Real.log_le_log (partitionFunction_pos W3_exp_integrable) partitionFunction_W3_upper
  have ht := Enclosures.log_ratio_taylor_bounds
    (by norm_num : (0:ℝ) ≤ 83047/183047)
    (by norm_num : (83047/183047:ℝ) < 1) 12
  have hq : ((1 + (83047/183047:ℝ))/(1 - (83047/183047:ℝ))) = (133047/50000:ℝ) := by norm_num
  rw [hq] at ht
  have he : 2 * (Enclosures.artanhTaylor 12 (83047/183047:ℝ) +
      Enclosures.artanhError 12 (83047/183047:ℝ)) ≤ (24467/25000:ℝ) := by
    norm_num [Enclosures.artanhTaylor, Enclosures.artanhError, Finset.sum_range_succ]
  exact h.trans (ht.2.trans he)

 theorem sigma3_lt : sigma3 < (9/100000:ℝ) := by
  rw [sigma3, diagonalApproximationDefect_formula,
    diagonalFiniteEntropyDensity_three_entropy, W3_diagonal_expectation,
    Real.log_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  linarith [log_partitionFunction_W3_upper, threeH_bounds.1, log_three_bounds.1]

end
end ENT.Small
