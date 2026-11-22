module

public import ENT.Pang.SignedIntegral
public import ENT.Pang.FourierRatios

/-! Pang's large-dimension curvature theorem for the actual diagonal density. -/

@[expose] public section

set_option autoImplicit false

open Set

namespace ENT.Pang

noncomputable section

theorem standardizedDensity_signed_derivative_neg {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) :
    iteratedDeriv 3 (standardizedDensity n t) 0 +
      (7 / 2) * deriv (standardizedDensity n t) 0 < 0 := by
  rw [standardizedDensity_signed_derivative_eq ht (by omega)]
  have h := mul_pos (skewFourierCoefficient_pos (by omega : 0 < n) ht)
    (pang_signed_integral_pos ht hn)
  nlinarith

theorem standardizedDensity_logThird_neg {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 150 ≤ n) :
    logThirdExpression (standardizedDensity n t 0)
      (deriv (standardizedDensity n t) 0)
      (iteratedDeriv 2 (standardizedDensity n t) 0)
      (iteratedDeriv 3 (standardizedDensity n t) 0) < 0 :=
  logThirdExpression_neg_of_pang_bounds (standardizedDensity_zero_pos (by omega) ht)
    (deriv_standardizedDensity_zero_pos ht hn)
    (standardizedDensity_lowerDerivativeBracket_lt ht hn)
    (standardizedDensity_signed_derivative_neg ht hn)

/-- Strict positivity of the third potential derivative on the positive interior.
The density is the actual normalized diagonal convolution density, not an abstract function. -/
theorem pang_large_n_curvature_pos {n : ℕ} (hn : 150 ≤ n) :
    ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ)),
      0 < deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x :=
  diagonalPotential_third_deriv_pos_of_pang_bounds hn
    (fun _ ht => deriv_standardizedDensity_zero_pos ht hn)
    (fun _ ht => standardizedDensity_lowerDerivativeBracket_lt ht hn)
    (fun _ ht => standardizedDensity_signed_derivative_neg ht hn)

theorem pang_large_n_curvature_nonneg {n : ℕ} (hn : 150 ≤ n) :
    ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt (n : ℝ)),
      0 ≤ deriv (deriv (deriv (Spline.diagonalSplinePotential n))) x :=
  fun x hx => (pang_large_n_curvature_pos hn x hx).le

end
end ENT.Pang
