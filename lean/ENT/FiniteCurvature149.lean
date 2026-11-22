module

public import ENT.MediumDimensions149

/-! The finite family of spline certificates bounds the third derivative of the diagonal potential in dimensions 7–149. -/

@[expose] public section
set_option autoImplicit false

namespace ENT
noncomputable section

theorem diagonal_density_curvature_seven_through_149 {n : ℕ}
    (hn0 : 7 ≤ n) (hn1 : n ≤ 149) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt (n : ℝ)) :
    (7 / (n : ℝ)) * x ≤ deriv (deriv (deriv
      (fun y => -Real.log
        ((Spline.diagonalFiniteEntropyDensity n (by omega)).density y)))) x :=
  Spline.diagonalFiniteEntropyDensity_curvature_of_cellwise n (by omega)
    (cellwise_curvature_seven_through_149 n hn0 hn1) x hx0 hx1

end
end ENT
