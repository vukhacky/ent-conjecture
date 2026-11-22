module

public import ENT.Pilot.CompleteN8K1
public import ENT.Pilot.CompleteN8K2
public import ENT.Pilot.CompleteN8K3
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension8_cellwise_from_complete_checker : CellwiseCurvature 8 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 3 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 8 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN8K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN8K1Data] using hs1)
  · rcases completeN8K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN8K2Data] using hs1)
  · rcases completeN8K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN8K3Data] using hs1)

theorem dimension8_potential_expectation_le (a : Fin 8 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 8 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 8 x ∂projectionLaw (diagonal 8) :=
  diagonalSplinePotential_expectation_le 8 (by decide)
    dimension8_cellwise_from_complete_checker a ha

end
end ENT.Pilot
