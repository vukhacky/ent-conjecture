module

public import ENT.Pilot.CompleteN11K1
public import ENT.Pilot.CompleteN11K2
public import ENT.Pilot.CompleteN11K3
public import ENT.Pilot.CompleteN11K4
public import ENT.Pilot.CompleteN11K5
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension11_cellwise_from_complete_checker : CellwiseCurvature 11 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 5 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 11 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN11K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN11K1Data] using hs1)
  · rcases completeN11K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN11K2Data] using hs1)
  · rcases completeN11K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN11K3Data] using hs1)
  · rcases completeN11K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN11K4Data] using hs1)
  · rcases completeN11K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN11K5Data] using hs1)

theorem dimension11_potential_expectation_le (a : Fin 11 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 11 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 11 x ∂projectionLaw (diagonal 11) :=
  diagonalSplinePotential_expectation_le 11 (by decide)
    dimension11_cellwise_from_complete_checker a ha

end
end ENT.Pilot
