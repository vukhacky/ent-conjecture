module

public import ENT.Pilot.CompleteN12K1
public import ENT.Pilot.CompleteN12K2
public import ENT.Pilot.CompleteN12K3
public import ENT.Pilot.CompleteN12K4
public import ENT.Pilot.CompleteN12K5
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension12_cellwise_from_complete_checker : CellwiseCurvature 12 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 5 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 12 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN12K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN12K1Data] using hs1)
  · rcases completeN12K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN12K2Data] using hs1)
  · rcases completeN12K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN12K3Data] using hs1)
  · rcases completeN12K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN12K4Data] using hs1)
  · rcases completeN12K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN12K5Data] using hs1)

theorem dimension12_potential_expectation_le (a : Fin 12 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 12 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 12 x ∂projectionLaw (diagonal 12) :=
  diagonalSplinePotential_expectation_le 12 (by decide)
    dimension12_cellwise_from_complete_checker a ha

end
end ENT.Pilot
