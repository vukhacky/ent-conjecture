module

public import ENT.Pilot.CompleteN13K1
public import ENT.Pilot.CompleteN13K2
public import ENT.Pilot.CompleteN13K3
public import ENT.Pilot.CompleteN13K4
public import ENT.Pilot.CompleteN13K5
public import ENT.Pilot.CompleteN13K6
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension13_cellwise_from_complete_checker : CellwiseCurvature 13 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 6 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 13 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN13K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN13K1Data] using hs1)
  · rcases completeN13K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN13K2Data] using hs1)
  · rcases completeN13K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN13K3Data] using hs1)
  · rcases completeN13K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN13K4Data] using hs1)
  · rcases completeN13K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN13K5Data] using hs1)
  · rcases completeN13K6_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN13K6Data] using hs1)

theorem dimension13_potential_expectation_le (a : Fin 13 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 13 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 13 x ∂projectionLaw (diagonal 13) :=
  diagonalSplinePotential_expectation_le 13 (by decide)
    dimension13_cellwise_from_complete_checker a ha

end
end ENT.Pilot
