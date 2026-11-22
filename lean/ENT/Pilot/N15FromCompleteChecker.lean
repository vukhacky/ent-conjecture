module

public import ENT.Pilot.CompleteN15K1
public import ENT.Pilot.CompleteN15K2
public import ENT.Pilot.CompleteN15K3
public import ENT.Pilot.CompleteN15K4
public import ENT.Pilot.CompleteN15K5
public import ENT.Pilot.CompleteN15K6
public import ENT.Pilot.CompleteN15K7
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension15_cellwise_from_complete_checker : CellwiseCurvature 15 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 7 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 15 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN15K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K1Data] using hs1)
  · rcases completeN15K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K2Data] using hs1)
  · rcases completeN15K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K3Data] using hs1)
  · rcases completeN15K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K4Data] using hs1)
  · rcases completeN15K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K5Data] using hs1)
  · rcases completeN15K6_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K6Data] using hs1)
  · rcases completeN15K7_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN15K7Data] using hs1)

theorem dimension15_potential_expectation_le (a : Fin 15 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 15 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 15 x ∂projectionLaw (diagonal 15) :=
  diagonalSplinePotential_expectation_le 15 (by decide)
    dimension15_cellwise_from_complete_checker a ha

end
end ENT.Pilot
