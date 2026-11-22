module

public import ENT.Pilot.CompleteN17K1
public import ENT.Pilot.CompleteN17K2
public import ENT.Pilot.CompleteN17K3
public import ENT.Pilot.CompleteN17K4
public import ENT.Pilot.CompleteN17K5
public import ENT.Pilot.CompleteN17K6
public import ENT.Pilot.CompleteN17K7
public import ENT.Pilot.CompleteN17K8
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension17_cellwise_from_complete_checker : CellwiseCurvature 17 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 8 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 17 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN17K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K1Data] using hs1)
  · rcases completeN17K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K2Data] using hs1)
  · rcases completeN17K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K3Data] using hs1)
  · rcases completeN17K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K4Data] using hs1)
  · rcases completeN17K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K5Data] using hs1)
  · rcases completeN17K6_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K6Data] using hs1)
  · rcases completeN17K7_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K7Data] using hs1)
  · rcases completeN17K8_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN17K8Data] using hs1)

theorem dimension17_potential_expectation_le (a : Fin 17 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 17 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 17 x ∂projectionLaw (diagonal 17) :=
  diagonalSplinePotential_expectation_le 17 (by decide)
    dimension17_cellwise_from_complete_checker a ha

end
end ENT.Pilot
