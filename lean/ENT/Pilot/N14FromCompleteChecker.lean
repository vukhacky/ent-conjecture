module

public import ENT.Pilot.CompleteN14K1
public import ENT.Pilot.CompleteN14K2
public import ENT.Pilot.CompleteN14K3
public import ENT.Pilot.CompleteN14K4
public import ENT.Pilot.CompleteN14K5
public import ENT.Pilot.CompleteN14K6
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension14_cellwise_from_complete_checker : CellwiseCurvature 14 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 6 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 14 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN14K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN14K1Data] using hs1)
  · rcases completeN14K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN14K2Data] using hs1)
  · rcases completeN14K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN14K3Data] using hs1)
  · rcases completeN14K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN14K4Data] using hs1)
  · rcases completeN14K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN14K5Data] using hs1)
  · rcases completeN14K6_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN14K6Data] using hs1)

theorem dimension14_potential_expectation_le (a : Fin 14 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 14 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 14 x ∂projectionLaw (diagonal 14) :=
  diagonalSplinePotential_expectation_le 14 (by decide)
    dimension14_cellwise_from_complete_checker a ha

end
end ENT.Pilot
