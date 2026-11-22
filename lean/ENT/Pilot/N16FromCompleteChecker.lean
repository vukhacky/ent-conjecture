module

public import ENT.Pilot.CompleteN16K1
public import ENT.Pilot.CompleteN16K2
public import ENT.Pilot.CompleteN16K3
public import ENT.Pilot.CompleteN16K4
public import ENT.Pilot.CompleteN16K5
public import ENT.Pilot.CompleteN16K6
public import ENT.Pilot.CompleteN16K7
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension16_cellwise_from_complete_checker : CellwiseCurvature 16 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 7 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 16 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN16K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K1Data] using hs1)
  · rcases completeN16K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K2Data] using hs1)
  · rcases completeN16K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K3Data] using hs1)
  · rcases completeN16K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K4Data] using hs1)
  · rcases completeN16K5_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K5Data] using hs1)
  · rcases completeN16K6_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K6Data] using hs1)
  · rcases completeN16K7_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN16K7Data] using hs1)

theorem dimension16_potential_expectation_le (a : Fin 16 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 16 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 16 x ∂projectionLaw (diagonal 16) :=
  diagonalSplinePotential_expectation_le 16 (by decide)
    dimension16_cellwise_from_complete_checker a ha

end
end ENT.Pilot
