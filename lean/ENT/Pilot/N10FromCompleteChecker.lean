module

public import ENT.Pilot.CompleteN10K1
public import ENT.Pilot.CompleteN10K2
public import ENT.Pilot.CompleteN10K3
public import ENT.Pilot.CompleteN10K4
public import ENT.Certificate.EdgeCell
public import ENT.Spline.CurvatureData

/-! Complete reflected-cell coverage. The edge is analytic; all other
cells invoke the complete checker and its unconditional soundness. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory

namespace ENT.Pilot
noncomputable section

theorem dimension10_cellwise_from_complete_checker : CellwiseCurvature 10 := by
  intro k hk s hs0 hs1
  have hkbound : k ≤ 4 := by omega
  interval_cases k
  · exact targetPolynomial_edge_nonneg 10 (by decide) s hs0 (by simpa using hs1)
  · rcases completeN10K1_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN10K1Data] using hs1)
  · rcases completeN10K2_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN10K2Data] using hs1)
  · rcases completeN10K3_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN10K3Data] using hs1)
  · rcases completeN10K4_conclusion with ⟨_, _, _, _, _, _, h⟩
    exact h s hs0 (by simpa [width, completeN10K4Data] using hs1)

theorem dimension10_potential_expectation_le (a : Fin 10 → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential 10 x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential 10 x ∂projectionLaw (diagonal 10) :=
  diagonalSplinePotential_expectation_le 10 (by decide)
    dimension10_cellwise_from_complete_checker a ha

end
end ENT.Pilot
