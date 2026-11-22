module

public import ENT.Pilot.N7FromCompleteChecker
public import ENT.Pilot.N8FromCompleteChecker
public import ENT.Pilot.N9FromCompleteChecker
public import ENT.Pilot.N10FromCompleteChecker
public import ENT.Pilot.N11FromCompleteChecker
public import ENT.Pilot.N12FromCompleteChecker
public import ENT.Pilot.N13FromCompleteChecker
public import ENT.Pilot.N14FromCompleteChecker
public import ENT.Pilot.N15FromCompleteChecker
public import ENT.Pilot.N16FromCompleteChecker
public import ENT.Pilot.N17FromCompleteChecker

/-! Complete cell coverage for dimensions 7–17. -/

@[expose] public section
set_option autoImplicit false

open ENT.Spline MeasureTheory

namespace ENT.Pilot

noncomputable section

theorem cellwise_curvature_seven_through_seventeen (n : ℕ) (hn0 : 7 ≤ n) (hn1 : n ≤ 17) :
    CellwiseCurvature n := by
  interval_cases n
  · exact dimension7_cellwise_from_complete_checker
  · exact dimension8_cellwise_from_complete_checker
  · exact dimension9_cellwise_from_complete_checker
  · exact dimension10_cellwise_from_complete_checker
  · exact dimension11_cellwise_from_complete_checker
  · exact dimension12_cellwise_from_complete_checker
  · exact dimension13_cellwise_from_complete_checker
  · exact dimension14_cellwise_from_complete_checker
  · exact dimension15_cellwise_from_complete_checker
  · exact dimension16_cellwise_from_complete_checker
  · exact dimension17_cellwise_from_complete_checker

theorem potential_expectation_le_seven_through_seventeen (n : ℕ) (hn0 : 7 ≤ n) (hn1 : n ≤ 17)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential n x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential n x ∂projectionLaw (diagonal n) :=
  diagonalSplinePotential_expectation_le n (by omega)
    (cellwise_curvature_seven_through_seventeen n hn0 hn1) a ha

end
end ENT.Pilot
