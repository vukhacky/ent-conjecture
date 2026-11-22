module

public import ENT.Pilot.FiniteRange7To20
public import ENT.Pilot.FiniteRange21To23
public import ENT.Pilot.FiniteRange24To27
public import ENT.FiniteCertificates.Range28To30
public import ENT.Spline.PureCertificateBridge

/-! Spline-cell curvature bounds through dimension 30. -/

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem cellwise_curvature_seven_through_thirty (n : ℕ)
    (hn0 : 7 ≤ n) (hn1 : n ≤ 30) : Spline.CellwiseCurvature n := by
  by_cases h20 : n ≤ 20
  · exact Pilot.cellwise_curvature_seven_through_twenty n hn0 h20
  by_cases h23 : n ≤ 23
  · exact Pilot.cellwise_curvature_twentyone_through_twentythree n (by omega) h23
  by_cases h27 : n ≤ 27
  · exact Pilot.FiniteRange24To27_cellwise n (by omega) h27
  exact Spline.cellwiseCurvature_of_pure_family n (by omega)
    Certificate.PureFast.fastCheckCell Certificate.PureFast.fastCheckCell_sound
    (family_28_30 n (by omega) hn1)

end ENT.FiniteCertificates
