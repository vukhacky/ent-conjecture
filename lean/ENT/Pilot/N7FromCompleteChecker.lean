module

public import ENT.Pilot.N7Complete
public import ENT.Spline.CertificateBridge

/-! End-to-end n=7 curvature whose certificate premise is discharged solely
through complete checker acceptance and its unconditional soundness theorem. -/

@[expose] public section

set_option autoImplicit false

open ENT.Certificate ENT.Spline

namespace ENT.Pilot

noncomputable section

theorem dimension7_cellwise_from_complete_checker : CellwiseCurvature 7 := by
  apply cellwiseCurvature_of_checked_data
  intro k hk
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · exact ⟨n7k0Data, rfl, rfl, n7k0_complete_check⟩
  · exact ⟨n7k1Data, rfl, rfl, n7k1_complete_check⟩
  · exact ⟨n7k2Data, rfl, rfl, n7k2_complete_check⟩
  · exact ⟨n7k3Data, rfl, rfl, n7k3_complete_check⟩

theorem dimension7_genuine_curvature_from_complete_checker (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < Real.sqrt 7) :
    x ≤ deriv (deriv (deriv
      (fun y => -Real.log ((diagonalFiniteEntropyDensity 7 (by norm_num)).density y)))) x := by
  have h := diagonalFiniteEntropyDensity_curvature_of_cellwise 7 (by norm_num)
    dimension7_cellwise_from_complete_checker x hx0 hx1
  convert h using 1 <;> norm_num

end
end ENT.Pilot
