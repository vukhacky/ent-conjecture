module

public import ENT.Pilot.CrossBinomialN21To30Size32Part0
public import ENT.Certificate.PureFastSoundness
public import ENT.Spline.PureCertificateBridge
public import ENT.Spline.CurvatureData

/-! Complete actual spline curvature and potential comparison
from private certificate witnesses and unconditional soundness. -/

@[expose] public section
set_option autoImplicit false

open ENT.Certificate ENT.Spline MeasureTheory
namespace ENT.Pilot
noncomputable section

theorem dimension21_cellwise_checked : CellwiseCurvature 21 := by
  apply cellwiseCurvature_of_pure_family 21 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 10 := by omega
  interval_cases k
  · exact crossBinomialR21To30S32N21K1_exists
  · exact crossBinomialR21To30S32N21K2_exists
  · exact crossBinomialR21To30S32N21K3_exists
  · exact crossBinomialR21To30S32N21K4_exists
  · exact crossBinomialR21To30S32N21K5_exists
  · exact crossBinomialR21To30S32N21K6_exists
  · exact crossBinomialR21To30S32N21K7_exists
  · exact crossBinomialR21To30S32N21K8_exists
  · exact crossBinomialR21To30S32N21K9_exists
  · exact crossBinomialR21To30S32N21K10_exists

theorem dimension22_cellwise_checked : CellwiseCurvature 22 := by
  apply cellwiseCurvature_of_pure_family 22 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 10 := by omega
  interval_cases k
  · exact crossBinomialR21To30S32N22K1_exists
  · exact crossBinomialR21To30S32N22K2_exists
  · exact crossBinomialR21To30S32N22K3_exists
  · exact crossBinomialR21To30S32N22K4_exists
  · exact crossBinomialR21To30S32N22K5_exists
  · exact crossBinomialR21To30S32N22K6_exists
  · exact crossBinomialR21To30S32N22K7_exists
  · exact crossBinomialR21To30S32N22K8_exists
  · exact crossBinomialR21To30S32N22K9_exists
  · exact crossBinomialR21To30S32N22K10_exists

theorem dimension23_cellwise_checked : CellwiseCurvature 23 := by
  apply cellwiseCurvature_of_pure_family 23 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 11 := by omega
  interval_cases k
  · exact crossBinomialR21To30S32N23K1_exists
  · exact crossBinomialR21To30S32N23K2_exists
  · exact crossBinomialR21To30S32N23K3_exists
  · exact crossBinomialR21To30S32N23K4_exists
  · exact crossBinomialR21To30S32N23K5_exists
  · exact crossBinomialR21To30S32N23K6_exists
  · exact crossBinomialR21To30S32N23K7_exists
  · exact crossBinomialR21To30S32N23K8_exists
  · exact crossBinomialR21To30S32N23K9_exists
  · exact crossBinomialR21To30S32N23K10_exists
  · exact crossBinomialR21To30S32N23K11_exists

theorem cellwise_curvature_twentyone_through_twentythree
    (n : ℕ) (hn0 : 21 ≤ n) (hn1 : n ≤ 23) : CellwiseCurvature n := by
  interval_cases n
  · exact dimension21_cellwise_checked
  · exact dimension22_cellwise_checked
  · exact dimension23_cellwise_checked

theorem potential_expectation_twentyone_through_twentythree
    (n : ℕ) (hn0 : 21 ≤ n) (hn1 : n ≤ 23) (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential n x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential n x ∂projectionLaw (diagonal n) :=
  diagonalSplinePotential_expectation_le n (by omega)
    (cellwise_curvature_twentyone_through_twentythree n hn0 hn1) a ha

end
end ENT.Pilot
