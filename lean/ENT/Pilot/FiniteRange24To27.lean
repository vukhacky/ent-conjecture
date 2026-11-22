module

public import ENT.Pilot.CrossBinomialN24To30Size16Part0
public import ENT.Pilot.CrossBinomialN24To30Size16Part1
public import ENT.Pilot.CrossBinomialN24To30Size16Part2
public import ENT.Certificate.PureFastSoundness
public import ENT.Spline.PureCertificateBridge
public import ENT.Spline.CurvatureData

/-! Combines the cell certificates for dimensions 24–27. -/

@[expose] public section
set_option autoImplicit false
open ENT.Certificate ENT.Spline MeasureTheory
namespace ENT.Pilot
noncomputable section

private theorem FiniteRange24To27_dimension24 : CellwiseCurvature 24 := by
  apply cellwiseCurvature_of_pure_family 24 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 11 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N24K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N24K11_exists

private theorem FiniteRange24To27_dimension25 : CellwiseCurvature 25 := by
  apply cellwiseCurvature_of_pure_family 25 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 12 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N25K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K11_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N25K12_exists

private theorem FiniteRange24To27_dimension26 : CellwiseCurvature 26 := by
  apply cellwiseCurvature_of_pure_family 26 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 12 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N26K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K11_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N26K12_exists

private theorem FiniteRange24To27_dimension27 : CellwiseCurvature 27 := by
  apply cellwiseCurvature_of_pure_family 27 (by decide) ENT.Certificate.PureFast.fastCheckCell ENT.Certificate.PureFast.fastCheckCell_sound
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 13 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N27K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K11_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K12_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N27K13_exists

theorem FiniteRange24To27_cellwise (n : ℕ) (hn0 : 24 ≤ n) (hn1 : n ≤ 27) :
    CellwiseCurvature n := by
  interval_cases n
  · exact FiniteRange24To27_dimension24
  · exact FiniteRange24To27_dimension25
  · exact FiniteRange24To27_dimension26
  · exact FiniteRange24To27_dimension27

theorem FiniteRange24To27_expectation (n : ℕ) (hn0 : 24 ≤ n) (hn1 : n ≤ 27)
    (a : Fin n → ℝ) (ha : IsUnit a) :
    (∫ x, diagonalSplinePotential n x ∂projectionLaw a) ≤
      ∫ x, diagonalSplinePotential n x ∂projectionLaw (diagonal n) :=
  diagonalSplinePotential_expectation_le n (by omega)
    (FiniteRange24To27_cellwise n hn0 hn1) a ha

end
end ENT.Pilot
