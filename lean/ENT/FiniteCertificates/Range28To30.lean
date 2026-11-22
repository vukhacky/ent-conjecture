module

public import ENT.Certificate.Family
public import ENT.Certificate.PureFast
public import ENT.Pilot.CrossBinomialN24To30Size16Part3
public import ENT.Pilot.CrossBinomialN24To30Size16Part4
public import ENT.Pilot.CrossBinomialN24To30Size16Part5
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option autoImplicit false
open ENT.Certificate ENT.Spline
namespace ENT.FiniteCertificates

theorem family_28 : PureCellFamily PureFast.fastCheckCell 28 := by
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 13 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N28K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K11_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K12_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N28K13_exists

theorem family_29 : PureCellFamily PureFast.fastCheckCell 29 := by
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 14 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N29K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K11_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K12_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K13_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N29K14_exists

theorem family_30 : PureCellFamily PureFast.fastCheckCell 30 := by
  intro k hkpos hk
  have hkmin : 1 ≤ k := by omega
  have hkmax : k ≤ 14 := by omega
  interval_cases k
  · exact ENT.Pilot.crossBinomialR24To30S16N30K1_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K2_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K3_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K4_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K5_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K6_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K7_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K8_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K9_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K10_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K11_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K12_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K13_exists
  · exact ENT.Pilot.crossBinomialR24To30S16N30K14_exists

theorem family_28_30 (n : ℕ) (hn0 : 28 ≤ n) (hn1 : n ≤ 30) :
    PureCellFamily PureFast.fastCheckCell n := by
  interval_cases n
  · exact family_28
  · exact family_29
  · exact family_30

end ENT.FiniteCertificates
