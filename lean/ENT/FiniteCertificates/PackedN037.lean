module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N037Part01
public import ENT.Pilot.KroneckerLiteData.N037Part00
public import ENT.Pilot.KroneckerLiteData.N037Part02
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_37 : PackedFamily 37 := by
  intro k hk0 hk2
  have hkmax : k ≤ 18 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k8_exists
  · exact ENT.Pilot.KroneckerData.n37k9_exists
  · exact ENT.Pilot.KroneckerData.n37k10_exists
  · exact ENT.Pilot.KroneckerData.n37k11_exists
  · exact ENT.Pilot.KroneckerData.n37k12_exists
  · exact ENT.Pilot.KroneckerData.n37k13_exists
  · exact ENT.Pilot.KroneckerData.n37k14_exists
  · exact ENT.Pilot.KroneckerData.n37k15_exists
  · exact ENT.Pilot.KroneckerData.n37k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n37k18_exists

end ENT.FiniteCertificates
