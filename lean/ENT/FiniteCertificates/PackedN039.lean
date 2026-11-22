module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N039Part01
public import ENT.Pilot.KroneckerLiteData.N039Part00
public import ENT.Pilot.KroneckerLiteData.N039Part02
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_39 : PackedFamily 39 := by
  intro k hk0 hk2
  have hkmax : k ≤ 19 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k8_exists
  · exact ENT.Pilot.KroneckerData.n39k9_exists
  · exact ENT.Pilot.KroneckerData.n39k10_exists
  · exact ENT.Pilot.KroneckerData.n39k11_exists
  · exact ENT.Pilot.KroneckerData.n39k12_exists
  · exact ENT.Pilot.KroneckerData.n39k13_exists
  · exact ENT.Pilot.KroneckerData.n39k14_exists
  · exact ENT.Pilot.KroneckerData.n39k15_exists
  · exact ENT.Pilot.KroneckerData.n39k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k18_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n39k19_exists

end ENT.FiniteCertificates
