module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerLiteData.N041Part00
public import ENT.Pilot.KroneckerLiteData.N041Part01
public import ENT.Pilot.KroneckerLiteData.N041Part02
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_41 : PackedFamily 41 := by
  intro k hk0 hk2
  have hkmax : k ≤ 20 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k18_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k19_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n41k20_exists

end ENT.FiniteCertificates
