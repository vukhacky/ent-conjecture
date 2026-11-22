module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N036Part00
public import ENT.Pilot.KroneckerData.N036Part02
public import ENT.Pilot.KroneckerLiteData.N036Part01
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_36 : PackedFamily 36 := by
  intro k hk0 hk2
  have hkmax : k ≤ 17 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n36k1_exists
  · exact ENT.Pilot.KroneckerData.n36k2_exists
  · exact ENT.Pilot.KroneckerData.n36k3_exists
  · exact ENT.Pilot.KroneckerData.n36k4_exists
  · exact ENT.Pilot.KroneckerData.n36k5_exists
  · exact ENT.Pilot.KroneckerData.n36k6_exists
  · exact ENT.Pilot.KroneckerData.n36k7_exists
  · exact ENT.Pilot.KroneckerData.n36k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n36k16_exists
  · exact ENT.Pilot.KroneckerData.n36k17_exists

end ENT.FiniteCertificates
