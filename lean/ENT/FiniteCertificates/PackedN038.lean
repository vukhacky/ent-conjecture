module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N038Part00
public import ENT.Pilot.KroneckerData.N038Part02
public import ENT.Pilot.KroneckerLiteData.N038Part01
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_38 : PackedFamily 38 := by
  intro k hk0 hk2
  have hkmax : k ≤ 18 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n38k1_exists
  · exact ENT.Pilot.KroneckerData.n38k2_exists
  · exact ENT.Pilot.KroneckerData.n38k3_exists
  · exact ENT.Pilot.KroneckerData.n38k4_exists
  · exact ENT.Pilot.KroneckerData.n38k5_exists
  · exact ENT.Pilot.KroneckerData.n38k6_exists
  · exact ENT.Pilot.KroneckerData.n38k7_exists
  · exact ENT.Pilot.KroneckerData.n38k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n38k16_exists
  · exact ENT.Pilot.KroneckerData.n38k17_exists
  · exact ENT.Pilot.KroneckerData.n38k18_exists

end ENT.FiniteCertificates
