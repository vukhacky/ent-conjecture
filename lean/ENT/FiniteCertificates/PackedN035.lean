module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N035Part01
public import ENT.Pilot.KroneckerLiteData.N035Part00
public import ENT.Pilot.KroneckerLiteData.N035Part02
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_35 : PackedFamily 35 := by
  intro k hk0 hk2
  have hkmax : k ≤ 17 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k8_exists
  · exact ENT.Pilot.KroneckerData.n35k9_exists
  · exact ENT.Pilot.KroneckerData.n35k10_exists
  · exact ENT.Pilot.KroneckerData.n35k11_exists
  · exact ENT.Pilot.KroneckerData.n35k12_exists
  · exact ENT.Pilot.KroneckerData.n35k13_exists
  · exact ENT.Pilot.KroneckerData.n35k14_exists
  · exact ENT.Pilot.KroneckerData.n35k15_exists
  · exact ENT.Pilot.KroneckerData.n35k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n35k17_exists

end ENT.FiniteCertificates
