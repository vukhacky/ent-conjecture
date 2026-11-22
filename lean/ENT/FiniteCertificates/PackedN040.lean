module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N040Part00
public import ENT.Pilot.KroneckerLiteData.N040Part01
public import ENT.Pilot.KroneckerLiteData.N040Part02
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_40 : PackedFamily 40 := by
  intro k hk0 hk2
  have hkmax : k ≤ 19 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n40k1_exists
  · exact ENT.Pilot.KroneckerData.n40k2_exists
  · exact ENT.Pilot.KroneckerData.n40k3_exists
  · exact ENT.Pilot.KroneckerData.n40k4_exists
  · exact ENT.Pilot.KroneckerData.n40k5_exists
  · exact ENT.Pilot.KroneckerData.n40k6_exists
  · exact ENT.Pilot.KroneckerData.n40k7_exists
  · exact ENT.Pilot.KroneckerData.n40k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k18_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n40k19_exists

end ENT.FiniteCertificates
