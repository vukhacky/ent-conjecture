module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerLiteData.N065Part00
public import ENT.Pilot.KroneckerLiteData.N065Part01
public import ENT.Pilot.KroneckerLiteData.N065Part02
public import ENT.Pilot.KroneckerLiteData.N065Part03
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_65 : PackedFamily 65 := by
  intro k hk0 hk2
  have hkmax : k ≤ 32 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k18_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k19_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k20_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k21_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k22_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k23_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k24_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k25_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k26_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k27_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k28_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k29_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k30_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k31_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n65k32_exists

end ENT.FiniteCertificates
