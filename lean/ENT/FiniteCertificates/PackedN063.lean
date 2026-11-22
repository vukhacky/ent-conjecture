module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerLiteData.N063Part00
public import ENT.Pilot.KroneckerLiteData.N063Part01
public import ENT.Pilot.KroneckerLiteData.N063Part02
public import ENT.Pilot.KroneckerLiteData.N063Part03
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_63 : PackedFamily 63 := by
  intro k hk0 hk2
  have hkmax : k ≤ 31 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k18_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k19_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k20_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k21_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k22_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k23_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k24_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k25_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k26_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k27_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k28_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k29_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k30_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n63k31_exists

end ENT.FiniteCertificates
