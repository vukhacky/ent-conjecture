module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerLiteData.N069Part00
public import ENT.Pilot.KroneckerLiteData.N069Part01
public import ENT.Pilot.KroneckerLiteData.N069Part02
public import ENT.Pilot.KroneckerLiteData.N069Part03
public import ENT.Pilot.KroneckerLiteData.N069Part04
public import ENT.Certificate.KroneckerLiteSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_69 : PackedFamily 69 := by
  intro k hk0 hk2
  have hkmax : k ≤ 34 := by omega
  interval_cases k
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k1_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k2_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k3_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k4_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k5_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k6_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k7_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k8_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k9_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k10_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k11_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k12_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k13_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k14_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k15_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k16_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k17_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k18_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k19_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k20_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k21_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k22_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k23_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k24_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k25_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k26_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k27_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k28_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k29_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k30_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k31_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k32_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k33_exists
  · exact Certificate.KroneckerLite.exists_valid_to_pure ENT.Pilot.KroneckerLiteData.n69k34_exists

end ENT.FiniteCertificates
