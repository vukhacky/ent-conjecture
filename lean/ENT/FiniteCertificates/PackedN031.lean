module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N031Part00
public import ENT.Pilot.KroneckerData.N031Part01

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_31 : PackedFamily 31 := by
  intro k hk0 hk2
  have hkmax : k ≤ 15 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n31k1_exists
  · exact ENT.Pilot.KroneckerData.n31k2_exists
  · exact ENT.Pilot.KroneckerData.n31k3_exists
  · exact ENT.Pilot.KroneckerData.n31k4_exists
  · exact ENT.Pilot.KroneckerData.n31k5_exists
  · exact ENT.Pilot.KroneckerData.n31k6_exists
  · exact ENT.Pilot.KroneckerData.n31k7_exists
  · exact ENT.Pilot.KroneckerData.n31k8_exists
  · exact ENT.Pilot.KroneckerData.n31k9_exists
  · exact ENT.Pilot.KroneckerData.n31k10_exists
  · exact ENT.Pilot.KroneckerData.n31k11_exists
  · exact ENT.Pilot.KroneckerData.n31k12_exists
  · exact ENT.Pilot.KroneckerData.n31k13_exists
  · exact ENT.Pilot.KroneckerData.n31k14_exists
  · exact ENT.Pilot.KroneckerData.n31k15_exists

end ENT.FiniteCertificates
