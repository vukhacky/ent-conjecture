module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N032Part00
public import ENT.Pilot.KroneckerData.N032Part01

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_32 : PackedFamily 32 := by
  intro k hk0 hk2
  have hkmax : k ≤ 15 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n32k1_exists
  · exact ENT.Pilot.KroneckerData.n32k2_exists
  · exact ENT.Pilot.KroneckerData.n32k3_exists
  · exact ENT.Pilot.KroneckerData.n32k4_exists
  · exact ENT.Pilot.KroneckerData.n32k5_exists
  · exact ENT.Pilot.KroneckerData.n32k6_exists
  · exact ENT.Pilot.KroneckerData.n32k7_exists
  · exact ENT.Pilot.KroneckerData.n32k8_exists
  · exact ENT.Pilot.KroneckerData.n32k9_exists
  · exact ENT.Pilot.KroneckerData.n32k10_exists
  · exact ENT.Pilot.KroneckerData.n32k11_exists
  · exact ENT.Pilot.KroneckerData.n32k12_exists
  · exact ENT.Pilot.KroneckerData.n32k13_exists
  · exact ENT.Pilot.KroneckerData.n32k14_exists
  · exact ENT.Pilot.KroneckerData.n32k15_exists

end ENT.FiniteCertificates
