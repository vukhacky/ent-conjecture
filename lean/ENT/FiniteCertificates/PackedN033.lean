module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N033Part00
public import ENT.Pilot.KroneckerData.N033Part01

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_33 : PackedFamily 33 := by
  intro k hk0 hk2
  have hkmax : k ≤ 16 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n33k1_exists
  · exact ENT.Pilot.KroneckerData.n33k2_exists
  · exact ENT.Pilot.KroneckerData.n33k3_exists
  · exact ENT.Pilot.KroneckerData.n33k4_exists
  · exact ENT.Pilot.KroneckerData.n33k5_exists
  · exact ENT.Pilot.KroneckerData.n33k6_exists
  · exact ENT.Pilot.KroneckerData.n33k7_exists
  · exact ENT.Pilot.KroneckerData.n33k8_exists
  · exact ENT.Pilot.KroneckerData.n33k9_exists
  · exact ENT.Pilot.KroneckerData.n33k10_exists
  · exact ENT.Pilot.KroneckerData.n33k11_exists
  · exact ENT.Pilot.KroneckerData.n33k12_exists
  · exact ENT.Pilot.KroneckerData.n33k13_exists
  · exact ENT.Pilot.KroneckerData.n33k14_exists
  · exact ENT.Pilot.KroneckerData.n33k15_exists
  · exact ENT.Pilot.KroneckerData.n33k16_exists

end ENT.FiniteCertificates
