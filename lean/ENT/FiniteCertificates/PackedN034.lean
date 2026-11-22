module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerData.N034Part00
public import ENT.Pilot.KroneckerData.N034Part01

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_34 : PackedFamily 34 := by
  intro k hk0 hk2
  have hkmax : k ≤ 16 := by omega
  interval_cases k
  · exact ENT.Pilot.KroneckerData.n34k1_exists
  · exact ENT.Pilot.KroneckerData.n34k2_exists
  · exact ENT.Pilot.KroneckerData.n34k3_exists
  · exact ENT.Pilot.KroneckerData.n34k4_exists
  · exact ENT.Pilot.KroneckerData.n34k5_exists
  · exact ENT.Pilot.KroneckerData.n34k6_exists
  · exact ENT.Pilot.KroneckerData.n34k7_exists
  · exact ENT.Pilot.KroneckerData.n34k8_exists
  · exact ENT.Pilot.KroneckerData.n34k9_exists
  · exact ENT.Pilot.KroneckerData.n34k10_exists
  · exact ENT.Pilot.KroneckerData.n34k11_exists
  · exact ENT.Pilot.KroneckerData.n34k12_exists
  · exact ENT.Pilot.KroneckerData.n34k13_exists
  · exact ENT.Pilot.KroneckerData.n34k14_exists
  · exact ENT.Pilot.KroneckerData.n34k15_exists
  · exact ENT.Pilot.KroneckerData.n34k16_exists

end ENT.FiniteCertificates
