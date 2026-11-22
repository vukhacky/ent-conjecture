module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerSplineData.N092Part00
public import ENT.Pilot.KroneckerSplineData.N092Part01
public import ENT.Pilot.KroneckerSplineData.N092Part02
public import ENT.Pilot.KroneckerSplineData.N092Part03
public import ENT.Pilot.KroneckerSplineData.N092Part04
public import ENT.Pilot.KroneckerSplineData.N092Part05
public import ENT.Certificate.KroneckerSplineSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_92 : PackedFamily 92 := by
  intro k hk0 hk2
  have hkmax : k ≤ 45 := by omega
  interval_cases k
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k1_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k2_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k3_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k4_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k5_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k6_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k7_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k8_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k9_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k10_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k11_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k12_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k13_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k14_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k15_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k16_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k17_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k18_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k19_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k20_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k21_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k22_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k23_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k24_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k25_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k26_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k27_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k28_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k29_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k30_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k31_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k32_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k33_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k34_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k35_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k36_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k37_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k38_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k39_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k40_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k41_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k42_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k43_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k44_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n92k45_exists

end ENT.FiniteCertificates
