module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerSplineData.N094Part00
public import ENT.Pilot.KroneckerSplineData.N094Part01
public import ENT.Pilot.KroneckerSplineData.N094Part02
public import ENT.Pilot.KroneckerSplineData.N094Part03
public import ENT.Pilot.KroneckerSplineData.N094Part04
public import ENT.Pilot.KroneckerSplineData.N094Part05
public import ENT.Certificate.KroneckerSplineSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_94 : PackedFamily 94 := by
  intro k hk0 hk2
  have hkmax : k ≤ 46 := by omega
  interval_cases k
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k1_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k2_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k3_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k4_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k5_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k6_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k7_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k8_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k9_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k10_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k11_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k12_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k13_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k14_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k15_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k16_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k17_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k18_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k19_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k20_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k21_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k22_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k23_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k24_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k25_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k26_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k27_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k28_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k29_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k30_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k31_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k32_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k33_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k34_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k35_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k36_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k37_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k38_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k39_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k40_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k41_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k42_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k43_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k44_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k45_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n94k46_exists

end ENT.FiniteCertificates
