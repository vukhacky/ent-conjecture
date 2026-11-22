module

public import ENT.FiniteCertificates.PackedFamily
public import Mathlib.Tactic.IntervalCases
public import ENT.Pilot.KroneckerSplineData.N085Part00
public import ENT.Pilot.KroneckerSplineData.N085Part01
public import ENT.Pilot.KroneckerSplineData.N085Part02
public import ENT.Pilot.KroneckerSplineData.N085Part03
public import ENT.Pilot.KroneckerSplineData.N085Part04
public import ENT.Pilot.KroneckerSplineData.N085Part05
public import ENT.Certificate.KroneckerSplineSoundness

@[expose] public section
set_option autoImplicit false

namespace ENT.FiniteCertificates

theorem family_packed_85 : PackedFamily 85 := by
  intro k hk0 hk2
  have hkmax : k ≤ 42 := by omega
  interval_cases k
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k1_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k2_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k3_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k4_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k5_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k6_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k7_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k8_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k9_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k10_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k11_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k12_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k13_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k14_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k15_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k16_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k17_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k18_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k19_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k20_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k21_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k22_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k23_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k24_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k25_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k26_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k27_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k28_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k29_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k30_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k31_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k32_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k33_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k34_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k35_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k36_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k37_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k38_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k39_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k40_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k41_exists
  · exact Certificate.KroneckerSpline.exists_valid_to_pure ENT.Pilot.KroneckerSplineData.n85k42_exists

end ENT.FiniteCertificates
